(* jsCoq
 *
 * Copyright (C) 2016-2019 Emilio J. Gallego Arias, Mines ParisTech, Paris.
 * Copyright (C) 2018-2022 Shachar Itzhaky, Technion - Israel Institute of Technology
 * Copyright (C) 2019-2022 Emilio J. Gallego Arias, INRIA
 *)

(* Inspection subroutines *)

module Qualified_object_prefix = struct
  type t =
    { dp: Names.DirPath.t
    ; mod_ids: Names.Id.t list
    }

  let of_mp mp =
    let dp, mod_ids = Lib.split_modpath mp in {dp; mod_ids}

  let of_dp dp = {dp; mod_ids = []}

end

module Qualified_name = struct

  type t =
    { prefix: Qualified_object_prefix.t
    ; basename: Names.Id.t
    }

  let of_kn kn =
    let mp, l = Names.KerName.repr kn in
    { prefix = Qualified_object_prefix.of_mp mp; basename = Names.Label.to_id l}

  let of_constant c = of_kn (Names.Constant.user c)

  let of_full_path fp =
    let (dp, id) = Libnames.repr_path fp in
    {prefix = Qualified_object_prefix.of_dp dp; basename = id}

  let to_string qn =
    let {prefix = {dp; mod_ids}; basename} = qn in (* todo use `ids` as well *)
    let dp = match Names.DirPath.repr dp with
      | [] -> [] | _ -> [Names.DirPath.to_string dp] in
    String.concat "." (dp @ (List.map Names.Id.to_string mod_ids) @ [Names.Id.to_string basename])

end

(* Get constants in global scope *)
let inspect_globals ~env () =
  let global_consts = List.to_seq @@
      Environ.fold_constants (fun name _ l -> name :: l) env [] in
  Seq.map Qualified_name.of_constant global_consts

let lookup_inductive env mi =
  let open Declarations in
  try
    let defn_body = Environ.lookup_mind mi env in
    Array.to_seq defn_body.mind_packets
      |> Seq.flat_map (fun p -> Seq.cons p.mind_typename
          (Array.to_seq p.mind_consnames))
  with Not_found -> Seq.empty

let lookup_inductive_mp env mp id =
  lookup_inductive env (Names.MutInd.make2 mp (Names.Label.of_id id))

(* from `prettyp.ml` *)
module DynHandle = Libobject.Dyn.Map(struct type 'a t = 'a -> Names.Id.t Seq.t end)
let handle (Libobject.Dyn.Dyn (tag, o)) h dft =
  match DynHandle.find tag h with
  | f -> f o
  | exception Not_found -> dft

let names_of_libobj env mp lobj =
  let case_const = DynHandle.add Declare.Internal.Constant.tag in
  let case_ind = DynHandle.add DeclareInd.Internal.objInductive in
  match lobj with
  | Libobject.AtomicObject o ->
    handle o (
      case_const (fun (id,_) -> [id] |> List.to_seq)             @@
      case_ind   (fun (id,_) -> lookup_inductive_mp env mp id)   @@
      DynHandle.empty
    ) Seq.empty
  | _ -> Seq.empty


let find_definitions env (node, objs) =
  let open Nametab in
  let dp = (Lib.node_prefix node).obj_dir in
  let mp = (Lib.node_prefix node).Nametab.obj_mp in
  List.to_seq objs
    |> Seq.flat_map (fun o -> names_of_libobj env mp o)
    |> Seq.map (fun nm -> Libnames.make_path dp nm)

(* Get definitions in current module *)
let inspect_library ~env () =
  let ls = Lib.contents () in
  Seq.flat_map (find_definitions env) (List.to_seq ls)
    |> Seq.map Qualified_name.of_full_path

(* Get local names in proof context *)
let inspect_locals ~env ?(dir_path=Names.DirPath.empty) () =
  let named_ctx = Environ.named_context env in
  List.to_seq (Context.Named.to_vars named_ctx |> Names.Id.Set.elements) |>
    Seq.map (Libnames.make_path dir_path)
    |> Seq.map Qualified_name.of_full_path

module Query = struct
  type t =
    | All
    | CurrentFile
    | ModulePrefix of Serlib.Ser_names.DirPath.t
    | Keyword of string
    | Locals

end

let string_contains s1 s2 =  (* from Rosetta Code *)
  let len1 = String.length s1
  and len2 = String.length s2 in
  if len1 < len2 then false else
    let rec aux i =
      (i >= 0) && ((String.sub s1 i len2 = s2) || aux (pred i))
    in
    aux (len1 - len2)

let all_symbols_for env (q : Query.t) =
  match q with
  | Locals       ->
    inspect_locals ~env ()
  | CurrentFile  ->
    Seq.append
      (inspect_library ~env ())
      (inspect_locals  ~env ())
  | _ ->
    inspect_globals ~env ()

let is_within qn prefix =
  let {Qualified_name.prefix = {dp}} = qn in
  Libnames.is_dirpath_prefix_of prefix dp

let filter_by (q : Query.t) =
  match q with
  | All | CurrentFile | Locals ->
    (fun _ -> true)
  | ModulePrefix prefix ->
    (fun nm -> is_within nm prefix)
  | Keyword s ->
    (fun nm -> string_contains (Qualified_name.to_string nm) s)

let symbols_for env q = all_symbols_for env q |> Seq.filter (filter_by q)
