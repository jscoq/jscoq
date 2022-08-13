(* jsCoq
 *
 * Copyright (C) 2016-2019 Emilio J. Gallego Arias, Mines ParisTech, Paris.
 * Copyright (C) 2018-2022 Shachar Itzhaky, Technion - Israel Institute of Technology
 * Copyright (C) 2019-2022 Emilio J. Gallego Arias, INRIA
 *)

module Qualified_object_prefix : sig
  type t =
    { dp: Names.DirPath.t
    ; mod_ids: Names.Id.t list
    }
end

module Qualified_name : sig
  type t =
    { prefix: Qualified_object_prefix.t
    ; basename: Names.Id.t
    }
  val to_string : t -> string
end

module Query : sig
  type t =
    | All
    | CurrentFile
    | ModulePrefix of Serlib.Ser_names.DirPath.t
    | Keyword of string
    | Locals
end

(* XXX: Document *)
val symbols_for : Environ.env -> Query.t -> Qualified_name.t Seq.t

(* XXX: Document *)
val filter_by : Query.t -> Qualified_name.t -> bool
