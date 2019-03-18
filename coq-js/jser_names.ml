
module Names = struct
  module Id = struct
    include Names.Id
    let to_yojson x = `String (Names.Id.to_string x)
  end
  module Name = struct
    include Names.Name
    type _t = [%import: Names.Name.t] [@@deriving to_yojson]
    let to_yojson = _t_to_yojson
  end
  module DirPath = struct
    include Names.DirPath
    let to_yojson x = `List (List.map Id.to_yojson (repr x))
  end
  module MBId = struct
    include Names.MBId
    type _t = MBId of int * Id.t * DirPath.t [@@deriving to_yojson]
    let to_yojson x = 
      let (i, id, dp) = repr x in
      _t_to_yojson @@ MBId (i, id, dp)
  end
  module Label = struct
    include Names.Label
    let to_yojson x = `String (to_string x)
  end
  module ModPath = struct
    include Names.ModPath
    type _t = [%import: Names.ModPath.t] [@@deriving to_yojson]
    let to_yojson = _t_to_yojson
  end
  module KerName = struct
    include Names.KerName
    type _t = KerName of ModPath.t * Label.t [@@deriving to_yojson]
    let to_yojson x = 
      let mp, l = repr x in
      _t_to_yojson @@ KerName (mp, l)
  end
  module Constant = struct 
    include Names.Constant
    type _t = Constant of KerName.t * KerName.t [@@deriving to_yojson]
    let to_yojson x = _t_to_yojson @@ Constant (user x, canonical x)
  end
  module MutInd = struct 
    include Names.MutInd
    type _t = MutInd of KerName.t * KerName.t [@@deriving to_yojson]
    let to_yojson x = _t_to_yojson @@ MutInd (user x, canonical x)
  end
  module Projection = struct 
    include Names.Projection
    type _t = Projection of Constant.t * bool [@@deriving to_yojson]
    let to_yojson x = _t_to_yojson @@ Projection (constant x, unfolded x)
  end
  type inductive = [%import: Names.inductive] [@@deriving to_yojson]
  type constructor = [%import: Names.constructor] [@@deriving to_yojson]
  type variable = [%import: Names.variable] [@@deriving to_yojson]
  (* type global_reference = [%import: Names.global_reference] [@@deriving to_yojson] *)

  module MPmap = Names.MPmap
end


type 'a seq = 'a Seq.t

let seq_to_yojson f s = `List (Seq.fold_left (fun l x -> f x :: l) [] s |> List.rev)
