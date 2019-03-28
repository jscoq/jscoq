open Jser_names

type 'a hyp =
  [%import: 'a Serapi_goals.hyp]
  [@@deriving to_yojson]

type 'a reified_goal =
  [%import: 'a Serapi_goals.reified_goal]
  [@@deriving to_yojson]

type 'a pre_goals =
  [%import: 'a Proof.pre_goals]
  [@@deriving to_yojson]

