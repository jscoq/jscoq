open Jser_names
open Jser_feedback

type 'a hyp =
  [%import: 'a Serapi_goals.hyp]
  [@@deriving to_yojson]

type 'a reified_goal =
  [%import: 'a Serapi_goals.reified_goal]
  [@@deriving to_yojson]

type 'a ser_goals =
  [%import: 'a Serapi_goals.ser_goals]
  [@@deriving to_yojson]
