
open Form

type smtlib_answer =
  | SmtSat
  | SmtUnsat
  | SmtUnknown
  | SmtModel of Model.model
  | SmtError of string
