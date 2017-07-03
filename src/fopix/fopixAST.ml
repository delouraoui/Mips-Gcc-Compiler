(** The abstract syntax tree for fopix programs. *)

open Position

type program = definition list

and definition =
  | DefineValue      of identifier * expression
  | DefineFunction   of function_identifier * formals * expression
  | ExternalFunction of function_identifier

and expression =
  | Literal of literal
  | Variable of identifier
  | Define of identifier * expression * expression
  | FunCall of function_identifier * expression list
  | IfThenElse of expression * expression * expression
  | UnknownFunCall of expression * expression list
  | Switch of expression * expression array * expression option

and literal =
  | LInt    of Int32.t
  | LString of string
  | LChar   of char
  | LBool   of bool
  | LFun    of function_identifier

and identifier =
  | Id of string

and formals =
    identifier list

and function_identifier =
  | FunId of string

and t = program
