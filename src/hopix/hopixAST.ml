(** The abstract syntax tree for hopix programs. *)

open Position

(** A program is a list of definitions. *)
type program = definition located list

and definition =
  (** A toplevel declaration for an external value. *)
  | DeclareExtern of identifier located * ty located
  (** A toplevel definition for a value. *)
  | DefineValue of identifier located * expression located
  (** A toplevel definition for mutually recursive values. *)
  | DefineRecValue of (identifier located * expression located) list
  (** A type definition. *)
  | DefineType of type_constructor located * type_variable located list * type_definition

and type_definition =
  (** A sum type for tagged values [{ K₁ : ty₁₁ * ... * ty₁ₙ | ... | Kₙ : tyₙ₁ * ... * tyₘₖ}]. *)
  | DefineSumType of (constructor located * ty located list) list
  (** A record type [{ l₁ : ty₁; ...; l₂ : ty₂ }]. *)
  | DefineRecordType of (label located * ty located) list
  (** A type with no visible definition. *)
  | Abstract

and expression =
  (** A literal is a constant written "as is". *)
  | Literal of literal located
  (** A variable identifies a value. *)
  | Variable of identifier located
  (** A local definition [val x₁ := e₁ ; e₂]. *)
  | Define of identifier located * expression located * expression located
  (** Local mutually recursive values [rec x₁ := e₁ and ... and xₙ := eₙ; e]. *)
  | DefineRec of (identifier located * expression located) list * expression located
  (** A function application [a b]. *)
  | Apply of expression located * expression located
  (** A conditional expression of the form [if ... then ... else ... fi]. *)
  | IfThenElse of expression located * expression located * expression located
  (** An anonymous function [ \ p => e ]. *)
  | Fun of pattern located * expression located
  (** A tagged value [K (e_1, ..., e_n)]. *)
  | Tagged of constructor located * expression located list
  (** A pattern matching [e ? p_1 => e_1 | ... | p_n => e_n]. *)
  | Case of expression located * branch located list
  (** A type annotation [(e : ty)]. *)
  | TypeAnnotation of expression located * ty located
  (** A record [{l₁ := e₁; ...; lₙ := eₙ}]. *)
  | Record of (label located * expression located) list
  (** A record field access [e.l]. *)
  | Field of expression located * label located
  (** A record field mutation [e.l <- e]. *)
  | ChangeField of expression located * label located * expression located

and pattern =
  (** A pattern with a type annotation of type form [p : ty] *)
  | PTypeAnnotation of pattern located * ty located
  (** A pattern which is simply an identifier. *)
  | PVariable of identifier located
  (** A pattern for a tagged value [K (p_1, ..., p_n)]. *)
  | PTaggedValue of constructor located * pattern located list
  (** A wildcard pattern [_]. *)
  | PWildcard
  (** A literal pattern. *)
  | PLiteral of literal located
  (** A pattern for a record [{ l_1 = p_1; ...; l_n = p_n}]. *)
  | PRecord of (label located * pattern located) list
  (** A disjunctive pattern [ p₁ | ... | pₙ ]. *)
  | POr of pattern located list
  (** A conjunctive pattern [ p₁ & ... & pₙ ]. *)
  | PAnd of pattern located list

and branch =
  (** A branch in a pattern matching [p => e]. *)
  | Branch of pattern located * expression located

and ty =
  (** An instantiated type constructor [t [ty_1, .., ty_2]]. *)
  | TyCon of type_constructor * ty located list
  
  (** A type variable ['a]. *)
  | TyVar of type_variable

and literal =
  | LInt    of Int32.t
  | LString of string
  | LChar   of char
  | LBool   of bool

and identifier =
  | Id of string

and type_constructor =
  | TCon of string

and type_variable =
  | TId of string

and constructor =
  | KId of string

and label =
  | LId of string

and t = program


let rec split_or_pattern = ListMonad.(function
  | POr ps ->
    pick ps >>= fun p ->
    located split_or_pattern p
  | PTypeAnnotation (p, _) ->
    located split_or_pattern p
  | PTaggedValue (k, ps) ->
    split_or_patterns ps >>= fun ps ->
    return (PTaggedValue (k, ps))
  | PRecord fs ->
    let ls, ps = List.split fs in
    split_or_patterns ps >>= fun ps ->
    return (PRecord (List.combine ls ps))
  | PAnd ps ->
    split_or_patterns ps >>= fun ps ->
    return (PAnd ps)
  | (PVariable _ | PWildcard | PLiteral _) as p ->
    return p
)

and split_or_patterns = ListMonad.(function
  | [] ->
    return []
  | p :: ps ->
    let pos = Position.position p in
    located split_or_pattern p >>= fun p ->
    split_or_patterns ps >>= fun ps ->
    return (Position.with_pos pos p :: ps)
)

