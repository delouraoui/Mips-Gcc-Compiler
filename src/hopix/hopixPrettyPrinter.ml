open PPrint
open PPrintCombinators
open PPrintEngine
open ExtPPrint
open HopixAST
open Position

let int i = string (Int32.to_string i)

let gtype_definition sep what ks =
    string ":=" ++ group (
      string "{"
      ++ separate_map (break 1 ^^ string sep ^^ break 1) what ks
      ++ string "}"
    )

let rec program p =
  separate_map hardline (located definition) p

and definition = function
  | DefineValue (x, e) ->
    group (value_definition "val" (x, e) ^^ string ".")
  | DefineRecValue rv ->
    group (string "rec" ++ separate_map (hardline ^^ string "and") (value_definition "") rv)
    ^^ string "."
  | DeclareExtern (x, t) ->
    group (string "extern" ++ located identifier x ++ string ":" ++ located ty t ^^ string ".")
  | DefineType (t, ts, tdef) ->
    nest 2 (
      group (group (string "type"
		    ++ located type_constructor t
		    ^^ group (type_parameters ts))
	     ++ group (type_definition tdef))
      ^^ string "."
    )

and type_parameters = function
  | [] ->
    empty
  | ts ->
    string "["
    ++ separate_map (comma ^^ break 1) (located type_variable) ts
    ++ string "]"

and type_definition = function
  | DefineSumType ks ->
    gtype_definition "|" dataconstructor_definition ks
  | DefineRecordType fs ->
    gtype_definition ";" field_definition fs
  | Abstract ->
    empty

and field_definition (l, t) =
  located label l ++ string ":" ++ located ty t

and label (LId s) =
  string s

and dataconstructor_definition (k, tys) =
  match tys with
    | [] ->
      located dataconstructor k
    | _ ->
      located dataconstructor k
      ++ string ":"
      ++ separate_map (break 1 ^^ string "*" ^^ break 1) (located ty) tys

and dataconstructor (KId k) =
  string k

and value_definition what (x, e) =
  nest 2 (group (group (string what ++ located identifier x ++ string ":=")
		 ++ group (located expression e)))

and ty t = match t with
  | TyCon (TCon "->", [a; b]) ->
    group (located (mayparen_ty t) a ++ string "->" ++ located ty b)
  | TyCon (tcon, []) ->
    type_constructor tcon
  | TyCon (tcon, tys) ->
    group (type_constructor tcon
	   ++ string "["
	   ++ separate_map (string "," ^^ break 1) (located ty) tys
	   ++ string "]")
  | TyVar tvar ->
    type_variable tvar

and mayparen_ty ctx a =
  match ctx, a with
    | TyCon (TCon "->", _), TyCon (TCon "->", _) ->
      parens (ty a)
    | _, _ ->
      ty a

and type_constructor (TCon s) =
  string s

and type_variable (TId x) =
  string x

and identifier (Id x) =
  string x

and expression = function
  | Literal l ->
    located literal l

  | Variable x ->
    located identifier x

  | TypeAnnotation (e, t) ->
    parens (located expression e ++ group (string ":" ++ located ty t))

  | Define (x, e1, e2) ->
    nest 2 (
      group (value_definition "val" (x, e1) ^^ string ";"
    ))
    ++ group (located expression e2)

  | DefineRec (vs, e) ->
    nest 2 (group (
      string "rec"
      ++ separate_map (break 1 ^^ string "and" ^^ break 1) (value_definition "") vs
      ^^ string ";"
    )) ++ group (located expression e)

  | Fun (p, e) ->
    nest 2 (group (
      group (string "\\" ^^ located pattern p ++ string "=>") ++
	group (located expression e)
    ))

  | Apply (a, b) -> 
    group (
      parens_at_left_of_application a (located expression a)
      ++ parens_at_right_of_application b (located expression b)
    )

  | IfThenElse (c, t, f) ->
    nest 2 (group (
      group (string "if"
             ++ group (located expression c)
             ++ string "then"
      )
      ++ group (located expression t)
    ))
    ++ nest 2 (group (
      string "else"
      ++ group (located expression f)
      ++ string "fi"
    ))

  | Tagged (k, []) ->
    located dataconstructor k

  | Tagged (k, es) ->
    group (
      located dataconstructor k
      ++ parens (separate_map (comma ^^ break 1) (located expression) es)
    )

  | Case (e, bs) ->
    group (
      group (located expression e ++ string "?")
      ++ group (
	string "{"
	++ separate_map (break 1) (located branch) bs
	++ string "}")
    )

  | Record fs ->
    string "{" ++ separate_map (string ";" ^^ break 1) field fs ++ string "}"

  | Field (e, f) ->
    located may_paren_record_expression e ^^ string "#" ^^ located label f

  | ChangeField (e, f, r) ->
    group (
      located may_paren_record_expression e
      ^^ string "#" ^^ located label f
      ++ string "<-")
    ++ located may_paren_record_expression r

and field (f, e) =
  group (located label f ++ string ":=" ++ located may_paren_expression e)

and may_paren_record_expression e = match e with
  | Case _ | Fun _ | Define _ | DefineRec _ | ChangeField _ ->
    parens (expression e)
  | _ ->
    expression e

and may_paren_expression e = match e with
  | Case _ | Fun _ | Define _ | DefineRec _ -> parens (expression e)
  | _ -> expression e

and branch (Branch (p, e)) =
  group (nest 2 (group (string "|" ++ located pattern p ++ string "=>") 
		 ++ located expression e))

and pattern = function
  | PWildcard ->
    string "_"
  | PVariable x ->
    located identifier x
  | PTypeAnnotation (p, t) ->
    parens (located pattern p ++ string ":" ++ located ty t)
  | PTaggedValue (k, []) ->
    located dataconstructor k
  | PTaggedValue (k, ps) ->
    located dataconstructor k
    ++ parens (separate_map (comma ^^ break 1) (located pattern) ps)
  | PRecord fs ->
    string "{"
    ++ separate_map (string ";" ^^ break 1) field_pattern fs
    ++ string "}"
  | PAnd ps ->
    parens
      (separate_map (break 1 ^^ string "&" ^^ break 1) (located pattern) ps)
  | POr ps ->
    parens
      (separate_map (break 1 ^^ string "|" ^^ break 1) (located pattern) ps)
  | PLiteral l ->
    located literal l

and field_pattern (f, p) =
  located label f ++ string "=" ++ located pattern p

and literal = function
  | LInt x ->
    int x
  | LChar c ->
    char c
  | LString s ->
    string_literal s
  | LBool true ->
    string "true"
  | LBool false ->
    string "false"

and char c =
  group (string "'" ^^ string (Char.escaped c) ^^ string "'")

and string_literal s =
  group (string "\"" ^^ string (String.escaped s) ^^ string "\"")

and parens_at_left_of_application e =
  match Position.value e with
  | Apply _ | Variable _ | Literal _ -> fun x -> x
  | _ -> parens

and parens_at_right_of_application e =
  match Position.value e with
  | Variable _ | Literal _ -> fun x -> x
  | _ -> parens

let to_string f x =
  let b = Buffer.create 13 in
  ToBuffer.pretty 0.8 80 b (f x);
  Buffer.contents b
