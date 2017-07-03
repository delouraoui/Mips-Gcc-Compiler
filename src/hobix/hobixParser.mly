%{

  open HobixAST

  let make_fun ps e =
    List.fold_left (fun e p ->
      Position.map (fun _ -> Fun (p, e)) e
    ) e (List.rev ps)

  let sequence pos b a =
    let id = Position.map (fun _ -> Id "nothing") a in
    Position.with_pos pos (Define (id, a, b))

  let flat_or p = match Position.value p with
    | POr ps -> ps (* invariant: ps should already be or-flattened *)
    | _ -> [p]

  let mkPOr p1 p2 = POr (flat_or p1 @ flat_or p2)

  let flat_and p = match Position.value p with
    | PAnd ps -> ps (* invariant: ps should already be and-flattened *)
    | _ -> [p]

  let mkPAnd p1 p2 = PAnd (flat_and p1 @ flat_and p2)
(* </corrige> *)

%}

%token VAL
%token PLUS MINUS STAR SLASH
%token LPAREN RPAREN
%token SEMICOLON DOT DEQUAL EOF
%token<Int32.t> INT
%token<string> ID INFIXID


%start<HopixAST.t> program

%%

program: ds=located(definition)* EOF
{
  ds
}

definition:
VAL x=located(identifier) DEQUAL e=located(expression) DOT
{
  DefineValue (x, e)
}


expression:
s=simple_expression
{
      s
}
| lhs=located(expression) b=located(binop) rhs=located(expression)
{
  let op = Position.(map (fun x -> Variable (map (fun _ -> Id x) b))) b in
  let app1 = Position.with_poss $startpos(lhs) $endpos(b) (Apply (op, lhs)) in
  Apply (app1, rhs)
}
simple_expression:
| a=located(simple_expression) b=located(very_simple_expression)
{
  Apply (a, b)
}
| e=very_simple_expression
{
  e
}


very_simple_expression:
  l=located(literal)
{
  Literal l
}
| x=located(identifier)
{
  Variable x
}
| LPAREN e=expression RPAREN
{
  e
}

%inline binop:
  x=INFIXID { String.(sub x 0 (length x - 1)) }
| PLUS  { "`+"  }
| MINUS { "`-"  }
| STAR  { "`*"  }
| SLASH { "`/"  }

%inline literal:
  x=INT
{
  LInt x
}


%inline identifier: x=ID {
  Id x
}

%inline located(X): x=X {
  Position.with_poss $startpos $endpos x
}
