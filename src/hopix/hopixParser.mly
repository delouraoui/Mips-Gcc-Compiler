%{

  open HopixAST


%}

%token REC VAL TYPE EXTERN
%token PLUS MINUS STAR SLASH PIPE BSLASH EQUAL USCORE QMARK AMPER
%token FATARROW LARROW RARROW
%token SHARP AAND
%token IF THEN ELSE FI DO DONE
%token LPAREN RPAREN LBRACK RBRACK LCURLY RCURLY
%token COLON SEMICOLON COMMA DOT DEQUAL EOF 
%token<Int32.t> INT
%token<char> CHAR 
%token<bool> BOOL
%token<string> STRING
%token LEQ GEQ LT GT
%token AND OR

(** identificateur tokens **)
%token<string> INFIXID BID PREFIXID TVAR KID


(** associativity operators **)

%left alias
%left PIPE
%left AMPER SEMICOLON 
%right FATARROW
       
%right RARROW
%right LARROW
      
%left OR
%left AND
%nonassoc LT GT LEQ GEQ EQUAL  
%left INFIXID

%left PLUS MINUS
%left STAR SLASH
%left QMARK
%left SHARP 



%start<HopixAST.t> program

%%

program: ds=located(definition)* EOF { ds }



(** DEFINITION **)
definition:
| TYPE x=located(type_constructor) 
  y=epsilon_list(LBRACK, COMMA, located(type_variable), RBRACK)
  z=option (t_definition)
  DOT
{
  DefineType (x, y, match z with Some s -> s | _ -> Abstract)
}

(* externe extern value *)
| EXTERN x=located(identifier) COLON t=located(ty) DOT 
{ 
  
  DeclareExtern(x,t) 
}
| vdef=vdefinition DOT {vdef}


(** DEFINITION DE VALEUR **)
vdefinition:
(* define value *)
|VAL id=located(identifier) l=largs w =option(preceded(COLON,located(ty))) DEQUAL e=located(expression) 
{
  let compose y = Position.with_poss $startpos(e) $endpos(e) (y) in 
      let dec z j = compose (Fun(z, j)) in 
        let constructArgs liste xe =
          (List.fold_right (fun z j -> (dec z j) ) liste xe) in 
        let finalisation d = match d with 
                            | None -> DefineValue(id,constructArgs l e)
                            | Some a -> let xe = compose (TypeAnnotation(e,a)) in 
                            DefineValue(id, constructArgs l xe )
        in finalisation w

}

(* define recvalue *)
| REC liste = lrecargs
{
  DefineRecValue(liste)
}

(** TYPE DEFINITION **)
t_definition:

(* type enregistrement *)
| DEQUAL x=nonepsilon_list(LCURLY, SEMICOLON, tpair1, RCURLY)
{
  DefineRecordType x
}

(* type somme *)
| DEQUAL LCURLY option(PIPE) 
      x=separated_nonempty_list (PIPE, tpair2)
  RCURLY
{
  DefineSumType x
}

%inline tpair1:
x=located(label_id) COLON y=located(ty) 
{
  (x,y)
}
%inline tpair2:
x=located(constr_id) COLON y=separated_nonempty_list(STAR, located(ty))
{
  (x, y)
}
| x=located(constr_id)
{
  (x, [])
}

(** **)



(** EXPRESSION **)

expression: 

s=simple_expression { s }

(* annotation de type *)
| LPAREN x=located(expression) COLON y=located(ty) RPAREN
{
  TypeAnnotation (x, y)
}

(*  Definition locale *)

| e1= vdefinition
  SEMICOLON e2=located(expression) 
{
  let extract arg = match arg with
                | DefineValue(x,e) -> Define (x, e, e2)
                | DefineRecValue(liste) ->  DefineRec(liste,e2)
                | _ -> failwith "erreur parsing"
  in extract e1

}

(*  SÃ©quencement *)
| DO firstE = expression 
 DONE
{
  firstE
}
| DO firstE = located(expression)  SEMICOLON li =doexpression 
{
  let compose y = Position.with_poss $startpos(firstE) $endpos(firstE) (y) in 
    let rec construction l= match l with
      | [] -> failwith "false"
      | a::[] -> a
      | a::b::[] -> (compose (Define(compose ( Id("nothing") ), a , b)) )
      | a :: q ->  (compose (Define(compose (Id("nothing")), a ,construction q)) ) in 
    Define ( compose (Id("nothing")),firstE ,(construction (li)) )
}
(* modification d'un champ *)
| e=record_champ LARROW z=located(expression)
{
  let res = 
   function 
    | Field (x, y) -> ChangeField (x, y, z)
    | _ -> failwith "parsing error"
    in res e
}
(* operation binaire *)
| lhs=located(expression) b=located(binop) rhs=located(expression)
{
  let op = Position.(map (fun x -> Variable (map (fun _ -> Id x) b))) b in
  let app1 = Position.with_poss $startpos(lhs) $endpos(b) (Apply (op, lhs)) in
  Apply (app1, rhs)
}

(* fonction anonyme *)
| BSLASH x=located(simpl_pattern) l=largs FATARROW y=located(expression)
{
  let compose y = Position.with_poss $startpos(y) $endpos(y) (y) in 
      let dec z j = compose (Fun(z, j)) in 
        let constructArgs liste =
          (List.fold_right (fun z j -> (dec z j) ) liste y) in Fun (x, (constructArgs l) )

}

(* construction d'une donnÃ©e etiquetÃ© *)
| x=located(constr_id) 
  y=nonepsilon_list(LPAREN, COMMA, located(expression), RPAREN)
{
  Tagged (x, y)
}

(* analyse de motif *)

| x=located(expression) QMARK y=branches
{
  Case (x, y)
}

(* construction d'un enregistrement *)
| LCURLY x=separated_nonempty_list(SEMICOLON, epair) RCURLY
{
  Record x
}


(*
|  x=located(expression) QMARK  option(PIPE) y=separated_nonempty_list(PIPE, located(branch)) { Case (x, y)}
|  x=located(expression) QMARK  LCURLY option(PIPE) y=separated_nonempty_list(PIPE, located(branch)) RCURLY { Case (x, y)}


| x=located(expression) QMARK 
  LCURLY PIPE? 
      y=separated_nonempty_list(PIPE, located(branch)) 
  RCURLY
{
  Case (x, y)
}
*)

(* conditionnelle *)
| IF x=located(expression) 
  THEN y=located(expression) 
  ELSE z=located(expression)
  FI
{
  IfThenElse (x, y, z)
}


%inline epair:
x=located(label_id) DEQUAL y=located(expression)
{
  (x, y)
}

simple_expression:
| a=located(simple_expression) b=located(record_champ)
{
  Apply (a, b)
}
| e=record_champ
{
  e
}

record_champ:
(* acces a un champ *)
| x=located(record_champ) SHARP y=located(label_id)
{
  Field (x, y)
}
|e=mega_simple
{
  e
}

mega_simple:

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
| e=feuille
{
  e
}
feuille:
| x=located(constr_id) 
{
  Tagged (x, [])
}


lrecargs: x=separated_nonempty_list(AAND, recargs) {x}

recargs:
  x=located(identifier) l=largs w =option(preceded(COLON,located(ty))) DEQUAL e=located(expression){
     let compose y = Position.with_poss $startpos(e) $endpos(e) (y) in 
      let dec z j = compose (Fun(z, j)) in 
        let constructArgs liste xe =
          (List.fold_right (fun z j -> (dec z j) ) liste xe) in 
        let finalisation d = match d with 
                            | None -> (x,constructArgs l e)
                            | Some a -> let xe = compose (TypeAnnotation(e,a)) in 
                            (x, constructArgs l xe )
        in finalisation w
}


largs: 
  x=list(args) {x}

args: 
|x= located(simpl_pattern) {
  x
}




(** TYPE **)
ty:
| LPAREN x=ty RPAREN 
{
  x
}
| x=type_constructor y=epsilon_list(LBRACK, COMMA, located(ty), RBRACK)
{
  TyCon (x, y)
}
| a=located(ty) RARROW b=located(ty)
{
  TyCon ((TCon("->")),[a;b])
}

| x=type_variable
{
  TyVar x
}


(** BRANCH **)

branches:
| LCURLY PIPE x=smart_list (PIPE, located(branch)) RCURLY
{
  x
}
| LCURLY x=smart_list (PIPE, located(branch)) RCURLY
{
  x
}
| PIPE x=smart_list (PIPE, located(branch)) 
{
  x
}
| x=smart_list (PIPE, located(branch))
{
  x
}


branch:
x=located(pattern) FATARROW y=located(expression)
{
  Branch (x, y)
}



simpl_pattern:

(* etiquette *)
x=located(constr_id) 
{
  PTaggedValue (x, [])
}

| x=located(identifier)
{
  PVariable x
}
(* motif universel non liant *)
| USCORE 
{ 
  PWildcard
}
(* parenthesage *)
| LPAREN x=pattern RPAREN
{
  x
}
(* Annotation de type *)
| LPAREN x=located(pattern) COLON y=located(ty) RPAREN
{
  PTypeAnnotation (x, y)
}
(* enregistrement *)
| LCURLY x=separated_nonempty_list (SEMICOLON, ppair) RCURLY
{
  PRecord x
}
| x=located(literal) 
{ 
  PLiteral x 
}

doexpression:
| exp = located(expression) SEMICOLON q = doexpression
{
  exp::q
}
| exp = located(expression) SEMICOLON? DONE
{
  exp::[]
}
(** PATTERN **)
pattern:

x=located(constr_id) 
  y=nonepsilon_list(LPAREN, COMMA, located(pattern), RPAREN)
{
  PTaggedValue (x, y)
}

(* disjonction *)
| x=located(pattern) PIPE y=located(pattern)
{
  POr (
    (match (Position.value x) with POr l -> l | _ -> [x]) @ 
    (match (Position.value y) with POr l -> l | _ -> [y]))
}

(* conjonction *)
| x=located(pattern) AMPER y=located(pattern)
{
  PAnd (
    (match (Position.value x) with PAnd l -> l | _ -> [x]) @ 
    (match (Position.value y) with PAnd l -> l | _ -> [y]))
}

(* motif simple *)
| x = simpl_pattern 
{
  x
}


%inline ppair:
x=separated_pair (located(label_id), EQUAL, located(pattern))
{
  x
}





(** BINOP **)
%inline binop:
  x=INFIXID { String.(sub x 0 (length x - 1)) }
| PLUS    { "`+"   }
| MINUS   { "`-"   }
| STAR    { "`*"   }
| SLASH   { "`/"   }
| LT      { "`<"   }
| GT      { "`>"   }
| LEQ     { "`<="  }
| GEQ     { "`>="  }
| EQUAL   { "`="   }
| AND     { "`&&"  }
| OR      { "`||"  }
(** **)



(** Identificateur **)
%inline literal:
  x=INT     { LInt x    }
| x=STRING  { LString x }
| x=CHAR    { LChar x   }
| x=BOOL    { LBool x   }

%inline type_constructor: 
x=BID { TCon x }

%inline type_variable:
x=TVAR { TId x }

%inline label_id:
x=BID { LId x } 

%inline constr_id:
x=KID { KId x }

%inline identifier: 
| x=BID { Id x }
| x=PREFIXID { Id x }
(** **)



(** liste delimite **)
epsilon_list (opening, sep, X, closing):
x=loption(delimited(
    opening,
       separated_nonempty_list (sep, X),
    closing))
{
  x
}

nonepsilon_list (opening, sep, X, closing):
x=delimited(
    opening,
       separated_nonempty_list (sep, X),
    closing)
{
  x
}

smart_list(separator, X):
x = X %prec alias
{ [ x ] }
| x = X; separator; xs = smart_list(separator, X)
{ x :: xs }



%inline located(X): x=X {
  Position.with_poss $startpos $endpos x
}
