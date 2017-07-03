{
  open Lexing
  open Error
  open Position
  open HobixParser

  let next_line_and f lexbuf  =
    Lexing.new_line lexbuf;
    f lexbuf

  let error lexbuf =
    error "during lexing" (lex_join lexbuf.lex_start_p lexbuf.lex_curr_p)


}

let newline = ('\010' | '\013' | "\013\010")

let blank   = [' ' '\009' '\012']

let symbol = [ '+' '-' '*' '/' '<' '=' '>' ]

let digit = ['0'-'9']

let lowercase_alpha = ['a'-'z']

let uppercase_alpha = ['A'-'Z']

let alpha = lowercase_alpha | uppercase_alpha

let alphanum = alpha | digit | '_'

let basic_identifier = lowercase_alpha alphanum*

let prefix_alien_identifier = "`" (alpha | symbol | digit)+

let infix_alien_identifier = "`" (alpha | symbol | digit)+ "`"

let identifier = basic_identifier | prefix_alien_identifier


rule token = parse
  (** Layout *)
  | newline         { next_line_and token lexbuf }
  | blank+          { token lexbuf               }

  (** Keywords *)
  | "val"           { VAL  }

  (** Identifiers *)
  | identifier as i  { ID i  }
  | infix_alien_identifier as i { INFIXID i }

  (** Literals *)
  | digit+ as d     { INT (Int32.of_string d) }

  (** Infix operators *)
  | "-"             { MINUS       }
  | "+"             { PLUS        }
  | "*"             { STAR        }
  | "/"             { SLASH       }

  (** Punctuation *)
  | ":="	    { DEQUAL    }
  | ";"             { SEMICOLON }
  | "."             { DOT       }
  | "("             { LPAREN    }
  | ")"             { RPAREN    }
  | eof             { EOF       }

  (** Lexing error. *)
  | _               { error lexbuf "unexpected character." }

