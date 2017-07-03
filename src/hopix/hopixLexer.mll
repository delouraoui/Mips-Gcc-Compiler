{
  open Lexing
  open Error
  open Position
  open HopixParser
  exception NotAscii
  let next_line_and f lexbuf  =
    Lexing.new_line lexbuf;
    f lexbuf

  let error lexbuf =
    error "during lexing" (lex_join lexbuf.lex_start_p lexbuf.lex_curr_p)

   let extactCodeAscii numb = 
   	if int_of_string numb > 127 then raise NotAscii
   	else  Char.chr (int_of_string numb)
}


let newline' = ('\010' | '\013')

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

let constr_id = (uppercase_alpha | '_') alphanum* 
  
let type_variable = "'" basic_identifier


rule token = parse
  (** Layout *)
  | newline         		{ next_line_and token lexbuf }
  | blank+          		{ token lexbuf               }
  | "**"            		{ commentLine lexbuf; token lexbuf  }
  | "{*"            		{ comment lexbuf; token lexbuf}

  (** Literals *)

  (************************* CHAR ***************************)

  (*  Lexing des caracteres echape ascii caracteres   *)
  | "'" '\\' '/' "'" 		{ CHAR('/') }
  | "'" '\\' '\\' "'"		{ CHAR('\\') }
  | "'" '\\' 'b' "'" 		{ CHAR('\b') }
  | "'" '\\' 'n' "'" 		{ CHAR('\n') }
  | "'" '\\' 'r' "'"		{ CHAR('\r') }
  | "'" '\\' 't' "'" 		{ CHAR('\t') }
  | "'" '\\' '"' "'"		{ CHAR('\"') }
  | "'" '\\' ''' "'"		{ CHAR('\'')}
  | "'" _ as char "'" {CHAR(String.get (Scanf.unescaped char) 1)}

  (*  Lexing des caracteres echape ascii sous forme de sequence binaire  *)
  | "'" '\\' (['0'-'9'] as int1) (['0'-'9'] as int2) (['0'-'9'] as int3) "'" {
  								let conv = (String.make 1 int1)^(String.make 1 int2)^(String.make 1 int3) in 
  								let nb = int_of_string conv in
	  							if nb >= 0 && nb <= 255 then CHAR(Char.chr nb) else error lexbuf "unexpected character."					
 							}
  (*  Lexing des caracteres echape ascii sous forme de sequence hexadecimale *)
  | "'" '\\' '0' ['x' 'X'] (['0'-'9' 'a'-'f' 'A'-'F'] as str1) (['0'-'9' 'a'-'f' 'A'-'F'] as str2) "'" {
  								let conv = "0x"^(String.make 1 str1)^(String.make 1 str2) in 
  								let nb = int_of_string conv in
	  							if nb >= 0 && nb <= 255 then CHAR(Char.chr nb) else error lexbuf "unexpected character."
 							}
  | "'" '\\' '0' ['b' 'B'] (digit+ as d) "'" {
  								let conv = "0b"^d in 
  								let nb = int_of_string conv in
	  							if nb >= 0 && nb <= 255 then CHAR(Char.chr nb) else error lexbuf "unexpected character."
 							}


 (************************* INT ***************************)

  (*  Lexing des entiers donne sous forme hexadecimale   *)
  | "0" (['x' 'X']as pre) (['0'-'9' 'a'-'f' 'A'-'F'])+ as hex	   {
                      let _ = pre in 
                      let conv = hex in 
                      let nb = Int32.of_string conv in
                      INT(nb)
                    }
  (*  Lexing des entiers donne sous forme octale   *)
  | "0" (['o' 'O']as pre) (['0'-'7'] )+ as oct   { 
                      let _ = pre in 
                      let conv = oct in 
                      let nb = Int32.of_string conv in
                      INT(nb)
                    }
   (*  Lexing des entiers donne sous forme binaire   *)
  | "0" (['b' 'B'] as pre) (['0'-'1'])+ as bin  { 
                      let _ = pre in 
                      let conv = bin in 
                      let nb = Int32.of_string conv in
                      INT(nb)
                    }
  | digit+ as d    { INT (Int32.of_string d)   }

  (************************* STRING ***************************)
  
  | '"'             { STRING( (stringBuffer (Buffer.create 128) lexbuf) ) }

   (************************* BOOL ***************************)

  | "true"          { BOOL(true)   }
  | "false"         { BOOL(false)  } 

  (** Keywords *)

  | "if"                  { IF        }
  | "then"                { THEN      }
  | "else"                { ELSE      }
  | "fi"                  { FI        }
  | "do"           	  {  	DO 			}
  | "done"          			{  	DONE 		}
  | "val"           			{ 	VAL  		}
  | "type"          			{ 	TYPE 		}		
  | "rec"           			{ 	REC     } 
  | "and"           			{ 	AAND    }
  | "extern"        			{	EXTERN 		}


  (** Infix operators *)
  | "-"             { MINUS       }
  | "+"             { PLUS        }
  | "*"             { STAR        }
  | "/"             { SLASH       }

  (** Punctuation *)
  | ":="            { DEQUAL    }
  | "="             { EQUAL     }
  | ":"             { COLON     }
  | ";"             { SEMICOLON }
  | "."             { DOT       }
  | "("             { LPAREN    }
  | ")"             { RPAREN    }
  | "["             { LBRACK    }
  | "]"             { RBRACK    }
  | "{"             { LCURLY    }
  | "}"             { RCURLY    }
  | ","             { COMMA     }
  | "|"             { PIPE      }
  | "\\"            { BSLASH    }
  | "=>"            { FATARROW  }
  | "_"             { USCORE    }
  | "#"             { SHARP     }
  | "<-"            { LARROW    }
  | "->"            { RARROW    }
  | "?"             { QMARK     }
  | "&"             { AMPER     }
  | "<"             { LT        }
  | ">"             { GT        }
  | "<="            { LEQ       }
  | ">="            { GEQ       }
  | "&&"            { AND       }
  | "||"            { OR        }
  | eof             { EOF       }

  (** Identifiers *)

  | basic_identifier as i        { BID i      }
  | type_variable as i           { TVAR i     }
  | constr_id as i               { KID i      }
  | infix_alien_identifier as i  { INFIXID i  }
  | prefix_alien_identifier as i { PREFIXID i }


  (** Lexing error. *)
  | _               { error lexbuf "unexpected character." }

and comment = parse
  | "*}" { () }
  | "{*" { comment lexbuf; comment lexbuf }
  | eof  { error lexbuf "Unterminated comment ." }
  | _   { comment lexbuf }

and commentLine = parse
  | "\n" { () }
  | eof  { ()  }
  | _   { commentLine lexbuf }

and  stringBuffer buffer = parse
        | '"'       		{ Buffer.contents buffer }
        | newline' as c  	{ Buffer.add_char buffer c; stringBuffer buffer lexbuf }
        | '\\' '/'  		{ Buffer.add_char buffer '/'; stringBuffer buffer lexbuf }
        | '\\' '\\' 		{ Buffer.add_char buffer '\\'; stringBuffer buffer lexbuf }
        | '\\' 'b'  		{ Buffer.add_char buffer '\b'; stringBuffer buffer lexbuf }
        | '\\' 'n'  		{ Buffer.add_char buffer '\n'; stringBuffer buffer lexbuf }
        | '\\' 'r'  		{ Buffer.add_char buffer '\r'; stringBuffer buffer lexbuf }
        | '\\' 't'  		{ Buffer.add_char buffer '\t'; stringBuffer buffer lexbuf }
        | '\\' '"'			{ Buffer.add_char buffer '\"'; stringBuffer buffer lexbuf }
        | '\\' '''			{ Buffer.add_char buffer '\''; stringBuffer buffer lexbuf }
        (* les sequences *)
 		| '\\' (['0'-'9'] as int1) (['0'-'9'] as int2) (['0'-'9'] as int3) {
  								let conv = (String.make 1 int1)^(String.make 1 int2)^(String.make 1 int3) in 
  								let nb = int_of_string conv in
	  							if nb >= 0 && nb <= 255 then 
	  							Buffer.add_char buffer (Char.chr nb)
	  							else Buffer.add_string buffer conv;	
	  							stringBuffer buffer lexbuf				
 							}
		  (*  Lexing des caracteres echape ascii sous forme de sequence hexadecimale *)
		| '\\' '0' ['x' 'X'] (['0'-'9' 'a'-'f' 'A'-'F'] as str1) (['0'-'9' 'a'-'f' 'A'-'F'] as str2){
		  								let conv = "0x"^(String.make 1 str1)^(String.make 1 str2) in 
		  								let nb = int_of_string conv in
			  							if nb >= 0 && nb <= 255 then 
			  							Buffer.add_char buffer (Char.chr nb)
			  							else Buffer.add_string buffer conv;	
			  							stringBuffer buffer lexbuf	
		 							}
		| '\\' '0' ['b' 'B'] (digit+ as d) {
		  								let conv = "0b"^d in 
		  								let nb = int_of_string conv in
			  							if nb >= 0 && nb <= 255 then 
			  							Buffer.add_char buffer (Char.chr nb)
			  							else Buffer.add_string buffer conv;	
			  							stringBuffer buffer lexbuf	
		 							}
		| '\\' _ as char	{ Buffer.add_string buffer char; stringBuffer buffer lexbuf }
        | eof  { error lexbuf "Unterminated comment ." }
        | _ as char { Buffer.add_char buffer char; stringBuffer buffer lexbuf }


and parsescapeInteger tampon = parse
        | eof  	  { error lexbuf "Unterminated comment ." }
        | ['0'-'9' 'a'-'f' 'A'-'F']+ as d {Buffer.add_string tampon d;Int32.of_string( Buffer.contents tampon )} 






