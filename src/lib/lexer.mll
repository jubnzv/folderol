{
  open Parser
}

let whitespace = ['\r' '\t' ' ' '\n']

let upper_letter = [ 'A'-'Z' ]
let lower_letter = [ 'a'-'z']
let digit	= ['0'-'9']
let idx = digit+

rule initial =
  parse
  | whitespace+           { initial lexbuf }
  | "("                   { TLParen }
  | ")"                   { TRParen }
  | ","                   { TComma }
  | "."                   { TDot }
  | "?"                   { TQuotation }
  | "∧" | "&"             { TConj }
  | "∨" | "|"             { TDisj }
  | "→" | "-->"           { TImpl }
  | "↔" | "<->"           { TEq }
  | "¬" | "~"             { TNeg }
  | "∀" | "FORALL"        { TForall }
  | "∃" | "EXISTS"        { TExists }
  | upper_letter+ as id   { TIdUppercase(id) }
  | lower_letter+ as id   { TIdLowercase(id) }
  | idx as idx            { TIdx(int_of_string idx) }
  | eof                   { TEOF }
