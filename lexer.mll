{
  open Lexing
  open Parser

  let keywords = Hashtbl.create 97
  let () = List.iter (fun (s,t) -> Hashtbl.add keywords s t)
  ["access",ACCESS;"and",AND;"begin",BEGIN;"else",ELSE;"elsif",ELSIF;"end",END;
  "false",FALSE;"for",FOR;"function",FUNCTION;"if",IF;"in",IN;"is",IS;"loop",LOOP;
  "new",NEW;"not",NOT;"or",OR;"out",OUT;"null",NULL;"procedure",PROCEDURE;"record",
  RECORD;"rem",REM;"return",RETURN;"reverse",REVERSE;"then",THEN;"true",TRUE;"type",
  TYPE;"use",USE;"while",WHILE;"with",WITH]

  let newline lexbuf=
    let pos=lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-{pos with pos_lnum=pos.pos_lnum+1 ; pos_bol= pos.pos_cnum}
}

let letter = ['a'-'z' 'A'-'Z']
let digit = ['0'-'9']
let ident = letter (letter | digit | '_')*

rule token = parse
| '\n' {newline lexbuf ; token lexbuf}
| [' ' '\t']+ { token lexbuf }
| "--" {comment lexbuf}
| "Ada.Text_IO" {OULARDEUR}
| "character ' val" {APO}
| "=" {CMPE Be}
| "/=" {CMPE Bne}
| ">" {CMPC Bg}
| ">=" {CMPC Bge}
| "<" {CMPC Bl}
| "<=" {CMPC Ble}
| "+" {PLUS}
| "-" {MOINS}
| "*" {TIME}
| "/" {DIV}
| "." {DOT}
| ".." {DDOT}
| ident as s { let s = String.lowercase s in try Hashtbl.find keywords s with Not_found -> IDENT s }
| digit + as s {try let sp = (int_of_string s)  in
                    if sp > 2147483647 then failwith "too voluminous integer"
                    else ENTIER sp with _-> failwith "Constante trop grande"}
| ";" {PV}
| ":" {DP}
| ":=" {DPE}
| "," {V}
| "(" {PO}
| ")" {PF}
| "'"  _ as s  "'" {C s}
| eof {EOF}

and comment = parse
|'\n' {token lexbuf}
| eof {EOF}
| _     { comment lexbuf }
