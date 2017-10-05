open Format
open Lexing
open Lexer
open Typer
open Compiler

let fichier = Sys.argv.(2)



let arg = Sys.argv.(1)

let () = let n = String.length fichier in
  if (fichier.[n-1]<>'b')||(fichier.[n-2]<>'d')||(fichier.[n-3]<>'a')||(fichier.[n-4]<>'.') then
    (print_string "*.adb file expected" ; exit 2)

let phrase_loc pos = " Line " ^ string_of_int pos.pos_lnum ^ " column " ^ string_of_int (pos.pos_cnum - pos.pos_bol + 1)
let phrase_loc2 s p1 p2 =
        print_string (
        "File \""^fichier
        ^"\", line "^(string_of_int p1.pos_lnum)^",
        characters "^(string_of_int (p1.pos_cnum - p1.pos_bol + 1))^
        "-"^(string_of_int (p2.pos_cnum - p2.pos_bol + 1))^": \n"^s)

let () = match arg with
 | "--type-only" -> begin
  let c = open_in fichier in
  let lb = Lexing.from_channel c in
  try
    let f = Parser.fichier Lexer.token lb in
    let a = Typer.type_f f in () ;
  with
    | Error((p1,p2),s) -> phrase_loc2 s p1 p2; exit 1
    | Error3((p1,p2),s) -> phrase_loc2 s p1 p2; exit 1
    end ; exit  0
  |"--parse-only" -> begin
  let c = open_in fichier in
  let lb = Lexing.from_channel c in
  try
    let f = Parser.fichier Lexer.token lb in ();
    with
     |_ -> print_string "Lexing or parsing error." ; exit 1
    end
  |_->begin let c = open_in fichier in
  let lb = Lexing.from_channel c in
  (try
    let f = Parser.fichier Lexer.token lb in
    let a = Typer.type_f f in Compiler.compile a (fichier^".s")
  with
    | Error((p1,p2),s) -> phrase_loc2 s p1 p2; exit 1
    | Error3((p1,p2),s) -> phrase_loc2 s p1 p2; exit 1
    | e -> raise e ; exit 1)
      end ; exit  0
