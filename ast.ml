open Lexing

type typ = Integer | Character | Boolean | R of string | AccessR of typ | Typenull | NT

type binope = Be | Bne

type binopc = Bg | Bge | Bl | Ble

type entier = int

type modif = Modifin | Modifinout

type charactere = string

module Smap = Map.Make ( struct type t = string let compare = Pervasives.compare end )

type ident = string

type type_ident=Id of ident | AcId of ident

type champ_ident=(ident list) * type_ident

type mode =In | Inout

type param = (ident list) * (mode option) * type_ident

type params = (param list)

type binop = Eq | Neq | Gr | Gre | Lo | Loe | Plus | Time | Div | Rem | Moins | And | And_then | Or | Or_else

type fichier = ident * (declaration list) * (instruction list) * (ident option)

and declaration = {desc_dec : desc_dec ;
                   loc_dec : Lexing.position * Lexing.position ;
                   typ_dec : typ ;
                   ctx_dec : contxt
                  }
and desc_dec =
  |Dtype of ident |Dtypeis of ident * ident |Dtypeisrecord of ident * (champ_ident list)
  |DDP of (ident list) * type_ident * (expression option)
  |Dprocedure of ident * (params option) * (declaration list) * (instruction list) * (ident option)
  |Dfunction of ident * (params option) * (type_ident) * (declaration list) * (instruction list) * (ident option)

and expression= { desc_exp:desc_exp ;
                  loc_exp : Lexing.position * Lexing.position ;
                  typ_exp : typ ;
                  ctx_exp : contxt
                }
and desc_exp =
  |Eentier of entier
  |Echaracter of string
  |Eboolean of bool
  |Etypenull
  |Eacces of acces_ident
  |Ebinop of binop*expression * expression
  |Enot of expression|Eoppose of expression
  |Enew of ident
  |Eidentp of ident*(expression list)
  |Eapo of expression

and instruction= {desc_ins:desc_ins ;
                  loc_ins : Lexing.position * Lexing.position ;
                  typ_ins : typ ;
                  ctx_ins : contxt
                 }
and desc_ins =
  |IDPE of acces_ident * expression
  |IPV of ident
  |IPVm of ident * (expression list)
  |Ireturn of (expression option)
  |Iif of expression * (instruction list) * ((expression * (instruction list)) list) * ((instruction list) option)
  |Ifor of ident * bool * expression * expression * (instruction list)
  |Iwhile of expression * (instruction list)


and acces_ident= {desc_ai : desc_ai ;
                  loc_ai : Lexing.position * Lexing.position ;
                  typ_ai : typ ;
                  ctx_ai : contxt
                 }
and desc_ai = AId of ident | DId of expression * ident

and contxt = { mutable va : typ Smap.t ;
               mutable is_modif_va : modif Smap.t;
               mutable fu : (((typ * modif) list) * typ) Smap.t ;
               mutable pr : ((typ * modif) list) Smap.t ;
               mutable re : (typ Smap.t) Smap.t ;
               mutable t : typ Smap.t ;
               mutable id_used : string list ;
               mutable dec_level : string list}

let ctx_0 () = { va = Smap.empty ;
                 is_modif_va = Smap.empty;
                 fu = Smap.empty ;
                 pr = Smap.empty;
                 re = Smap.empty ;
                 t = Smap.empty ;
                 id_used = [] ;
                 dec_level = []}

let copy_context c = { va = c.va ;
                 is_modif_va = c.is_modif_va;
                 fu = c.fu ;
                 pr = c.pr;
                 re = c.re ;
                 t = c.t ;
                 id_used = c.id_used ;
                 dec_level = c.dec_level}

type ident_p = {ident : string ; level : int ; offstet : int }

type type_ident_p = IdP of ident_p | AcIdP of ident_p

type champ_ident_p = (ident_p list) * type_ident

type param_p = (ident_p list) * (mode option) * type_ident_p

type params_p = (param_p list)

type fichier_p = ident_p * (declaration_p list) * (instruction_p list) * (ident_p option)

and acces_ident_p= {desc_aip : desc_aip ;
                    loc_aip : Lexing.position * Lexing.position ;
                    typ_aip : typ ;
                    ctx_aip : contxt
                   }

and desc_aip = AIdP of ident_p | DIdP of expression_p * ident_p

and declaration_p = { desc_decp : desc_decp ;
                     loc_decp : Lexing.position * Lexing.position ;
                     typ_decp : typ ;
                     ctx_decp : contxt
                 }

and desc_decp =
 |DtypeP of ident
 |DtypeisP of ident * ident
 |DtypeisrecordP of ident * (champ_ident_p list)
 |DDPP of (ident_p list) * type_ident * (expression_p option)
 |DprocedureP of ident_p * (params option) * (declaration_p list) * (instruction_p list) * (ident_p option)
 |DfunctionP of ident_p * (params option) * (type_ident) * (declaration_p list) * (instruction_p list) * (ident_p option)

and expression_p= { desc_expp: desc_expp ;
                   loc_expp : Lexing.position * Lexing.position ;
                   typ_expp : typ ;
                   ctx_expp : contxt
               }

and desc_expp =
 |EentierP of entier
 |EcharacterP of string
 |EbooleanP of bool
 |EtypenullP
 |EaccesP of acces_ident_p
 |EbinopP of binop * expression_p * expression_p
 |EnotP of expression_p
 |EopposeP of expression_p
 |EnewP of ident_p
 |EidentpP of ident_p * (expression_p list)
 |EapoP of expression_p

and instruction_p= {desc_insp : desc_insp ;
                   loc_insp : Lexing.position * Lexing.position ;
                   typ_insp : typ ;
                   ctx_insp : contxt
                 }

and desc_insp =
 |IDPEP of acces_ident_p * expression_p
 |IPVP of ident_p
 |IPVmP of ident_p * (expression_p list)
 |IreturnP of (expression_p option)
 |IifP of expression_p * (instruction_p list) * ((expression_p * (instruction_p list)) list) * ((instruction_p list) option)
 |IforP of ident_p * bool * expression_p * expression_p * (instruction_p list)
 |IwhileP of expression_p * (instruction_p list)

and eng = { mutable fpid : int Smap.t ; (* sert à déterminer les nom des fonctions et procédures de manière injective *)
            mutable v : ident_p Smap.t ;
            mutable n : int} (* sert à déterminer les conditions de manière déterministe *)

and enl = { mutable va : ident_p Smap.t ; (* sert à associer localement ident_p à un ident de variable*)
           mutable fu : ident_p Smap.t ; (* sert à associer localement ident_p à un ident de fonction*)
           mutable pr : ident_p Smap.t ;
           mutable r :  (ident_p Smap.t) Smap.t ; (* sert à associer ident_p aux idents définissant les champs d'un record de type R r *)
           mutable en : ident_p Smap.t }
