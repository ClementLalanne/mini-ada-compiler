open Format
open X86_64
open Ast



(* Decoration adéquate des arbres *)

let rec taille_type t contexte = match t with
  | Integer -> 1
  | Character -> 1
  | Boolean  -> 1
  | R(s) -> Smap.fold (fun x y z -> (z + taille_type y contexte)) (Smap.find s contexte.re) 0
  | AccessR _ -> 1
  | Typenull -> 1
  | NT -> failwith "never happens"

and decore_decp decp deco = {desc_decp = decp ;
                              loc_decp = deco.loc_dec ;
                              typ_decp = deco.typ_dec ;
                              ctx_decp = deco.ctx_dec}

and to_decp d eng enl ofs lvl= match d.desc_dec with
  |Dtype (ident) ->
    print_endline "l25" ;
    decore_decp (DtypeP ident) d
  |Dtypeis(ident1 , ident2) ->
    print_endline "l28" ;
    decore_decp (DtypeisP(ident1,ident2)) d
  |Dtypeisrecord (ident , champ_ident_list) ->
    print_endline "l31" ;
    begin
    let typ_of_typident t = match t with
      |Id x -> x
      |AcId x -> x in
    enl.r <- Smap.add ident Smap.empty enl.r ;
    let ofsp = ref 0 in
    List.iter
      (fun (idl,t) -> List.iter
        (fun x -> enl.r <- Smap.add ident (Smap.add x
                            ({ ident = x ;
                             level = lvl + 1 ;
                             offstet = !ofsp } )
                              (Smap.find ident enl.r)) enl.r ;
                                                ofsp := !ofsp + (taille_type (Smap.find (typ_of_typident t) d.ctx_dec.t) d.ctx_dec)) idl) champ_ident_list;
    let champ_ident_list_p = List.map (fun (idl,t) -> (List.map (fun x -> Smap.find x (Smap.find ident enl.r))idl,t) )champ_ident_list in
     decore_decp (DtypeisrecordP(ident,champ_ident_list_p) ) d
     end
  |DDP (ident_list , tident , exprop) ->
    print_endline "l50" ;
   (match exprop with
    |None   ->
      let ident_list_p = List.map (fun x ->
                                            enl.va <- Smap.add x {ident = x; level = lvl ; offstet = !ofs} enl.va ;
                                            ofs := !ofs + (taille_type (Smap.find x d.ctx_dec.va) d.ctx_dec) ;
                                            Smap.find x enl.va) ident_list in
      decore_decp (DDPP(ident_list_p , tident , None)) d
    |Some e ->
      print_endline "l59" ;
      let enlp = { va = enl.va ;
                  fu = enl.fu ;
                  pr = enl.pr ;
                  r = enl.r ;
                  en = enl.en } in
      let ep = to_expp e eng enlp in
      let ident_list_p = List.map (fun x ->
                                            enl.va <- Smap.add x {ident = x; level = lvl ; offstet = !ofs} enl.va ;
                                            ofs := !ofs + (taille_type (Smap.find x d.ctx_dec.va) d.ctx_dec) ;
                                            Smap.find x enl.va) ident_list in
      decore_decp (DDPP(ident_list_p , tident ,Some ep)) d )
  |Dprocedure (ident , params_o , declaration_l  , instruction_l , ident_o) ->
        print_endline "l72" ;
        begin
        let lid = (match Smap.mem ident eng.fpid with
           | true -> ident ^ string_of_int (Smap.find ident eng.fpid)
           | false -> eng.fpid <- Smap.add ident 0 eng.fpid  ;
                      ident ^ "0"      ) in
       eng.fpid <- Smap.add ident (1 + (Smap.find ident eng.fpid)) eng.fpid ;
       enl.pr <- Smap.add ident {ident = lid ; level = lvl ; offstet = 0}  enl.pr ;
       let new_enl = { va = enl.va ;
                       fu = enl.fu ;
                       pr = enl.pr ;
                       r = enl.r ;
                       en = enl.en } in
        let list_of_list_option lo = match lo with
          |None -> []
          |Some l -> l in
        let typ_of_typident t = match t with
          |Id x -> x
          |AcId x -> x in
        let ri = ref 0 in
        List.iter ( fun (il,mo,t) ->
                      List.iter (fun i -> new_enl.va <- Smap.add i {ident = i ; level = lvl+1; offstet = -2 - !ri}
                                                                  new_enl.va ;
                                                                  ri := !ri + (taille_type (Smap.find (typ_of_typident t) d.ctx_dec.t) d.ctx_dec)) (List.rev il) ;
                      ) (List.rev (list_of_list_option params_o)) ;
        let ofs = ref 1 in
        let declaration_l_p = List.map (fun x -> to_decp x eng new_enl ofs (lvl+1)) declaration_l in
        let instruction_l_p = List.map (fun x -> to_insp x eng new_enl (lvl+1)) instruction_l in
        (match ident_o with
          |None   -> decore_decp  (DprocedureP( {ident = lid ; level = lvl ; offstet = 0} , params_o, declaration_l_p , instruction_l_p , None)) d
          |Some x ->  decore_decp  (DprocedureP( {ident = lid ; level = lvl ; offstet = 0} , params_o, declaration_l_p , instruction_l_p ,Some {ident = lid ; level = lvl ; offstet = 0})) d)

       end
  |Dfunction (ident , params_o , ti , declaration_l  , instruction_l , ident_o) ->
        print_endline "l109" ;
        begin
        let lid = (match Smap.mem ident eng.fpid with
           | true -> ident ^ string_of_int (Smap.find ident eng.fpid)
           | false -> eng.fpid <- Smap.add ident 0 eng.fpid  ;
                      ident ^ "0"      ) in
       eng.fpid <- Smap.add ident (1 + (Smap.find ident eng.fpid)) eng.fpid ;
       enl.pr <- Smap.add ident {ident = lid ; level = lvl ; offstet = 0}  enl.pr ;
       let new_enl = { va = enl.va ;
                       fu = enl.fu ;
                       pr = enl.pr ;
                       r = enl.r ;
                       en = enl.en } in
        let list_of_list_option lo = match lo with
          |None -> []
          |Some l -> l in
        let typ_of_typident t = match t with
          |Id x -> x
          |AcId x -> x in
        let ri = ref 0 in
        List.iter ( fun (il,mo,t) ->
                      List.iter (fun i -> new_enl.va <- Smap.add i {ident = i ; level = lvl+1; offstet = -2 - !ri}
                                                                  new_enl.va ;
                                                                  ri := !ri + (taille_type (Smap.find (typ_of_typident t) d.ctx_dec.t) d.ctx_dec)) (List.rev il) ;
                      ) (List.rev (list_of_list_option params_o)) ;
        let ofs = ref 1 in
        let declaration_l_p = List.map (fun x -> to_decp x eng new_enl ofs (lvl+1)) declaration_l in
        let instruction_l_p = List.map (fun x -> to_insp x eng new_enl (lvl+1)) instruction_l in
        (match ident_o with
          |None   -> decore_decp  (DfunctionP( {ident = lid ; level = lvl ; offstet = 0} , params_o, ti , declaration_l_p , instruction_l_p , None)) d
          |Some x ->  decore_decp  (DfunctionP( {ident = lid ; level = lvl ; offstet = 0} , params_o, ti , declaration_l_p , instruction_l_p ,Some {ident = lid ; level = lvl ; offstet = 0})) d)

       end

and decore_insp insp inso =  {desc_insp = insp ;
                              loc_insp = inso.loc_ins ;
                              typ_insp = inso.typ_ins ;
                              ctx_insp = inso.ctx_ins}

and to_insp i eng enl lvl = match i.desc_ins with
  |IDPE (ai , expression) ->
     print_endline "l150" ;
   ( match ai.desc_ai with
      | AId a -> let  aip =  {desc_aip = AIdP (Smap.find a enl.va) ;
                              loc_aip = ai.loc_ai ;
                              typ_aip = ai.typ_ai ;
                              ctx_aip = ai.ctx_ai
                          } in
                decore_insp (IDPEP(aip,to_expp expression eng enl)) i
      | DId(er,id) -> let  aip =  {desc_aip = DIdP (to_expp er eng enl , Smap.find id (Smap.find ((fun (R s) -> s) er.typ_exp) enl.r)) ;
                                 loc_aip = ai.loc_ai ;
                                 typ_aip = ai.typ_ai ;
                                 ctx_aip = ai.ctx_ai
                          } in
                decore_insp (IDPEP(aip,to_expp expression eng enl)) i )
  |IPV (ident) ->
    print_endline "l165" ;
    decore_insp (IPVP (Smap.find ident enl.pr)) i
  |IPVm (ident , expl) ->
    print_endline "l168" ;
    decore_insp (IPVmP (Smap.find ident enl.pr , List.map (fun x -> to_expp x eng enl) expl)) i
  |Ireturn ( expo ) ->
    print_endline "l171" ;
    begin
      match expo with
        |None -> decore_insp (IreturnP None) i
        |Some exp -> decore_insp (IreturnP (Some (to_expp exp eng enl))) i
      end
  |Iif (exp , instrl , l , il_o ) ->
    print_endline "l178" ;
    begin
    let list_of_list_option lo = match lo with
      |None -> []
      |Some l -> l in
    let il = list_of_list_option il_o in
    let lp = List.map (fun (e,lr) -> (to_expp e eng enl , List.map (fun x -> to_insp x eng enl lvl) lr )) l in
    decore_insp (IifP(to_expp exp eng enl , List.map (fun i -> to_insp i eng enl lvl) instrl , lp , Some(List.map (fun i -> to_insp i eng enl lvl) il))) i
    end
  |Ifor (ident ,b , exp1 , exp2 , il ) ->
    print_endline "l188" ;
    begin
    let exp1p = to_expp exp1 eng enl in
    let exp2p = to_expp exp2 eng enl in
    let new_enl = { va = enl.va ;
                    fu = enl.fu ;
                    pr = enl.pr ;
                    r = enl.r ;
                    en = enl.en } in
    new_enl.va <- Smap.add ident {ident = ident ; level = lvl + 1 ; offstet = -2} new_enl.va;
    decore_insp (IforP({ident = ident ; level = lvl + 1 ; offstet = -1},b,exp1p,exp2p,List.map (fun x -> to_insp x eng new_enl (lvl+1) )il)) i
    end
  |Iwhile (expr , instl) ->
    print_endline "l201" ;
    decore_insp (IwhileP (to_expp expr eng enl , List.map (fun x -> to_insp x eng enl lvl) instl )) i

and decore_expp expp expo = { desc_expp = expp ;
                              loc_expp = expo.loc_exp ;
                              typ_expp = expo.typ_exp ;
                              ctx_expp = expo.ctx_exp}

and to_expp e eng enl = match e.desc_exp with
  |Eentier i ->
    print_endline "l211" ;
    decore_expp (EentierP i) e
  |Echaracter c ->
    print_endline "l214" ;
    decore_expp (EcharacterP c) e
  |Eboolean b ->
    print_endline "l217" ;
    decore_expp (EbooleanP b) e
  |Etypenull ->
    print_endline "l220" ;
    decore_expp (EtypenullP) e
  |Eacces ( ai ) ->
    print_endline "l223" ;
   ( match ai.desc_ai with
      | AId a -> let  aip =  {desc_aip = AIdP (Smap.find a enl.va) ;
                              loc_aip = ai.loc_ai ;
                              typ_aip = ai.typ_ai ;
                              ctx_aip = ai.ctx_ai
                          } in
                decore_expp (EaccesP aip) e
      | DId(er,i) -> let  aip =  {desc_aip = DIdP (to_expp er eng enl , Smap.find i (Smap.find ((fun (R s) -> s) er.typ_exp) enl.r)) ;
                                 loc_aip = ai.loc_ai ;
                                 typ_aip = ai.typ_ai ;
                                 ctx_aip = ai.ctx_ai
                          } in
                decore_expp (EaccesP aip) e )
  |Ebinop(op,e1,e2) ->
    print_endline "l238" ;
    decore_expp (EbinopP(op, to_expp e1 eng enl, to_expp e2 eng enl)) e
  |Enot e2 ->
    print_endline "l240" ;
    decore_expp (EnotP (to_expp e2 eng enl)) e
  |Eoppose e2 ->
    print_endline "l243" ;
    decore_expp (EopposeP (to_expp e2 eng enl)) e
  |Enew i ->
    print_endline "l247" ;
    decore_expp (EnewP (Smap.find i enl.va)) e
  |Eidentp(i,el) ->
    print_endline "l250" ;
    decore_expp (EidentpP(Smap.find i enl.fu , List.map (fun x -> to_expp x eng enl) el)) e
  |Eapo(e) ->
    let ep = to_expp e eng enl in
    decore_expp (EapoP ep) e

and to_fichierp ((id , dels , insl , ido) :fichier) =
  let eng = { fpid = Smap.add id 1 Smap.empty ;
              v = Smap.empty ;
              n = 0 } in
  let enl = { va = Smap.empty ;
              fu = Smap.add id {ident = id ; level = 0 ; offstet = 0} Smap.empty ;
              pr = Smap.empty ;
              r = Smap.empty ;
              en = Smap.empty } in
  enl.pr <- Smap.add "put" {ident = "put" ; level = 0 ; offstet = 0} enl.pr;
  enl.pr <- Smap.add "new_line" {ident = "new_line" ; level = 0 ; offstet = 0} enl.pr;
  let lvl = 0 in
  let ofs = ref 1 in
  let dl = List.map (fun x -> to_decp x eng enl ofs lvl) dels  in
  let il = List.map (fun x -> to_insp x eng enl lvl) insl in
  (match ido with
    |None ->
      (({ident = id ; level = 0 ; offstet = 0}, dl, il, None) : fichier_p)
    |Some a ->
      (({ident = id ; level = 0 ; offstet = 0}, dl , il ,Some {ident = id ; level = 0 ; offstet = 0})) : fichier_p)

(* Production de code *)

and compile_fichier a = match a with
  |id_p, declsl, inspl, _ ->
    let eng=ref { fpid = Smap.empty ;
                v = Smap.empty ;
                n = 0 } in
    (List.fold_left (fun a x -> a ++ (compile_dec eng 0 x)) nop declsl) ++
    glabel "main" ++
    (List.fold_left (fun a x -> a ++ (compile_ins eng 0 x)) nop inspl) ++
    movq (imm 0) (reg rax) ++
    ret


and iter n code =
  if n = 0 then nop
  else code ++
       iter (n-1) code

and framesize ctx (dl : declaration_p list)  = match dl with
  |[]->0
  |h::q-> (match h.desc_decp with
             | DDPP(l,typ,id) -> 8 * (taille_type h.typ_decp ctx) + (framesize ctx q )
             | _ -> (framesize ctx q ) )

and compile_dec eng level dec = match dec.desc_decp with
  |DprocedureP(identp,_,dl, il,_)->
    let fs = framesize dec.ctx_decp dl in
    label identp.ident ++
    subq (imm fs) (reg rsp) ++
    movq (reg rbp) (ind ~ofs:(fs-8) rsp) ++
    leaq (ind ~ofs:(fs-8) rsp) rbp ++
    (List.fold_left (fun a i ->a ++ (compile_ins eng (level+1) i)) (nop) il)++
    movq (reg rbp) (reg rsp) ++
    popq rbp++
    ret
  |DfunctionP(identp,_,_,dl,il,_) ->
    let fs = framesize dec.ctx_decp dl in
    label identp.ident ++
    subq (imm fs) (reg rsp) ++
    movq (reg rbp) (ind ~ofs:(fs-8) rsp) ++
    leaq (ind ~ofs:(fs-8) rsp) rbp ++
    (List.fold_left (fun a i ->a ++ (compile_ins eng (level+1) i)) (nop) il)++
    movq (reg rbp) (reg rsp) ++
    popq rbp++
    ret
  |DDPP (identpl,typid,expr) ->(* match expr with
                                  |None -> nop
                                  |Some e -> List.fold_left (fun x id -> x ++ )*) assert false
  |DtypeP _ ->
    nop
  |DtypeisP _ ->
    nop
  |DtypeisrecordP _->
    nop

and compile_expr eng level expr = match expr.desc_expp with
  |EentierP(x) ->
    pushq (imm x)
  |EbooleanP(true) ->
    pushq (imm 1)
  |EbooleanP(false) ->
    pushq (imm 0)
  |EtypenullP ->
    pushq (imm 0)
  |EcharacterP(c) ->
    pushq (imm (Char.code (String.get c 1)))
  |EapoP(e) ->
    compile_expr eng level e
  |EbinopP(b,e1,e2)->
    (match b with
     | Plus ->
         compile_expr eng level e1 ++
         compile_expr eng level e2 ++
         popq rbx ++
         popq rax ++
         addq (reg rbx) (reg rax)
     | Moins ->
         compile_expr eng level e1 ++
         compile_expr eng level e2 ++
         popq rbx ++
         popq rax ++
         subq (reg rbx) (reg rax)
     | Time ->
         compile_expr eng level e1 ++
         compile_expr eng level e2 ++
         popq rbx ++
         popq rax ++
         imulq (reg rbx) (reg rax)
     | Div ->
         compile_expr eng level e1 ++
         compile_expr eng level e2 ++
         popq rbx ++
         popq rax ++
         cqto ++
         idivq (reg rbx)
     | Rem ->
         compile_expr eng level e1 ++
         compile_expr eng level e2 ++
         popq rbx ++ popq rax ++
         cqto ++
         idivq (reg rbx) ++
         movq (reg rdx) (reg rax)
     | Eq ->
         compile_expr eng level e1 ++
         compile_expr eng level e2 ++
         popq rbx ++ popq rax ++
         xorq (reg r11) (reg r11) ++
         cmpq (reg rbx) (reg rax) ++
         setle (reg r11b) ++
         xorq (reg rax) (reg rax) ++
         movq (reg r11) (reg rax)
     | Neq ->
         compile_expr eng level e1 ++
         compile_expr eng level e2 ++
         popq rbx ++ popq rax ++
         xorq (reg r11) (reg r11) ++
         cmpq (reg rbx) (reg rax) ++
         setle (reg r11b) ++
         xorq (reg rax) (reg rax) ++
         movq (reg r11) (reg rax)
     | Gr ->
         compile_expr eng level e1 ++
         compile_expr eng level e2 ++
         popq rbx ++
         popq rax ++
         xorq (reg r11) (reg r11) ++
         cmpq (reg rbx) (reg rax) ++
         setle (reg r11b) ++
         xorq (reg rax) (reg rax) ++
         movq (reg r11) (reg rax)
     | Gre ->
         compile_expr eng level e1 ++
         compile_expr eng level e2 ++
         popq rbx ++
         popq rax ++
         xorq (reg r11) (reg r11) ++
         cmpq (reg rbx) (reg rax) ++
         setle (reg r11b) ++
         xorq (reg rax) (reg rax) ++
         movq (reg r11) (reg rax)
     | Lo ->
         compile_expr eng level e1 ++
         compile_expr eng level e2 ++
         popq rbx ++ popq rax ++
         xorq (reg r11) (reg r11) ++
         cmpq (reg rbx) (reg rax) ++
         setle (reg r11b) ++
         xorq (reg rax) (reg rax) ++
         movq (reg r11) (reg rax)
     | Loe ->
         compile_expr eng level e1 ++
         compile_expr eng level e2 ++
         popq rbx ++
         popq rax ++
         xorq (reg r11) (reg r11) ++
         cmpq (reg rbx) (reg rax) ++
         setle (reg r11b) ++
         xorq (reg rax) (reg rax) ++
         movq (reg r11) (reg rax)
     | And ->
         compile_expr eng level e1 ++
         compile_expr eng level e2 ++
         popq rbx ++
         popq rax ++
         andq (reg rbx) (reg rax)
     | Or ->
         compile_expr eng level e1 ++
         compile_expr eng level e2 ++
         popq rbx ++
         popq rax ++
         orq (reg rbx) (reg rax)
     | And_then ->
         let n = string_of_int(!eng.n) in
         let () = !eng.n <- !eng.n + 1 in
         compile_expr eng level e1 ++
         xorq (reg r11) (reg r11) ++
         popq rax ++
         testq (reg rax) (reg rax) ++
         setne (reg r11b) ++
         testq (reg rax) (reg rax) ++
         je ("aux"^n) ++
         compile_expr eng level e2 ++
         xorq (reg r11) (reg r11) ++
         popq rax ++
         setne (reg r11b) ++
         label ("aux"^n) ++
         movq (reg r11) (reg rax)

     | Or_else ->
         compile_expr eng level e1 ++
         xorq (reg r11) (reg r11) ++
         popq rax ++ (
         let n = string_of_int(!eng.n) in !eng.n <- !eng.n+1 ;
         testq (reg rax) (reg rax) ++
         setne (reg r11b) ++
         testq (reg rax) (reg rax) ++
         jne ("aux"^(n)) ++
         compile_expr eng level e2 ++
         xorq (reg r11) (reg r11) ++
         popq rax ++
         setne (reg r11b) ++
         label ("aux"^(n)) ++
         movq (reg r11) (reg rax)
       )
    ) ++
    pushq (reg rax)
  |EnotP(e1)->
      compile_expr eng level e1 ++
      xorq (reg r11) (reg r11) ++
      popq rax ++
      sete (reg r11b) ++
      movq (reg r11) (reg rax) ++
      pushq (reg rax)
  |EopposeP(e1)->
      compile_expr eng level e1 ++
      popq rbx ++
      movq  (imm 0) (reg rax)++
      subq (reg rbx) (reg rax) ++
      pushq (reg rax)
  |EaccesP(acide) ->
    begin
    match acide.desc_aip with
      |AIdP(idp)->
        let nom, lvl, ofs = idp.ident, idp.level, -8*idp.offstet in
        movq (reg rbp) (reg rax) ++
        iter (level - lvl) (movq (ind ~ofs:16 rax) (reg rax))++
        addq (imm ofs) (reg rax) ++
        pushq (reg rax)
      |DIdP(expp,idp)-> compile_expr eng level expp ++
                            (match expp.typ_expp with
                               | AccessR _ -> popq rax ++
                                              movq (ind rax) (reg rax) ++
                                              subq (imm (idp.offstet)) (reg rax) ++
                                              pushq (ind rax)
                               | _ ->failwith "tries to acces to an unreferenced register.")

    end
  |EidentpP(idp,el)->
    let nom, lvl, ofs =idp.ident, idp.level, 8*idp.offstet in
      (List.fold_left
        (fun acc e -> acc ++ compile_expr eng level e)
      nop el) ++
      movq (reg rbp) (reg rsi) ++
      iter (level - lvl) (movq (ind ~ofs:16 rsi) (reg rsi)) ++
      pushq (reg rsi) ++
      call idp.ident ++
      addq (imm (8 + 8 * List.length el)) (reg rsp)
  |EnewP(idp)->
      let n=taille_type expr.typ_expp expr.ctx_expp in
      movq (imm n) (reg rdi) ++
      call "malloc" ++
      pushq (reg rax)



and compile_ins eng level ins = match ins.desc_insp with
  |IDPEP(ai,e1)->
    begin
    compile_expr eng level e1++
    (match ai.desc_aip with
      |AIdP(idp)->let lvl, ofs = idp.level, -8*idp.offstet in
          movq (reg rbp) (reg rsi) ++
          iter (level-lvl) (movq (ind ~ofs:16 rsi) (reg rsi))++
          addq (imm ofs) (reg rsi) ++
          popq rax ++
          movq (reg rax) (ind rsi)
      |DIdP(expp,idp)->compile_expr eng level expp ++
                        (match expp.typ_expp with
                               | AccessR _ -> popq rax ++
                                              movq (ind rax) (reg rax) ++
                                              subq (imm (idp.offstet)) (reg rax) ++
                                              popq (rsi) ++
                                              movq (ind rsi) (ind rax)
                               | _ ->failwith "tries to acces to an unreferenced register."))
      end
  |IreturnP(reto)->
    begin
    match reto with
      |None ->
          movq (reg rbp) (reg rsp) ++
          popq rbp ++ ret
      |Some e1 ->
        compile_expr eng level e1 ++
        popq rax ++
        movq (reg rbp) (reg rsp) ++
        popq rbp ++
        ret
    end
  |IPVP(idp)->
    begin
    let nom, lvl, ofs =idp.ident, idp.level, -8*idp.offstet in
    movq (reg rbp) (reg rsi) ++
    iter (level - lvl) (movq (ind ~ofs:16 rsi) (reg rsi)) ++
    pushq (reg rsi) ++
    call idp.ident ++
    addq (imm (8)) (reg rsp)
    end
  |IPVmP(idp,el)->
    begin
    let nom, lvl, ofs =idp.ident, idp.level, -8*idp.offstet in
    (List.fold_left
      (fun acc e -> acc ++ compile_expr eng level e)
    nop el) ++
    movq (reg rbp) (reg rsi) ++
    iter (level - lvl) (movq (ind ~ofs:16 rsi) (reg rsi)) ++
    pushq (reg rsi) ++
    call idp.ident ++
    addq (imm (8 + 8 * List.length el)) (reg rsp)
    end
  |IwhileP(b,il)->
    begin
    let n=string_of_int(!eng.n) and np= string_of_int(!eng.n+1) in !eng.n <- !eng.n + 2 ;
    label ("aux"^n) ++
    compile_expr eng level b ++
    popq rax ++
    testq (reg rax) (reg rax) ++
    je ("aux"^np) ++
    List.fold_left (fun a i ->a ++ (compile_ins eng level i)) (nop) il ++
    jmp ("aux"^n) ++
    label ("aux"^np)
    end
  |IifP(b,il, elsifl, elselo) ->
    begin
    let nf = string_of_int(!eng.n) in !eng.n <- !eng.n +1 ;
    let n = ref (string_of_int(!eng.n)) in !eng.n<- !eng.n+1 ;
    let a =
    compile_expr eng level b ++
    popq rax ++
    testq (reg rax) (reg rax) ++
    je ("aux"^(!n)) ++
    (List.fold_left (fun a i ->a ++ (compile_ins eng level i)) (nop) il) ++
    jmp ("aux"^nf)
    in let b=
    (List.fold_left
    (
      (fun a (b, ilelif) ->
        a ++
        let c=
        label ("aux"^(!n)) in
        let d=
        compile_expr eng level b ++
        popq rax ++
        testq (reg rax) (reg rax) ++
        (n:=string_of_int(!eng.n) ;
        !eng.n <- !eng.n +1 ;
        je ("aux"^(!n)))
        ++
        nop ++
        (List.fold_left (fun a i ->a ++ (compile_ins eng level i)) (nop) ilelif)++
        jmp ("aux"^nf) in c++d)
    )
    (nop)
    elsifl)
    in let c=
      (match elselo with
        |None-> (nop)
        |Some(ile)-> label ("aux"^(!n)) ++
          (List.fold_left (fun a i ->a ++ (compile_ins eng level i)) (nop) ile)) in
      a++b++c++
      label ("aux"^nf)
    end
  |IforP(id, rever, dep,fin, il) ->
        begin
        let n=string_of_int(!eng.n) and np= string_of_int(!eng.n+1) in !eng.n <- !eng.n + 2 ;
        compile_expr eng level fin++
        compile_expr eng level dep++
        pushq (reg rbp) ++
        movq (reg rsp) (reg rbp) ++
        label ("aux"^n) ++
        cmpq (ind ~ofs:8 rbp) (ind ~ofs:16 rbp) ++
        je ("aux"^np) ++
        (List.fold_left (fun a i ->a ++ (compile_ins eng (level+1) i)) (nop) il)++
        movq (ind ~ofs:8 rbp) (reg r11) ++
        (if rever
          then
            subq (imm 1) (reg r11)
          else
            addq (imm 1) (reg r11)) ++
        movq (reg r11) (ind ~ofs:8 rbp)++
        jmp ("aux"^n) ++
        label ("aux"^np) ++
        movq (reg rbp) (reg rsp)++
        popq (rbp)++
        addq (imm 16) (reg rsp)
        end

        let compile arbre name =
          let arbre_decoreP = to_fichierp arbre in
          let fichier= open_out name in
          let fmt = Format.formatter_of_out_channel fichier in
          let programme = {text = compile_fichier arbre_decoreP ; data = nop} in
          print_program fmt programme ;
          output_string fichier
"new_line:
  movq $newline, %rdi
  movq $0, %rax
  call printf
  ret
put:
  subq $8, %rsp
  movq %rbp,(%rsp)
  leaq (%rsp), %rbp
  movq $message, %rdi
  movq 24(%rsp),%rsi
  movq $0, %rax
  call printf
  movq %rbp, %rsp
  popq %rbp
  ret
.data
message:.string \"%c\"
newline:.string \"\\n\"
";
          close_out fichier
