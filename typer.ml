
open Ast
open Lexer

exception Error of (Lexing.position * Lexing.position) * string
exception Error2 of string
exception Error3 of (Lexing.position * Lexing.position) * string


let contexte_0 = ctx_0 ()

let sametype x y = match x,y with
  |Integer , Integer->true
  |Character , Character-> true
  |Boolean , Boolean->true
  |R x ,R y -> x = y
  |AccessR _ , Typenull ->true
  |Typenull , AccessR _ ->true
  |AccessR _ , AccessR _ ->true
  |Typenull , Typenull->true
  |_ , _ -> false

let modif_comp m1 m2 = match (m1,m2) with
  |Modifinout , Modifin -> false
  |_ -> true


(*   TYPAGE DES EXPRESSIONS     *)




let decore_exp exp expo typ ctx= {desc_exp = exp ;
                                 loc_exp = expo.loc_exp ;
                                 typ_exp=typ ;
                                 ctx_exp = ctx}

let rec type_exp contexte expression = match expression.desc_exp with
  |Etypenull ->
      decore_exp expression.desc_exp expression Typenull (copy_context contexte)
  |Eboolean _ ->
      decore_exp expression.desc_exp expression Boolean (copy_context contexte)
  |Eentier _ ->
      decore_exp expression.desc_exp expression Integer (copy_context contexte)
  |Echaracter _ ->
      decore_exp expression.desc_exp expression Character (copy_context contexte)
  |Eacces(a) ->
      let ap=(type_acces contexte a) in
      decore_exp (Eacces(ap)) expression ap.typ_ai (copy_context contexte)
  |Ebinop(bin,x,y) when (bin=Eq) || (bin=Neq) ->
      let  (a,b) = ((type_exp contexte x),(type_exp contexte y)) in
      if sametype a.typ_exp b.typ_exp
      then decore_exp (Ebinop(bin,a,b)) expression Boolean (copy_context contexte)
      else raise (Error (expression.loc_exp ,"Typing error."))
  |Ebinop(bin,x,y) when (bin=Gr)||(bin=Gre)||(bin=Lo)||(bin=Loe) ->
      let a,b=(type_exp contexte x),(type_exp contexte y) in
      if ((a.typ_exp)!=Integer) || ((b.typ_exp)!=Integer)
      then raise (Error (expression.loc_exp ,"Typing error."))
      else decore_exp (Ebinop(bin,a,b)) expression Boolean (copy_context contexte)
  |Ebinop(bin,x,y) ->
      let a,b=(type_exp contexte x),(type_exp contexte y) in
      if ((a.typ_exp)!=Integer)||((b.typ_exp)!=Integer)
      then raise (Error (expression.loc_exp ,"Typing error."))
      else decore_exp (Ebinop(bin,a,b)) expression Integer (copy_context contexte)
  |Enot(a)->
      let b = type_exp contexte a in
      if b.typ_exp = Boolean
      then decore_exp (Enot(b)) expression Boolean (copy_context contexte)
      else raise (Error (expression.loc_exp ,"Typing error."))
  |Eoppose(a)->
      let b = type_exp contexte a in
      if b.typ_exp = Integer
      then decore_exp (Eoppose(b)) expression Integer (copy_context contexte)
      else raise (Error (expression.loc_exp ,"Typing error."))
  |Enew(r) ->
    if not (Smap.mem r (contexte.t)) then
      raise (Error (expression.loc_exp, "Undefined type :"^r)) ;
    let t = Smap.find r (contexte.t) in
    (match t with
     | R _-> ()
     | _ -> raise (Error (expression.loc_exp, "New expects a register"))) ;
    decore_exp (Enew(r)) expression (AccessR(t)) (copy_context contexte)
  |Eapo(e)->
      let b= type_exp contexte e in
      if b.typ_exp =Integer
      then decore_exp (Eapo(b)) expression Character (copy_context contexte)
      else raise (Error (expression.loc_exp ,"Typing error."))
  |Eidentp(id, expl) ->
      if Smap.mem id contexte.fu
      then let a = Smap.find id contexte.fu in
      let explp = List.map (type_exp contexte) expl in
             ( match a with
                |argl, typee-> (matchlist (List.map (fun x -> x.typ_exp) explp) argl ;
                                check_modif_lists contexte (List.map snd (fst a)) explp;
                                                     decore_exp (Eidentp(id,explp)) expression typee)) (copy_context contexte)
      else raise (Error (expression.loc_exp, "Undefined fuction."))

and modif_state_exp contexte e = match e with
        |Eacces x -> (try is_modifiable contexte x ;
                         Modifinout
                     with
                        |Error3(_,_)-> Modifin
                        |Error(x,y) -> raise ( Error(x,y)) )
        | _ -> Modifin

and check_modif_lists contexte l1 l2 = match (l1,l2) with
  |[] , [] -> ()
  |t1 :: q1 , t2 :: q2 -> if (not (modif_comp t1 (modif_state_exp contexte t2.desc_exp))) then raise (Error (t2.loc_exp,"This expression has not a compatible modifiable state"))
                          else check_modif_lists contexte q1 q2
  |_ -> raise  (Error2 "Invalid number of arguments")

(*   TYPAGE DES ACCES     *)


and type_acces contexte a =
  match a.desc_ai with
      |AId(id) ->
      if not (Smap.mem id (contexte.va)) then
        raise (Error (a.loc_ai, "Undefined variable : "^id)) ;
            {desc_ai = AId(id) ;
               loc_ai = a.loc_ai ;
                typ_ai = (Smap.find id contexte.va) ;
                ctx_ai = (copy_context contexte)
              }
  |DId(ex, id) -> let exp = type_exp contexte ex in
                  try
                    (match exp.typ_exp with
                      | AccessR (R s ) ->
                          {desc_ai = DId( exp , id) ;
                           loc_ai = a.loc_ai ;
                           typ_ai = (Smap.find id (Smap.find s contexte.re)) ;
                           ctx_ai = (copy_context contexte)
                          }
                      | R s ->
                          {desc_ai = DId( exp , id) ;
                           loc_ai = a.loc_ai ;
                           typ_ai = (Smap.find id (Smap.find s contexte.re)) ;
                           ctx_ai = (copy_context contexte)
                          }
                      | _ -> raise ( Error ( exp.loc_exp , "A record is expected here." ) ) )
                  with
                    | _ -> raise ( Error ( a.loc_ai , "Undefined type or undefined champ." ) )


and is_modifiable contexte a = match a.desc_ai with
  |AId(id) ->
              if not (Smap.mem id (contexte.is_modif_va)) then
                raise (Error (a.loc_ai, "Undefined variable : "^id)) ;
              (match (Smap.find id contexte.is_modif_va) with
                |Modifin -> raise (Error3 (a.loc_ai,"Unmodifiable variable"))
                |_ -> ()
              )
  |_ -> ()


and matchlist l1 l2 = match l1,l2 with
  |[],[] -> ()
  |_,[] | [],_-> raise (Error2 "Number of arguments doesn't match")
  |p::q, (r,_)::s -> if not (sametype p r) then raise (Error2 "Typing error") else matchlist q s


(*   Quelques fonctions utiles    *)

and list_of_list_option a = match a with
  |None -> []
  |Some l -> l

and returneraqqch l =
  let rec aux ins = match ins.desc_ins with
    |Ireturn _ -> true
    |Iif(_,l,l1,None) -> (returneraqqch l) && (aux2 l1)
    |Iif(_,l,l1,Some l2) -> (returneraqqch l) && (aux2 l1) && (returneraqqch l2)
    |Ifor(_,_,_,_,l) -> returneraqqch l
    |Iwhile(_,l) -> returneraqqch l
    |_ -> false
  and aux2 l = match l with
    |[]->true
    |(_,l1)::q -> (returneraqqch l1) && (aux2 q) in
  match l with
    | p::q -> (aux p) || (returneraqqch q)
    |[] -> false


(*   TYPAGE DES INSTRUCTIONS     *)


and decore_ins ins inso typ ctx = {desc_ins = ins ;
                                   loc_ins = inso.loc_ins ;
                                   typ_ins = typ ;
                                   ctx_ins = ctx}

and type_ins contexte instruction = match instruction.desc_ins with
  |IDPE(a,e) ->
      (let ep = type_exp contexte e in
       let ap = type_acces contexte a in
       is_modifiable contexte ap ;
       if sametype ep.typ_exp  ap.typ_ai
       then (decore_ins (IDPE(ap,ep)) instruction Typenull   (copy_context contexte) )
       else raise (Error (instruction.loc_ins ,"Typing error."))
      )
  |IPV(i) ->
      if not (Smap.mem i (contexte.pr)) then
        raise (Error (instruction.loc_ins, "Undefined procedure : "^i)) ;
      let p = Smap.find i contexte.pr in
      if p = [] then decore_ins (IPV(i)) instruction Typenull (copy_context contexte)
      else raise (Error (instruction.loc_ins , "Process usage or definition failure."))
  |IPVm(i,el) ->
      if not (Smap.mem i (contexte.pr)) then
        raise (Error (instruction.loc_ins, "Undefined procedure : "^i)) ;
      let tl = Smap.find i contexte.pr in
      (try
         let l = List.map (fun x -> type_exp contexte x) el in
         matchlist (List.map (fun x -> x.typ_exp) l) tl ;
         check_modif_lists contexte (List.map snd tl) l;
         decore_ins (IPVm(i,l)) instruction Typenull (copy_context contexte)
         with
          |Error2 x ->raise ( Error (instruction.loc_ins , x )   )
    )
  |Ireturn(eo) ->
      (match eo with
      |None  -> decore_ins (Ireturn(None)) instruction Typenull (copy_context contexte)
      |Some e -> let ep = type_exp contexte e in
                 decore_ins (Ireturn(Some ep)) instruction ep.typ_exp (copy_context contexte))
  |Iif(e,ithen,elifthenl,elopt) ->
      let ep = type_exp contexte e in
      let el = list_of_list_option elopt in
      let ithenp = List.map (type_ins contexte) ithen in
      let elifthenlp = List.map (fun (e,l) -> (type_exp contexte e , List.map (type_ins contexte) l) ) elifthenl in
      let eloptp = List.map (type_ins contexte) el in
      if (ep.typ_exp = Boolean) && (List.for_all (fun x -> (fst x).typ_exp = Boolean) elifthenlp)
      then
       begin
       let rec last_type l = match l with
         |[] -> Typenull
         |[a] -> a.typ_ins
         |t :: q -> (match t.desc_ins with
                      | Ireturn opt -> (match opt with
                                         |None -> Typenull
                                         |Some x -> x.typ_exp )
                      | _ -> last_type q  )in
         match elifthenlp with
           | [] -> if sametype (last_type ithenp) (last_type eloptp)
                   then (decore_ins (Iif(ep,ithenp,[],Some eloptp)) instruction (last_type ithenp) (copy_context contexte))
                   else raise (Error (instruction.loc_ins , "In a If Then Else sheme, instructions should have the same type." ))
           | _ -> if (sametype (last_type ithenp) (last_type eloptp)) && (List.for_all (fun x -> sametype (last_type ithenp) (last_type (snd x))) elifthenlp )
                  then (decore_ins (Iif(ep,ithenp,elifthenlp,Some eloptp)) instruction (last_type ithenp) (copy_context contexte))
                  else raise (Error (instruction.loc_ins , "In a If Then Else sheme, instructions should have the same type." ))
       end
      else raise (Error (e.loc_exp , "A boolean is expected as condition." ))
  |Ifor(id, b, e1, e2, il )->
      let e1p = type_exp contexte e1 in
      let e2p = type_exp contexte e2 in
      if not (sametype e1p.typ_exp  e2p.typ_exp)
      then raise (Error (e2.loc_exp , "Incompatible type" ))
      else
        begin
        let new_contexte =
               {
                 va = Smap.add id e1p.typ_exp contexte.va ;
                 is_modif_va = Smap.add id Modifin contexte.is_modif_va ;
                 fu = contexte.fu ;
                 pr = contexte.pr ;
                 re = contexte.re ;
                 t = contexte.t ;
                 id_used = [] ;
                 dec_level = []
               } in
        let ilp = List.map (type_ins new_contexte) il in
        let rec last_type l = match l with
          |[] -> Typenull
          |[a] -> a.typ_ins
          |t :: q -> (match t.desc_ins with
                       | Ireturn opt -> (match opt with
                                          |None -> Typenull
                                          |Some x -> x.typ_exp )
                       | _ -> last_type q  )in
        decore_ins (Ifor(id,b,e1p,e2p,ilp)) instruction (last_type ilp) (copy_context contexte)
        end
  |Iwhile(e,il) ->
      let ep = type_exp contexte e in
      let ilp = List.map (type_ins contexte) il in
      if ep.typ_exp <> Boolean
      then raise (Error (e.loc_exp , "A Boolean is expected." ))
      else
       (
         let rec last_type l = match l with
           |[] -> Typenull
           |[a] -> a.typ_ins
           |t :: q -> (match t.desc_ins with
                        | Ireturn opt -> (match opt with
                                           |None -> Typenull
                                           |Some x -> x.typ_exp )
                        | _ -> last_type q  )in
         decore_ins (Iwhile(ep,ilp)) instruction (last_type ilp) (copy_context contexte)
        )

(*   TYPAGE DES TYPES     *)

and type_type_ident contexte t = match t with
  |Id(i) ->
    if not (Smap.mem i (contexte.t)) then
      raise (Error2 ("Undefined procedure : "^i)) ;
    let x =Smap.find i contexte.t in
    (match x with
      |NT -> raise (Error2 ("Untiped type : " ^ i) )
      |_ -> x)
  |AcId(i) ->
    if not (Smap.mem i (contexte.t)) then
      raise (Error2 ("Undefined procedure : "^i)) ;
    let x = AccessR (Smap.find i contexte.t ) in
    (match x with
      |AccessR NT -> raise (Error2 ("Untiped type : " ^ i) )
      |_ -> x )

(*   fonctions utiles *)

and type_instruction_list contexte l = match l with
  |[] -> Typenull
  |t :: q -> if returneraqqch [t] then (type_ins contexte t).typ_ins else type_instruction_list contexte q



(*   TYPAGE DES DECLARATIONS     *)

and check_disponibility contexte i dec =
  if List.mem i contexte.id_used then raise (Error(dec.loc_dec,"The ident used is already used at the same level."))
  else ()


and decore_dec dec deco typ ctx = {desc_dec = dec ;
                                   loc_dec = deco.loc_dec ;
                                   typ_dec = typ ;
                                   ctx_dec = ctx}

and check_dec_same_level l =
  let aux1 = function
    |Dtypeis _ -> true
    |Dtypeisrecord _ -> true
    |_ -> false in
  let aux2 = List.filter aux1 in
  let aux3 = function
    |Dtypeis(i1,i2)-> i1
    |Dtypeisrecord(i,ci) -> i
    |_ -> failwith "This case never happens." in
  let lp = List.map aux3 (aux2 l) in
  let rec sans_doublons l acc = match l with
    |[] -> true
    |t :: q -> if List.mem t acc then false else sans_doublons q (t::acc) in
  match (sans_doublons lp []) with
    |true -> ()
    |false -> raise (Error2 "Variable already defined.")

and type_dec contexte declaration = match declaration.desc_dec with (*penser a la fin a verifier que toute variable declaree est definie*)
  |Dtype (i) ->
      contexte.t <- Smap.add i NT contexte.t ;
      check_disponibility contexte i declaration ;
      if List.mem i contexte.dec_level then (raise (Error(declaration.loc_dec,"A type can only be declared once at a same level.")));
      contexte.dec_level <- i :: contexte.dec_level ;
      decore_dec (Dtype i) declaration Typenull (copy_context contexte)
  |Dtypeis (i1,i2) ->
      begin
        check_disponibility contexte i1 declaration ;
        contexte.id_used <- i1 :: contexte.id_used ;
        try
          let t = Smap.find i2 contexte.t in
          contexte.t <- Smap.add i1 (AccessR t) contexte.t ;
          decore_dec (Dtypeis (i1 ,i2)) declaration Typenull (copy_context contexte)
        with Not_found -> raise( Error(declaration.loc_dec , "Type not defined"))
      end
  |Dtypeisrecord(i,ci) ->
      begin
        check_disponibility contexte i declaration ;
        contexte.id_used <- i :: contexte.id_used ;
        contexte.t <- Smap.add i (R(i)) contexte.t ;
        contexte.re <- Smap.add i Smap.empty contexte.re ;
        let rec aux1 l = match l with
          |([],_) -> []
          |(t::q,j) -> (t,j) :: (aux1 (q,j)) in
        let rec aux2 l = match l with
          |[] -> []
          |t::q -> (aux1 t) @ (aux2 q) in
        let l = aux2 ci in
        let used = ref [] in
        let ajoute i =
          if not (List.mem i !used) then used := i :: !used
          else raise (Error(declaration.loc_dec,"Champs of a record can't have the same name.")) in
        let allowed_type_type_ident a = match a with
          | AcId(ip) -> ()
          | Id(ip) -> begin
               match i = ip with
                |true -> raise (Error(declaration.loc_dec,"A record type can't be recursive."))
                |false -> () end in
        List.iter (fun (x,y) -> ajoute x ;
                              (contexte.re <- Smap.add i (Smap.add x y (
            (if not (Smap.mem i contexte.re) then raise (Error(declaration.loc_dec, "Undefined register "^i))) ;
            Smap.find i contexte.re) )  contexte.re)) (List.map (fun (a,b) -> allowed_type_type_ident b ; (a, type_type_ident contexte b)) l) ;
        decore_dec (Dtypeisrecord(i ,ci)) declaration Typenull (copy_context contexte)
      end
  |DDP(il,ti,eo) ->
      begin
        List.iter (fun i -> check_disponibility contexte i declaration ;
                           contexte.id_used <- i :: contexte.id_used ) il ;
       (match eo with
         |None -> List.iter (fun x -> (contexte.va <- Smap.add x (type_type_ident contexte ti) contexte.va ;
                                       contexte.is_modif_va <- Smap.add x Modifinout contexte.is_modif_va)) il ;
                  decore_dec (DDP(il,ti,None)) declaration Typenull (copy_context contexte)
         |Some e -> let ep = type_exp contexte e in
                    if not (sametype (type_type_ident contexte ti) ep.typ_exp) then raise (Error (e.loc_exp ,"This expression is not of announced type.") );
                    List.iter (fun x -> (contexte.va <- Smap.add x (type_type_ident contexte ti) contexte.va ;
                                         contexte.is_modif_va <- Smap.add x Modifinout contexte.is_modif_va)) il ;
                    decore_dec (DDP(il,ti,Some ep)) declaration Typenull (copy_context contexte)
       )
      end
  |Dprocedure(i,po,decl,insl,io) ->
      begin
      let used = ref [] in
      let ajoute i =
        if not (List.mem i !used) then used := i :: !used
        else raise (Error(declaration.loc_dec,"Params of a procedure can't have the same name.")) in
      (match po with
        |None -> ()
        |Some pl -> List.iter (fun (x,y,z) -> List.iter ajoute x) pl );
      check_disponibility contexte i declaration ;
      contexte.id_used <- i :: contexte.id_used ;
      match io with
        |Some(iop) when i <> iop -> raise (Error (declaration.loc_dec , "Only the declarated function can be called after its declatation." ))
        |_-> () ;
      let mode_of_mode_option m = match m with
        |None -> Modifin
        |Some x -> (
                    match x with
                      |In -> Modifin
                      |Inout -> Modifinout
                    ) in
      let rec aux1 contexte l = match l with
        |([],_,_) -> []
        |(t::q,j,k) -> (t,mode_of_mode_option j,type_type_ident contexte k) :: (aux1 contexte  (q,j,k)) in
      let rec aux2 contexte l = match l with
        |[] -> []
        |t::q -> (aux1 contexte t) @ (aux2 contexte q) in
      let aux3 po = match po with
        |None -> []
        |Some x -> x in
      let pop = aux2 contexte (aux3 po) in
      contexte.pr <- Smap.add i ( (List.map (fun (x,y,z) -> (z,y)) pop)) contexte.pr ;
      contexte.va <- Smap.add i (Typenull) contexte.va;
      contexte.is_modif_va <-Smap.add i (Modifin) contexte.is_modif_va;
      let nm = ref Smap.empty in
      Smap.iter (fun k v -> nm := Smap.add k v !nm) contexte.is_modif_va ;
      List.iter (fun (x,y,z) -> nm := Smap.add x y !nm) pop ;
      let new_contexte =
             {
               va =  List.fold_left (fun c (x,_,z) -> Smap.add x z c) contexte.va pop;
               is_modif_va = !nm ;
               fu = contexte.fu ;
               pr = contexte.pr ;
               re = contexte.re ;
               t = contexte.t ;
               id_used = [] ;
               dec_level = []
             } in
      let dlp = List.map (type_dec new_contexte ) decl in
      let ilp = List.map (type_ins new_contexte ) insl in
      if not (sametype (type_instruction_list contexte ilp) Typenull )
      then raise (Error (declaration.loc_dec , "Procedure should return typenull or at least something as useless as typenull")) ;
      if (List.exists (fun x -> (Smap.find x new_contexte.t) = NT) new_contexte.dec_level)
      then raise (Error (declaration.loc_dec , "Every declared type should be defined.")) ;
      decore_dec (Dprocedure(i,po,dlp,ilp,io)) declaration Typenull (copy_context contexte)
                                      end
  |Dfunction(i,po,ti,dl,il,io) ->
      begin
      contexte.va <- Smap.add i (type_type_ident contexte ti) contexte.va ;
      let used = ref [] in
      let ajoute i =
        if not (List.mem i !used) then used := i :: !used
        else raise (Error(declaration.loc_dec,"Params of a function can't have the same name.")) in
      (match po with
        |None -> ()
        |Some pl -> List.iter (fun (x,y,z) -> List.iter ajoute x) pl );
      check_disponibility contexte i declaration ;
      contexte.id_used <- i :: contexte.id_used ;
      if not (returneraqqch il) then raise (Error (declaration.loc_dec , "A function should finish by a return." )) ;
      match io with
        |Some(iop) when i <> iop -> raise (Error (declaration.loc_dec , "Only the declarated function can be called after its declatation." ))
        |_-> () ;
      let mode_of_mode_option m = match m with
        |None -> Modifin
        |Some x -> (
                    match x with
                      |In -> Modifin
                      |Inout -> Modifinout
          ) in
      let rec aux1 contexte l = match l with
        |([],_,_) -> []
        |(t::q,j,k) -> (t,mode_of_mode_option j,type_type_ident contexte k) :: (aux1 contexte  (q,j,k)) in
      let rec aux2 contexte l = match l with
        |[] -> []
        |t::q -> (aux1 contexte t) @ (aux2 contexte q) in
      let aux3 po = match po with
        |None -> []
        |Some x -> x in
      let pop = aux2 contexte (aux3 po) in
      contexte.fu <- Smap.add i ( (List.map (fun (x,y,z) -> (z,y)) pop) , type_type_ident contexte ti) contexte.fu ;contexte.va <- Smap.add i (type_type_ident contexte ti) contexte.va;
      contexte.is_modif_va <-Smap.add i (Modifin) contexte.is_modif_va;
      let nm = ref Smap.empty in
      Smap.iter (fun k v -> nm := Smap.add k v !nm) contexte.is_modif_va ;
      List.iter (fun (x,y,z) -> nm := Smap.add x y !nm) pop ;
      let new_contexte =
             {
               va =  List.fold_left (fun c (x,_,z) -> Smap.add x z c) contexte.va pop;
               is_modif_va = !nm ;
               fu = contexte.fu ;
               pr = contexte.pr ;
               re = contexte.re ;
               t = contexte.t ;
               id_used = [] ;
               dec_level = []
             } in
      let dlp = List.map (type_dec new_contexte ) dl in
      let ilp = List.map (type_ins new_contexte ) il in
      if (type_type_ident contexte ti) <> (type_instruction_list contexte ilp)
      then raise (Error (declaration.loc_dec , "The return type of the function is not the same as the declaration." )) ;
      if (List.exists (fun x -> (Smap.find x new_contexte.t) = NT) new_contexte.dec_level)
      then raise (Error (declaration.loc_dec , "Every declared type should be defined.")) ;
      decore_dec (Dfunction(i,po,ti,dlp,ilp,io)) declaration Typenull (copy_context contexte)
      end

(*   TYPAGE DU FICHIER     *)

and type_f (i , dl , il , io) =
  let contexte = {
                va =  Smap.empty ;
                is_modif_va = Smap.empty ;
                fu = Smap.empty ;
                pr = Smap.empty ;
                re = Smap.empty ;
                t = Smap.empty ;
                id_used = [] ;
                dec_level = []
               } in
  contexte.t <- Smap.add "integer" Integer contexte.t ;
  contexte.t <- Smap.add "character" Character contexte.t ;
  contexte.t <- Smap.add "boolean" Boolean contexte.t ;
  contexte.t <- Smap.add "null" Typenull contexte.t ;
  contexte.t <- Smap.add "Integer" Integer contexte.t ;
  contexte.t <- Smap.add "Character" Character contexte.t ;
  contexte.t <- Smap.add "Boolean" Boolean contexte.t ;
  contexte.t <- Smap.add "Null" Typenull contexte.t ;
  contexte.pr <- Smap.add "Put" [(Character,Modifin)] contexte.pr ;
  contexte.pr <- Smap.add "put" [(Character,Modifin)] contexte.pr ;
  contexte.pr <- Smap.add "New_Line" [] contexte.pr ;
  contexte.pr <- Smap.add "new_line" [] contexte.pr ;
  contexte.pr <- Smap.add i [] contexte.pr ;
  let dlp = List.map (type_dec contexte) dl in
  let ilp = List.map (type_ins contexte) il in
  if type_instruction_list contexte ilp <> Typenull then raise (Error2 "The core of the program is a procedure and can't return something") ;
  if (List.exists (fun x -> (Smap.find x contexte.t) = NT) contexte.dec_level)
  then raise (Error2 "Every declared type in the core procedure should be defined.") ;
  match io with
    | None -> (i , dlp , ilp , io)
    | Some ip -> if i = ip
                 then (i , dlp , ilp , io)
                 else raise (Error2 "The ident after the core procedure can anly be the same as the procedure itself.")
