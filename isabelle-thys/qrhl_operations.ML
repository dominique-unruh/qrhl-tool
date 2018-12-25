structure QRHL_Operations = 
struct

fun make_ctxt_ref ctx = let
  val id = serial ()
  val _ = Refs.Ctxt.write id ctx
in
  id
end

fun make_thm_ref thm = let
  val id = serial ()
  val _ = Refs.Thm.write id thm
in
  id
end

structure Terms = struct
val table = Synchronized.var ("term_table") (Inttab.empty, Termtab.empty)
fun term_to_id ctxt t = Synchronized.change_result table (fn (tab1,tab2) =>
  case Termtab.lookup tab2 t of SOME id => (id,(tab1,tab2))
  | NONE => let
      val id = serial ()
      val tab2' = Termtab.update_new (t,id) tab2
      val tab1' = Inttab.update_new (id, (t, Lazy.lazy (fn _ => YXML.content_of (Syntax.string_of_term ctxt t)))) tab1
    in (id,(tab1',tab2')) end)
fun lookup_id id = case Inttab.lookup (Synchronized.value table |> fst) id of NONE => error "QRHL_Operations.Terms.lookup_id"
  | SOME x => x
fun id_to_term id = fst (lookup_id id)
fun id_to_string id = snd (lookup_id id) |> Lazy.force
end


fun context_decode (XML.Elem(("context",[("id",id)]),[])) = Refs.Ctxt.read (parse_int id) |> Codec.Success
  | context_decode xml = Codec.Failure ("invalid encoding for a context",[xml])

fun context_encode ctxt = let val id = make_ctxt_ref ctxt in XML.Elem(("context",[("id",string_of_int id)]),[]) end

val context_codec = Codec.basic {encode=context_encode, decode=context_decode}

fun thm_decode (XML.Elem(("thm",[("id",id)]),[])) = Refs.Thm.read (parse_int id) |> Codec.Success
  | thm_decode xml = Codec.Failure ("invalid encoding for a thm",[xml])

fun thm_encode ctxt = let val id = make_thm_ref ctxt in XML.Elem(("thm",[("id",string_of_int id)]),[]) end

val thm_codec = Codec.basic {encode=thm_encode, decode=thm_decode}

fun tac_dummy_thm NONE = NONE
  | tac_dummy_thm (SOME ts) = SOME (ts,@{thm TrueI})

fun parse_term ctx str T = let
  val parsed = Syntax.parse_term ctx str
  val constrained = Const("_type_constraint_", T --> T) $ parsed
  val term = Syntax.check_term ctx constrained
in term end


(** A codec for types that leads to much more compact serializations *)

fun class_tight_encode c = XML.Elem((c,[]),[])
fun class_tight_decode (XML.Elem((c,[]),[])) = Codec.Success c
  | class_tight_decode xml = Codec.Failure ("invalid encoding for a type class",[xml])

fun typ_tight_encode (Type(name,Ts)) = XML.Elem (("t",[]), XML.Text name :: map typ_tight_encode Ts)
  | typ_tight_encode (TFree(name,sort)) = XML.Elem (("f",[]), XML.Text name :: map class_tight_encode sort)
  | typ_tight_encode (TVar((name,idx),sort)) = XML.Elem (("v",[(name,string_of_int idx)]), map class_tight_encode sort)

fun typ_tight_decode (XML.Elem (("t",[]), XML.Text name :: xmls)) : typ Codec.result = 
       Codec.bind_result (fn Ts => Codec.Success (Type(name, Ts))) (Codec.traverse_results typ_tight_decode xmls)
  | typ_tight_decode (XML.Elem (("f",[]), XML.Text name :: xmls)) =
       Codec.bind_result (fn sort => Codec.Success (TFree(name,sort))) (Codec.traverse_results class_tight_decode xmls)
  | typ_tight_decode (xml as XML.Elem (("v",[(name,idx)]), xmls)) =
       (Codec.bind_result (fn sort => Codec.Success (TVar((name,parse_int idx),sort))) (Codec.traverse_results class_tight_decode xmls)
       handle Fail str => Codec.Failure ("invalid encoding for a schematic type variable: "^str, [xml]))
  | typ_tight_decode xml = Codec.Failure ("invalid encoding for a type",[xml])

val typ_tight_codec = Codec.basic {decode=typ_tight_decode, encode=typ_tight_encode}

(** A codec for terms that leads to much more compact serializations *)

fun term_tight_encode (Const(name,typ)) = XML.Elem(("c",[]),[XML.Text name,typ_tight_encode typ])
  | term_tight_encode (t1 $ t2) = XML.Elem(("a",[]),[term_tight_encode t1, term_tight_encode t2])
  | term_tight_encode (Free(name,typ)) = XML.Elem (("f",[]), [XML.Text name, typ_tight_encode typ])
  | term_tight_encode (Var((name,idx),typ)) = XML.Elem (("v",[(name,string_of_int idx)]), [typ_tight_encode typ])
  | term_tight_encode (Abs((name,T,body))) = XML.Elem (("A",[]), [XML.Text name, typ_tight_encode T, term_tight_encode body])
  | term_tight_encode (Bound i) = XML.Elem (("b",[]), [XML.Text (string_of_int i)])

fun term_tight_decode (XML.Elem(("c",[]),[XML.Text name,typ])) = 
      Codec.bind_result (fn typ => Codec.Success (Const(name,typ))) (typ_tight_decode typ)
  | term_tight_decode (XML.Elem(("a",[]),[t1, t2])) =
      Codec.bind_result (fn t1 => Codec.bind_result (fn t2 => Codec.Success (t1$t2)) (term_tight_decode t2))
      (term_tight_decode t1)
  | term_tight_decode (XML.Elem (("f",[]), [XML.Text name, xml])) =
       Codec.bind_result (fn typ => Codec.Success (Free(name,typ))) (typ_tight_decode xml)
  | term_tight_decode (xml as XML.Elem (("v",[(name,idx)]), [xml1])) =
       (Codec.bind_result (fn typ => Codec.Success (Var((name,parse_int idx),typ))) (typ_tight_decode xml1)
       handle Fail str => Codec.Failure ("invalid encoding for a schematic variable: "^str, [xml]))
  | term_tight_decode (XML.Elem (("A",[]), [XML.Text name, xml_T, xml_body])) =
       Codec.bind_result (fn T => Codec.bind_result (fn body => Codec.Success (Abs(name,T,body)))
       (term_tight_decode xml_body)) (typ_tight_decode xml_T)
  | term_tight_decode (XML.Elem (("A",[]), [xml_T, xml_body])) =
       Codec.bind_result (fn T => Codec.bind_result (fn body => Codec.Success (Abs("",T,body)))
       (term_tight_decode xml_body)) (typ_tight_decode xml_T)
  | term_tight_decode (xml as XML.Elem (("b",[]), [XML.Text (i)])) =
       (Codec.Success (Bound (parse_int i))
       handle Fail str => Codec.Failure ("invalid encoding for a schematic variable: "^str, [xml]))
  | term_tight_decode xml = Codec.Failure ("invalid encoding for a term",[xml])

val term_tight_codec = Codec.basic { encode=term_tight_encode, decode=term_tight_decode }

(** A codec for terms that additionally attaches a human readable representation *)

(* TODO rename expression -> richterm *)

fun expression_encode ctxt t = let
  (* val ctxt = Context.the_local_context () *)
  (* val str = YXML.content_of (Syntax.string_of_term ctxt t) *)
  val id = Terms.term_to_id ctxt t |> string_of_int
  (* val xml = XML.Elem (("expression",[]),[XML.Text str, term_tight_encode t, typ_tight_encode (fastype_of t)]) *)
  val xml = XML.Elem(("expression",[("id",id)]), [typ_tight_encode (fastype_of t)])
  in xml end
(* fun expression_decode (XML.Elem (("expression",[]),[XML.Text _, xml, _])) = term_tight_decode xml
  | expression_decode xml = Codec.Failure ("invalid encoding for a term (expression codec)",[xml]) *)
fun expression_decode (XML.Elem (("expression",[]),[t])) = term_tight_decode t
  | expression_decode (XML.Elem(("expression",[("id",id)]), [])) = Terms.id_to_term (parse_int id) |> Codec.Success

val expression_codec = Codec.basic { encode=fn _ => error "expression_codec: encode not allowed", decode=expression_decode }
fun expression_codec' ctxt = Codec.basic { encode=expression_encode ctxt, decode=expression_decode }


(* Statement codec *)

local open Programs open Codec in
fun call_encode (CALL (name,args)) = XML.Elem(("call",[("name",name)]), map call_encode args)

fun call_decode (XML.Elem(("call",[("name",name)]), args)) =
  map_result (fn a => CALL (name,a)) (traverse_results call_decode args)
  | call_decode xml = Codec.Failure ("invalid encoding for a call specification",[xml])


fun statement_encode ctxt (Block stmts) = XML.Elem(("block",[]), map (fn s => statement_encode ctxt (s)) stmts)
  | statement_encode ctxt (Assign (var, rhs)) = XML.Elem(("assign",[("lhs",var)]), [expression_encode ctxt rhs])
  | statement_encode ctxt (Sample (var, rhs)) = XML.Elem(("sample",[("lhs",var)]), [expression_encode ctxt rhs])
  | statement_encode _ (Call c) = call_encode c
  | statement_encode ctxt (Measurement (var,loc,exp)) = XML.Elem(("measurement",[("lhs",var)]), 
        expression_encode ctxt (exp) :: map (Codec.encode Codec.string) loc)
  | statement_encode ctxt (QInit (loc,exp)) = XML.Elem(("qinit",[]), 
        expression_encode ctxt (exp) :: map (Codec.encode Codec.string) loc)
  | statement_encode ctxt (QApply (loc,exp)) = XML.Elem(("qapply",[]), 
        expression_encode ctxt (exp) :: map (Codec.encode Codec.string) loc)
  | statement_encode ctxt (IfThenElse (e,p1,p2)) = XML.Elem(("ifte",[]),
        [expression_encode ctxt (e), statement_encode ctxt ( Block p1), statement_encode ctxt ( Block p2)])
  | statement_encode ctxt (While (e,p1)) = XML.Elem(("while",[]),
        [expression_encode ctxt (e), statement_encode ctxt ( Block p1)])

fun statement_decode (xml as XML.Elem(("block",_), _)) : statement result = 
      block_decode xml |> map_result Block
  | statement_decode (XML.Elem(("assign",[("lhs",var)]), [e])) = 
      Codec.map_result (fn e => Assign (var, e)) (expression_decode e)
  | statement_decode (XML.Elem(("sample",[("lhs",var)]), [e])) = 
      Codec.map_result (fn e => Sample (var, e)) (expression_decode e)
  | statement_decode (xml as XML.Elem(("call",_),_)) = Codec.map_result Call (call_decode xml)
  | statement_decode (XML.Elem(("measurement",[("lhs",var)]), exp :: loc)) =
      bind_result (fn exp => map_result (fn loc => Measurement (var,loc,exp))
          (traverse_results (Codec.decode Codec.string) loc))
         (expression_decode exp)
  | statement_decode (XML.Elem(("qinit",[]), exp :: loc)) =
      bind_result (fn exp => map_result (fn loc => QInit (loc,exp))
          (traverse_results (Codec.decode Codec.string) loc))
         (expression_decode exp)
  | statement_decode (XML.Elem(("qapply",[]), exp :: loc)) =
      bind_result (fn exp => map_result (fn loc => QApply (loc,exp))
          (traverse_results (Codec.decode Codec.string) loc))
         (expression_decode exp)
  | statement_decode (XML.Elem(("ifte",[]), [e, p1, p2])) =
      bind_result (fn e => bind_result (fn p1 => map_result (fn p2 => IfThenElse (e,p1,p2))
         (block_decode p2)) (block_decode p1)) (expression_decode e)
  | statement_decode (XML.Elem(("while",[]), [e, p1])) =
      bind_result (fn e => map_result (fn p1 => While (e,p1))
         (block_decode p1)) (expression_decode e)
  | statement_decode xml = Codec.Failure ("invalid encoding for a statement",[xml])

and
  block_decode (XML.Elem(("block",[]), stmts)) : statement list result = 
    Codec.traverse_results statement_decode stmts
  | block_decode xml = Codec.Failure ("invalid encoding for a block",[xml])

val statement_codec = Codec.basic {encode=fn _ => error "statement_codec: encode not allowed", decode=statement_decode}
fun statement_codec' ctxt = Codec.basic {encode=statement_encode ctxt, decode=statement_decode}

datatype subgoal = Subgoal_QRHL of Relational_Hoare.qrhl_judgment * term list | Subgoal_Ambient of term

fun subgoal_to_term ctxt (Subgoal_QRHL (qrhl, assms)) = 
    fold_rev (fn a => fn g => HOLogic.mk_imp (a, g)) assms (Relational_Hoare.qrhl_judgment_to_term ctxt qrhl)
  | subgoal_to_term _ (Subgoal_Ambient t) = t

fun term_to_subgoal ctxt t = let
  fun split_assms assms (Const(\<^const_name>\<open>implies\<close>,_) $ a $ b) = split_assms (a::assms) b
    | split_assms assms t = (assms,t)
  val (assms,t') = split_assms [] t
  in
    case t' of (Const(\<^const_name>\<open>qrhl\<close>,_) $ _ $ _ $ _ $ _) => 
      Subgoal_QRHL (Relational_Hoare.term_to_qrhl_judgment ctxt t', assms)
   | _ => Subgoal_Ambient t
  end

fun qrhl_encode (ctxt, Relational_Hoare.QRHL_Judgment (pre,p1,p2,post)) = XML.Elem(("qrhl",[]),
  [expression_encode ctxt (pre), statement_encode ctxt (Programs.Block p1), statement_encode ctxt (Programs.Block p2),
   expression_encode ctxt (post)])

fun qrhl_decode (XML.Elem(("qrhl",[]), [pre,p1,p2,post])) =
  bind_result (fn pre => 
  bind_result (fn p1 => 
  bind_result (fn p2 => 
  map_result (fn post => Relational_Hoare.QRHL_Judgment (pre,p1,p2,post)) (expression_decode post))
  (block_decode p2)) (block_decode p1)) (expression_decode pre)
  | qrhl_decode xml = Codec.Failure ("invalid encoding for a qrhl statement",[xml])


fun subgoal_encode ctxt (Subgoal_QRHL (qrhl,assms)) = XML.Elem(("qrhlgoal",[]), 
  qrhl_encode (ctxt, qrhl) :: map (fn assm => expression_encode ctxt ( assm)) assms) 
  | subgoal_encode ctxt (Subgoal_Ambient t) = XML.Elem(("ambient",[]), [expression_encode ctxt ( t)])

fun subgoal_decode (XML.Elem(("qrhlgoal",[]), qrhl::assms)) =
  bind_result (fn qrhl => (map_result (fn assms => Subgoal_QRHL (qrhl,assms)) 
      (traverse_results expression_decode assms))) (qrhl_decode qrhl)
  | subgoal_decode (XML.Elem(("ambient",[]), [t])) = expression_decode t |> map_result Subgoal_Ambient
  | subgoal_decode xml = Codec.Failure ("invalid encoding for a subgoal",[xml])

val subgoal_codec = Codec.basic {encode=fn _ => error "subgoal_codec: encode not allowed", decode=subgoal_decode}
fun subgoal_codec' ctxt = Codec.basic {encode=subgoal_encode ctxt, decode=subgoal_decode}

fun apply_tactic_on_term_concl tac (arg,subgoal,ctxt) = let
  (* val _ = warning "STEP 1" *)
  val goal = subgoal_to_term ctxt subgoal
  (* val _ = warning "STEP 2" *)
  val subgoals = Tactics.tac_on_term_concl (tac ctxt arg) ctxt goal
  (* val _ = warning "STEP 3" *)
  val subgoals = subgoals |> Option.map (map (term_to_subgoal ctxt))
  (* val _ = warning "STEP 4" *)
  val subgoals = subgoals |> tac_dummy_thm
  (* val _ = warning "STEP 5" *)
  val encoded = subgoals |> Codec.encode (Codec.option (Codec.tuple (Codec.list (subgoal_codec' ctxt)) thm_codec))
  (* val _ = warning "STEP 6" *)
  in encoded end

fun apply_tactic_on_term tac name (arg,subgoal,ctxt) = let
  val goal = subgoal_to_term ctxt subgoal
  val cgoal = Thm.cterm_of ctxt (HOLogic.mk_Trueprop goal)
  val goal' = Goal.init cgoal
  val goal'' = case SINGLE (tac ctxt arg) goal' of
                NONE => raise TERM(name arg^" could not be applied", [goal])
               | SOME x => x
  val subgoals = Thm.prems_of goal''
  val subgoals' = map HOLogic.dest_Trueprop subgoals
  in SOME (subgoals' |> map (term_to_subgoal ctxt),goal'')  |> Codec.encode (Codec.option (Codec.tuple (Codec.list (subgoal_codec' ctxt)) thm_codec)) end
end

end