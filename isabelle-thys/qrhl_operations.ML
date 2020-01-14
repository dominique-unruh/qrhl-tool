structure QRHL_Operations = 
struct

fun tuple4 a b c d =
  Codec.tuple a (Codec.triple b c d)
  |> Codec.transform (fn (a, (b, c, d)) => (a, b, c, d)) (fn (a, b, c, d) => (a, (b, c, d)))

fun tuple5 a b c d e =
  Codec.tuple a (tuple4 b c d e)
  |> Codec.transform (fn (a, (b, c, d, e)) => (a, b, c, d, e)) (fn (a, b, c, d, e) => (a, (b, c, d, e)))


fun tuple6 a b c d e f =
  Codec.tuple a (tuple5 b c d e f)
  |> Codec.transform (fn (a, (b, c, d, e, f)) => (a, b, c, d, e, f)) (fn (a, b, c, d, e, f) => (a, (b, c, d, e, f)))


fun tuple7 a b c d e f g =
  Codec.tuple a (tuple6 b c d e f g)
  |> Codec.transform (fn (a, (b, c, d, e, f, g)) => (a, b, c, d, e, f, g)) (fn (a, b, c, d, e, f, g) => (a, (b, c, d, e, f, g)))

fun tuple8 a b c d e f g h =
  Codec.tuple a (tuple7 b c d e f g h)
  |> Codec.transform (fn (a, (b, c, d, e, f, g, h)) => (a, b, c, d, e, f, g, h)) (fn (a, b, c, d, e, f, g, h) => (a, (b, c, d, e, f, g, h)))

fun tuple9 a b c d e f g h i =
  Codec.tuple a (tuple8 b c d e f g h i)
  |> Codec.transform (fn (a, (b, c, d, e, f, g, h, i)) => (a, b, c, d, e, f, g, h, i)) (fn (a, b, c, d, e, f, g, h, i) => (a, (b, c, d, e, f, g, h, i)))

fun tuple10 a b c d e f g h i j =
  Codec.tuple a (tuple9 b c d e f g h i j)
  |> Codec.transform (fn (a, (b, c, d, e, f, g, h, i, j)) => (a, b, c, d, e, f, g, h, i, j)) (fn (a, b, c, d, e, f, g, h, i, j) => (a, (b, c, d, e, f, g, h, i, j)))

fun tuple11 a b c d e f g h i j k =
  Codec.tuple a (tuple10 b c d e f g h i j k)
  |> Codec.transform (fn (a, (b, c, d, e, f, g, h, i, j, k)) => (a, b, c, d, e, f, g, h, i, j, k)) (fn (a, b, c, d, e, f, g, h, i, j, k) => (a, (b, c, d, e, f, g, h, i, j, k)))

fun tuple12 a b c d e f g h i j k l =
  Codec.tuple a (tuple11 b c d e f g h i j k l)
  |> Codec.transform (fn (a, (b, c, d, e, f, g, h, i, j, k, l)) => (a, b, c, d, e, f, g, h, i, j, k, l))
                     (fn (a, b, c, d, e, f, g, h, i, j, k, l) => (a, (b, c, d, e, f, g, h, i, j, k, l)))


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

fun richterm_encode ctxt t = let
  (* val ctxt = Context.the_local_context () *)
  (* val str = YXML.content_of (Syntax.string_of_term ctxt t) *)
  val id = Terms.term_to_id ctxt t |> string_of_int
  (* val xml = XML.Elem (("richterm",[]),[XML.Text str, term_tight_encode t, typ_tight_encode (fastype_of t)]) *)
  val xml = XML.Elem(("richterm",[("id",id)]), [typ_tight_encode (fastype_of t)])
  in xml end
(* fun richterm_decode (XML.Elem (("richterm",[]),[XML.Text _, xml, _])) = term_tight_decode xml
  | richterm_decode xml = Codec.Failure ("invalid encoding for a term (richterm codec)",[xml]) *)
fun richterm_decode (XML.Elem (("richterm",[]),[t])) = term_tight_decode t
  | richterm_decode (XML.Elem(("richterm",[("id",id)]), [])) = Terms.id_to_term (parse_int id) |> Codec.Success
  | richterm_decode _ = error "richterm_decode"

val richterm_codec = Codec.basic { encode=fn _ => error "richterm_codec: encode not allowed", decode=richterm_decode }
fun richterm_codec' ctxt = Codec.basic { encode=richterm_encode ctxt, decode=richterm_decode }


(* Statement codec *)

local open Programs open Codec open Prog_Variables in
fun call_encode (CALL (name,args)) = XML.Elem(("call",[("name",name)]), map call_encode args)

fun call_decode (XML.Elem(("call",[("name",name)]), args)) =
  map_result (fn a => CALL (name,a)) (traverse_results call_decode args)
  | call_decode xml = Codec.Failure ("invalid encoding for a call specification",[xml])

fun string_tree_encode VTUnit = XML.Elem(("u",[]),[])
  | string_tree_encode (VTCons(a,b)) = XML.Elem(("c",[]),[string_tree_encode a,string_tree_encode b])
  | string_tree_encode (VTSingle s) = XML.Elem(("s",[]),[XML.Text s])

fun string_tree_decode (XML.Elem(("u",[]),[])) : string tree result = Codec.Success VTUnit
  | string_tree_decode (XML.Elem(("c",[]),[a,b])) =
      bind_result (fn a' => map_result (fn b' => VTCons(a',b'))
        (string_tree_decode b)) (string_tree_decode a)
  | string_tree_decode (XML.Elem(("s",[]),[XML.Text s])) = Codec.Success (VTSingle s)
  | string_tree_decode xml = Codec.Failure ("invalid encoding for a string tree",[xml])

fun varterm_encode VTUnit = XML.Elem(("u",[]),[])
  | varterm_encode (VTCons(a,b)) = XML.Elem(("c",[]),[varterm_encode a, varterm_encode b])
  | varterm_encode (VTSingle (n,T)) = XML.Elem(("s",[]),[XML.Elem(("V",[("name",n)]), [typ_tight_encode T])])


fun varterm_decode (XML.Elem(("u",[]),[])) : (string*typ) tree result = Codec.Success VTUnit
  | varterm_decode (XML.Elem(("c",[]),[a,b])) =
      bind_result (fn a' => map_result (fn b' => VTCons(a',b'))
        (varterm_decode b)) (varterm_decode a)
  | varterm_decode (XML.Elem(("s",[]),[XML.Elem(("V",[("name",n)]), [typ])])) = 
      map_result (fn T => VTSingle (n,T)) (typ_tight_decode typ)
  | varterm_decode xml = Codec.Failure ("invalid encoding for a string tree",[xml])


(* fun string_list_encode l = XML.Elem(("l",[]),map (Codec.encode Codec.string) l) *)
(* fun string_list_decode (XML.Elem(("l",[]), l)) = traverse_results (Codec.decode Codec.string) l *)

fun statement_encode ctxt (Block stmts) = XML.Elem(("block",[]), map (fn s => statement_encode ctxt (s)) stmts)
  | statement_encode ctxt (Local(cvars,qvars,stmts)) = (XML.Elem(("local",[]), 
      [varterm_encode cvars, varterm_encode qvars, statement_encode ctxt (Block stmts)]))
  | statement_encode ctxt (Assign (var, rhs)) = XML.Elem(("assign",[]), [string_tree_encode var, richterm_encode ctxt rhs])
  | statement_encode ctxt (Sample (var, rhs)) = XML.Elem(("sample",[]), [string_tree_encode var, richterm_encode ctxt rhs])
  | statement_encode _ (Call c) = call_encode c
  | statement_encode ctxt (Measurement (var,loc,exp)) = XML.Elem(("measurement",[]), 
        [string_tree_encode var, string_tree_encode loc, richterm_encode ctxt exp])
  | statement_encode ctxt (QInit (loc,exp)) = XML.Elem(("qinit",[]), 
        [string_tree_encode loc, richterm_encode ctxt (exp)])
  | statement_encode ctxt (QApply (loc,exp)) = XML.Elem(("qapply",[]), 
        [string_tree_encode loc, richterm_encode ctxt (exp)])
  | statement_encode ctxt (IfThenElse (e,p1,p2)) = XML.Elem(("ifte",[]),
        [richterm_encode ctxt (e), statement_encode ctxt (Block p1), statement_encode ctxt (Block p2)])
  | statement_encode ctxt (While (e,p1)) = XML.Elem(("while",[]),
        [richterm_encode ctxt (e), statement_encode ctxt (Block p1)])

fun statement_decode (xml as XML.Elem(("block",_), _)) : statement result = 
      block_decode xml |> map_result Block
  | statement_decode (XML.Elem(("local",_), [cvars,qvars,body])) =
      bind_result (fn cvars' => bind_result (fn qvars' => map_result (fn stmts => Local(cvars',qvars',stmts))
        (block_decode body)) (varterm_decode qvars)) (varterm_decode cvars)
  | statement_decode (XML.Elem(("assign",[]), [lhs,e])) = 
      bind_result (fn lhs' => map_result (fn e' => Assign (lhs',e'))
        (richterm_decode e)) (string_tree_decode lhs)
  | statement_decode (XML.Elem(("sample",[]), [lhs,e])) = 
      bind_result (fn lhs' => map_result (fn e' => Sample (lhs',e'))
        (richterm_decode e)) (string_tree_decode lhs)
  | statement_decode (xml as XML.Elem(("call",_),_)) = Codec.map_result Call (call_decode xml)
  | statement_decode (XML.Elem(("measurement",[]), [lhs,loc,exp])) =
      bind_result (fn lhs' => bind_result (fn loc' => map_result (fn exp' => Measurement(lhs',loc',exp'))
        (richterm_decode exp)) (string_tree_decode loc)) (string_tree_decode lhs)
  | statement_decode (XML.Elem(("qinit",[]), [loc,exp])) =
      bind_result (fn loc' => map_result (fn e' => QInit (loc',e'))
        (richterm_decode exp)) (string_tree_decode loc)
  | statement_decode (XML.Elem(("qapply",[]), [loc,exp])) =
      bind_result (fn loc' => map_result (fn e' => QApply (loc',e'))
        (richterm_decode exp)) (string_tree_decode loc)
  | statement_decode (XML.Elem(("ifte",[]), [e, p1, p2])) =
      bind_result (fn e => bind_result (fn p1 => map_result (fn p2 => IfThenElse (e,p1,p2))
         (block_decode p2)) (block_decode p1)) (richterm_decode e)
  | statement_decode (XML.Elem(("while",[]), [e, p1])) =
      bind_result (fn e => map_result (fn p1 => While (e,p1))
         (block_decode p1)) (richterm_decode e)
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

fun contains_var (t $ u) = contains_var t orelse contains_var u
  | contains_var (Const _) = false
  | contains_var (Abs (_,_,t)) = contains_var t
  | contains_var (Free _) = false
  | contains_var (Var _) = true
  | contains_var (Bound _) = false

fun term_to_subgoal ctxt t = let
  val _ = if contains_var t then raise TERM("New subgoal contains schematic variables",[t]) else ()
  fun split_assms assms (Const(\<^const_name>\<open>implies\<close>,_) $ a $ b) = split_assms (a::assms) b
    | split_assms assms (Const(\<^const_name>\<open>Trueprop\<close>,_) $ t) = split_assms assms t
    | split_assms assms t = (assms,t)
  val (assms,t') = split_assms [] t
  in
    case t' of (Const(\<^const_name>\<open>qrhl\<close>,_) $ _ $ _ $ _ $ _) => 
      Subgoal_QRHL (Relational_Hoare.term_to_qrhl_judgment ctxt t', assms)
   | _ => Subgoal_Ambient t
  end

(* val _ = term_to_subgoal \<^context> @{term "qrhl Expr[top] [xxx] [xxx] Expr[top]"} |> \<^print> *)

fun qrhl_encode (ctxt, Relational_Hoare.QRHL_Judgment (pre,p1,p2,post)) = XML.Elem(("qrhl",[]),
  [richterm_encode ctxt (pre), statement_encode ctxt (Programs.Block p1), statement_encode ctxt (Programs.Block p2),
   richterm_encode ctxt (post)])

fun qrhl_decode (XML.Elem(("qrhl",[]), [pre,p1,p2,post])) =
  bind_result (fn pre => 
  bind_result (fn p1 => 
  bind_result (fn p2 => 
  map_result (fn post => Relational_Hoare.QRHL_Judgment (pre,p1,p2,post)) (richterm_decode post))
  (block_decode p2)) (block_decode p1)) (richterm_decode pre)
  | qrhl_decode xml = Codec.Failure ("invalid encoding for a qrhl statement",[xml])


fun subgoal_encode ctxt (Subgoal_QRHL (qrhl,assms)) = XML.Elem(("qrhlgoal",[]), 
  qrhl_encode (ctxt, qrhl) :: map (fn assm => richterm_encode ctxt ( assm)) assms) 
  | subgoal_encode ctxt (Subgoal_Ambient t) = XML.Elem(("ambient",[]), [richterm_encode ctxt ( t)])

fun subgoal_decode (XML.Elem(("qrhlgoal",[]), qrhl::assms)) =
  bind_result (fn qrhl => (map_result (fn assms => Subgoal_QRHL (qrhl,assms)) 
      (traverse_results richterm_decode assms))) (qrhl_decode qrhl)
  | subgoal_decode (XML.Elem(("ambient",[]), [t])) = richterm_decode t |> map_result Subgoal_Ambient
  | subgoal_decode xml = Codec.Failure ("invalid encoding for a subgoal",[xml])

val subgoal_codec = Codec.basic {encode=fn _ => error "subgoal_codec: encode not allowed", decode=subgoal_decode}
fun subgoal_codec' ctxt = Codec.basic {encode=subgoal_encode ctxt, decode=subgoal_decode}

fun apply_tactic_on_term_concl tac (arg,subgoal,ctxt) = let
  val goal = subgoal_to_term ctxt subgoal
  val subgoals = Tactics.tac_on_term_concl (tac ctxt arg) ctxt goal
  val subgoals = subgoals |> Option.map (map (term_to_subgoal ctxt))
  val subgoals = subgoals |> tac_dummy_thm
  val encoded = subgoals |> Codec.encode (Codec.option (Codec.tuple (Codec.list (subgoal_codec' ctxt)) thm_codec))
  in encoded end

fun atomize ctxt t =
  let val t' = Object_Logic.atomize_term ctxt t
      val _ = if fastype_of t' <> \<^typ>\<open>bool\<close> then
                raise TERM("QRHL_Operations.atomize: could not convert term to a bool",[t])
              else ()
  in t' end

fun apply_tactic_on_term tac name (arg,subgoal,ctxt) = let
  val goal = subgoal_to_term ctxt subgoal
  val cgoal = Thm.cterm_of ctxt (HOLogic.mk_Trueprop goal)
  val goal' = Goal.init cgoal
  val goal'' = case SINGLE (tac ctxt arg) goal' of
                NONE => raise TERM(name arg^" could not be applied", [goal])
               | SOME x => x
  val subgoals = Thm.prems_of goal''
  val subgoals' = map (atomize ctxt) subgoals
  in SOME (subgoals' |> map (term_to_subgoal ctxt),goal'')  |> Codec.encode (Codec.option (Codec.tuple (Codec.list (subgoal_codec' ctxt)) thm_codec)) end
end

fun local_thy_file thy = let val name = Context.theory_long_name thy in
  if String.isPrefix "Draft." name then
  let val short = Context.theory_name thy
      val dir = Thy_Info.master_directory name
  in SOME (Path.append dir (Path.basic (short^".thy")) |> Path.implode) end
  else NONE 
end
  
fun create_context thy_names = let
     val thys = map Thy_Info.get_theory thy_names
     val thy = Theory.begin_theory ("QRHL_Session", Position.none) thys
     val files = thy |> Theory.ancestors_of 
                     |> map_filter local_thy_file 
     val ctxt = Proof_Context.init_global thy
in (make_ctxt_ref ctxt,files) end


fun addAssumption name term ctx =
  let val prop = case fastype_of term of
                   \<^typ>\<open>bool\<close> => HOLogic.mk_Trueprop term
                 | \<^typ>\<open>prop\<close> => term
                 | T => raise (TYPE("expected a boolean expression",[T],[term]))
      val (_,ctx) = Proof_Context.add_assms Assumption.assume_export
                               [((Binding.name name,[]), [(prop,[])])] ctx
  in
    ctx
  end

fun declare_abstract_program ctxt (name:string) (cvars:(string*typ)list) (cwvars:(string*typ)list) (qvars:(string*typ)list) (numOracles:int)= let
  val T = if numOracles=0 then \<^typ>\<open>program\<close> else \<^typ>\<open>oracle_program\<close>

  (* Declare the program name as a fixed variable *)
  val (vs,ctxt) = Proof_Context.add_fixes [(Binding.name name, SOME T, NoSyn)] ctxt
  val _ = if vs<>[name] then error("variable "^name^" already declared") else ()

  fun declare_prog_vars vars pfx fv_program fv_oracle_program ctxt = let
    (* Add theorem pfx^name: "fv_program/fv_oracle_program name = variable_names \<lbrakk>vars\<rbrakk> *)
    val fv_lhs = (if numOracles=0 then fv_program else fv_oracle_program) $ Free(name,T) 
    val (varterm,vartermT) = vars |> Prog_Variables.varterm_from_list |> Prog_Variables.mk_varterm
    val fv_rhs = @{const set(string)} $
            (Const(\<^const_name>\<open>variable_names\<close>, Prog_Variables.mk_variablesT vartermT --> \<^typ>\<open>string list\<close>) $ varterm)
    val fv = HOLogic.mk_eq (fv_lhs, fv_rhs) |> HOLogic.mk_Trueprop
    val fv_thm_name = Binding.name (pfx^name)
    val ([(_,fv_thm)],ctxt) = Proof_Context.add_assms Assumption.assume_export
                                 [((fv_thm_name, []), [(fv,[])])] ctxt
    (* Add fv_name to dynamic fact program_fv *)
    val (_,ctxt) = Attrib.local_notes "" [((Binding.empty, @{attributes [Programs.program_fv]}), [(fv_thm,[])])] ctxt
  in ctxt end

  val var_cvars = map (fn (n,T) => ("var_"^n,T)) cvars
  val var_cwvars = map (fn (n,T) => ("var_"^n,T)) cwvars
  val ctxt = declare_prog_vars var_cvars "fvc_" \<^const>\<open>fvc_program\<close> \<^const>\<open>fvc_oracle_program\<close> ctxt
  val ctxt = declare_prog_vars var_cwvars "fvcw_" \<^const>\<open>fvcw_program\<close> \<^const>\<open>fvcw_oracle_program\<close> ctxt
  val ctxt = declare_prog_vars qvars "fvq_" \<^const>\<open>fvq_program\<close> \<^const>\<open>fvq_oracle_program\<close> ctxt

  (* Add abbreviations:
        name_cvars1 == (x1,y1,z1) if cvars=x,y,z (same with 2, and w/o index)
        name_qvars1 == \<lbrakk>x1,y1,z1\<rbrakk> if qvars=x,y,z (same with 2, and w/o index) *)
  fun add_vars_abbrev suffix ctxt = let
    val cvartuple = HOLogic.mk_tuple (map (fn (n,T) => Free(n^suffix,T)) cvars)
    val (_,ctxt) = Proof_Context.add_abbrev Print_Mode.input (Binding.name (name^"_cvars"^suffix), cvartuple) ctxt
    val (qvarterm,_) = qvars |> (map (fn (n,T) => (n^suffix,T))) |> Prog_Variables.varterm_from_list |> Prog_Variables.mk_varterm
    val (_,ctxt) = Proof_Context.add_abbrev Print_Mode.input (Binding.name (name^"_qvars"^suffix), qvarterm) ctxt
  in ctxt end

  val ctxt = add_vars_abbrev "" ctxt
  val ctxt = add_vars_abbrev "1" ctxt
  val ctxt = add_vars_abbrev "2" ctxt
in ctxt end

fun declare_concrete_program ctxt (name:string) (cvars:(string*typ)list) (cwvars:(string*typ)list) (qvars:(string*typ)list) (oracles:string list) (body:Programs.statement) = let
  val ctxt = declare_abstract_program ctxt name cvars cwvars qvars (length oracles)

  fun tag ora = "@"^ora
  val body_rhs = Programs.statement_to_term ctxt body
  val body_lhs = if null oracles
                 then Free(name,\<^typ>\<open>program\<close>)
                 else \<^const>\<open>instantiateOracles\<close> $ Free(name,\<^typ>\<open>oracle_program\<close>) $ 
                      HOLogic.mk_list \<^typ>\<open>program\<close> (map (fn n => Free(tag n,\<^typ>\<open>program\<close>)) oracles)
  val body_def = HOLogic.mk_eq (body_lhs, body_rhs) |> HOLogic.mk_Trueprop
  val body_def = fold_rev (fn ora => fn t => Logic.all (Free(tag ora,\<^typ>\<open>program\<close>)) t) oracles body_def
  val body_def_name = Binding.name name |> Binding.suffix_name "_def"
  val ([(_,body_thm)],ctxt) = Proof_Context.add_assms Assumption.assume_export
                               [((body_def_name, []), [(body_def,[])])] ctxt
  val (_,ctxt) = Attrib.local_notes "" [((Binding.empty, @{attributes [Programs.program_bodies]}), [(body_thm,[])])] ctxt

in ctxt end

fun get_thms ctxt spec = let
  val toks = Token.explode0 (Thy_Header.get_keywords' ctxt) spec
             |> filter (not o Token.is_blank)
             |> (fn t => t @ [Token.eof])
  val (parsed,leftover) = Scan.catch Parse.thm toks
  val _ = case leftover of [_] => ()
          | _ => error ("Error parsing theorem name \"" ^ spec ^ 
                "\". Leftover tokens: " ^ Pretty.string_of (Token.pretty_src ctxt leftover))
  val fact = Attrib.eval_thms ctxt [parsed] (* Gives me "?t=?t", not "x=x" *)
in fact end

(* val _ = get_thms \<^context> "refl" |> \<^print>  *)

fun debug ctxt = let
  val obj = Proof_Context.get_fact ctxt (Facts.named "Programs.program_fv")
  val str = \<^make_string> obj |> YXML.content_of
  in str end


fun simp_any t ctx =
  let val ct = Thm.cterm_of ctx t
      val ct_eq_thm = Simplifier.asm_full_rewrite ctx ct
      val ct_eq = ct_eq_thm |> Thm.prop_of
      val (lhs,rhs) = Logic.dest_equals ct_eq
      val _ = if lhs<>t then raise TERM("conversion returned wrong lhs\n",[t,lhs,rhs]) else ()
  in
    (rhs,ct_eq_thm)
  end

fun simp_prop t ctx = 
  let val ct = Thm.cterm_of ctx t
      val goal = Goal.init ct
      val result = SINGLE (asm_full_simp_tac ctx 1) goal
  in
    case result of
      NONE => raise TERM("asm_full_simp_tac failed",[t])
    | SOME thm => case Thm.prems_of thm of
                    [t'] => (t',thm)
                  | [] => (\<^prop>\<open>True\<close>,thm)
                  | _ => raise THM("asm_full_simp_tac produced multiple subgoals",0,[thm])
  end       

fun simp_bool t ctx =
  let val prop = HOLogic.mk_Trueprop t
      val (res,thm) = simp_prop prop ctx
  in
    case res of
      (Const (\<^const_name>\<open>Trueprop\<close>, _) $ P) => (P,thm)
    | _ => raise TERM("simp_prop did not return a term starting with Trueprop",[t,res])
  end

fun simp t facts ctxt =
  let val thms = (map (get_thms ctxt) facts |> List.concat)
      val ctxt  = fold (fn name => fn ctx => ctx addsimps thms) facts ctxt
  in case fastype_of t of
        Type(\<^type_name>\<open>prop\<close>,_) => simp_prop t ctxt
      | Type(\<^type_name>\<open>bool\<close>,_) => simp_bool t ctxt
      | _ => simp_any t ctxt
  end

fun conseq_qrhl_replace_in_predicate ctxt predicate beforeLeft afterLeft beforeRight afterRight = let
(* val _ = \<^print> predicate *)
  val (pred_lhs, qeq_left, qeq_right) = case predicate of
      Const(\<^const_name>\<open>inf\<close>,_) $ pred_lhs $ (Const(\<^const_name>\<open>quantum_equality_full\<close>,_) $ U $ Q $ V $ R) => let
        val _ = case U of Const(\<^const_name>\<open>idOp\<close>,_) => () | _ => 
            raise TERM("The quantum equality must be a simple one (\<lbrakk>...\<rbrakk> \<equiv>\<^sub>\<qq> \<lbrakk>...\<rbrakk>), not one with operators (quantum_equality_full U \<lbrakk>...\<rbrakk> V \<lbrakk>...\<rbrakk>)", [predicate])
        val _ = case V of Const(\<^const_name>\<open>idOp\<close>,_) => () | _ => 
            raise TERM("The quantum equality must be a simple one (\<lbrakk>...\<rbrakk> \<equiv>\<^sub>\<qq> \<lbrakk>...\<rbrakk>), not one with operators (quantum_equality_full U \<lbrakk>...\<rbrakk> V \<lbrakk>...\<rbrakk>)", [predicate])
        in (pred_lhs, Q, R) end
    | _ => raise TERM("Pre/postcondition must be of the form {... \<sqinter> \<lbrakk>...\<rbrakk> \<equiv>\<^sub>\<qq> \<lbrakk>...\<rbrakk>}", [predicate])
  val vt_left = Prog_Variables.parse_varlist qeq_left
  val vt_right = Prog_Variables.parse_varlist qeq_right
  val _ = if List.drop (vt_left, (length vt_left - length beforeLeft)) = beforeLeft
          then ()
          else raise TERM("Lhs of quantum equality does not end with the right variables",[predicate,qeq_left])
  val _ = if List.drop (vt_right, (length vt_right - length beforeRight)) = beforeRight
          then ()
          else raise TERM("Rhs of quantum equality does not end with the right variables",[predicate,qeq_right])
  val keep_left = List.take (vt_left, (length vt_left - length beforeLeft))
  val keep_right = List.take (vt_right, (length vt_right - length beforeRight))
  val (_,keep_leftT) = Prog_Variables.varterm_from_list keep_left |> Prog_Variables.mk_varterm
  val (_,keep_rightT) = Prog_Variables.varterm_from_list keep_right |> Prog_Variables.mk_varterm
  val _ = if keep_leftT = keep_rightT then ()
          else error "conseq_qrhl_replace_in_predicate: type error"
  (* val qeq_keep = QRHL.mk_quantum_equality keep_left_vt keep_right_vt keep_leftT *)
  val (replaced_left_vt,replaced_leftT) = Prog_Variables.varterm_from_list (keep_left @ afterLeft) |> Prog_Variables.mk_varterm
  val (replaced_right_vt,replaced_rightT) = Prog_Variables.varterm_from_list (keep_right @ afterRight) |> Prog_Variables.mk_varterm
  val _ = if replaced_leftT = replaced_rightT then ()
          else error "conseq_qrhl_replace_in_predicate: type error"
  val qeq_replaced = QRHL.mk_quantum_equality replaced_left_vt replaced_right_vt replaced_leftT
  val pred' = @{const inf(predicate)} $ pred_lhs $ qeq_replaced
  (* val pred_keep = @{const inf(predicate)} $ pred_lhs $ qeq_keep *)
  val all_vars0 = beforeLeft @ beforeRight @ afterLeft @ afterRight
  val (all_vars, all_varsT) = all_vars0
                 |> Prog_Variables.varterm_from_list |> Prog_Variables.mk_varterm
(*   val beforeLeft_set = Symtab.make_set (map fst beforeLeft)
  val beforeRight_set = Symtab.make_set (map fst beforeRight)
  val afterLeft_set = Symtab.make_set (map fst afterLeft)
  val afterRight_set = Symtab.make_set (map fst afterRight) *)
  val keepLeft_set = Symtab.make_set (map fst keep_left)
  val keepRight_set = Symtab.make_set (map fst keep_right)
  val _ = if not (List.exists (fn (n,_) => Symtab.defined keepLeft_set n) beforeLeft) then ()
          else error "Left quantum equality has duplicate variables"
  val _ = if not (List.exists (fn (n,_) => Symtab.defined keepRight_set n) beforeRight) then ()
          else error "Right quantum equality has duplicate variables"
  val _ = if not (List.exists (fn (n,_) => Symtab.defined keepLeft_set n) afterLeft) then ()
          else error "Left quantum equality has variables that conflict with replacement variables"
  val _ = if not (List.exists (fn (n,_) => Symtab.defined keepRight_set n) afterRight) then ()
          else error "Left quantum equality has variables that conflict with replacement variables"
  val colocality = Const(\<^const_name>\<open>colocal_pred_qvars\<close>, \<^typ>\<open>predicate\<close> --> QRHL.mk_variablesT all_varsT --> HOLogic.boolT)
                 $ pred_lhs $ all_vars
in
  (pred', colocality)
end
;;

(* val _ = conseq_qrhl_replace_in_predicate \<^context> \<^term>\<open>Cla[x1=1] \<sqinter> Qeq[q1,Z1::int variable = r2,Z2]\<close>
        [("Z1",\<^typ>\<open>int\<close>)] [("s1",\<^typ>\<open>int\<close>),("t1",\<^typ>\<open>int\<close>)]
        [("Z2",\<^typ>\<open>int\<close>)] [("s2",\<^typ>\<open>int\<close>),("t2",\<^typ>\<open>int\<close>)]
|> \<^print> *)

fun method_tac ctxt str = let
  val (text,_) = Method.read_closure_input ctxt (Input.string str)
  val tactic = Method.evaluate text ctxt [] |> Method.NO_CONTEXT_TACTIC ctxt
in tactic end

end
