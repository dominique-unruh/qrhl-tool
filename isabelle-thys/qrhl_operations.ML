structure QRHL_Operations = 
struct

open Programs
open Prog_Variables
open QRHL

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


fun tac_dummy_thm NONE = NONE
  | tac_dummy_thm (SOME ts) = SOME (ts,@{thm TrueI})

fun parse_term ctx str T = let
  val parsed = Syntax.parse_term ctx str
  val constrained = Const("_type_constraint_", T --> T) $ parsed
  val term = Syntax.check_term ctx constrained
in term end


(* Statement codec *)

local in

datatype subgoal = Subgoal_QRHL of Relational_Hoare.qrhl_judgment * term list
  | Subgoal_Ambient of term | Subgoal_Denotational_Eq of Programs.statement * Programs.statement * term list

fun qrhl_subgoal_to_term (ctxt,left,right,pre,post,assms) =
  fold_rev (fn a => fn g => HOLogic.mk_imp (a, g)) assms 
    (Relational_Hoare.qrhl_judgment_to_term ctxt (Relational_Hoare.QRHL_Judgment (pre,left,right,post)))

fun denotational_eq_subgoal_to_term (ctxt, left, right, assms) =
    fold_rev (fn a => fn g => HOLogic.mk_imp (a, g)) assms 
      (HOLogic.mk_eq (\<^Const>\<open>denotation\<close> $ statement_to_term ctxt left, \<^Const>\<open>denotation\<close> $ statement_to_term ctxt right))

fun subgoal_to_term ctxt (Subgoal_QRHL (qrhl, assms)) = 
    fold_rev (fn a => fn g => HOLogic.mk_imp (a, g)) assms (Relational_Hoare.qrhl_judgment_to_term ctxt qrhl)
  | subgoal_to_term ctxt (Subgoal_Denotational_Eq (left, right, assms)) =
    denotational_eq_subgoal_to_term (ctxt, left, right, assms)
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
   | (\<^Const_>\<open>HOL.equal _\<close> $ (\<^Const_>\<open>denotation\<close> $ p1) $ (\<^Const_>\<open>denotation\<close> $ p2)) => 
      Subgoal_Denotational_Eq (term_to_statement ctxt p1, term_to_statement ctxt p2, assms)
   | _ => Subgoal_Ambient t
  end

fun apply_tactic_on_term_concl tac (arg,subgoal,ctxt) = let
  val goal = subgoal_to_term ctxt subgoal
  val subgoals = Tactics.tac_on_term_concl (tac ctxt arg) ctxt goal
  val subgoals = subgoals |> Option.map (map (term_to_subgoal ctxt))
  val subgoals = subgoals |> tac_dummy_thm
  (* val encoded = subgoals |> Codec.encode (Codec.option (Codec.tuple (Codec.list (subgoal_codec' ctxt)) thm_codec)) *)
  in subgoals end

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
                NONE => error (name arg^" could not be applied to the current goal")
               | SOME x => x
  val subgoals = Thm.prems_of goal''
  val subgoals' = map (atomize ctxt) subgoals
  in SOME (subgoals' |> map (term_to_subgoal ctxt),goal'') end
end

fun local_thy_file thy : Path.T option = let val name = Context.theory_long_name thy in
  if String.isPrefix "Draft." name then
  let val short = Context.theory_name thy
      val dir = Thy_Info.master_directory name
  in SOME (Path.append dir (Path.basic (short^".thy"))(*  |> Path.implode *)) end
  else NONE 
end
  
(* fun create_context thy_names = let
     val thys = map Thy_Info.get_theory thy_names
     val thy = Theory.begin_theory ("QRHL_Session", Position.none) thys
     val files = thy |> Theory.ancestors_of 
                     |> map_filter local_thy_file 
     val ctxt = Proof_Context.init_global thy
in (ctxt,files) end *)


fun addAssumption (name, term, ctx) =
  let val prop = case fastype_of term of
                   \<^typ>\<open>bool\<close> => HOLogic.mk_Trueprop term
                 | \<^typ>\<open>prop\<close> => term
                 | T => raise (TYPE("expected a boolean expression",[T],[term]))
      val (_,ctx) = Proof_Context.add_assms Assumption.assume_export
                               [((Binding.name name,[]), [(prop,[])])] ctx
  in
    ctx
  end

fun declare_abstract_program (ctxt, name:string, cvars:(string*typ)list, cwvars:(string*typ)list, 
                              qvars:(string*typ)list, numOracles:int) = let
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

fun declare_concrete_program (ctxt, name:string, cvars:(string*typ)list, cwvars:(string*typ) list, qvars:(string*typ)list, oracles:string list, body:Programs.statement) = let
  val ctxt = declare_abstract_program (ctxt, name, cvars, cwvars, qvars, length oracles)

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

fun simp (t, facts, ctxt) =
  let val thms = (map (get_thms ctxt) facts |> List.concat)
      val ctxt  = fold (fn name => fn ctx => ctx addsimps thms) facts ctxt
  in case fastype_of t of
        Type(\<^type_name>\<open>prop\<close>,_) => simp_prop t ctxt
      | Type(\<^type_name>\<open>bool\<close>,_) => simp_bool t ctxt
      | _ => simp_any t ctxt
  end

fun conseq_qrhl_replace_in_predicate (predicate, beforeLeft, afterLeft, beforeRight, afterRight) = let
  (* Parse predicate as \<open>pred_lhs \<sqinter> \<lbrakk>vt_left\<rbrakk> \<equiv>\<^sub>\<qq> \<lbrakk>vt_right\<rbrakk>\<close> *)
  val (pred_lhs, qeq_left, qeq_right) = case predicate of
      Const(\<^const_name>\<open>inf\<close>,_) $ pred_lhs $ (Const(\<^const_name>\<open>quantum_equality_full\<close>,_) $ U $ Q $ V $ R) => let
        val _ = case U of Const(\<^const_name>\<open>id_cblinfun\<close>,_) => () | _ => 
            raise TERM("The quantum equality must be a simple one (\<lbrakk>...\<rbrakk> \<equiv>\<^sub>\<qq> \<lbrakk>...\<rbrakk>), not one with operators (quantum_equality_full U \<lbrakk>...\<rbrakk> V \<lbrakk>...\<rbrakk>)", [predicate])
        val _ = case V of Const(\<^const_name>\<open>id_cblinfun\<close>,_) => () | _ => 
            raise TERM("The quantum equality must be a simple one (\<lbrakk>...\<rbrakk> \<equiv>\<^sub>\<qq> \<lbrakk>...\<rbrakk>), not one with operators (quantum_equality_full U \<lbrakk>...\<rbrakk> V \<lbrakk>...\<rbrakk>)", [predicate])
        in (pred_lhs, Q, R) end
    | _ => raise TERM("Pre/postcondition must be of the form {... \<sqinter> \<lbrakk>...\<rbrakk> \<equiv>\<^sub>\<qq> \<lbrakk>...\<rbrakk>}", [predicate])
  val vt_left = Prog_Variables.parse_varlist qeq_left
  val vt_right = Prog_Variables.parse_varlist qeq_right

  (* Check: no duplicate variables in qeq *)
  val _ = if has_duplicates Prog_Variables.nameq (vt_left @ vt_right)
          then raise TERM("Quantum equality has duplicate variables",[predicate,qeq_left])
          else ()

  (* Check: beforeLeft is suffix of vt_left,
            beforeRight is suffix of vt_right *)
  val _ = if List.drop (vt_left, (length vt_left - length beforeLeft)) = beforeLeft
          then ()
          else raise TERM("Lhs of quantum equality does not end with the right variables",[predicate,qeq_left])
  val _ = if List.drop (vt_right, (length vt_right - length beforeRight)) = beforeRight
          then ()
          else raise TERM("Rhs of quantum equality does not end with the right variables",[predicate,qeq_right])

  (* keep_left, keep_right are the vars before beforeLeft/beforeRight (in vt_left/right) *)
  val keep_left = List.take (vt_left, (length vt_left - length beforeLeft))
  val keep_right = List.take (vt_right, (length vt_right - length beforeRight))
  val (_,keep_leftT) = Prog_Variables.varterm_from_list keep_left |> Prog_Variables.mk_varterm
  val (_,keep_rightT) = Prog_Variables.varterm_from_list keep_right |> Prog_Variables.mk_varterm

  (* Check: keep_left/right have the same type (as variable tuple *)
  (* (Should never fail.) *)
  val _ = if keep_leftT = keep_rightT then ()
          else error "conseq_qrhl_replace_in_predicate: type error"

  (* replaced_left_vt := left_vt with beforeLeft replace by afterLeft
     replaced_right_vt analogous *)
  val replaced_left = keep_left @ afterLeft
  val (replaced_left_vt,replaced_leftT) = Prog_Variables.varterm_from_list replaced_left |> Prog_Variables.mk_varterm
  val replaced_right = keep_right @ afterRight
  val (replaced_right_vt,replaced_rightT) = Prog_Variables.varterm_from_list replaced_right |> Prog_Variables.mk_varterm
  (* Should never fail: *)
  val _ = if replaced_leftT = replaced_rightT then ()
          else error "conseq_qrhl_replace_in_predicate: type error"

  (* qeq_replaced := \<lbrakk>replaced_left_vt\<rbrakk> \<equiv>\<^sub>\<qq> \<lbrakk>replaced_right_vt\<rbrakk> *)
  val qeq_replaced = QRHL.mk_quantum_equality replaced_left_vt replaced_right_vt replaced_leftT

  (* Check: after replacement, qeq has no duplicate variables *)
  val _ = if has_duplicates Prog_Variables.nameq (replaced_left @ replaced_right)
          then raise TERM("Quantum equality has duplicate variables",[predicate,qeq_left])
          else ()

  (* predicate, with \<lbrakk>vt_left\<rbrakk> \<equiv>\<^sub>\<qq> \<lbrakk>vt_right\<rbrakk> replaced by \<lbrakk>replaced_left_vt\<rbrakk> \<equiv>\<^sub>\<qq> \<lbrakk>replaced_right_vt\<rbrakk> *)
  (* This is the first return value. *)
  val pred' = @{const inf(predicate)} $ pred_lhs $ qeq_replaced

  (* All of before/afterLeft/Right *)
  val all_vars0 = beforeLeft @ beforeRight @ afterLeft @ afterRight
  val (all_vars, all_varsT) = all_vars0
                 |> Prog_Variables.varterm_from_list |> Prog_Variables.mk_varterm

  val keepLeft_set = Symtab.make_set (map fst keep_left)
  val keepRight_set = Symtab.make_set (map fst keep_right)
(*   (* Check: beforeLeft disjoint from keep_left (the vars in the lhs of the qeq that are not replaced) *)
  val _ = if not (List.exists (fn (n,_) => Symtab.defined keepLeft_set n) beforeLeft) then ()
          else error "Left quantum equality has duplicate variables"
  (* Check: analogous for beforeRight, afterLeft, afterRight *)
  val _ = if not (List.exists (fn (n,_) => Symtab.defined keepRight_set n) beforeRight) then ()
          else error "Right quantum equality has duplicate variables"
  val _ = if not (List.exists (fn (n,_) => Symtab.defined keepLeft_set n) afterLeft) then ()
          else error "Left quantum equality has variables that conflict with replacement variables"
  val _ = if not (List.exists (fn (n,_) => Symtab.defined keepRight_set n) afterRight) then ()
          else error "Left quantum equality has variables that conflict with replacement variables" *)

  (* Condition that implies that `all_vars` do not occur in `pred_lhs` (the predictate without the qeq) *)
  val colocality = Const(\<^const_name>\<open>distinct_qvars_pred_vars\<close>, \<^typ>\<open>predicate\<close> --> QRHL.mk_variablesT all_varsT --> HOLogic.boolT)
                 $ pred_lhs $ all_vars
in
  (pred', colocality)
end
;;

fun method_tac ctxt str = let
  val (text,_) = Method.read_closure_input ctxt (Input.string str)
  val tactic = Method.evaluate text ctxt [] |> Context_Tactic.NO_CONTEXT_TACTIC ctxt
in tactic end

fun is_finite (ctxt, T) = let
  val goal = Const(\<^const_name>\<open>finite\<close>, HOLogic.mk_setT T --> HOLogic.boolT) $ HOLogic.mk_UNIV T
   |> HOLogic.mk_not
   |> HOLogic.mk_Trueprop
   |> Thm.cterm_of ctxt
  val result = Raw_Simplifier.rewrite_cterm (false,false,false) (K (K NONE)) ctxt goal |> Thm.rhs_of |> Thm.term_of
  (* val _ = \<^print> result *)
in result = \<^prop>\<open>True\<close> end


fun byQRHLPre (cvars, qvars) =
  let val cEqs = map (fn (v1,v2,T) => HOLogic.mk_eq (Free(v1,T), Free(v2,T))) cvars
      val cEqs' = \<^const>\<open>classical_subspace\<close> $ QRHL.mk_conjs cEqs
      val (qvars1',qvars1T) = QRHL.variables (map (fn (v1,_ ,T) => Free(v1,QRHL.mk_variableT T)) qvars)
      val (qvars2',qvars2T) = QRHL.variables (map (fn (_ ,v2,T) => Free(v2,QRHL.mk_variableT T)) qvars)
      val _ = if qvars1T <> qvars2T then raise TYPE("mismatch",[qvars1T,qvars2T],[]) else () (* Shouldn't happen *)
      val qvarsEq = if qvars=[] then @{const top(predicate)} else QRHL.mk_quantum_equality qvars1' qvars2' qvars1T
  in
    @{const inf(predicate)} $ cEqs' $ qvarsEq
  end

type statement = Programs.statement
exception E_Subgoal of subgoal
exception E_Statement of statement
exception E_Varterm of exn Prog_Variables.tree
exception E_Call of call

fun whatStatement (Block _) = "block"
  | whatStatement (Local _) = "local"
  | whatStatement (Assign _) = "assign"
  | whatStatement (Sample _) = "sample"
  | whatStatement (Call _) = "call"
  | whatStatement (Measurement _) = "measurement"
  | whatStatement (QInit _) = "qinit"
  | whatStatement (QApply _) = "qapply"
  | whatStatement (IfThenElse _) = "ifthenelse"
  | whatStatement (While _) = "while"

fun declare_quantum_variable (name,typ,ctxt) =
  Prog_Variables.declare_variable ctxt (Binding.name name) typ Prog_Variables.Quantum

fun declare_classical_variable (name,typ,ctxt) =
  Prog_Variables.declare_variable ctxt (Binding.name name) typ Prog_Variables.Classical

fun term_to_expression (ctxt,t) =
  Expressions.term_to_expression ctxt t

fun expression_to_term (ctxt,t) =
  Expressions.expression_to_term ctxt t

fun whatVarterm (VTCons _) = "cons"
  | whatVarterm (VTSingle _) = "single"
  | whatVarterm VTUnit = "unit"

fun show_oracles_lines thm : string list = let
  val ctxt = thm |> Thm.theory_of_thm |> Proof_Context.init_global
  val text = Extended_Sorry.show_oracles_lines ctxt [thm] |> map YXML.content_of
  in text end

local
fun freeze_typ (Type(n,Ts)) = Type (n, map freeze_typ Ts)
  | freeze_typ (T as TFree _) = T
  | freeze_typ (TVar((n,i),s)) = TFree("?"^n^string_of_int i, s)
fun freeze_term (Const(n,T)) = Const (n, freeze_typ T)
  | freeze_term (t $ u) = freeze_term t $ freeze_term u
  | freeze_term (Abs(n,T,body)) = Abs (n, freeze_typ T, freeze_term body)
  | freeze_term (t as Bound _) = t
  | freeze_term (Free(n,T)) = Free(n, freeze_typ T)
  | freeze_term (Var((n,i),T)) = Free("?"^n^string_of_int i, freeze_typ T)
in
fun thms_as_subgoals (ctxt, rule) = let
  val thms = get_thms ctxt rule
  val subgoals = thms |> map Thm.prop_of |> map freeze_term |> map (term_to_subgoal ctxt)
  in subgoals end
end

fun declare_variable (ctxt, name, T) = let
  val ([v],ctxt') = Proof_Context.add_fixes [(Binding.name name, SOME T, NoSyn)] ctxt
  val _ = if v<>name then error("variable "^name^" already declared") else ()
  in ctxt' end

fun colocal_pred_qvars (predicate, qvars) = let
     val (varterm,vartermT) = qvars |> Prog_Variables.varterm_from_list |> Prog_Variables.mk_varterm
     val colocality = Const(\<^const_name>\<open>distinct_qvars_pred_vars\<close>, \<^typ>\<open>predicate\<close> --> QRHL.mk_variablesT vartermT --> HOLogic.boolT)
               $ predicate $ varterm
   in colocality end

fun swap_variables_conv (ctxt, pred) =
     QRHL.swap_variables_conv ctxt (Thm.cterm_of ctxt pred)
           |> Thm.prop_of |> Logic.dest_equals |> snd

fun makeQrhlSubgoal (left,right,pre,post,assms) =
  Subgoal_QRHL (Relational_Hoare.QRHL_Judgment (pre,left,right,post), assms)

fun destQrhlSubgoal (Subgoal_QRHL (Relational_Hoare.QRHL_Judgment (pre,left,right,post), assms)) =
  (left,right,pre,post,assms)

val joint_sample_equal_tac : unit * subgoal * Proof.context -> (subgoal list * thm) option =
   apply_tactic_on_term_concl (fn ctxt => fn _ => Joint_Sample.joint_sample_equal_seq_tac ctxt 1)

val joint_sample_tac =
  apply_tactic_on_term_concl (fn ctxt => fn witness => 
      let val witness_expr = witness |> Expressions.term_to_expression ctxt |> Thm.cterm_of ctxt in
      Joint_Sample.joint_sample_seq_tac ctxt witness_expr 1 end)

val seq_tac =
 apply_tactic_on_term_concl (fn ctxt => fn (i,j,B) => Tactics.seq_tac i j B ctxt 1)

fun conseq_qrhl_cardinality_condition (ctxt,befor,after) = let
     val (_,beforeT) = befor |> Prog_Variables.varterm_from_list |> Prog_Variables.mk_varterm
     val (_,afterT) = after |> Prog_Variables.varterm_from_list |> Prog_Variables.mk_varterm
     val before_UNIV = HOLogic.mk_UNIV beforeT
     val after_UNIV = HOLogic.mk_UNIV afterT
     (* finite (UNIV::beforeT set) *)
     val before_finite = Const(\<^const_name>\<open>finite\<close>, HOLogic.mk_setT beforeT --> HOLogic.boolT) $ before_UNIV
     (* infinite (UNIV::beforeT set) *)
     val before_infinite = HOLogic.mk_not before_finite
     (* finite (UNIV::afterT set) *)
     val after_finite = Const(\<^const_name>\<open>finite\<close>, HOLogic.mk_setT afterT --> HOLogic.boolT) $ after_UNIV
     (* card (UNIV::beforeT set) *)
     val before_card = Const(\<^const_name>\<open>card\<close>, HOLogic.mk_setT beforeT --> HOLogic.natT) $ before_UNIV
     (* card (UNIV::afterT set) *)
     val after_card = Const(\<^const_name>\<open>card\<close>, HOLogic.mk_setT afterT --> HOLogic.natT) $ after_UNIV
     (* card (UNIV::beforeT set) \<ge> card (UNIV::afterT set) *)
     val before_geq_after = \<^term>\<open>(\<ge>) :: nat\<Rightarrow>_\<Rightarrow>_\<close> $ before_card $ after_card
     (* infinite (UNIV::beforeT set) \<or> (finite (UNIV::afterT set) \<and> card (UNIV::beforeT set) \<ge> card (UNIV::afterT set) *)
     val term = HOLogic.mk_disj (before_infinite, HOLogic.mk_conj (after_finite, before_geq_after))
  in term end

fun add_index_to_expression (t,left) =
  Expressions.add_index_to_expression t left

val wp_tac = 
  apply_tactic_on_term_concl (fn ctxt => fn (left,right) => Weakest_Precondition.wp_seq_tac left right ctxt 1)

val sp_tac = 
  apply_tactic_on_term_concl (fn ctxt => fn (left,right) => Strongest_Postcondition.sp_seq_tac left right ctxt 1)

val apply_rule = let
  fun tac ctxt name = resolve_tac ctxt (get_thms ctxt name) 1
  in apply_tactic_on_term tac (fn rule => "rule "^rule) end


val joint_measure_simple_tac : unit * subgoal * Proof.context -> (subgoal list * thm) option = 
  apply_tactic_on_term_concl (fn ctxt => fn _ => Joint_Measure.joint_measure_simple_seq_tac ctxt 1)

val o2h_tac : unit * subgoal * Proof.context -> (subgoal list * thm) option =
  apply_tactic_on_term (fn ctxt => fn _ => O2H.o2h_tac ctxt 1) (fn _ => "o2h")

val semiclassical_tac : unit * subgoal * Proof.context -> (subgoal list * thm) option =
  apply_tactic_on_term 
    (fn ctxt => fn _ => Semi_Classical_Search.semi_classical_search_tac ctxt 1) 
    (fn _ => "o2h")

val apply_method = 
  apply_tactic_on_term method_tac (fn str => "method "^str)

val squash_tac = 
  apply_tactic_on_term_concl (fn ctxt => fn left => Squash_Sampling.squash_sampling_tac left ctxt 1)

val sym_tac : unit * subgoal * Proof.context -> (subgoal list * thm) option =
  apply_tactic_on_term_concl (fn ctxt => fn _ => Basic_Rules.sym_tac ctxt 1)

fun applyToplevelCommand (ctxt, command) = let
  val thy = Proof_Context.theory_of ctxt
  val transactions = Outer_Syntax.parse_text thy (K thy) Position.none command
  fun map_thy thy = 
    fold (Toplevel.command_exception true) transactions (Toplevel.theory_toplevel thy) |> Toplevel.theory_of
  val ctxt = Proof_Context.background_theory map_thy ctxt
in ctxt end

fun print_as_statement ctxt name fixes extra_lines assms concl : string =
  let
    (* val ((fixes, assms, concl), ctxt) = eigen_context_for_statement (fixes, assms, concl) ctxt *)
    val ctxt = fold (fn opt => Config.put opt false)
      [show_markup, Printer.show_type_emphasis, show_types, show_sorts, show_consts] ctxt
    val lemma_s = "lemma " ^ name ^ ":"
    val fixes_s = if null fixes then []
                  else ["  fixes " ^ space_implode " and "
                        (map (fn (v, T) => v ^ " :: " ^ print_typ ctxt T) fixes)]
    val assms_s = map (fn t => "  assumes " ^ print_term ctxt t) assms
    val conclusion_s = "  shows " ^ print_term ctxt concl
    val result_string = cat_lines ([lemma_s] @ fixes_s @ extra_lines @ assms_s @ [conclusion_s])
  in
    YXML.content_of result_string
  end

end
