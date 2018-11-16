theory QRHL_Operations
  imports "HOL-Protocol.Protocol_Main" QRHL_Core Tactics Hashed_Terms Joint_Measure Extended_Sorry
    Weakest_Precondition
begin

ML {*
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

fun tac_dummy_thm NONE = NONE
  | tac_dummy_thm (SOME ts) = SOME (ts,0)
*}

operation_setup create_context = {*
  {from_lib = Codec.list Codec.string,
   to_lib = Codec.int,
   action = fn thy_names => let
     val thys = map Thy_Info.get_theory thy_names
     val thy = Theory.begin_theory ("QRHL_Session", Position.none) thys
     val ctx = Proof_Context.init_global thy
   in make_ctxt_ref ctx end}
*}

operation_setup check_type = {*
  {from_lib = Codec.tuple Codec.int Codec.term,
   to_lib = Codec.typ,
   action = fn (ctx_id,t) => QRHL.checkType (Refs.Ctxt.read ctx_id) t} *}

operation_setup delete_context = {*
  {from_lib = Codec.int,
   to_lib = Codec.unit,
   action = Refs.Ctxt.delete}
*}

operation_setup delete_thm = {*
  {from_lib = Codec.int,
   to_lib = Codec.unit,
   action = Refs.Thm.delete}
*}

operation_setup print_term = {*
  {from_lib = Codec.tuple Codec.int Codec.term,
   to_lib = Codec.string,
   action = fn (ctx_id, t) => YXML.content_of (Syntax.string_of_term (Refs.Ctxt.read ctx_id) t)}
*}

operation_setup print_typ = {*
  {from_lib = Codec.tuple Codec.int Codec.typ,
   to_lib = Codec.string,
   action = fn (ctx_id, t) => YXML.content_of (Syntax.string_of_typ (Refs.Ctxt.read ctx_id) t)}
*}

operation_setup add_assumption = {*
  {from_lib = Codec.triple Codec.string Codec.term Codec.int,
   to_lib = Codec.int,
   action = fn (name,assm,ctx_id) => make_ctxt_ref (QRHL.addAssumption name assm (Refs.Ctxt.read ctx_id))}
*}

operation_setup read_typ = {*
  {from_lib = Codec.tuple Codec.int Codec.string,
   to_lib = Codec.typ,
   action = fn (ctx_id, str) => Syntax.read_typ (Refs.Ctxt.read ctx_id) str}
*}

operation_setup read_term = {*
  {from_lib = Codec.triple Codec.int Codec.string Codec.typ,
   to_lib = Codec.term,
   action = fn (ctx_id, str, T) =>
     let val ctx = Refs.Ctxt.read ctx_id
         val parsed = Syntax.parse_term ctx str
         val constrained = Const("_type_constraint_", T --> T) $ parsed
         val term = Syntax.check_term ctx constrained
     in
       term
     end}
*}

operation_setup byQRHLPre = {*
  {from_lib = Codec.tuple (Codec.list (Codec.triple Codec.string Codec.string Codec.typ)) (Codec.list (Codec.triple Codec.string Codec.string Codec.typ)),
   to_lib = Codec.term,
   action = fn (cvars,qvars) => QRHL.byQRHLPre cvars qvars}
*}

(* Ambient variables *)
operation_setup declare_variable = {*
  {from_lib = Codec.triple Codec.int Codec.string Codec.typ,
   to_lib = Codec.int,
   action = fn (ctx_id, name, T) =>
            let val ([v],ctx') = Proof_Context.add_fixes [(Binding.name name, SOME T, NoSyn)] (Refs.Ctxt.read ctx_id)
                val _ = if v<>name then error("variable v already declared") else ()
            in make_ctxt_ref ctx' end }
*}

operation_setup declare_quantum_variable = {*
  {from_lib = Codec.triple Codec.string Codec.typ Codec.int,
   to_lib = Codec.int,
   action = fn (name,typ,ctx_id) => make_ctxt_ref (Prog_Variables.declare_variable (Refs.Ctxt.read ctx_id) (Binding.name name) typ Prog_Variables.Quantum)}
*}

operation_setup declare_classical_variable = {*
  {from_lib = Codec.triple Codec.string Codec.typ Codec.int,
   to_lib = Codec.int,
   action = fn (name,typ,ctx_id) => make_ctxt_ref (Prog_Variables.declare_variable (Refs.Ctxt.read ctx_id) (Binding.name name) typ Prog_Variables.Classical)}
*}

operation_setup callWp = {*
  {from_lib = Codec.tuple (Codec.triple (Codec.list Codec.term) (Codec.list Codec.term) (Codec.list Codec.term))
                          (Codec.tuple  (Codec.list Codec.term) Codec.term),
   to_lib = Codec.tuple Codec.term Codec.term,
   action = fn ((cvars1, cvars2, qvars1), (qvars2, B)) => QRHL.callWp cvars1 cvars2 qvars1 qvars2 B}
*}

operation_setup fixTac = {*
  {from_lib = Codec.tuple Codec.term Codec.string,
   to_lib = Codec.tuple Codec.term Codec.typ,
   action = fn (expr,var) => QRHL.fixTac expr var}
*}

operation_setup rndWp = {*
  {from_lib = Codec.tuple (Codec.triple Codec.string Codec.term Codec.string) (Codec.triple Codec.term Codec.typ Codec.term),
   to_lib = Codec.term,
   action = fn ((v1, e1, v2), (e2, T, B)) => QRHL.rndWp v1 e1 v2 e2 T B}
*}

operation_setup rndWp2 = {*
  {from_lib = Codec.triple (Codec.triple Codec.string Codec.typ Codec.term) (Codec.triple Codec.string Codec.typ Codec.term) (Codec.tuple Codec.term Codec.term),
   to_lib = Codec.term,
   action = fn ((v1, T1, e1), (v2, T2, e2), (f, B)) => QRHL.rndWp2 v1 T1 e1 v2 T2 e2 f B}
*}

operation_setup applyRule = {*
  {from_lib = Codec.triple Codec.string Codec.term Codec.int,
   to_lib = Codec.option (Codec.tuple (Codec.list Codec.term) Codec.int),
   action = fn (name,goal,ctx_id) => let
     val ctxt = Refs.Ctxt.read ctx_id
     val (ts,thm) = QRHL.applyRule name goal ctxt
     in SOME (ts,make_thm_ref thm) end}
*}

operation_setup simplify_term = {*
  {from_lib = Codec.triple Codec.term (Codec.list Codec.string) Codec.int,
   to_lib = Codec.tuple Codec.term Codec.int,
   action = fn (t,thms,ctx_id) => let
     val ctxt = Refs.Ctxt.read ctx_id
     val (t,thm) = QRHL.simp t thms ctxt
     in (t,make_thm_ref thm) end}
*}

operation_setup add_index_to_expression = {*
  {from_lib = Codec.tuple Codec.term Codec.bool,
   to_lib = Codec.term,
   action = fn (t,left) => Expressions.add_index_to_expression t left}
*}

operation_setup term_to_expression = {*
  {from_lib = Codec.tuple Codec.int Codec.term,
   to_lib = Codec.term,
   action = fn (ctxId, t) => Expressions.term_to_expression (Refs.Ctxt.read ctxId) t}
*}

operation_setup expression_to_term = {*
  {from_lib = Codec.tuple Codec.int Codec.term,
   to_lib = Codec.tuple Codec.term Codec.typ,
   action = fn (ctxId, t) => Expressions.expression_to_term_typ (Refs.Ctxt.read ctxId) t}
*}

operation_setup seq_tac = {*
  {from_lib = Codec.triple (Codec.triple Codec.int Codec.int Codec.term) Codec.term Codec.int,
   to_lib = Codec.option (Codec.tuple (Codec.list Codec.term) Codec.int),
   action = fn ((i,j,B),goal,ctx_id) => Tactics.seq_tac_on_term i j B (Refs.Ctxt.read ctx_id) goal |> tac_dummy_thm}
*}

operation_setup wp_tac = {*
  {from_lib = Codec.triple Codec.bool Codec.term Codec.int,
   to_lib = Codec.option (Codec.tuple (Codec.list Codec.term) Codec.int),
   action = fn (left,goal,ctx_id) => Weakest_Precondition.wp_tac_on_term left (Refs.Ctxt.read ctx_id) goal |> tac_dummy_thm}
*}

operation_setup joint_measure_simple_tac = {*
  {from_lib = Codec.triple Codec.unit Codec.term Codec.int,
   to_lib = Codec.option (Codec.tuple (Codec.list Codec.term) Codec.int),
   action = fn ((),goal,ctx_id) => 
     let val ctxt = Refs.Ctxt.read ctx_id
         val subgoals = Tactics.tac_on_term_concl (Joint_Measure.joint_measure_simple_seq_tac ctxt 1) ctxt goal |> tac_dummy_thm
     in subgoals end}
*}

(* TODO remove *)
operation_setup term_test = {*
  {from_lib = Codec.unit,
   to_lib = Hashed_Terms.term_codec,
   action = fn () => \<^term>\<open>True\<close>}
*}

operation_setup show_oracles_lines = {*
  {from_lib = Codec.int,
   to_lib = Codec.list Codec.string,
   action = map YXML.content_of o Extended_Sorry.show_oracles_lines o Refs.Thm.read}
*}

operation_setup (sequential, bracket) use_thys2 = \<open>
  {from_lib = Codec.list Codec.string,
   to_lib = Codec.unit,
   action = List.app Thy_Info.use_thy}
\<close>

end
