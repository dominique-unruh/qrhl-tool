theory QRHL_Operations
  imports "HOL-Protocol.Protocol_Main" QRHL_Core Tactics Hashed_Terms Joint_Measure Extended_Sorry
    Weakest_Precondition
begin

ML_file "qrhl_operations.ML"

ML \<open>open QRHL_Operations\<close>

(* ML \<open>
fun xxx (XML.Elem(("expression",_),[XML.Text x,_,_])) = x
\<close>

axiomatization bla :: 'a

ML \<open>
expression_encode \<^term>\<open>bla a+b\<close> |> xxx
\<close> *)

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
  {from_lib = Codec.tuple Codec.int term_tight_codec,
   to_lib = typ_tight_codec,
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
  {from_lib = Codec.tuple Codec.int term_tight_codec,
   to_lib = Codec.string,
   action = fn (ctx_id, t) => YXML.content_of (Syntax.string_of_term (Refs.Ctxt.read ctx_id) t)}
*}

operation_setup print_typ = {*
  {from_lib = Codec.tuple Codec.int typ_tight_codec,
   to_lib = Codec.string,
   action = fn (ctx_id, t) => YXML.content_of (Syntax.string_of_typ (Refs.Ctxt.read ctx_id) t)}
*}

operation_setup add_assumption = {*
  {from_lib = Codec.triple Codec.string term_tight_codec Codec.int,
   to_lib = Codec.int,
   action = fn (name,assm,ctx_id) => make_ctxt_ref (QRHL.addAssumption name assm (Refs.Ctxt.read ctx_id))}
*}

operation_setup read_typ = {*
  {from_lib = Codec.tuple Codec.int Codec.string,
   to_lib = typ_tight_codec,
   action = fn (ctx_id, str) => Syntax.read_typ (Refs.Ctxt.read ctx_id) str}
*}

(* DEPRECATED, use read_expression *)
operation_setup read_term = {*
  {from_lib = Codec.triple Codec.int Codec.string typ_tight_codec,
   to_lib = term_tight_codec,
   action = fn (ctx_id, str, T) => parse_term (Refs.Ctxt.read ctx_id) str T}
*}

(* TODO: rename to read_term *)
operation_setup read_expression = {*
  {from_lib = Codec.triple Codec.int Codec.string typ_tight_codec,
   to_lib = expression_codec,
   action = fn (ctx_id, str, T) => 
      let val ctxt = Refs.Ctxt.read ctx_id
          val t = parse_term ctxt str T in (ctxt,t) end}
*}

operation_setup byQRHLPre = {*
  {from_lib = Codec.triple Codec.int (Codec.list (Codec.triple Codec.string Codec.string typ_tight_codec)) (Codec.list (Codec.triple Codec.string Codec.string typ_tight_codec)),
   to_lib = expression_codec,
   action = fn (ctxt_id,cvars,qvars) => 
      let val ctxt = Refs.Ctxt.read ctxt_id
          val t = QRHL.byQRHLPre cvars qvars in (ctxt,t) end}
*}

(* Ambient variables *)
operation_setup declare_variable = {*
  {from_lib = Codec.triple Codec.int Codec.string typ_tight_codec,
   to_lib = Codec.int,
   action = fn (ctx_id, name, T) =>
            let val ([v],ctx') = Proof_Context.add_fixes [(Binding.name name, SOME T, NoSyn)] (Refs.Ctxt.read ctx_id)
                val _ = if v<>name then error("variable v already declared") else ()
            in make_ctxt_ref ctx' end }
*}

operation_setup declare_quantum_variable = {*
  {from_lib = Codec.triple Codec.string typ_tight_codec Codec.int,
   to_lib = Codec.int,
   action = fn (name,typ,ctx_id) => make_ctxt_ref (Prog_Variables.declare_variable (Refs.Ctxt.read ctx_id) (Binding.name name) typ Prog_Variables.Quantum)}
*}

operation_setup declare_classical_variable = {*
  {from_lib = Codec.triple Codec.string typ_tight_codec Codec.int,
   to_lib = Codec.int,
   action = fn (name,typ,ctx_id) => make_ctxt_ref (Prog_Variables.declare_variable (Refs.Ctxt.read ctx_id) (Binding.name name) typ Prog_Variables.Classical)}
*}

operation_setup callWp = {*
  {from_lib = Codec.tuple (Codec.triple (Codec.list term_tight_codec) (Codec.list term_tight_codec) (Codec.list term_tight_codec))
                          (Codec.triple  (Codec.list term_tight_codec) term_tight_codec Codec.int),
   to_lib = Codec.tuple expression_codec expression_codec,
   action = fn ((cvars1, cvars2, qvars1), (qvars2, B, ctxt_id)) => 
    let val ctxt = Refs.Ctxt.read ctxt_id
        val (t1,t2) = QRHL.callWp cvars1 cvars2 qvars1 qvars2 B
    in ((ctxt,t1),(ctxt,t2)) end}
*}

operation_setup fixTac = {*
  {from_lib = Codec.triple Codec.int term_tight_codec Codec.string,
   to_lib = Codec.tuple expression_codec typ_tight_codec,
   action = fn (ctxt_id,expr,var) => 
      let val ctxt = Refs.Ctxt.read ctxt_id
          val (t,T) = QRHL.fixTac expr var
      in ((ctxt,t),T) end}
*}

operation_setup rndWp = {*
  {from_lib = Codec.triple Codec.int (Codec.triple Codec.string term_tight_codec Codec.string) (Codec.triple term_tight_codec typ_tight_codec term_tight_codec),
   to_lib = expression_codec,
   action = fn (ctxt_id, (v1, e1, v2), (e2, T, B)) => 
     let val ctxt = Refs.Ctxt.read ctxt_id
         val t = QRHL.rndWp v1 e1 v2 e2 T B
      in (ctxt,t) end}
*}

operation_setup rndWp2 = {*
  {from_lib = Codec.triple (Codec.triple Codec.string typ_tight_codec term_tight_codec) 
                           (Codec.triple Codec.string typ_tight_codec term_tight_codec)
                           (Codec.triple term_tight_codec term_tight_codec Codec.int),
   to_lib = expression_codec,
   action = fn ((v1, T1, e1), (v2, T2, e2), (f, B, ctxt_id)) => 
     let val ctxt = Refs.Ctxt.read ctxt_id
         val t = QRHL.rndWp2 v1 T1 e1 v2 T2 e2 f B
      in (ctxt,t) end}
*}

operation_setup applyRule = {*
  {from_lib = Codec.triple Codec.string term_tight_codec Codec.int,
   to_lib = Codec.option (Codec.tuple (Codec.list expression_codec) Codec.int),
   action = fn (name,goal,ctx_id) => let
     val ctxt = Refs.Ctxt.read ctx_id
     val (ts,thm) = QRHL.applyRule name goal ctxt
     in SOME (map (fn t => (ctxt,t)) ts,make_thm_ref thm) end}
*}

operation_setup simplify_term = {*
  {from_lib = Codec.triple term_tight_codec (Codec.list Codec.string) Codec.int,
   to_lib = Codec.tuple expression_codec Codec.int,
   action = fn (t,thms,ctx_id) => let
     val ctxt = Refs.Ctxt.read ctx_id
     val (t,thm) = QRHL.simp t thms ctxt
     in ((ctxt,t),make_thm_ref thm) end}
*}

operation_setup add_index_to_expression = {*
  {from_lib = Codec.triple Codec.int term_tight_codec Codec.bool,
   to_lib = expression_codec,
   action = fn (ctxt_id,t,left) => let
     val ctxt = Refs.Ctxt.read ctxt_id
     val t = Expressions.add_index_to_expression t left
    in (ctxt,t) end}
*}

operation_setup term_to_expression = {*
  {from_lib = Codec.tuple Codec.int term_tight_codec,
   to_lib = expression_codec,
   action = fn (ctxId, t) => let
     val ctxt = Refs.Ctxt.read ctxId
     val t' = Expressions.term_to_expression ctxt t
    in (ctxt,t') end}
*}

operation_setup expression_to_term = {*
  {from_lib = Codec.tuple Codec.int term_tight_codec,
   to_lib = expression_codec,
   action = fn (ctxId, t) => let
     val ctxt = Refs.Ctxt.read ctxId
     val t' = Expressions.expression_to_term (Refs.Ctxt.read ctxId) t
    in (ctxt,t') end}
*}

operation_setup seq_tac = {*
  {from_lib = Codec.triple (Codec.triple Codec.int Codec.int term_tight_codec) term_tight_codec Codec.int,
   to_lib = Codec.option (Codec.tuple (Codec.list expression_codec) Codec.int),
   action = fn ((i,j,B),goal,ctx_id) => let
     val ctxt = Refs.Ctxt.read ctx_id
     val result = Tactics.seq_tac_on_term i j B ctxt goal |> tac_dummy_thm
    in Option.map (apfst (map (fn t => (ctxt,t)))) result end}
*}

operation_setup wp_tac = {*
  {from_lib = Codec.triple Codec.bool term_tight_codec Codec.int,
   to_lib = Codec.option (Codec.tuple (Codec.list expression_codec) Codec.int),
   action = fn (left,goal,ctx_id) => let
     val ctxt = Refs.Ctxt.read ctx_id
     val result = Weakest_Precondition.wp_tac_on_term left (Refs.Ctxt.read ctx_id) goal |> tac_dummy_thm
    in Option.map (apfst (map (fn t => (ctxt,t)))) result end}
*}

operation_setup joint_measure_simple_tac = {*
  {from_lib = Codec.triple Codec.unit term_tight_codec Codec.int,
   to_lib = Codec.option (Codec.tuple (Codec.list expression_codec) Codec.int),
   action = fn ((),goal,ctx_id) => 
     let val ctxt = Refs.Ctxt.read ctx_id
         val subgoals = Tactics.tac_on_term_concl (Joint_Measure.joint_measure_simple_seq_tac ctxt 1) ctxt goal |> tac_dummy_thm
     in Option.map (apfst (map (fn t => (ctxt,t)))) subgoals end}
*}

(* (* TODO remove *)
operation_setup term_test = {*
  {from_lib = Codec.unit,
   to_lib = Hashed_Terms.term_codec,
   action = fn () => \<^term>\<open>True\<close>}
*} *)

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

operation_setup statement_to_term = \<open>
  {from_lib = Codec.tuple Codec.int statement_codec2,
   to_lib = expression_codec,
   action = fn (ctxt_id, statement) =>
     let val ctxt = Refs.Ctxt.read ctxt_id
     in (ctxt, Programs.statement_to_term ctxt statement) end}
\<close>

operation_setup statements_to_term = \<open>
  {from_lib = Codec.tuple Codec.int (Codec.list statement_codec2),
   to_lib = expression_codec,
   action = fn (ctxt_id, statements) =>
     let val ctxt = Refs.Ctxt.read ctxt_id
     in (ctxt, Programs.statements_to_term ctxt statements) end}
\<close>

end
