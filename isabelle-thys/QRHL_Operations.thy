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
   to_lib = Codec.id,
   action = fn (ctx_id, str, T) => 
      let val ctxt = Refs.Ctxt.read ctx_id in
        parse_term ctxt str T |> expression_encode ctxt end}
*}

operation_setup byQRHLPre = {*
  {from_lib = Codec.triple Codec.int (Codec.list (Codec.triple Codec.string Codec.string typ_tight_codec)) (Codec.list (Codec.triple Codec.string Codec.string typ_tight_codec)),
   to_lib = Codec.id,
   action = fn (ctxt_id,cvars,qvars) => 
      let val ctxt = Refs.Ctxt.read ctxt_id in
          QRHL.byQRHLPre cvars qvars |> expression_encode ctxt end}
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
   to_lib = Codec.id,
   action = fn ((cvars1, cvars2, qvars1), (qvars2, B, ctxt_id)) => 
    let val ctxt = Refs.Ctxt.read ctxt_id in
        QRHL.callWp cvars1 cvars2 qvars1 qvars2 B
        |> Codec.encode (Codec.tuple (expression_codec' ctxt) (expression_codec' ctxt)) end}
*}

operation_setup fixTac = {*
  {from_lib = Codec.triple Codec.int term_tight_codec Codec.string,
   to_lib = Codec.id,
   action = fn (ctxt_id,expr,var) => 
      let val ctxt = Refs.Ctxt.read ctxt_id in
          QRHL.fixTac expr var |> Codec.encode (Codec.tuple (expression_codec' ctxt) typ_tight_codec) end}
*}

operation_setup rndWp = {*
  {from_lib = Codec.triple Codec.int (Codec.triple Codec.string term_tight_codec Codec.string) (Codec.triple term_tight_codec typ_tight_codec term_tight_codec),
   to_lib = Codec.id,
   action = fn (ctxt_id, (v1, e1, v2), (e2, T, B)) => 
     let val ctxt = Refs.Ctxt.read ctxt_id in
         QRHL.rndWp v1 e1 v2 e2 T B |> expression_encode ctxt end}
*}

operation_setup rndWp2 = {*
  {from_lib = Codec.triple (Codec.triple Codec.string typ_tight_codec term_tight_codec) 
                           (Codec.triple Codec.string typ_tight_codec term_tight_codec)
                           (Codec.triple term_tight_codec term_tight_codec Codec.int),
   to_lib = Codec.id,
   action = fn ((v1, T1, e1), (v2, T2, e2), (f, B, ctxt_id)) => 
     let val ctxt = Refs.Ctxt.read ctxt_id in
         QRHL.rndWp2 v1 T1 e1 v2 T2 e2 f B |> expression_encode ctxt end}
*}

operation_setup apply_rule = {*
  {from_lib = Codec.triple Codec.string subgoal_codec context_codec,
   to_lib = Codec.id,
   action = apply_tactic_on_term 
      (fn ctxt => fn name => resolve_tac ctxt (Proof_Context.get_thms ctxt name) 1) 
      (fn rule => "rule "^rule)

(*  fn (name,goal,ctx_id) => let
     val ctxt = Refs.Ctxt.read ctx_id
     val (ts,thm) = QRHL.applyRule name goal ctxt
     in SOME (ts,make_thm_ref thm) 
          |> Codec.encode (Codec.option (Codec.tuple (Codec.list (expression_codec' ctxt)) Codec.int))
      end *)
}
*}

operation_setup simplify_term = {*
  {from_lib = Codec.triple term_tight_codec (Codec.list Codec.string) Codec.int,
   to_lib = Codec.id,
   action = fn (t,thms,ctx_id) => let
     val ctxt = Refs.Ctxt.read ctx_id
     val (t,thm) = QRHL.simp t thms ctxt
     in (t,make_thm_ref thm)
        |> Codec.encode (Codec.tuple (expression_codec' ctxt) Codec.int)
       end}
*}

operation_setup add_index_to_expression = {*
  {from_lib = Codec.triple Codec.int term_tight_codec Codec.bool,
   to_lib = Codec.id,
   action = fn (ctxt_id,t,left) => let
     val ctxt = Refs.Ctxt.read ctxt_id in
     Expressions.add_index_to_expression t left |> expression_encode ctxt end}
*}

operation_setup term_to_expression = {*
  {from_lib = Codec.tuple Codec.int term_tight_codec,
   to_lib = Codec.id,
   action = fn (ctxId, t) => let
     val ctxt = Refs.Ctxt.read ctxId in
        Expressions.term_to_expression ctxt t |> expression_encode ctxt end}
*}

operation_setup expression_to_term = {*
  {from_lib = Codec.tuple Codec.int term_tight_codec,
   to_lib = Codec.id,
   action = fn (ctxId, t) => let
     val ctxt = Refs.Ctxt.read ctxId in
     Expressions.expression_to_term (Refs.Ctxt.read ctxId) t |> expression_encode ctxt end}
*}

operation_setup seq_tac = {*
  {from_lib = Codec.triple (Codec.triple Codec.int Codec.int expression_codec) subgoal_codec context_codec,
   to_lib = Codec.id,
   action = apply_tactic_on_term_concl (fn ctxt => fn (i,j,B) => Tactics.seq_tac i j B ctxt 1)}
(* 
  {from_lib = Codec.triple (Codec.triple Codec.int Codec.int term_tight_codec) term_tight_codec Codec.int,
   to_lib = Codec.id,
   action = fn ((i,j,B),goal,ctx_id) => let
     val ctxt = Refs.Ctxt.read ctx_id
     val result = Tactics.seq_tac_on_term i j B ctxt goal |> tac_dummy_thm
    in result 
        |> Codec.encode (Codec.option (Codec.tuple (Codec.list (expression_codec' ctxt)) Codec.int))
    end} *)
*}

operation_setup wp_tac = {*
  {from_lib = Codec.triple Codec.bool subgoal_codec context_codec,
   to_lib = Codec.id,
   action = apply_tactic_on_term_concl (fn ctxt => fn left => Weakest_Precondition.wp_seq_tac left ctxt 1)}
(* fn (left,goal,ctx_id) => let
     val ctxt = Refs.Ctxt.read ctx_id
     val result = Weakest_Precondition.wp_tac_on_term left (Refs.Ctxt.read ctx_id) goal |> tac_dummy_thm
    in result |> Codec.encode (Codec.option (Codec.tuple (Codec.list (expression_codec' ctxt)) Codec.int)) end} *)
*}



operation_setup joint_measure_simple_tac = {*
  {from_lib = Codec.triple Codec.unit subgoal_codec context_codec,
   to_lib = Codec.id,
   action = apply_tactic_on_term_concl (fn ctxt => fn _ => Joint_Measure.joint_measure_simple_seq_tac ctxt 1)}
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
  {from_lib = Codec.tuple Codec.int statement_codec,
   to_lib = Codec.id,
   action = fn (ctxt_id, statement) =>
     let val ctxt = Refs.Ctxt.read ctxt_id
     in Programs.statement_to_term ctxt statement
         |> expression_encode ctxt  end}
\<close>

operation_setup statements_to_term = \<open>
  {from_lib = Codec.tuple Codec.int (Codec.list statement_codec),
   to_lib = Codec.id,
   action = fn (ctxt_id, statements) =>
     let val ctxt = Refs.Ctxt.read ctxt_id
     in Programs.statements_to_term ctxt statements |> expression_encode ctxt end}
\<close>

operation_setup subgoal_to_term = \<open>
  {from_lib = Codec.tuple context_codec subgoal_codec,
   to_lib = Codec.id,
   action = fn (ctxt, subgoal) => subgoal_to_term ctxt subgoal
      |> Codec.encode (expression_codec' ctxt)}\<close>

operation_setup retrieve_term = \<open>
  {from_lib = Codec.int,
   to_lib = Codec.tuple typ_tight_codec term_tight_codec,
   action = fn id => let val t = Terms.id_to_term id in (fastype_of t, t) end}\<close>

operation_setup retrieve_term_string = \<open>
  {from_lib = Codec.int,
   to_lib = Codec.string,
   action = Terms.id_to_string}\<close>

end
