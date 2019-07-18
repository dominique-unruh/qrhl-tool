theory QRHL_Operations
  imports "HOL-Protocol.Protocol_Main" QRHL_Core Tactics Hashed_Terms Joint_Measure Bounded_Operators.Extended_Sorry
    Weakest_Precondition Joint_Sample Squash_Sampling O2H Semi_Classical_Search
begin

ML_file "qrhl_operations.ML"

ML \<open>
(* Codec.add_exception_printer (fn pr => fn exn => case Par_Exn.dest exn of 
  NONE => NONE | 
  SOME exns => exns |> map pr |> String.concatWith "\n" |> SOME);; *)
Codec.add_exception_printer (fn _ => fn exn => exn |> Runtime.thread_context |> Runtime.exn_context (SOME \<^context>) |> Runtime.exn_message |> YXML.parse_body |> XML.content_of |> SOME)
\<close>

ML \<open>open QRHL_Operations\<close>

operation_setup o2h_tac = \<open>
  {from_lib = Codec.triple Codec.unit subgoal_codec context_codec,
   to_lib = Codec.id,
   action = apply_tactic_on_term 
      (fn ctxt => fn _ => O2H.o2h_tac ctxt 1) 
      (fn _ => "o2h")}
\<close>

operation_setup semiclassical_tac = \<open>
  {from_lib = Codec.triple Codec.unit subgoal_codec context_codec,
   to_lib = Codec.id,
   action = apply_tactic_on_term 
      (fn ctxt => fn _ => Semi_Classical_Search.semi_classical_search_tac ctxt 1) 
      (fn _ => "o2h")}
\<close>

operation_setup create_context = \<open>
  {from_lib = Codec.list Codec.string,
   to_lib = Codec.tuple Codec.int (Codec.list Codec.string),
   action = create_context}
\<close>

operation_setup check_type = \<open>
  {from_lib = Codec.tuple Codec.int term_tight_codec,
   to_lib = typ_tight_codec,
   action = fn (ctx_id,t) => QRHL.checkType (Refs.Ctxt.read ctx_id) t} \<close>

operation_setup delete_context = \<open>
  {from_lib = Codec.int,
   to_lib = Codec.unit,
   action = Refs.Ctxt.delete}
\<close>

operation_setup delete_thm = \<open>
  {from_lib = Codec.int,
   to_lib = Codec.unit,
   action = Refs.Thm.delete}
\<close>

operation_setup print_term = \<open>
  {from_lib = Codec.tuple Codec.int term_tight_codec,
   to_lib = Codec.string,
   action = fn (ctx_id, t) => YXML.content_of (Syntax.string_of_term (Refs.Ctxt.read ctx_id) t)}
\<close>

operation_setup print_typ = \<open>
  {from_lib = Codec.tuple Codec.int typ_tight_codec,
   to_lib = Codec.string,
   action = fn (ctx_id, t) => YXML.content_of (Syntax.string_of_typ (Refs.Ctxt.read ctx_id) t)}
\<close>

operation_setup add_assumption = \<open>
  {from_lib = Codec.triple Codec.string term_tight_codec Codec.int,
   to_lib = Codec.int,
   action = fn (name,assm,ctx_id) => make_ctxt_ref (QRHL_Operations.addAssumption name assm (Refs.Ctxt.read ctx_id))}
\<close>

operation_setup read_typ = \<open>
  {from_lib = Codec.tuple Codec.int Codec.string,
   to_lib = typ_tight_codec,
   action = fn (ctx_id, str) => Syntax.read_typ (Refs.Ctxt.read ctx_id) str}
\<close>

(* DEPRECATED, use read_expression *)
operation_setup read_term = \<open>
  {from_lib = Codec.triple Codec.int Codec.string typ_tight_codec,
   to_lib = term_tight_codec,
   action = fn (ctx_id, str, T) => parse_term (Refs.Ctxt.read ctx_id) str T}
\<close>

(* TODO: rename to read_term *)
operation_setup read_expression = \<open>
  {from_lib = Codec.triple Codec.int Codec.string typ_tight_codec,
   to_lib = Codec.id,
   action = fn (ctx_id, str, T) => 
      let val ctxt = Refs.Ctxt.read ctx_id in
        parse_term ctxt str T |> richterm_encode ctxt end}
\<close>

operation_setup byQRHLPre = \<open>
  {from_lib = Codec.triple Codec.int (Codec.list (Codec.triple Codec.string Codec.string typ_tight_codec)) (Codec.list (Codec.triple Codec.string Codec.string typ_tight_codec)),
   to_lib = Codec.id,
   action = fn (ctxt_id,cvars,qvars) => 
      let val ctxt = Refs.Ctxt.read ctxt_id in
          QRHL.byQRHLPre cvars qvars |> richterm_encode ctxt end}
\<close>

(* Ambient variables *)
operation_setup declare_variable = \<open>
  {from_lib = Codec.triple Codec.int Codec.string typ_tight_codec,
   to_lib = Codec.int,
   action = fn (ctxt_id, name, T) =>
            let val ([v],ctxt') = Proof_Context.add_fixes [(Binding.name name, SOME T, NoSyn)] (Refs.Ctxt.read ctxt_id)
                val _ = if v<>name then error("variable "^name^" already declared") else ()
            in make_ctxt_ref ctxt' end }
\<close>

operation_setup declare_quantum_variable = \<open>
  {from_lib = Codec.triple Codec.string typ_tight_codec Codec.int,
   to_lib = Codec.int,
   action = fn (name,typ,ctx_id) => make_ctxt_ref (Prog_Variables.declare_variable (Refs.Ctxt.read ctx_id) (Binding.name name) typ Prog_Variables.Quantum)}
\<close>

operation_setup declare_classical_variable = \<open>
  {from_lib = Codec.triple Codec.string typ_tight_codec Codec.int,
   to_lib = Codec.int,
   action = fn (name,typ,ctx_id) => make_ctxt_ref (Prog_Variables.declare_variable (Refs.Ctxt.read ctx_id) (Binding.name name) typ Prog_Variables.Classical)}
\<close>

operation_setup callWp = \<open>
  {from_lib = tuple10 
      (Codec.list term_tight_codec)
      (Codec.list term_tight_codec)
      (Codec.list term_tight_codec)
      (Codec.list term_tight_codec)
      (Codec.list term_tight_codec)
      (Codec.list term_tight_codec)
      (Codec.list term_tight_codec)
      (Codec.list term_tight_codec)
      term_tight_codec
      Codec.int,
   to_lib = Codec.id,
   action = fn (in_cvars1, in_cvars2, in_qvars1, in_qvars2, cvars1, cvars2, qvars1, qvars2, B, ctxt_id) => 
    let val ctxt = Refs.Ctxt.read ctxt_id in
        QRHL.callWp in_cvars1 in_cvars2 in_qvars1 in_qvars2 cvars1 cvars2 qvars1 qvars2 B
        |> Codec.encode (Codec.triple (richterm_codec' ctxt) (richterm_codec' ctxt) (richterm_codec' ctxt)) end}
\<close>

operation_setup fixTac = \<open>
  {from_lib = Codec.triple Codec.int term_tight_codec Codec.string,
   to_lib = Codec.id,
   action = fn (ctxt_id,expr,var) => 
      let val ctxt = Refs.Ctxt.read ctxt_id in
          QRHL.fixTac expr var |> Codec.encode (Codec.tuple (richterm_codec' ctxt) typ_tight_codec) end}
\<close>

(* TODO remove (incl QRHL.rndWp). Same for rndWp2 *)
operation_setup rndWp = \<open>
  {from_lib = Codec.triple Codec.int (Codec.triple Codec.string term_tight_codec Codec.string) (Codec.triple term_tight_codec typ_tight_codec term_tight_codec),
   to_lib = Codec.id,
   action = fn (ctxt_id, (v1, e1, v2), (e2, T, B)) => 
     let val ctxt = Refs.Ctxt.read ctxt_id in
         QRHL.rndWp v1 e1 v2 e2 T B |> richterm_encode ctxt end}
\<close>

operation_setup rndWp2 = \<open>
  {from_lib = Codec.triple (Codec.triple Codec.string typ_tight_codec term_tight_codec) 
                           (Codec.triple Codec.string typ_tight_codec term_tight_codec)
                           (Codec.triple term_tight_codec term_tight_codec Codec.int),
   to_lib = Codec.id,
   action = fn ((v1, T1, e1), (v2, T2, e2), (f, B, ctxt_id)) => 
     let val ctxt = Refs.Ctxt.read ctxt_id in
         QRHL.rndWp2 v1 T1 e1 v2 T2 e2 f B |> richterm_encode ctxt end}
\<close>

operation_setup apply_rule = \<open> let
fun tac ctxt name = resolve_tac ctxt (get_thms ctxt name) 1
in
  {from_lib = Codec.triple Codec.string subgoal_codec context_codec,
   to_lib = Codec.id,
   action = apply_tactic_on_term 
      tac 
      (fn rule => "rule "^rule)}
end
\<close>

operation_setup simplify_term = \<open>
  {from_lib = Codec.triple term_tight_codec (Codec.list Codec.string) Codec.int,
   to_lib = Codec.id,
   action = fn (t,thms,ctx_id) => let
     val ctxt = Refs.Ctxt.read ctx_id
     val (t,thm) = QRHL.simp t thms ctxt
     in (t,make_thm_ref thm)
        |> Codec.encode (Codec.tuple (richterm_codec' ctxt) Codec.int)
       end}
\<close>

operation_setup add_index_to_expression = \<open>
  {from_lib = Codec.triple Codec.int term_tight_codec Codec.bool,
   to_lib = Codec.id,
   action = fn (ctxt_id,t,left) => let
     val ctxt = Refs.Ctxt.read ctxt_id in
     Expressions.add_index_to_expression t left |> richterm_encode ctxt end}
\<close>

operation_setup term_to_expression = \<open>
  {from_lib = Codec.tuple Codec.int term_tight_codec,
   to_lib = Codec.id,
   action = fn (ctxId, t) => let
     val ctxt = Refs.Ctxt.read ctxId in
        Expressions.term_to_expression ctxt t |> richterm_encode ctxt end}
\<close>

operation_setup expression_to_term = \<open>
  {from_lib = Codec.tuple Codec.int term_tight_codec,
   to_lib = Codec.id,
   action = fn (ctxId, t) => let
     val ctxt = Refs.Ctxt.read ctxId in
     Expressions.expression_to_term (Refs.Ctxt.read ctxId) t |> richterm_encode ctxt end}
\<close>

operation_setup seq_tac = \<open>
  {from_lib = Codec.triple (Codec.triple Codec.int Codec.int richterm_codec) subgoal_codec context_codec,
   to_lib = Codec.id,
   action = apply_tactic_on_term_concl (fn ctxt => fn (i,j,B) => Tactics.seq_tac i j B ctxt 1)}
(* 
  {from_lib = Codec.triple (Codec.triple Codec.int Codec.int term_tight_codec) term_tight_codec Codec.int,
   to_lib = Codec.id,
   action = fn ((i,j,B),goal,ctx_id) => let
     val ctxt = Refs.Ctxt.read ctx_id
     val result = Tactics.seq_tac_on_term i j B ctxt goal |> tac_dummy_thm
    in result 
        |> Codec.encode (Codec.option (Codec.tuple (Codec.list (richterm_codec' ctxt)) Codec.int))
    end} *)
\<close>

operation_setup wp_tac = \<open>
  {from_lib = Codec.triple (Codec.tuple Codec.int Codec.int) subgoal_codec context_codec,
   to_lib = Codec.id,
   action = apply_tactic_on_term_concl (fn ctxt => fn (left,right) => Weakest_Precondition.wp_seq_tac left right ctxt 1)}
(* fn (left,goal,ctx_id) => let
     val ctxt = Refs.Ctxt.read ctx_id
     val result = Weakest_Precondition.wp_tac_on_term left (Refs.Ctxt.read ctx_id) goal |> tac_dummy_thm
    in result |> Codec.encode (Codec.option (Codec.tuple (Codec.list (richterm_codec' ctxt)) Codec.int)) end} *)
\<close>

operation_setup squash_tac = \<open>
  {from_lib = Codec.triple Codec.bool subgoal_codec context_codec,
   to_lib = Codec.id,
   action = apply_tactic_on_term_concl (fn ctxt => fn left => Squash_Sampling.squash_sampling_tac left ctxt 1)}
\<close>



operation_setup joint_measure_simple_tac = \<open>
  {from_lib = Codec.triple Codec.unit subgoal_codec context_codec,
   to_lib = Codec.id,
   action = apply_tactic_on_term_concl (fn ctxt => fn _ => Joint_Measure.joint_measure_simple_seq_tac ctxt 1)}
\<close>

operation_setup joint_sample_equal_tac = \<open>
  {from_lib = Codec.triple Codec.unit subgoal_codec context_codec,
   to_lib = Codec.id,
   action = apply_tactic_on_term_concl (fn ctxt => fn _ => Joint_Sample.joint_sample_equal_seq_tac ctxt 1)}
\<close>

operation_setup joint_sample_tac = \<open>
  {from_lib = Codec.triple term_tight_codec subgoal_codec context_codec,
   to_lib = Codec.id,
   action = apply_tactic_on_term_concl (fn ctxt => fn witness => 
      let val witness_expr = witness |> Expressions.term_to_expression ctxt |> Thm.cterm_of ctxt in
      Joint_Sample.joint_sample_seq_tac ctxt witness_expr 1 end)}
\<close>

(* (* TODO remove *)
operation_setup term_test = \<open>
  {from_lib = Codec.unit,
   to_lib = Hashed_Terms.term_codec,
   action = fn () => \<^term>\<open>True\<close>}
\<close> *)

operation_setup show_oracles_lines = \<open>
  {from_lib = Codec.int,
   to_lib = Codec.list Codec.string,
   action = map YXML.content_of o Extended_Sorry.show_oracles_lines o Refs.Thm.read}
\<close>

(* operation_setup (sequential, bracket) use_thys2 = \<open>
  {from_lib = Codec.list Codec.string,
   to_lib = Codec.unit,
   action = List.app Thy_Info.use_thy}
\<close> *)

operation_setup statement_to_term = \<open>
  {from_lib = Codec.tuple Codec.int statement_codec,
   to_lib = Codec.id,
   action = fn (ctxt_id, statement) =>
     let val ctxt = Refs.Ctxt.read ctxt_id
     in Programs.statement_to_term ctxt statement
         |> richterm_encode ctxt  end}
\<close>

operation_setup statements_to_term = \<open>
  {from_lib = Codec.tuple Codec.int (Codec.list statement_codec),
   to_lib = Codec.id,
   action = fn (ctxt_id, statements) =>
     let val ctxt = Refs.Ctxt.read ctxt_id
     in Programs.statements_to_term ctxt statements |> richterm_encode ctxt end}
\<close>

operation_setup subgoal_to_term = \<open>
  {from_lib = Codec.tuple context_codec subgoal_codec,
   to_lib = Codec.id,
   action = fn (ctxt, subgoal) => subgoal_to_term ctxt subgoal
      |> Codec.encode (richterm_codec' ctxt)}\<close>

operation_setup retrieve_term = \<open>
  {from_lib = Codec.int,
   to_lib = term_tight_codec,
   action = fn id => Terms.id_to_term id}\<close>

operation_setup retrieve_term_string = \<open>
  {from_lib = Codec.int,
   to_lib = Codec.string,
   action = Terms.id_to_string}\<close>

operation_setup declare_abstract_program = \<open>
  {from_lib = tuple6 Codec.int (* ctxt *)
                     Codec.string (* prog name *)
                     (Codec.list (Codec.tuple Codec.string typ_tight_codec)) (* cvars *)
                     (Codec.list (Codec.tuple Codec.string typ_tight_codec)) (* cwvars *)
                     (Codec.list (Codec.tuple Codec.string typ_tight_codec)) (* qvars *)
                     Codec.int, (* num oracles *)
   to_lib = Codec.int,
   action = fn (ctxt_id,name,cvars,cwvars,qvars,numOracles) => 
     make_ctxt_ref (QRHL_Operations.declare_abstract_program (Refs.Ctxt.read ctxt_id) name cvars cwvars  qvars numOracles)}
\<close>

operation_setup declare_concrete_program = \<open>
  {from_lib = tuple7 Codec.int (* ctxt *)
                     Codec.string (* prog name *)
                     (Codec.list (Codec.tuple Codec.string typ_tight_codec)) (* cvars *)
                     (Codec.list (Codec.tuple Codec.string typ_tight_codec)) (* cwvars *)
                     (Codec.list (Codec.tuple Codec.string typ_tight_codec)) (* qvars *)
                     (Codec.list Codec.string) (* oracles *)
                     statement_codec, (* body *)
   to_lib = Codec.int,
   action = fn ((ctxt_id,name,cvars,cwvars,qvars,oracles,body)) => 
     make_ctxt_ref (QRHL_Operations.declare_concrete_program (Refs.Ctxt.read ctxt_id) name cvars cwvars qvars oracles body)}
\<close>

operation_setup debug = \<open>
  {from_lib = Codec.int,
   to_lib = Codec.string,
   action = fn ctxt_id => QRHL_Operations.debug (Refs.Ctxt.read ctxt_id)}
\<close>

operation_setup thms_as_subgoals = \<open>
  {from_lib = Codec.tuple Codec.int (* ctxt *)
                          Codec.string (* rule *),
   to_lib = Codec.id,
   action = fn (ctxt_id, rule) => let
     val ctxt = Refs.Ctxt.read ctxt_id
     val thms = get_thms ctxt rule
     val subgoals = thms |> map Thm.prop_of |> map (term_to_subgoal ctxt)
     val encoded = Codec.encode (Codec.list (subgoal_codec' ctxt)) subgoals
   in encoded end}
\<close>

operation_setup colocal_pred_qvars = \<open>
  {from_lib = Codec.triple
              Codec.int (* ctxt *)
              term_tight_codec (* predicate *)
              (Codec.list (Codec.tuple Codec.string typ_tight_codec)), (* qvars *)
   to_lib = Codec.id,
   action = fn (ctxt_id, predicate, qvars) => let
     val ctxt = Refs.Ctxt.read ctxt_id
     val (varterm,vartermT) = qvars |> Prog_Variables.varterm_from_list |> Prog_Variables.mk_varterm
     val colocality = Const(\<^const_name>\<open>colocal_pred_qvars\<close>, \<^typ>\<open>predicate\<close> --> QRHL.mk_variablesT vartermT --> HOLogic.boolT)
               $ predicate $ varterm
   in Codec.encode (richterm_codec' ctxt) colocality end}\<close>
   

end
