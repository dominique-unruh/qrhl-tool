theory Joint_Measure
  imports (* Expressions *) Tactics
begin

(* TODO: assume that x y Q R are registes *)
lemma joint_measure_simple:
  fixes e f x y Q R B
  assumes \<open>cregister x\<close> \<open>cregister y\<close> \<open>qregister Q\<close> \<open>qregister R\<close>
  defines "e\<^sub>1 \<equiv> (\<lambda>m. e (fst m))"
  defines "f\<^sub>2 \<equiv> (\<lambda>m. f (snd m))"
  defines "x\<^sub>1 \<equiv> cregister_chain cFst x"
  defines "y\<^sub>2 \<equiv> cregister_chain cSnd y"
  defines "Q\<^sub>1 \<equiv> qregister_chain qFst Q"
  defines "R\<^sub>2 \<equiv> qregister_chain qSnd R"
  defines "B' z \<equiv> (\<lambda>m. B (setter y\<^sub>2 z (setter x\<^sub>1 z m)))"
  defines "\<And>e\<^sub>1 z. ebar e\<^sub>1 z \<equiv> ((mproj e\<^sub>1 z)\<guillemotright>Q\<^sub>1) \<cdot> top"
  defines "\<And>f\<^sub>2 z. fbar f\<^sub>2 z \<equiv> ((mproj f\<^sub>2 z)\<guillemotright>R\<^sub>2) \<cdot> top"
  defines "A \<equiv> (\<lambda>m.
    Cla[e\<^sub>1=f\<^sub>2] \<sqinter> quantum_equality Q\<^sub>1 R\<^sub>2 \<sqinter> 
    (INF z. ((B' z m \<sqinter> ebar (e\<^sub>1 m) z \<sqinter> fbar (f\<^sub>2 m) z) + (- ebar (e\<^sub>1 m) z) + (- fbar (f\<^sub>2 m) z))))"
  shows "qrhl A [measurement x Q e] [measurement y R f] B"
  sorry

(* lemma joint_measure_simple_tac:
  fixes e f x y Q R B
  assumes "e\<^sub>1 \<equiv> e o fst"
  assumes "f\<^sub>2 \<equiv> f o snd"
  assumes "x\<^sub>1 \<equiv> cregister_chain cFst x"
  assumes "y\<^sub>2 \<equiv> cregister_chain cSnd y"
  assumes "Q\<^sub>1 \<equiv> qregister_chain qFst Q"
  assumes "R\<^sub>2 \<equiv> qregister_chain qSnd R"
  assumes "\<And>z. \<sigma>1 z = substitute_vars x\<^sub>1 (const_expression z)"
  assumes "\<And>z. \<sigma>2 z = substitute_vars y\<^sub>2 (const_expression z)"
  assumes "\<And>z. \<sigma> z = \<sigma>1 z @ \<sigma>2 z"
  assumes "\<And>z. B' z = subst_expression (\<sigma> z) B"
  defines "\<And>e\<^sub>1 z. ebar e\<^sub>1 z \<equiv> ((mproj e\<^sub>1 z)\<guillemotright>Q\<^sub>1) \<cdot> top"
  defines "\<And>f\<^sub>2 z. fbar f\<^sub>2 z \<equiv> ((mproj f\<^sub>2 z)\<guillemotright>R\<^sub>2) \<cdot> top"
  assumes "A = map_expression3' (\<lambda>e\<^sub>1 f\<^sub>2 B'. 
    Cla[e\<^sub>1=f\<^sub>2] \<sqinter> quantum_equality Q\<^sub>1 R\<^sub>2 \<sqinter> 
    (INF z. let ebar = ebar e\<^sub>1 z; fbar = fbar f\<^sub>2 z in ((B' z \<sqinter> ebar \<sqinter> fbar) + - ebar + - fbar))) e\<^sub>1 f\<^sub>2 B'"
  shows "qrhl A [measurement x Q e] [measurement y R f] B"
unfolding assms Let_def by (rule joint_measure_simple) *)

ML \<open>
structure Joint_Measure = struct
fun joint_measure_simple_tac ctxt =
  resolve_tac ctxt @{thms joint_measure_simple}
  THEN' Prog_Variables.distinct_vars_tac ctxt
  THEN' Prog_Variables.distinct_vars_tac ctxt
  THEN' Prog_Variables.distinct_vars_tac ctxt
  THEN' Prog_Variables.distinct_vars_tac ctxt

(*   THEN' Expressions.index_tac ctxt
  THEN' Expressions.index_tac ctxt
  THEN' Expressions.index_tac ctxt
  THEN' Expressions.index_tac ctxt
  THEN' Expressions.index_tac ctxt
  THEN' Expressions.index_tac ctxt
  THEN' Expressions.substitute_vars_tac ctxt
  THEN' Expressions.substitute_vars_tac ctxt
  THEN' Misc.append_list_tac ctxt
  THEN' Expressions.subst_expression_tac ctxt
  THEN' Expressions.map_expression_tac ctxt *)

fun joint_measure_simple_seq_tac ctxt i =
  Tactics.seq_tac ~2 ~2 (Var(("precondition",0),\<^typ>\<open>predicate expression2\<close>)) ctxt i
  THEN
  joint_measure_simple_tac ctxt (i+1)
  THEN
  CONVERSION ((Expressions.clean_expression_conv |> Misc.mk_ctxt_conv Conv.arg_conv |> Misc.concl_conv_Trueprop) ctxt) i
end
\<close>

experiment
  fixes x :: \<open>bit cvariable\<close> and y :: \<open>bit cvariable\<close> and Q :: \<open>bit qvariable\<close> and R :: \<open>bit qvariable\<close>
  assumes [register]: \<open>cregister x\<close> \<open>cregister y\<close> \<open>qregister Q\<close> \<open>qregister R\<close>
begin

lemma
  shows "qrhl A [hello, measurement x Q e] [bye, measurement y R f] B"
  apply (tactic \<open>Joint_Measure.joint_measure_simple_seq_tac \<^context> 1\<close>)
  oops
end

end
