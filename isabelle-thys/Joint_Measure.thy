theory Joint_Measure
  imports Expressions Encoding Tactics
begin


lemma joint_measure_simple:
  fixes e f x y Q R B
  defines "e\<^sub>1 \<equiv> index_expression True e"
  defines "f\<^sub>2 \<equiv> index_expression False f"
  defines "x\<^sub>1 \<equiv> index_var True x"
  defines "y\<^sub>2 \<equiv> index_var False y"
  defines "Q\<^sub>1 \<equiv> index_vars True Q"
  defines "R\<^sub>2 \<equiv> index_vars False R"
  defines "B' z \<equiv> subst_expression [substitute1 x\<^sub>1 (const_expression z),
                                     substitute1 y\<^sub>2 (const_expression z)] B"
  defines "\<And>e\<^sub>1 z. ebar e\<^sub>1 z \<equiv> ((mproj e\<^sub>1 z)\<guillemotright>Q\<^sub>1) \<cdot> top"
  defines "\<And>f\<^sub>2 z. fbar f\<^sub>2 z \<equiv> ((mproj f\<^sub>2 z)\<guillemotright>R\<^sub>2) \<cdot> top"
  defines "A \<equiv> map_expression3' (\<lambda>e\<^sub>1 f\<^sub>2 B'. 
    Cla[e\<^sub>1=f\<^sub>2] \<sqinter> quantum_equality Q\<^sub>1 R\<^sub>2 \<sqinter> 
    (INF z. ((B' z \<sqinter> ebar e\<^sub>1 z \<sqinter> fbar f\<^sub>2 z) + ortho (ebar e\<^sub>1 z) + ortho (fbar f\<^sub>2 z)))) e\<^sub>1 f\<^sub>2 B'"
  shows "qrhl A [measurement x Q e] [measurement y R f] B"
  sorry


lemma joint_measure_simple_tac:
  fixes e f x y Q R B
  assumes "e\<^sub>1 = index_expression True e"
  assumes "f\<^sub>2 = index_expression False f"
  assumes "x\<^sub>1 = index_var True x"
  assumes "y\<^sub>2 = index_var False y"
  assumes "Q\<^sub>1 = index_vars True Q"
  assumes "R\<^sub>2 = index_vars False R"
  assumes "\<And>z. B' z = subst_expression [substitute1 x\<^sub>1 (const_expression z),
                                         substitute1 y\<^sub>2 (const_expression z)] B"
  defines "\<And>e\<^sub>1 z. ebar e\<^sub>1 z \<equiv> ((mproj e\<^sub>1 z)\<guillemotright>Q\<^sub>1) \<cdot> top"
  defines "\<And>f\<^sub>2 z. fbar f\<^sub>2 z \<equiv> ((mproj f\<^sub>2 z)\<guillemotright>R\<^sub>2) \<cdot> top"
  assumes "A = map_expression3' (\<lambda>e\<^sub>1 f\<^sub>2 B'. 
    Cla[e\<^sub>1=f\<^sub>2] \<sqinter> quantum_equality Q\<^sub>1 R\<^sub>2 \<sqinter> 
    (INF z. let ebar = ebar e\<^sub>1 z; fbar = fbar f\<^sub>2 z in ((B' z \<sqinter> ebar \<sqinter> fbar) + ortho ebar + ortho fbar))) e\<^sub>1 f\<^sub>2 B'"
  shows "qrhl A [measurement x Q e] [measurement y R f] B"
  unfolding assms Let_def by (rule joint_measure_simple)

ML \<open>
structure Joint_Measure = struct
fun joint_measure_simple_tac ctxt =
  resolve_tac ctxt @{thms joint_measure_simple_tac}
  THEN' Expressions.index_tac ctxt
  THEN' Expressions.index_tac ctxt
  THEN' Expressions.index_tac ctxt
  THEN' Expressions.index_tac ctxt
  THEN' Expressions.index_tac ctxt
  THEN' Expressions.index_tac ctxt
  THEN' Expressions.subst_expression_tac ctxt
  THEN' Expressions.map_expression_tac ctxt

fun joint_measure_simple_seq_tac ctxt i =
  Tactics.seq_tac ~2 ~2 (Var(("precondition",0),\<^typ>\<open>predicate expression\<close>)) ctxt i
  THEN
  joint_measure_simple_tac ctxt (i+1)
end
\<close>


end
