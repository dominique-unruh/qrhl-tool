theory Joint_Sample
  imports Expressions Tactics Basic_Rules
begin

lemma joint_sample:
  fixes e f x y Q R B witness
  defines "e\<^sub>1 \<equiv> index_expression True e"
  defines "f\<^sub>2 \<equiv> index_expression False f"
  defines "x\<^sub>1 \<equiv> index_vars True x"
  defines "y\<^sub>2 \<equiv> index_vars False y"
  defines "B' z \<equiv> subst_expression (substitute_vars x\<^sub>1 (const_expression (fst z)) @
                                     substitute_vars y\<^sub>2 (const_expression (snd z))) B"
  defines "A \<equiv> map_expression4' (\<lambda>witness e\<^sub>1 f\<^sub>2 B'. 
    Cla[map_distr fst witness = e\<^sub>1 \<and> map_distr snd witness = f\<^sub>2] \<sqinter>  
    (INF z\<in>supp witness. ((B' z)))) witness e\<^sub>1 f\<^sub>2 B'"
  shows "qrhl A [sample x e] [sample y f] B"
  by (cheat joint_sample)


lemma joint_sample_equal:
  fixes e f x y Q R B
  defines "e\<^sub>1 \<equiv> index_expression True e"
  defines "f\<^sub>2 \<equiv> index_expression False f"
  defines "x\<^sub>1 \<equiv> index_vars True x"
  defines "y\<^sub>2 \<equiv> index_vars False y"
  defines "B' z \<equiv> subst_expression (substitute_vars x\<^sub>1 (const_expression z) @
                                     substitute_vars y\<^sub>2 (const_expression z)) B"
  defines "A \<equiv> map_expression3' (\<lambda>e\<^sub>1 f\<^sub>2 B'. 
    Cla[e\<^sub>1 = f\<^sub>2] \<sqinter> (INF z\<in>supp e\<^sub>1. ((B' z)))) e\<^sub>1 f\<^sub>2 B'"
  shows "qrhl A [sample x e] [sample y f] B"
  (* apply (rule conseq_rule[rotated], rule)
  apply (rule joint_sample[where witness="map_expression (\<lambda>e. map_distr (\<lambda>x. (x,x)) e) e\<^sub>1"]) *)
  by (cheat joint_sample_equal)

lemma joint_sample_tac:
  fixes e f x y Q R B witness
  assumes "e\<^sub>1 = index_expression True e"
  assumes "f\<^sub>2 = index_expression False f"
  assumes "x\<^sub>1 = index_vars True x"
  assumes "y\<^sub>2 = index_vars False y"
  assumes "\<And>z. \<sigma>1 z = substitute_vars x\<^sub>1 (const_expression (fst z))"
  assumes "\<And>z. \<sigma>2 z = substitute_vars y\<^sub>2 (const_expression (snd z))"
  assumes "\<And>z. \<sigma> z = \<sigma>1 z @ \<sigma>2 z"
  assumes "\<And>z. B' z = subst_expression (\<sigma> z) B"
  assumes "A = map_expression4' (\<lambda>witness e\<^sub>1 f\<^sub>2 B'. 
    Cla[map_distr fst witness = e\<^sub>1 \<and> map_distr snd witness = f\<^sub>2] \<sqinter>  
    (INF z\<in>supp witness. ((B' z)))) witness e\<^sub>1 f\<^sub>2 B'"
  shows "qrhl A [sample x e] [sample y f] B"
unfolding assms Let_def by (rule joint_sample)

lemma joint_sample_equal_tac:
  fixes e f x y Q R B
  assumes "e\<^sub>1 = index_expression True e"
  assumes "f\<^sub>2 = index_expression False f"
  assumes "x\<^sub>1 = index_vars True x"
  assumes "y\<^sub>2 = index_vars False y"
  assumes "\<And>z. \<sigma>1 z = substitute_vars x\<^sub>1 (const_expression z)"
  assumes "\<And>z. \<sigma>2 z = substitute_vars y\<^sub>2 (const_expression z)"
  assumes "\<And>z. \<sigma> z = \<sigma>1 z @ \<sigma>2 z"
  assumes "\<And>z. B' z = subst_expression (\<sigma> z) B"
  assumes "A = map_expression3' (\<lambda>e\<^sub>1 f\<^sub>2 B'. Cla[e\<^sub>1 = f\<^sub>2] \<sqinter>  
    (INF z\<in>supp e\<^sub>1. ((B' z)))) e\<^sub>1 f\<^sub>2 B'"
  shows "qrhl A [sample x e] [sample y f] B"
unfolding assms Let_def by (rule joint_sample_equal)

ML \<open>
structure Joint_Sample = struct

fun joint_sample_tac ctxt witness =
let val _ = if Expressions.is_explicit_expression (Thm.term_of witness) then ()
            else raise CTERM("joint_sample_tac: witness is not an explicit expression",[witness])
    val tac_thm = infer_instantiate ctxt [(("witness",0),witness)] @{thm joint_sample_tac} in
  resolve_tac ctxt [tac_thm]
  THEN' Expressions.index_tac ctxt
  THEN' Expressions.index_tac ctxt
  THEN' Expressions.index_tac ctxt
  THEN' Expressions.index_tac ctxt
  THEN' Expressions.substitute_vars_tac ctxt
  THEN' Expressions.substitute_vars_tac ctxt
  THEN' Misc.append_list_tac ctxt
  THEN' Expressions.subst_expression_tac ctxt
  THEN' Expressions.map_expression_tac ctxt
end

fun joint_sample_equal_tac ctxt =
  resolve_tac ctxt @{thms joint_sample_equal_tac}
  THEN' Expressions.index_tac ctxt
  THEN' Expressions.index_tac ctxt
  THEN' Expressions.index_tac ctxt
  THEN' Expressions.index_tac ctxt
  THEN' Expressions.substitute_vars_tac ctxt
  THEN' Expressions.substitute_vars_tac ctxt
  THEN' Misc.append_list_tac ctxt
  THEN' Expressions.subst_expression_tac ctxt
  THEN' Expressions.map_expression_tac ctxt

fun joint_sample_seq_tac ctxt witness i =
  Tactics.seq_tac ~2 ~2 (Var(("precondition",0),\<^typ>\<open>predicate expression\<close>)) ctxt i
  THEN
  joint_sample_tac ctxt witness (i+1)

fun joint_sample_equal_seq_tac ctxt i =
  Tactics.seq_tac ~2 ~2 (Var(("precondition",0),\<^typ>\<open>predicate expression\<close>)) ctxt i
  THEN
  joint_sample_equal_tac ctxt (i+1)
end
\<close>

(* variables classical x :: bit and classical y :: bit begin
schematic_goal xxx: "qrhl ?e [sample \<lbrakk>var_x\<rbrakk> Expr[uniform UNIV]] [sample \<lbrakk>var_y\<rbrakk> Expr[uniform UNIV]] Expr[Cla[x1=y2]]"
  by (tactic \<open>Joint_Sample.joint_sample_equal_tac \<^context> 1\<close>)
thm xxx
end *)

end