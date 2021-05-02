theory Weakest_Precondition
  imports Tactics Basic_Rules
begin

lemma wp1_assign_tac:
  fixes A B x e
  assumes "x1 = index_vars True x"
  assumes "e1 = index_expression True e"
  assumes "A = subst_expression (substitute_vars x1 e1) B"
  shows "qrhl A [assign x e] [] B"
  unfolding assms by (fact assign1_rule)

lemma wp2_assign_tac:
  fixes A B x e
  assumes "x1 = index_vars False x"
  assumes "e1 = index_expression False e"
  assumes "A = subst_expression (substitute_vars x1 e1) B"
  shows "qrhl A [] [assign x e] B"
  unfolding assms by (fact assign2_rule)

lemma wp1_sample_tac:
  fixes A B x e
  assumes "x1 = index_vars True x"
  assumes "e1 = index_expression True e"
  assumes "\<And>z. B' z = subst_expression (substitute_vars x1 (const_expression z)) B"
  assumes "A = map_expression2' (\<lambda>e1 B'. Cla[weight e1 = 1] \<sqinter> (INF z\<in>supp e1. B' z)) e1 B'"
  shows "qrhl A [sample x e] [] B"
  unfolding assms by (fact sample1_rule)

lemma wp2_sample_tac:
  fixes A B x e
  assumes "x1 = index_vars False x"
  assumes "e1 = index_expression False e"
  assumes "\<And>z. B' z = subst_expression (substitute_vars x1 (const_expression z)) B"
  assumes "A = map_expression2' (\<lambda>e1 B'. Cla[weight e1 = 1] \<sqinter> (INF z\<in>supp e1. B' z)) e1 B'"
  shows "qrhl A [] [sample x e] B"
  unfolding assms by (fact sample2_rule)

lemma wp1_qapply_tac:
  fixes A B Q e
  assumes "Q\<^sub>1 = index_vars True Q"
  assumes "e1 = index_expression True e"
  assumes "A = map_expression2 (\<lambda>e\<^sub>1 B. Cla[isometry e\<^sub>1] \<sqinter> (adj (e\<^sub>1\<guillemotright>Q\<^sub>1) \<cdot> (B \<sqinter> (e\<^sub>1\<guillemotright>Q\<^sub>1 \<cdot> top)))) e1 B"
  shows "qrhl A [qapply Q e] [] B"
  by (cheat wp1_qapply_tac)

lemma wp2_qapply_tac:
  fixes A B Q e
  assumes "Q\<^sub>1 = index_vars False Q"
  assumes "e1 = index_expression False e"
  assumes "A = map_expression2 (\<lambda>e\<^sub>1 B. Cla[isometry e\<^sub>1] \<sqinter> (adj (e\<^sub>1\<guillemotright>Q\<^sub>1) \<cdot> (B \<sqinter> (e\<^sub>1\<guillemotright>Q\<^sub>1 \<cdot> top)))) e1 B"
  shows "qrhl A [] [qapply Q e] B"
  by (cheat wp2_qapply_tac)

lemma wp1_qinit_tac:
  fixes B e Q
  assumes "Q1 = index_vars True Q"
  assumes "e1 = index_expression True e"
  assumes "A = map_expression2 (\<lambda>e\<^sub>1 B. Cla[norm e\<^sub>1 = 1] \<sqinter> (B \<div> e\<^sub>1 \<guillemotright> Q1)) e1 B"
  shows "qrhl A [qinit Q e] [] B"
  by (cheat wp1_qinit_tac)

lemma wp2_qinit_tac:
  fixes B e Q
  assumes "Q1 = index_vars False Q"
  assumes "e1 = index_expression False e"
  assumes "A = map_expression2 (\<lambda>e\<^sub>1 B. Cla[norm e\<^sub>1 = 1] \<sqinter> (B \<div> e\<^sub>1 \<guillemotright> Q1)) e1 B"
  shows "qrhl A [] [qinit Q e] B"
  by (cheat wp2_qinit_tac)

lemma wp1_if_tac:
  fixes e p1 p2 B
  assumes "e1 = index_expression True e"
  assumes "qrhl wp_true p1 [] B"
  assumes "qrhl wp_false p2 [] B"
  assumes "A = map_expression3 (\<lambda>e\<^sub>1 wp_true wp_false. (Cla[\<not>e\<^sub>1] + wp_true) \<sqinter> (Cla[e\<^sub>1] + wp_false))
               e1 wp_true wp_false"
  shows "qrhl A [ifthenelse e p1 p2] [] B"
  by (cheat wp1_if_tac)


lemma wp2_if_tac:
  fixes e p1 p2 B
  assumes "e1 = index_expression False e"
  assumes "qrhl wp_true [] p1 B"
  assumes "qrhl wp_false [] p2 B"
  assumes "A = map_expression3 (\<lambda>e\<^sub>1 wp_true wp_false. (Cla[\<not>e\<^sub>1] + wp_true) \<sqinter> (Cla[e\<^sub>1] + wp_false))
               e1 wp_true wp_false"
  shows "qrhl A [] [ifthenelse e p1 p2] B"
  by (cheat wp2_if_tac)

lemma wp1_block_tac:
  assumes "qrhl A p [] B"
  shows "qrhl A [block p] [] B"
  by (cheat wp1_block_tac)

lemma wp2_block_tac:
  assumes "qrhl A [] p B"
  shows "qrhl A [] [block p] B"
  by (cheat wp2_block_tac)

lemma wp1_measure_tac:
  fixes A B x Q e
  assumes "x1 = index_vars True x"
  assumes "Q1 = index_vars True Q"
  assumes "e\<^sub>1 = index_expression True e"
  assumes "\<And>z. B' z = subst_expression (substitute_vars x1 (const_expression z)) B"
  defines "\<And>e\<^sub>1 z. ebar e\<^sub>1 z \<equiv> ((mproj e\<^sub>1 z)\<guillemotright>Q1) \<cdot> top"
  assumes "A = map_expression2' (\<lambda>e\<^sub>1 B'. let M = e\<^sub>1 in Cla[mtotal M] \<sqinter> 
                         (INF z. let P = ebar M z in ((B' z \<sqinter> P) + - P))) e\<^sub>1 B'"
  shows "qrhl A [measurement x Q e] [] B"
  by (cheat wp1_measure_tac)

lemma wp2_measure_tac:
  fixes A B x Q e
  assumes "x1 = index_vars False x"
  assumes "Q1 = index_vars False Q"
  assumes "e\<^sub>1 = index_expression False e"
  assumes "\<And>z. B' z = subst_expression (substitute_vars x1 (const_expression z)) B"
  defines "\<And>e\<^sub>1 z. ebar e\<^sub>1 z \<equiv> ((mproj e\<^sub>1 z)\<guillemotright>Q1) \<cdot> top"
  assumes "A = map_expression2' (\<lambda>e\<^sub>1 B'. let M = e\<^sub>1 in Cla[mtotal M] \<sqinter> 
                         (INF z. let P = ebar M z in ((B' z \<sqinter> P) + - P))) e\<^sub>1 B'"
  shows "qrhl A [] [measurement x Q e] B"
  by (cheat wp2_measure_tac)

lemma wp1_cons_tac:
  assumes "qrhl A [p] [] B'"
    and "qrhl B' ps [] B"
  shows "qrhl A (p#ps) [] B"
  using assms seqREMOVE by fastforce

lemma wp2_cons_tac:
  assumes "qrhl A [] [p] B'"
    and "qrhl B' [] ps B"
  shows "qrhl A [] (p#ps) B"
  using assms seqREMOVE by fastforce

lemma wp_split_left_right_tac:
  assumes "qrhl B c [] C"
    and "qrhl A [] d B"
  shows "qrhl A c d C"
  by (rule seqREMOVE[OF _ _ assms(2) assms(1)], simp_all)

(* TODO move or remove *)
ML \<open>
fun get_variable_name ctxt (v as Free(n,T)) = let
  val vn = unprefix "var_" n handle Fail _ => n
  val varinfo = case Prog_Variables.lookup_variable ctxt vn of SOME vi => vi |
                  NONE => raise TERM("get_variable_name: unknown variable",[v])
  val thm = #name_thm varinfo
(*   val vn = unprefix "var_" n handle Fail _ => n
  val str = HOLogic.mk_string vn
  val _ = get_variable_name_count := (!get_variable_name_count) + 1
in (str, (fn _ => error "get_variable_name cert")) end
 *)
  val prop = Thm.prop_of thm
  val (n',T',str) = case prop of Const _ $ (Const _ $ (Const _ $ Free(n',T')) $ str) => (n',T',str)
  val _ = if n <> n' then raise TERM("get_variable_name: wrong name: "^n',[v]) else ()
  val _ = if T <> T' then raise TYPE("get_variable_name: wrong type",[T,T'],[v]) else ()
in (str, fn _ => thm) end
  | get_variable_name _ v = raise TERM("get_variable_name: not a variable",[v])
\<close>

ML_file "weakest_precondition.ML"



end
