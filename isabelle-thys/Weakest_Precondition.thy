theory Weakest_Precondition
  imports Encoding Tactics
begin

lemma skip_rule:
  shows "qrhl B [] [] B"
  sorry

lemma wp1_assign_tac:
  fixes A B x e
  assumes "x1 = index_var True x"
  assumes "e1 = index_expression True e"
  assumes "A = subst_expression [substitute1 x1 e1] B"
  shows "qrhl A [assign x e] [] B"
  sorry

lemma wp2_assign_tac:
  fixes A B x e
  assumes "x1 = index_var False x"
  assumes "e1 = index_expression False e"
  assumes "A = subst_expression [substitute1 x1 e1] B"
  shows "qrhl A [] [assign x e] B"
  sorry

lemma wp1_sample_tac:
  fixes A B x e
  assumes "x1 = index_var True x"
  assumes "e1 = index_expression True e"
  assumes "\<And>z. B' z = subst_expression [substitute1 x1 (const_expression z)] B"
  assumes "A = map_expression2' (\<lambda>e1 B'. Cla[weight e1 = 1] \<sqinter> (INF z:supp e1. B' z)) e1 B'"
  shows "qrhl A [sample x e] [] B"
  sorry

lemma wp2_sample_tac:
  fixes A B x e
  assumes "x1 = index_var False x"
  assumes "e1 = index_expression False e"
  assumes "\<And>z. B' z = subst_expression [substitute1 x1 (const_expression z)] B"
  assumes "A = map_expression2' (\<lambda>e1 B'. Cla[weight e1 = 1] \<sqinter> (INF z:supp e1. B' z)) e1 B'"
  shows "qrhl A [] [sample x e] B"
  sorry

lemma wp1_qapply_tac:
  fixes A B Q e
  assumes "Q\<^sub>1 = index_vars True Q"
  assumes "e1 = index_expression True e"
  assumes "A = map_expression2 (\<lambda>e\<^sub>1 B. Cla[isometry e\<^sub>1] \<sqinter> (adjoint (e\<^sub>1\<guillemotright>Q\<^sub>1) \<cdot> (B \<sqinter> (e\<^sub>1\<guillemotright>Q\<^sub>1 \<cdot> top)))) e1 B"
  shows "qrhl A [qapply Q e] [] B"
  sorry

lemma wp2_qapply_tac:
  fixes A B Q e
  assumes "Q\<^sub>1 = index_vars False Q"
  assumes "e1 = index_expression False e"
  assumes "A = map_expression2 (\<lambda>e\<^sub>1 B. Cla[isometry e\<^sub>1] \<sqinter> (adjoint (e\<^sub>1\<guillemotright>Q\<^sub>1) \<cdot> (B \<sqinter> (e\<^sub>1\<guillemotright>Q\<^sub>1 \<cdot> top)))) e1 B"
  shows "qrhl A [] [qapply Q e] B"
  sorry

lemma wp1_qinit_tac:
  fixes B e Q
  assumes "Q1 = index_vars True Q"
  assumes "e1 = index_expression True e"
  assumes "A = map_expression2 (\<lambda>e\<^sub>1 B. Cla[norm e\<^sub>1 = 1] \<sqinter> (B \<div> e\<^sub>1 \<guillemotright> Q1)) e1 B"
  shows "qrhl A [qinit Q e] [] B"
  sorry

lemma wp2_qinit_tac:
  fixes B e Q
  assumes "Q1 = index_vars False Q"
  assumes "e1 = index_expression False e"
  assumes "A = map_expression2 (\<lambda>e\<^sub>1 B. Cla[norm e\<^sub>1 = 1] \<sqinter> (B \<div> e\<^sub>1 \<guillemotright> Q1)) e1 B"
  shows "qrhl A [] [qinit Q e] B"
  sorry

lemma wp1_if_tac:
  fixes e p1 p2 B
  assumes "e1 = index_expression True e"
  assumes "qrhl wp_true p1 [] B"
  assumes "qrhl wp_false p2 [] B"
  assumes "A = map_expression3 (\<lambda>e\<^sub>1 wp_true wp_false. (Cla[\<not>e\<^sub>1] + wp_true) \<sqinter> (Cla[e\<^sub>1] + wp_false))
               e1 wp_true wp_false"
  shows "qrhl A [ifthenelse e p1 p2] [] B"
  sorry


lemma wp2_if_tac:
  fixes e p1 p2 B
  assumes "e1 = index_expression False e"
  assumes "qrhl wp_true [] p1 B"
  assumes "qrhl wp_false [] p2 B"
  assumes "A = map_expression3 (\<lambda>e\<^sub>1 wp_true wp_false. (Cla[\<not>e\<^sub>1] + wp_true) \<sqinter> (Cla[e\<^sub>1] + wp_false))
               e1 wp_true wp_false"
  shows "qrhl A [] [ifthenelse e p1 p2] B"
  sorry

lemma wp1_block_tac:
  assumes "qrhl A p [] B"
  shows "qrhl A [block p] [] B"
  sorry

lemma wp2_block_tac:
  assumes "qrhl A [] p B"
  shows "qrhl A [] [block p] B"
  sorry

lemma wp1_measure_tac:
  fixes A B x Q e
  assumes "x1 = index_var True x"
  assumes "Q1 = index_vars True Q"
  assumes "e\<^sub>1 = index_expression True e"
  assumes "\<And>z. B' z = subst_expression [substitute1 x1 (const_expression z)] B"
  defines "\<And>e\<^sub>1 z. ebar e\<^sub>1 z \<equiv> ((mproj e\<^sub>1 z)\<guillemotright>Q1) \<cdot> top"
  assumes "A = map_expression2' (\<lambda>e\<^sub>1 B'. let M = e\<^sub>1 in Cla[mtotal M] \<sqinter> 
                         (INF z. let P = ebar M z in ((B' z \<sqinter> P) + ortho P))) e\<^sub>1 B'"
  shows "qrhl A [measurement x Q e] [] B"
  sorry


lemma wp2_measure_tac:
  fixes A B x Q e
  assumes "x1 = index_var False x"
  assumes "Q1 = index_vars False Q"
  assumes "e\<^sub>1 = index_expression False e"
  assumes "\<And>z. B' z = subst_expression [substitute1 x1 (const_expression z)] B"
  defines "\<And>e\<^sub>1 z. ebar e\<^sub>1 z \<equiv> ((mproj e\<^sub>1 z)\<guillemotright>Q1) \<cdot> top"
  assumes "A = map_expression2' (\<lambda>e\<^sub>1 B'. let M = e\<^sub>1 in Cla[mtotal M] \<sqinter> 
                         (INF z. let P = ebar M z in ((B' z \<sqinter> P) + ortho P))) e\<^sub>1 B'"
  shows "qrhl A [] [measurement x Q e] B"
  sorry

lemma wp1_cons_tac:
  assumes "qrhl A [p] [] B'"
    and "qrhl B' ps [] B"
  shows "qrhl A (p#ps) [] B"
  sorry

lemma wp2_cons_tac:
  assumes "qrhl A [] [p] B'"
    and "qrhl B' [] ps B"
  shows "qrhl A [] (p#ps) B"
  sorry

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
