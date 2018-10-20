theory Weakest_Precondition
  imports Encoding
begin

lemma seq:
  assumes "qrhl A c1 d1 B"
  and "qrhl B c2 d2 C"
  shows "qrhl A (c1@c2) (d1@d2) C"
  sorry



lemma seqREMOVE:
  assumes "c = c1@c2" and "d = d1@d2"
  assumes "qrhl A c1 d1 B"
    and "qrhl B c2 d2 C"
  shows "qrhl A c d C"
  using assms using seq by auto
  

lemma wp_skip:
  shows "qrhl B [] [] B"
  sorry

lemma wp1_assign:
  fixes A B x e
  defines "A \<equiv> subst_expression [substitute1 (index_var True x) (index_expression True e)] B"
  shows "qrhl A [assign x e] [] B"
  sorry

(* TODO remove *)
lemma wp1_assign_old:
  fixes A B x e
  defines "A \<equiv> subst_expression_old (substitute1 (index_var True x) (index_expression True e)) B"
  shows "qrhl A [assign x e] [] B"
  sorry

lemma wp2_assign:
  fixes A B x e
  defines "A \<equiv> subst_expression [substitute1 (index_var False x) (index_expression False e)] B"
  shows "qrhl A [] [assign x e] B"
  sorry

(* TODO remove *)
lemma wp2_assign_old:
  fixes A B x e
  defines "A \<equiv> subst_expression_old (substitute1 (index_var False x) (index_expression False e)) B"
  shows "qrhl A [] [assign x e] B"
  sorry

lemma wp1_sample:
  fixes A B x e
  defines "e' \<equiv> index_expression True e"
  defines "B' z \<equiv> subst_expression [substitute1 (index_var True x) (const_expression z)] B"
  defines "A \<equiv> map_expression2' (\<lambda>e' B'. Cla[weight e' = 1] \<sqinter> (INF z:supp e'. B' z)) e' B'"
  shows "qrhl A [sample x e] [] B"
  sorry

(* TODO remove *)
lemma wp1_sample_old:
  fixes A B x e
  defines "e' \<equiv> index_expression True e"
  defines "B' z \<equiv> subst_expression_old (substitute1 (index_var True x) (const_expression z)) B"
  defines "A \<equiv> map_expression2' (\<lambda>e' B'. Cla[weight e' = 1] \<sqinter> (INF z:supp e'. B' z)) e' B'"
  shows "qrhl A [sample x e] [] B"
  sorry

lemma wp2_sample:
  fixes A B x e
  defines "e' \<equiv> index_expression False e"
  defines "B' z \<equiv> subst_expression [substitute1 (index_var False x) (const_expression z)] B"
  defines "A \<equiv> map_expression2' (\<lambda>e' B'. Cla[weight e' = 1] \<sqinter> (INF z:supp e'. B' z)) e' B'"
  shows "qrhl A [] [sample x e] B"
  sorry


lemma wp2_sample_old:
  fixes A B x e
  defines "e' \<equiv> index_expression False e"
  defines "B' z \<equiv> subst_expression_old (substitute1 (index_var False x) (const_expression z)) B"
  defines "A \<equiv> map_expression2' (\<lambda>e' B'. Cla[weight e' = 1] \<sqinter> (INF z:supp e'. B' z)) e' B'"
  shows "qrhl A [] [sample x e] B"
  sorry

lemma wp1_qapply:
  fixes A B Q e
  defines "Q\<^sub>1 \<equiv> index_vars True Q"
  defines "A \<equiv> map_expression2 (\<lambda>e\<^sub>1 B. Cla[isometry e\<^sub>1] \<sqinter> (adjoint (e\<^sub>1\<guillemotright>Q\<^sub>1) \<cdot> (B \<sqinter> (e\<^sub>1\<guillemotright>Q\<^sub>1 \<cdot> top)))) (index_expression True e) B"
  shows "qrhl A [qapply Q e] [] B"
  sorry

lemma wp2_qapply:
  fixes A B Q e
  defines "Q\<^sub>2 \<equiv> index_vars False Q"
  defines "A \<equiv> map_expression2 (\<lambda>e\<^sub>2 B. Cla[isometry e\<^sub>2] \<sqinter> (adjoint (e\<^sub>2\<guillemotright>Q\<^sub>2) \<cdot> (B \<sqinter> (e\<^sub>2\<guillemotright>Q\<^sub>2 \<cdot> top)))) (index_expression False e) B"
  shows "qrhl A [] [qapply Q e] B"
  sorry

lemma wp1_measure:
  fixes A B x Q e
  defines "e\<^sub>1 \<equiv> index_expression True e"
  defines "B' z \<equiv> subst_expression [substitute1 (index_var True x) (const_expression z)] B"
  defines "\<And>e\<^sub>1 z. ebar e\<^sub>1 z \<equiv> ((mproj e\<^sub>1 z)\<guillemotright>(index_vars True Q)) \<cdot> top"
  defines "A \<equiv> map_expression2' (\<lambda>e\<^sub>1 B'. let M = e\<^sub>1 in Cla[mtotal M] \<sqinter> 
           (INF z. let P = ebar M z in ((B' z \<sqinter> P) + ortho P))) e\<^sub>1 B'"
  shows "qrhl A [measurement x Q e] [] B"
  sorry

lemma wp2_measure:
  fixes A B x Q e
  defines "e\<^sub>2 \<equiv> index_expression False e"
  defines "B' z \<equiv> subst_expression [substitute1 (index_var False x) (const_expression z)] B"
  defines "\<And>e\<^sub>2 z. ebar e\<^sub>2 z \<equiv> ((mproj e\<^sub>2 z)\<guillemotright>(index_vars False Q)) \<cdot> top"
  defines "A \<equiv> map_expression2' (\<lambda>e\<^sub>2 B'. let M = e\<^sub>2 in Cla[mtotal M] \<sqinter> 
           (INF z. let P = ebar M z in ((B' z \<sqinter> P) + ortho P))) e\<^sub>2 B'"
  shows "qrhl A [] [measurement x Q e] B"
  sorry

lemma wp1_measure_old:
  fixes A B x Q e
  defines "e\<^sub>1 \<equiv> index_expression True e"
  defines "B' z \<equiv> subst_expression_old (substitute1 (index_var True x) (const_expression z)) B"
  defines "\<And>e\<^sub>1 z. ebar e\<^sub>1 z \<equiv> ((mproj e\<^sub>1 z)\<guillemotright>(index_vars True Q)) \<cdot> top"
  defines "A \<equiv> map_expression2' (\<lambda>e\<^sub>1 B'. let M = e\<^sub>1 in Cla[mtotal M] \<sqinter> 
           (INF z. let P = ebar M z in ((B' z \<sqinter> P) + ortho P))) e\<^sub>1 B'"
  shows "qrhl A [measurement x Q e] [] B"
  sorry

lemma wp2_measure_old:
  fixes A B x Q e
  defines "e\<^sub>2 \<equiv> index_expression False e"
  defines "B' z \<equiv> subst_expression_old (substitute1 (index_var False x) (const_expression z)) B"
  defines "\<And>e\<^sub>2 z. ebar e\<^sub>2 z \<equiv> ((mproj e\<^sub>2 z)\<guillemotright>(index_vars False Q)) \<cdot> top"
  defines "A \<equiv> map_expression2' (\<lambda>e\<^sub>2 B'. let M = e\<^sub>2 in Cla[mtotal M] \<sqinter> 
           (INF z. let P = ebar M z in ((B' z \<sqinter> P) + ortho P))) e\<^sub>2 B'"
  shows "qrhl A [] [measurement x Q e] B"
  sorry

lemma wp1_qinit:
  fixes B e Q
  defines "A \<equiv> map_expression2 (\<lambda>e\<^sub>1 B. Cla[norm e\<^sub>1 = 1] \<sqinter> (B \<div> e\<^sub>1 \<guillemotright> (index_vars True Q)))
           (index_expression True e) B"
  shows "qrhl A [qinit Q e] [] B"
  sorry

lemma wp2_qinit:
  fixes B e Q
  defines "A \<equiv> map_expression2 (\<lambda>e\<^sub>2 B. Cla[norm e\<^sub>2 = 1] \<sqinter> (B \<div> e\<^sub>2 \<guillemotright> (index_vars False Q)))
           (index_expression False e) B"
  shows "qrhl A [] [qinit Q e] B"
  sorry

lemma wp1_if:
  fixes e p1 p2 B
  assumes "qrhl wp_true p1 [] B"
  assumes "qrhl wp_false p2 [] B"
  defines "A \<equiv> map_expression3 (\<lambda>e\<^sub>1 wp_true wp_false. (Cla[\<not>e\<^sub>1] + wp_true) \<sqinter> (Cla[e\<^sub>1] + wp_false))
           (index_expression True e) wp_true wp_false"
  shows "qrhl A [ifthenelse e p1 p2] [] B"
  sorry

lemma wp2_if:
  fixes e p1 p2 B
  assumes "qrhl wp_true [] p1 B"
  assumes "qrhl wp_false [] p2 B"
  defines "A \<equiv> map_expression3 (\<lambda>e\<^sub>2 wp_true wp_false. (Cla[\<not>e\<^sub>2] + wp_true) \<sqinter> (Cla[e\<^sub>2] + wp_false))
           (index_expression False e) wp_true wp_false"
  shows "qrhl A [] [ifthenelse e p1 p2] B"
  sorry

lemma wp1_block:
  assumes "qrhl A p [] B"
  shows "qrhl A [block p] [] B"
  sorry

lemma wp2_block:
  assumes "qrhl A [] p B"
  shows "qrhl A [] [block p] B"
  sorry

lemma wp1_cons:
  assumes "qrhl A [p] [] B'"
    and "qrhl B' ps [] B"
  shows "qrhl A (p#ps) [] B"
  sorry

lemma wp2_cons:
  assumes "qrhl A [] [p] B'"
    and "qrhl B' [] ps B"
  shows "qrhl A [] (p#ps) B"
  sorry

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




end
