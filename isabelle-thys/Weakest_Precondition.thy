theory Weakest_Precondition
  imports Tactics Basic_Rules
begin

thm assign1_rule
(* Use assign1/2_rule, sample1/2_rule directly  *)
(* lemma wp1_assign_tac:
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
  unfolding assms by (fact sample2_rule) *)

lemma wp1_qapply_tac:
  fixes A B Q e
  assumes \<open>qregister Q\<close>
  defines "Q\<^sub>1 \<equiv> qregister_chain qFst Q"
  defines "e\<^sub>1 \<equiv> (\<lambda>m. e (fst m))"
  defines "A \<equiv> (\<lambda>m. Cla[isometry (e\<^sub>1 m)] \<sqinter> (adj ((e\<^sub>1 m)\<guillemotright>Q\<^sub>1) \<cdot> (B m \<sqinter> ((e\<^sub>1 m)\<guillemotright>Q\<^sub>1 \<cdot> top))))"
  shows "qrhl A [qapply Q e] [] B"
  by (cheat wp1_qapply_tac)

(* TODO move, name *)
(* lemma [simp]: \<open>index_flip_subspace (apply_qregister qSnd S) = apply_qregister qFst S\<close> *)
lemma [simp]: \<open>index_flip_subspace (A *\<^sub>S S) = apply_qregister qswap A *\<^sub>S index_flip_subspace S\<close>
  sorry
lemma [simp]: \<open>apply_qregister qswap (apply_qregister qFst x) = apply_qregister qSnd x\<close>
  sorry
lemma [simp]: \<open>apply_qregister qswap (apply_qregister qSnd x) = apply_qregister qFst x\<close>
  sorry
lemma [simp]: \<open>index_flip_subspace (A \<div> \<psi> \<guillemotright> Q) = index_flip_subspace A \<div> \<psi> \<guillemotright> index_flip_qvar Q\<close>
  sorry
lemma [simp]: \<open>index_flip_subspace (index_flip_subspace S) = S\<close>
  sorry
lemma [simp]: \<open>index_flip_subspace (A \<squnion> B) = index_flip_subspace A \<squnion> index_flip_subspace B\<close>
  sorry
lemma [simp]: \<open>prod.swap (setter x a m) = setter (cregister_chain cswap x) a (prod.swap m)\<close>
  sorry
lemma [simp]: \<open>apply_cregister cswap (apply_cregister cFst x) = apply_cregister cSnd x\<close>
  sorry
lemma [simp]: \<open>apply_cregister cswap (apply_cregister cSnd x) = apply_cregister cFst x\<close>
  sorry
lemma [simp]: \<open>cregister_chain cswap (cregister_chain cFst x) = cregister_chain cSnd x\<close>
  by (metis ccompatible_Fst_Snd cregister_chain_assoc cregister_chain_pair_Fst cregister_pair_iff_compatible cswap_def distinct_cvars_swap)
lemma [simp]: \<open>cregister_chain cswap (cregister_chain cSnd x) = cregister_chain cFst x\<close>
  by (metis ccompatible_Fst_Snd ccompatible_sym cregister_chain_assoc cregister_chain_pair_Snd cswap_def)

lemma wp2_qapply_tac:
  fixes A B Q e
  assumes \<open>qregister Q\<close>
  defines "Q\<^sub>1 \<equiv> qregister_chain qSnd Q"
  defines "e\<^sub>1 \<equiv> (\<lambda>m. e (snd m))"
  defines "A \<equiv> (\<lambda>m. Cla[isometry (e\<^sub>1 m)] \<sqinter> (adj ((e\<^sub>1 m)\<guillemotright>Q\<^sub>1) \<cdot> (B m \<sqinter> ((e\<^sub>1 m)\<guillemotright>Q\<^sub>1 \<cdot> top))))"
  shows "qrhl A [] [qapply Q e] B"
  apply (rule sym_rule)
  apply (subst asm_rl[of \<open>(\<lambda>m. index_flip_subspace (A (prod.swap m))) = _\<close>]) defer
   apply (rule wp1_qapply_tac)
  using assms by auto

lemma wp1_qinit_tac:
  fixes B e Q
  assumes \<open>qregister Q\<close>
  defines "Q\<^sub>1 \<equiv> qregister_chain qFst Q"
  defines "e\<^sub>1 \<equiv> (\<lambda>m. e (fst m))"
  defines "A \<equiv> map_expression2 (\<lambda>e\<^sub>1 B. Cla[norm e\<^sub>1 = 1] \<sqinter> (B \<div> e\<^sub>1 \<guillemotright> Q\<^sub>1)) e\<^sub>1 B"
  shows "qrhl A [qinit Q e] [] B"
  by (cheat wp1_qinit_tac)

lemma wp2_qinit_tac:
  fixes B e Q
  assumes \<open>qregister Q\<close>
  defines "Q\<^sub>1 \<equiv> qregister_chain qSnd Q"
  defines "e\<^sub>1 \<equiv> (\<lambda>m. e (snd m))"
  defines "A \<equiv> map_expression2 (\<lambda>e\<^sub>1 B. Cla[norm e\<^sub>1 = 1] \<sqinter> (B \<div> e\<^sub>1 \<guillemotright> Q\<^sub>1)) e\<^sub>1 B"
  shows "qrhl A [] [qinit Q e] B"
  apply (rule sym_rule)
  apply (subst asm_rl[of \<open>(\<lambda>m. index_flip_subspace (A (prod.swap m))) = _\<close>]) defer
   apply (rule wp1_qinit_tac)
  using assms by auto

lemma wp1_if_tac:
  fixes e p1 p2 B
  defines "e\<^sub>1 \<equiv> (\<lambda>m. e (fst m))"
  assumes "qrhl wp_true p1 [] B"
  assumes "qrhl wp_false p2 [] B"
  defines "A \<equiv> (\<lambda>m. (Cla[\<not> e\<^sub>1 m] + wp_true m) \<sqinter> (Cla[e\<^sub>1 m] + wp_false m))"
  shows "qrhl A [ifthenelse e p1 p2] [] B"
  by (cheat wp1_if_tac)

lemma wp2_if_tac:
  fixes e p1 p2 B
  defines "e\<^sub>1 \<equiv> (\<lambda>m. e (snd m))"
  assumes "qrhl wp_true [] p1 B"
  assumes "qrhl wp_false [] p2 B"
  defines "A \<equiv> (\<lambda>m. (Cla[\<not> e\<^sub>1 m] + wp_true m) \<sqinter> (Cla[e\<^sub>1 m] + wp_false m))"
  shows "qrhl A [] [ifthenelse e p1 p2] B"
  apply (rule sym_rule)
  apply (subst asm_rl[of \<open>(\<lambda>m. index_flip_subspace (A (prod.swap m))) = _\<close>]) defer
   apply (rule wp1_if_tac[where wp_true=\<open>(\<lambda>m. index_flip_subspace (wp_true (prod.swap m)))\<close>
        and wp_false=\<open>(\<lambda>m. index_flip_subspace (wp_false (prod.swap m)))\<close>])
    apply (rule sym_rule)
  using assms(2) apply simp
   apply (rule sym_rule)
  using assms(3) apply simp
  unfolding A_def e\<^sub>1_def by simp

lemma wp1_block_tac:
  assumes "qrhl A p [] B"
  shows "qrhl A [block p] [] B"
  apply (subst qrhl_denotation_replace[where c'=p and d'=\<open>[]\<close>])
  using assms by (auto simp: denotation_block)

lemma wp2_block_tac:
  assumes "qrhl A [] p B"
  shows "qrhl A [] [block p] B"
  apply (subst qrhl_denotation_replace[where c'=\<open>[]\<close> and d'=p])
  using assms by (auto simp: denotation_block)

lemma wp1_measure_tac:
  fixes A B x Q e
  assumes \<open>cregister x\<close> \<open>qregister Q\<close>
  defines "x\<^sub>1 \<equiv> cregister_chain cFst x"
  defines "Q\<^sub>1 \<equiv> qregister_chain qFst Q"
  defines "e\<^sub>1 \<equiv> (\<lambda>m. e (fst m))"
  defines "\<And>z. B' z \<equiv> (\<lambda>m. B (setter x\<^sub>1 z m))"
  defines "\<And>e\<^sub>1 z. ebar e\<^sub>1 z \<equiv> ((mproj e\<^sub>1 z)\<guillemotright>Q\<^sub>1) \<cdot> top"
  defines "A \<equiv> (\<lambda>m. let M = e\<^sub>1 m in Cla[mtotal M] \<sqinter> 
                         (INF z. let P = ebar M z in ((B' z m \<sqinter> P) + - P)))"
  shows "qrhl A [measurement x Q e] [] B"
  by (cheat wp1_measure_tac)

lemma wp2_measure_tac:
  fixes A B x Q e
  assumes \<open>cregister x\<close> \<open>qregister Q\<close>
  defines "x\<^sub>1 \<equiv> cregister_chain cSnd x"
  defines "Q\<^sub>1 \<equiv> qregister_chain qSnd Q"
  defines "e\<^sub>1 \<equiv> (\<lambda>m. e (snd m))"
  defines "\<And>z. B' z \<equiv> (\<lambda>m. B (setter x\<^sub>1 z m))"
  defines "\<And>e\<^sub>1 z. ebar e\<^sub>1 z \<equiv> ((mproj e\<^sub>1 z)\<guillemotright>Q\<^sub>1) \<cdot> top"
  defines "A \<equiv> (\<lambda>m. let M = e\<^sub>1 m in Cla[mtotal M] \<sqinter> 
                         (INF z. let P = ebar M z in ((B' z m \<sqinter> P) + - P)))"
  shows "qrhl A [] [measurement x Q e] B"
  apply (rule sym_rule)
  apply (subst asm_rl[of \<open>(\<lambda>m. index_flip_subspace (A (prod.swap m))) = _\<close>]) defer
   apply (rule wp1_measure_tac)
  using assms by (auto simp: Let_def)

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

(* (* TODO move or remove *)
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
\<close> *)

ML_file "weakest_precondition.ML"

experiment
  fixes x y :: \<open>nat cvariable\<close> assumes [variable]: \<open>cregister \<lbrakk>x,y\<rbrakk>\<close>
begin

abbreviation \<open>x1 \<equiv> cregister_chain cFst x\<close>

lemma \<open>qrhl (\<lambda>m. Cla[getter x1 m = 1]) [assign x (\<lambda>m. 2)] []  (\<lambda>m. Cla[getter x1 m = 2])\<close>
  apply (tactic \<open>Weakest_Precondition.wp_seq_tac 1 0 \<^context> 1\<close>)
  oops

end

end
