theory Registers_Automation
  imports Registers_ML Quantum_Reg_Conversions Classical_Reg_Ranges
begin

subsection \<open>Setup for \<open>INDEX_REGISTER_norm_conv\<close>\<close>

lemma INDEX_REGISTER_norm_conv_aux1: \<open>QREGISTER_pair (QREGISTER_chain A F) (QREGISTER_pair B (QREGISTER_chain A G))
            = QREGISTER_pair B (QREGISTER_chain A (QREGISTER_pair F G))\<close>
  apply (simp flip: QREGISTER_pair_QREGISTER_chain)
  using QREGISTER_pair_assoc QREGISTER_pair_sym
  by metis

hide_fact (open) INDEX_REGISTER_norm_conv_aux1

lemma INDEX_REGISTER_norm_conv_aux2: \<open>QREGISTER_pair (QREGISTER_chain A F) (QREGISTER_pair (QREGISTER_chain A G) B)
            = QREGISTER_pair B (QREGISTER_chain A (QREGISTER_pair F G))\<close>
  apply (simp flip: QREGISTER_pair_QREGISTER_chain)
  using QREGISTER_pair_assoc QREGISTER_pair_sym
  by metis

hide_fact (open) INDEX_REGISTER_norm_conv_aux2

subsection \<open>Setup for \<open>ACTUAL_QREGISTER_tac\<close>\<close>

lemma ACTUAL_QREGISTER_tac_aux1: \<open>ACTUAL_QREGISTER (QREGISTER_pair (QREGISTER_chain qSnd G) (QREGISTER_chain qFst F))\<close> if \<open>ACTUAL_QREGISTER F \<and> ACTUAL_QREGISTER G\<close>
  by (simp add: QREGISTER_pair_sym that ACTUAL_QREGISTER_pair_fst_snd)
hide_fact (open) ACTUAL_QREGISTER_tac_aux1
lemma ACTUAL_QREGISTER_tac_aux2: \<open>ACTUAL_QREGISTER (QREGISTER_pair QREGISTER_fst (QREGISTER_chain qSnd F))\<close> if \<open>ACTUAL_QREGISTER F\<close>
  by (metis ACTUAL_QREGISTER_top QREGISTER_chain_fst_top that ACTUAL_QREGISTER_pair_fst_snd)
hide_fact (open) ACTUAL_QREGISTER_tac_aux2
lemma ACTUAL_QREGISTER_tac_aux3: \<open>ACTUAL_QREGISTER (QREGISTER_pair QREGISTER_snd (QREGISTER_chain qFst F))\<close> if \<open>ACTUAL_QREGISTER F\<close>
  by (metis ACTUAL_QREGISTER_top QREGISTER_chain_snd_top that Registers_Automation.ACTUAL_QREGISTER_tac_aux1)
hide_fact (open) ACTUAL_QREGISTER_tac_aux3
lemma ACTUAL_QREGISTER_tac_aux4: \<open>ACTUAL_QREGISTER (QREGISTER_pair (QREGISTER_chain qSnd F) QREGISTER_fst)\<close> if \<open>ACTUAL_QREGISTER F\<close>
  by (simp add: QREGISTER_pair_sym that Registers_Automation.ACTUAL_QREGISTER_tac_aux2)
hide_fact (open) ACTUAL_QREGISTER_tac_aux4
lemma ACTUAL_QREGISTER_tac_aux5: \<open>ACTUAL_QREGISTER (QREGISTER_pair (QREGISTER_chain qFst F) QREGISTER_snd)\<close> if \<open>ACTUAL_QREGISTER F\<close>
  by (simp add: QREGISTER_pair_sym that Registers_Automation.ACTUAL_QREGISTER_tac_aux3)
hide_fact (open) ACTUAL_QREGISTER_tac_aux5

subsection \<open>Setup for \<open>translate_to_index_registers\<close> method\<close>

text \<open>Contains rules for the translate_to_index_registers-method.

Format of the rules: \<^term>\<open>assumptions \<Longrightarrow> lhs \<equiv> rhs\<close>.
Here lhs is of the form \<^term>\<open>op (apply_qregister F X) (apply_qregister G Y)\<close> (or similar with \<^const>\<open>apply_qregister_space\<close>, or with nothing if its not something liftable)
and rhs is of the form \<^term>\<open>apply_qregister H term3\<close> (or similar with \<^const>\<open>apply_qregister_space\<close>).

The assumptions can be used to instantiate variables in H or term3.
The assumptions are evaluated in forward order.
Only specific forms of assumptions are allowed, see the source of the ML function \<open>translate_to_index_registers_tac1\<close>.
\<close>
named_theorems translate_to_index_registers

(* TODO ensure that we descend into registers if descent-mode is on, even if there is no explicit TTIR_EQ-condition *)

definition \<open>TTIR_QREGISTER Q \<longleftrightarrow> qregister Q\<close>
definition \<open>TTIR_LUB F G FG F' G' \<longleftrightarrow> qregister FG \<and> F = qregister_chain FG F' \<and> G = qregister_chain FG G'\<close>
definition \<open>TTIR_APPLY_QREGISTER A F B \<longleftrightarrow> A = apply_qregister F B\<close>
definition \<open>TTIR_APPLY_QREGISTER_SPACE A F B \<longleftrightarrow> A = apply_qregister_space F B\<close>
definition \<open>PROP TTIR_EQ (A::'a::{}) B \<equiv> (A \<equiv> B)\<close>
(* For index-register F *)
definition \<open>TTIR_COMPLEMENT F G \<longleftrightarrow> qcomplements F G\<close>


lemma translate_to_index_registers_assm_lub_tac_aux: 
  assumes \<open>qregister_le F FG \<and> qregister_le G FG\<close>
  assumes \<open>qregister_conversion F FG = F'\<close>
  assumes \<open>qregister_conversion G FG = G'\<close>
  shows \<open>TTIR_LUB F G FG F' G'\<close>
  by (metis assms TTIR_LUB_def qregister_chain_conversion qregister_le_def)

lemma translate_to_index_registers_template_oo:
  assumes \<open>\<And>FG X Y. qregister FG \<Longrightarrow> 
        apply_qregister FG (f' X Y) = f (apply_qregister FG X) (apply_qregister FG Y)\<close>
  assumes \<open>TTIR_APPLY_QREGISTER A F A'\<close>
  assumes \<open>TTIR_APPLY_QREGISTER B G B'\<close>
  assumes \<open>TTIR_LUB F G FG F' G'\<close>
  shows \<open>TTIR_APPLY_QREGISTER (f A B) FG (f' (apply_qregister F' A') (apply_qregister G' B'))\<close>
  using assms by (simp add: TTIR_APPLY_QREGISTER_def TTIR_LUB_def)

lemma translate_to_index_registers_template_o:
  assumes \<open>\<And>F X. apply_qregister F (f' X) = f (apply_qregister F X)\<close>
  assumes \<open>TTIR_APPLY_QREGISTER A F A'\<close>
  shows \<open>TTIR_APPLY_QREGISTER (f A) F (f' A')\<close>
  using assms by (simp add: TTIR_APPLY_QREGISTER_def)

lemma translate_to_index_registers_template_o':
  assumes \<open>\<And>F X. f (apply_qregister F X) = f' X\<close>
  assumes \<open>TTIR_APPLY_QREGISTER A F A'\<close>
  shows \<open>PROP TTIR_EQ (f A) (f' A')\<close>
  using assms by (simp add: TTIR_APPLY_QREGISTER_def TTIR_EQ_def)

lemma translate_to_index_registers_template_o'_qr:
  assumes \<open>\<And>F X. qregister F \<Longrightarrow> f (apply_qregister F X) = f' X\<close>
  assumes \<open>TTIR_APPLY_QREGISTER A F A'\<close>
  assumes \<open>TTIR_QREGISTER F\<close>
  shows \<open>PROP TTIR_EQ (f A) (f' A')\<close>
  using assms by (simp add: TTIR_APPLY_QREGISTER_def TTIR_QREGISTER_def TTIR_EQ_def)

lemma translate_to_index_registers_template_o_s:
  assumes \<open>\<And>F X. apply_qregister_space F (f' X) = f (apply_qregister F X)\<close>
  assumes \<open>TTIR_APPLY_QREGISTER A F A'\<close>
  shows \<open>TTIR_APPLY_QREGISTER_SPACE (f A) F (f' A')\<close>
  using assms by (simp add: TTIR_APPLY_QREGISTER_def TTIR_APPLY_QREGISTER_SPACE_def)

lemma translate_to_index_registers_template_s_o:
  assumes \<open>\<And>F X. apply_qregister F (f' X) = f (apply_qregister_space F X)\<close>
  assumes \<open>TTIR_APPLY_QREGISTER_SPACE A F A'\<close>
  shows \<open>TTIR_APPLY_QREGISTER (f A) F (f' A')\<close>
  using assms by (simp add: TTIR_APPLY_QREGISTER_def TTIR_APPLY_QREGISTER_SPACE_def)

lemma translate_to_index_registers_template_o_s_qr:
  assumes \<open>\<And>F X. qregister F \<Longrightarrow> apply_qregister_space F (f' X) = f (apply_qregister F X)\<close>
  assumes \<open>TTIR_APPLY_QREGISTER A F A'\<close>
  assumes \<open>TTIR_QREGISTER F\<close>
  shows \<open>TTIR_APPLY_QREGISTER_SPACE (f A) F (f' A')\<close>
  using assms by (simp add: TTIR_APPLY_QREGISTER_def TTIR_APPLY_QREGISTER_SPACE_def TTIR_QREGISTER_def)

lemma translate_to_index_registers_template_s:
  assumes \<open>\<And>F X. apply_qregister_space F (f' X) = f (apply_qregister_space F X)\<close>
  assumes \<open>TTIR_APPLY_QREGISTER_SPACE A F A'\<close>
  shows \<open>TTIR_APPLY_QREGISTER_SPACE (f A) F (f' A')\<close>
  using assms by (simp add: TTIR_APPLY_QREGISTER_SPACE_def)

lemma translate_to_index_registers_template_s_qr:
  assumes \<open>\<And>F X. qregister F \<Longrightarrow> apply_qregister_space F (f' X) = f (apply_qregister_space F X)\<close>
  assumes \<open>TTIR_APPLY_QREGISTER_SPACE A F A'\<close>
  assumes \<open>TTIR_QREGISTER F\<close>
  shows \<open>TTIR_APPLY_QREGISTER_SPACE (f A) F (f' A')\<close>
  using assms by (simp add: TTIR_APPLY_QREGISTER_SPACE_def TTIR_QREGISTER_def)

lemma translate_to_index_registers_template_ss:
  assumes \<open>\<And>FG X Y. qregister FG \<Longrightarrow> 
        apply_qregister_space FG (f' X Y) = f (apply_qregister_space FG X) (apply_qregister_space FG Y)\<close>
  assumes \<open>TTIR_APPLY_QREGISTER_SPACE A F A'\<close>
  assumes \<open>TTIR_APPLY_QREGISTER_SPACE B G B'\<close>
  assumes \<open>TTIR_LUB F G FG F' G'\<close>
  shows \<open>TTIR_APPLY_QREGISTER_SPACE (f A B) FG (f' (apply_qregister_space F' A') (apply_qregister_space G' B'))\<close>
  using assms by (simp add: TTIR_APPLY_QREGISTER_SPACE_def TTIR_LUB_def)

lemma translate_to_index_registers_template_oo':
  assumes \<open>\<And>FG X Y. qregister FG \<Longrightarrow> 
        f (apply_qregister FG X) (apply_qregister FG Y) = f' X Y\<close>
  assumes \<open>TTIR_APPLY_QREGISTER A F A'\<close>
  assumes \<open>TTIR_APPLY_QREGISTER B G B'\<close>
  assumes \<open>TTIR_LUB F G FG F' G'\<close>
  shows \<open>PROP TTIR_EQ (f A B) (f' (apply_qregister F' A') (apply_qregister G' B'))\<close>
  using assms by (simp add: TTIR_APPLY_QREGISTER_def TTIR_EQ_def TTIR_LUB_def)

lemma translate_to_index_registers_template_ss':
  assumes \<open>\<And>FG X Y. qregister FG \<Longrightarrow> 
        f (apply_qregister_space FG X) (apply_qregister_space FG Y) = f' X Y\<close>
  assumes \<open>TTIR_APPLY_QREGISTER_SPACE A F A'\<close>
  assumes \<open>TTIR_APPLY_QREGISTER_SPACE B G B'\<close>
  assumes \<open>TTIR_LUB F G FG F' G'\<close>
  shows \<open>PROP TTIR_EQ (f A B) (f' (apply_qregister_space F' A') (apply_qregister_space G' B'))\<close>
  using assms by (simp add: TTIR_APPLY_QREGISTER_SPACE_def TTIR_EQ_def TTIR_LUB_def)

lemma translate_to_index_registers_template_os:
  assumes \<open>\<And>FG X Y. qregister FG \<Longrightarrow> 
        apply_qregister_space FG (f' X Y) = f (apply_qregister FG X) (apply_qregister_space FG Y)\<close>
  assumes \<open>TTIR_APPLY_QREGISTER A F A'\<close>
  assumes \<open>TTIR_APPLY_QREGISTER_SPACE B G B'\<close>
  assumes \<open>TTIR_LUB F G FG F' G'\<close>
  shows \<open>TTIR_APPLY_QREGISTER_SPACE (f A B) FG (f' (apply_qregister F' A') (apply_qregister_space G' B'))\<close>
  using assms by (simp add: TTIR_APPLY_QREGISTER_def TTIR_APPLY_QREGISTER_SPACE_def TTIR_LUB_def)

lemma translate_to_index_registers_template_s_empty:
  assumes \<open>\<And>FG. qregister FG \<Longrightarrow> apply_qregister_space FG f = f'\<close>
  shows \<open>TTIR_APPLY_QREGISTER_SPACE f' (empty_qregister :: (unit,_) qregister) f\<close>
  using assms by (simp add: TTIR_APPLY_QREGISTER_SPACE_def)

lemma translate_to_index_registers_template_o_empty:
  assumes \<open>\<And>FG. qregister FG \<Longrightarrow> apply_qregister FG f = f'\<close>
  shows \<open>TTIR_APPLY_QREGISTER f' (empty_qregister :: (unit,_) qregister) f\<close>
  using assms apply (simp add: TTIR_APPLY_QREGISTER_def)
  using apply_qregister_empty_qregister empty_qregister_is_register by blast

lemma translate_to_index_registers_apply[translate_to_index_registers]:
  assumes \<open>TTIR_APPLY_QREGISTER A G A'\<close>
  shows \<open>TTIR_APPLY_QREGISTER (apply_qregister F A) (qregister_chain F G) A'\<close>
  using assms by (auto simp: TTIR_APPLY_QREGISTER_def)

lemma translate_to_index_registers_apply_space[translate_to_index_registers]:
  assumes \<open>TTIR_APPLY_QREGISTER_SPACE A G A'\<close>
  shows \<open>TTIR_APPLY_QREGISTER_SPACE (apply_qregister_space F A) (qregister_chain F G) A'\<close>
  using assms by (auto simp: TTIR_APPLY_QREGISTER_SPACE_def)

lemmas translate_to_index_registers_compose[translate_to_index_registers] =
  translate_to_index_registers_template_oo[where f=cblinfun_compose, OF qregister_compose]

lemmas translate_to_index_registers_plus_op[translate_to_index_registers] =
  translate_to_index_registers_template_oo[where f=plus, OF apply_qregister_plus]

lemmas translate_to_index_registers_minus_op[translate_to_index_registers] =
  translate_to_index_registers_template_oo[where f=minus, OF apply_qregister_minus]

lemmas translate_to_index_registers_image[translate_to_index_registers] =
  translate_to_index_registers_template_os[where f=cblinfun_image, OF apply_qregister_space_image]

lemmas translate_to_index_registers_eq_op[translate_to_index_registers] =
  translate_to_index_registers_template_oo'[where f=HOL.eq, OF apply_qregister_inject', remove_prem]

lemmas translate_to_index_registers_inf[translate_to_index_registers] =
  translate_to_index_registers_template_ss[where f=inf, OF apply_qregister_space_inf]

lemmas translate_to_index_registers_minus_space[translate_to_index_registers] =
  translate_to_index_registers_template_ss[where f=minus, OF apply_qregister_space_minus]

lemmas translate_to_index_registers_sup[translate_to_index_registers] =
  translate_to_index_registers_template_ss[where f=sup, OF apply_qregister_space_sup]

lemmas translate_to_index_registers_plus_space[translate_to_index_registers] =
  translate_to_index_registers_template_ss[where f=plus, OF apply_qregister_space_plus]

lemmas translate_to_index_registers_eq_space[translate_to_index_registers] =
  translate_to_index_registers_template_ss'[where f=HOL.eq, OF apply_qregister_space_inject', remove_prem]

lemmas translate_to_index_registers_leq_space[translate_to_index_registers] =
  translate_to_index_registers_template_ss'[where f=less_eq, OF apply_qregister_space_mono, remove_prem]

lemmas translate_to_index_registers_leq_op[translate_to_index_registers] =
  translate_to_index_registers_template_oo'[where f=less_eq, OF apply_qregister_mono, remove_prem]

lemmas translate_to_index_registers_top[translate_to_index_registers] =
  translate_to_index_registers_template_s_empty[where f=top, OF apply_qregister_space_top, remove_prem]

lemmas translate_to_index_registers_bot[translate_to_index_registers] =
  translate_to_index_registers_template_s_empty[where f=bot, OF apply_qregister_space_bot]

lemmas translate_to_index_registers_id[translate_to_index_registers] =
  translate_to_index_registers_template_o_empty[where f=id_cblinfun, OF apply_qregister_of_id, remove_prem]

lemma translate_to_index_registers_1[translate_to_index_registers]:
  \<open>TTIR_APPLY_QREGISTER 1 (empty_qregister :: (unit,_) qregister) id_cblinfun\<close>
  using translate_to_index_registers_id by (simp flip: id_cblinfun_eq_1)

lemmas translate_to_index_registers_zero[translate_to_index_registers] =
  translate_to_index_registers_template_o_empty[where f=0, OF apply_qregister_of_0]

lemmas translate_to_index_registers_zero_space[translate_to_index_registers] =
  translate_to_index_registers_template_s_empty[where f=0, OF apply_qregister_space_of_0]

lemmas translate_to_index_registers_uminus_op[translate_to_index_registers] =
  translate_to_index_registers_template_o[where f=uminus, OF apply_qregister_uminus]

lemmas translate_to_index_registers_uminus_space[translate_to_index_registers] =
  translate_to_index_registers_template_s_qr[where f=uminus, OF apply_qregister_space_uminus, remove_prem]

lemmas translate_to_index_registers_adj[translate_to_index_registers] =
  translate_to_index_registers_template_o[where f=adj, OF apply_qregister_adj]

lemmas translate_to_index_registers_scaleC[translate_to_index_registers] =
  translate_to_index_registers_template_o[where f=\<open>scaleC _\<close>, OF apply_qregister_scaleC]

lemmas translate_to_index_registers_scaleR[translate_to_index_registers] =
  translate_to_index_registers_template_o[where f=\<open>scaleR _\<close>, OF apply_qregister_scaleR]

lemmas translate_to_index_registers_scaleC_space[translate_to_index_registers] =
  translate_to_index_registers_template_s_qr[where f=\<open>scaleC _\<close>, OF apply_qregister_space_scaleC, remove_prem]

lemmas translate_to_index_registers_scaleR_space[translate_to_index_registers] =
  translate_to_index_registers_template_s_qr[where f=\<open>scaleR _\<close>, OF apply_qregister_space_scaleR, remove_prem]

lemmas translate_to_index_registers_norm[translate_to_index_registers] =
  translate_to_index_registers_template_o'_qr[where f=norm, OF apply_qregister_norm, remove_prem]

lemmas translate_to_index_registers_Proj[translate_to_index_registers] =
  translate_to_index_registers_template_s_o[where f=Proj, OF apply_qregister_Proj]

lemmas translate_to_index_registers_is_Proj[translate_to_index_registers] =
  translate_to_index_registers_template_o'_qr[where f=is_Proj, OF apply_qregister_is_Proj, remove_prem]

lemmas translate_to_index_registers_kernel[translate_to_index_registers] =
  translate_to_index_registers_template_o_s_qr[where f=Complex_Bounded_Linear_Function.kernel, OF apply_qregister_space_kernel, remove_prem]

lemmas translate_to_index_registers_eigenspace[translate_to_index_registers] =
  translate_to_index_registers_template_o_s_qr[where f=\<open>eigenspace _\<close>, OF apply_qregister_space_eigenspace, remove_prem]

lemmas translate_to_index_registers_orthogonal_spaces[translate_to_index_registers] =
  translate_to_index_registers_template_ss'[where f=orthogonal_spaces, OF apply_qregister_space_orthogonal_spaces, remove_prem]

lemmas translate_to_index_registers_abs_op[translate_to_index_registers] =
  translate_to_index_registers_template_o[where f=abs_op, OF apply_qregister_abs_op]

lemmas translate_to_index_registers_sqrt_op[translate_to_index_registers] =
  translate_to_index_registers_template_o[where f=sqrt_op, OF apply_qregister_sqrt_op]

lemmas translate_to_index_registers_polar_decomposition[translate_to_index_registers] =
  translate_to_index_registers_template_o[where f=polar_decomposition, OF apply_qregister_polar_decomposition]

lemmas translate_to_index_registers_unitary[translate_to_index_registers] =
  translate_to_index_registers_template_o'_qr[where f=unitary, OF apply_qregister_unitary, remove_prem]

lemmas translate_to_index_registers_isometry[translate_to_index_registers] =
  translate_to_index_registers_template_o'_qr[where f=isometry, OF apply_qregister_isometry, remove_prem]

lemmas translate_to_index_registers_partial_isometry[translate_to_index_registers] =
  translate_to_index_registers_template_o'_qr[where f=partial_isometry, OF apply_qregister_partial_isometry, remove_prem]

lemma translate_to_index_registers_INF[translate_to_index_registers]:
  assumes \<open>\<And>x. TTIR_APPLY_QREGISTER_SPACE (S x) Q (T x)\<close>
  assumes \<open>TTIR_QREGISTER Q\<close>
  shows \<open>TTIR_APPLY_QREGISTER_SPACE (INF x\<in>A. S x) Q (INF x\<in>A. T x)\<close>
  using assms
  by (simp add: TTIR_APPLY_QREGISTER_SPACE_def TTIR_QREGISTER_def apply_qregister_space_INF)

lemma translate_to_index_registers_SUP[translate_to_index_registers]:
  assumes \<open>\<And>x. TTIR_APPLY_QREGISTER_SPACE (S x) Q (T x)\<close>
  shows \<open>TTIR_APPLY_QREGISTER_SPACE (SUP x\<in>A. S x) Q (SUP x\<in>A. T x)\<close>
  using assms
  by (simp add: TTIR_APPLY_QREGISTER_SPACE_def TTIR_QREGISTER_def apply_qregister_space_SUP)

lemma translate_to_index_registers_let_ss[translate_to_index_registers]:
  fixes S :: \<open>'a ell2 ccsubspace \<Rightarrow> 'b ell2 ccsubspace\<close>
  assumes \<open>TTIR_APPLY_QREGISTER_SPACE A R B\<close>
  assumes \<open>\<And>x. TTIR_APPLY_QREGISTER_SPACE (S (apply_qregister_space R x)) Q (T x)\<close>
  shows \<open>TTIR_APPLY_QREGISTER_SPACE (let x = A in S x) Q (let x = B in T x)\<close>
  using assms by (simp add: Let_def TTIR_APPLY_QREGISTER_SPACE_def)

lemma translate_to_index_registers_let_os[translate_to_index_registers]:
  fixes S :: \<open>'a qupdate \<Rightarrow> 'b ell2 ccsubspace\<close>
  assumes \<open>TTIR_APPLY_QREGISTER A R B\<close>
  assumes \<open>\<And>x. TTIR_APPLY_QREGISTER_SPACE (S (apply_qregister R x)) Q (T x)\<close>
  shows \<open>TTIR_APPLY_QREGISTER_SPACE (let x = A in S x) Q (let x = B in T x)\<close>
  using assms by (simp add: Let_def TTIR_APPLY_QREGISTER_def TTIR_APPLY_QREGISTER_SPACE_def)

lemma translate_to_index_registers_let_sx[translate_to_index_registers]:
  fixes S :: \<open>'a ell2 ccsubspace \<Rightarrow> 'b ell2 ccsubspace\<close>
  assumes \<open>TTIR_APPLY_QREGISTER_SPACE A R B\<close>
  assumes \<open>\<And>x. PROP TTIR_EQ (S (apply_qregister_space R x)) (T x)\<close>
  shows \<open>PROP TTIR_EQ (let x = A in S x) (let x = B in T x)\<close>
  using assms by (simp add: Let_def TTIR_APPLY_QREGISTER_SPACE_def)

lemma translate_to_index_registers_let_ox[translate_to_index_registers]:
  fixes S :: \<open>'a qupdate \<Rightarrow> 'b ell2 ccsubspace\<close>
  assumes \<open>TTIR_APPLY_QREGISTER A R B\<close>
  assumes \<open>\<And>x. PROP TTIR_EQ (S (apply_qregister R x)) (T x)\<close>
  shows \<open>PROP TTIR_EQ (let x = A in S x) (let x = B in T x)\<close>
  using assms by (simp add: Let_def TTIR_APPLY_QREGISTER_def)

lemma translate_to_index_registers_let_so[translate_to_index_registers]:
  fixes S :: \<open>'a ell2 ccsubspace \<Rightarrow> 'b qupdate\<close>
  assumes \<open>TTIR_APPLY_QREGISTER_SPACE A R B\<close>
  assumes \<open>\<And>x. TTIR_APPLY_QREGISTER (S (apply_qregister_space R x)) Q (T x)\<close>
  shows \<open>TTIR_APPLY_QREGISTER (let x = A in S x) Q (let x = B in T x)\<close>
  using assms by (simp add: Let_def TTIR_APPLY_QREGISTER_def TTIR_APPLY_QREGISTER_SPACE_def)

lemma translate_to_index_registers_let_oo[translate_to_index_registers]:
  fixes S :: \<open>'a qupdate \<Rightarrow> 'b qupdate\<close>
  assumes \<open>TTIR_APPLY_QREGISTER A R B\<close>
  assumes \<open>\<And>x. TTIR_APPLY_QREGISTER (S (apply_qregister R x)) Q (T x)\<close>
  shows \<open>TTIR_APPLY_QREGISTER (let x = A in S x) Q (let x = B in T x)\<close>
  using assms by (simp add: Let_def TTIR_APPLY_QREGISTER_def)

lemma translate_to_index_registers_let_s[translate_to_index_registers]:
  assumes \<open>\<And>x. TTIR_APPLY_QREGISTER_SPACE (S x) Q (T x)\<close>
  shows \<open>TTIR_APPLY_QREGISTER_SPACE (let x = y in S x) Q (let x = y in T x)\<close>
  by (simp add: assms)

lemma translate_to_index_registers_let_o[translate_to_index_registers]:
  assumes \<open>\<And>x. TTIR_APPLY_QREGISTER (S x) Q (T x)\<close>
  shows \<open>TTIR_APPLY_QREGISTER (let x = y in S x) Q (let x = y in T x)\<close>
  by (simp add: assms)

(* Could be an alternative to the more complex (but more let-duplication-avoiding) TTIR_APPLY_QREGISTER_SPACE-rules for let above *)
lemma translate_to_index_registers_let1':
  assumes \<open>TTIR_APPLY_QREGISTER_SPACE (S y) Q T\<close>
  shows \<open>TTIR_APPLY_QREGISTER_SPACE (let x = y in S x) Q T\<close>
  by (simp add: assms)
lemma translate_to_index_registers_let2':
  assumes \<open>TTIR_APPLY_QREGISTER (S y) Q T\<close>
  shows \<open>TTIR_APPLY_QREGISTER (let x = y in S x) Q T\<close>
  by (simp add: assms)

subsection \<open>Setup for \<open>QCOMPLEMENT_INDEX_REGISTER_conv\<close>\<close>

lemma QCOMPLEMENT_INDEX_REGISTER_conv_aux1:
  assumes \<open>ACTUAL_QREGISTER F\<close>
  shows \<open>QCOMPLEMENT (QREGISTER_pair QREGISTER_fst (QREGISTER_chain qSnd F))
    = QREGISTER_chain qSnd (QCOMPLEMENT F)\<close>
  using QCOMPLEMENT_pair_fst_snd[where F=\<top> and G=F] assms
  by simp
hide_fact (open) QCOMPLEMENT_INDEX_REGISTER_conv_aux1

lemma QCOMPLEMENT_INDEX_REGISTER_conv_aux2:
  assumes \<open>ACTUAL_QREGISTER F\<close>
  shows \<open>QCOMPLEMENT (QREGISTER_pair (QREGISTER_chain qFst F) QREGISTER_snd)
    = QREGISTER_chain qFst (QCOMPLEMENT F)\<close>
  using QCOMPLEMENT_pair_fst_snd[where F=F and G=\<top>] assms
  by simp
hide_fact (open) QCOMPLEMENT_INDEX_REGISTER_conv_aux2

subsection \<open>Setup for \<open>qcomplements_tac\<close>\<close>

lemma qcomplements_tac_aux1:
  assumes F: \<open>qregister F\<close>
  assumes CF: \<open>QCOMPLEMENT (QREGISTER_of F) = QREGISTER_of G\<close>
  assumes G: \<open>qregister G\<close>
  shows \<open>qcomplements F G\<close>
  using F apply (rule qcomplements_via_rangeI)
  using assms(2)[THEN Rep_QREGISTER_inject[THEN iffD2]]
  by (simp add: uminus_QREGISTER.rep_eq QREGISTER_of.rep_eq F G)

hide_fact (open) qcomplements_tac_aux1

subsection \<open>ML code\<close>

ML_file \<open>registers_automation.ML\<close>

end
