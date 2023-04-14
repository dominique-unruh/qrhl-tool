theory Prog_Variables
  imports
    (* Multi_Transfer *)
    HOL.Map
    BOLegacy
    Registers.Classical_Extra
    Quantum_Registers
    Classical_Registers
    Quantum_Reg_Ranges
    Classical_Reg_Ranges
    Quantum_Reg_Conversions
    Quantum_From_Classical_Reg
    Classical_Reg_Conversions
    Register_Syntax
  keywords "debug_translate_to_index_registers" :: "diag"
begin

unbundle cblinfun_notation
no_notation m_inv ("inv\<index> _" [81] 80)
hide_const (open) Order.top
no_notation Order.top ("\<top>\<index>")
hide_const (open) Axioms_Classical.getter
hide_const (open) Axioms_Classical.setter
declare [[simproc del: Laws_Quantum.compatibility_warn]]
declare [[simproc del: Laws_Classical.compatibility_warn]]
hide_const (open) Classical_Extra.X Classical_Extra.Y Classical_Extra.x Classical_Extra.y
hide_const (open) Coset.kernel

subsubsection \<open>Wrapper types around registers\<close>



typedecl cl
typedecl qu
instance qu :: default ..

type_synonym 'a cvariable = \<open>('a,cl) cregister\<close>
type_synonym 'a qvariable = \<open>('a,qu) qregister\<close>

type_synonym QVARIABLE = \<open>qu QREGISTER\<close>
type_synonym CVARIABLE = \<open>cl CREGISTER\<close>

(* datatype 'a vtree = VTree_Singleton 'a | VTree_Concat "'a vtree" "'a vtree" | VTree_Unit *)

section \<open>Distinct variables\<close>

abbreviation (input) "distinct_qvars Q == qregister Q" (* LEGACY *)
abbreviation (input) "distinct_cvars Q == cregister Q" (* LEGACY *)

lemma distinct_qvars_split1:
  "distinct_qvars (qregister_pair (qregister_pair Q R) S) = (distinct_qvars (qregister_pair Q R) \<and> distinct_qvars (qregister_pair Q S) \<and> distinct_qvars (qregister_pair R S))"
  using qcompatible3 by blast
lemma distinct_qvars_swap: "distinct_qvars (qregister_pair Q R) \<Longrightarrow> distinct_qvars (qregister_pair R Q)"
  using qcompatible_sym by auto
lemma distinct_qvars_split2: "distinct_qvars (qregister_pair S (qregister_pair Q R)) = (distinct_qvars (qregister_pair Q R) \<and> distinct_qvars (qregister_pair Q S) \<and> distinct_qvars (qregister_pair R S))"
  by (metis qcompatible3 qcompatible_sym)
lemma distinct_qvars_concat_unit1[simp]: "distinct_qvars (qregister_pair Q empty_qregister) = distinct_qvars Q" for Q::"'a qvariable"
  using qcompatible_QQcompatible qcompatible_empty by auto
lemma distinct_qvars_concat_unit2[simp]: "distinct_qvars (qregister_pair empty_qregister Q) = distinct_qvars Q" for Q::"'a::finite qvariable"
  using qcompatible_QQcompatible qcompatible_empty qcompatible_sym by blast
lemma distinct_qvars_unit[simp]: "distinct_qvars empty_qregister"
  by (simp add: )

lemma distinct_qvarsL: "distinct_qvars (qregister_pair Q R) \<Longrightarrow> distinct_qvars Q"
  by (simp add: qcompatible_QQcompatible)
lemma distinct_qvarsR: "distinct_qvars (qregister_pair Q R) \<Longrightarrow> distinct_qvars R"
  by (simp add: qcompatible_def)

lemma distinct_cvars_swap: "distinct_cvars (cregister_pair Q R) \<Longrightarrow> distinct_cvars (cregister_pair R Q)"
  using ccompatible_sym by blast
lemma distinct_cvars_split2: "distinct_cvars (cregister_pair S (cregister_pair Q R)) = (distinct_cvars (cregister_pair Q R) \<and> distinct_cvars (cregister_pair Q S) \<and> distinct_cvars (cregister_pair R S))"
  by (metis ccompatible3 distinct_cvars_swap)

section \<open>Indexed variables\<close>

type_synonym cl2 = \<open>cl \<times> cl\<close>
type_synonym qu2 = \<open>qu \<times> qu\<close>

type_synonym 'a c2variable = \<open>('a,cl2) cregister\<close>
type_synonym 'a q2variable = \<open>('a,qu2) qregister\<close>

definition index_cvar :: \<open>bool \<Rightarrow> 'a cvariable \<Rightarrow> 'a c2variable\<close> where
  \<open>index_cvar b x = cregister_chain (if b then cFst else cSnd) x\<close>
definition index_qvar :: \<open>bool \<Rightarrow> 'a qvariable \<Rightarrow> 'a q2variable\<close> where
  \<open>index_qvar b x = qregister_chain (if b then qFst else qSnd) x\<close>

definition index_flip_cvar :: \<open>'a c2variable \<Rightarrow> 'a c2variable\<close> where
  \<open>index_flip_cvar x = cregister_chain cswap x\<close>
definition index_flip_qvar :: \<open>'a q2variable \<Rightarrow> 'a q2variable\<close> where
  \<open>index_flip_qvar x = qregister_chain qswap x\<close>

lemma index_flip_qvar_register_pair[simp]: \<open>index_flip_qvar (qregister_pair Q R) = qregister_pair (index_flip_qvar Q) (index_flip_qvar R)\<close>
  unfolding index_flip_qvar_def
  apply (cases \<open>qcompatible Q R\<close>)
  by (simp_all add: qregister_chain_pair)

lemma index_flip_qvar_chain[simp]: \<open>index_flip_qvar (qregister_chain Q R) = qregister_chain (index_flip_qvar Q) R\<close>
  unfolding index_flip_qvar_def
  by (simp add: qregister_chain_assoc)

lemma index_flip_qvar_Fst[simp]: \<open>index_flip_qvar qFst = qSnd\<close>
  unfolding index_flip_qvar_def
  by (simp add: qcompatible_Fst_Snd qcompatible_sym qregister_chain_pair_Fst qswap_def)

lemma index_flip_qvar_Snd[simp]: \<open>index_flip_qvar qSnd = qFst\<close>
  by (simp add: index_flip_qvar_def qcompatible_Fst_Snd qcompatible_sym qregister_chain_pair_Snd qswap_def)

definition index_flip_mem2 :: "qu2 \<Rightarrow> qu2" where \<open>index_flip_mem2 = (\<lambda>(x,y). (y,x))\<close>

definition swap_cvariables_mem2 :: "'a c2variable \<Rightarrow> 'a c2variable \<Rightarrow> (cl2 \<Rightarrow> cl2)" where
  \<open>swap_cvariables_mem2 x y m = apply_cregister_total (cregister_pair x y) (\<lambda>(a,b). (b,a)) m\<close>

definition swap_variables_qvars :: \<open>'a q2variable \<Rightarrow> 'a q2variable \<Rightarrow> 'b q2variable \<Rightarrow> 'b q2variable\<close> where
  \<open>swap_variables_qvars Q Q' R = 
    qregister_chain (transform_qregister (apply_qregister (qregister_pair Q Q') swap_ell2)) R\<close>

section \<open>Unsorted\<close>


(* axiomatization lift_pure_state :: \<open>('a,'b) qregister \<Rightarrow> 'a ell2 \<Rightarrow> 'b ell2\<close> *)


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

section \<open>ML code\<close>

(* TODO remove *)
lemma distinct_cvarsL: "distinct_cvars (cregister_pair Q R) \<Longrightarrow> distinct_cvars Q"
  by (rule ccompatible_register1)
lemma distinct_cvarsR: "distinct_cvars (cregister_pair Q R) \<Longrightarrow> distinct_cvars R"
  by (rule ccompatible_register2)

ML_file "prog_variables.ML"

method_setup translate_to_index_registers = \<open>
  Scan.succeed (fn ctxt => SIMPLE_METHOD (CONVERSION (Prog_Variables.translate_to_index_registers_conv ctxt Prog_Variables.translate_to_index_registers_conv_default_options) 1))
\<close>

text \<open>Invocation: \<open>debug_translate_to_index_registers term for x y z and w z\<close>.
Meaning: x y z are assumed compatible, and so are w z.\<close>
ML \<open>
  Outer_Syntax.command \<^command_keyword>\<open>debug_translate_to_index_registers\<close> "try what translate_to_index_registers does to a subterm"
    ((Parse.term -- Scan.optional (Parse.$$$ "for" |-- Parse.!!! (Parse.and_list1 (Scan.repeat Parse.name))) []) >> 
  (fn (term_str,fixes) => Toplevel.keep (fn state => let
  val ctxt = Toplevel.context_of state
  val ctxt = Config.put Syntax.ambiguity_limit 0 ctxt
  val term_parsed = Syntax.parse_term ctxt term_str
  fun mk_tuple [] = error "unexpected"
    | mk_tuple [x] = Free(x,dummyT)
    | mk_tuple (x::xs) = \<^Const>\<open>qregister_pair dummyT dummyT dummyT\<close> $ mk_tuple [x] $ mk_tuple xs
  val assms_parsed = map (fn f => \<^Const>\<open>qregister dummyT dummyT\<close> $ mk_tuple f |> HOLogic.mk_Trueprop) fixes
  (* val _ = assms_parsed |> map (Syntax.string_of_term ctxt) |> map writeln *)
  val term :: assms = Syntax.check_terms ctxt (term_parsed :: assms_parsed)
  val ctxt = fold (fn assm => Context.proof_map (Prog_Variables.declare_register_simps_from_thm (Thm.assume (Thm.cterm_of ctxt assm)))) assms ctxt
  val ct = Thm.cterm_of ctxt term
  val rhs = Prog_Variables.translate_to_index_registers_conv ctxt Prog_Variables.translate_to_index_registers_conv_default_options ct |> Thm.rhs_of
  val result = Syntax.string_of_term ctxt (Thm.term_of rhs)
  val _ = writeln result
  in () end)));
\<close>

section \<open>Syntax\<close>


section \<open>Simprocs\<close>

(* A simproc that utters warnings whenever the simplifier tries to prove a distinct_qvars statement with distinct, explicitly listed variables but can't *)
(* syntax "_declared_qvars" :: "variable_list_args \<Rightarrow> bool" ("declared'_qvars \<lbrakk>_\<rbrakk>")
syntax "_declared_qvars" :: "variable_list_args \<Rightarrow> bool" ("declared'_qvars [|_|]") *)
(* LEGACY *)
abbreviation (input) \<open>declared_qvars Q \<equiv> qregister Q\<close>

(* parse_translation \<open>[("_declared_qvars", Prog_Variables.declared_qvars_parse_tr)]\<close> *)

(* simproc_setup warn_declared_qvars ("variable_name q") = Prog_Variables.warn_declared_qvars_simproc *)

(* simproc_setup index_var ("index_var lr v") = Prog_Variables.index_var_simproc *)
(* simproc_setup index_flip_var ("index_flip_var v") = Prog_Variables.index_flip_var_simproc *)

(* Simproc that rewrites a `qregister_conversion F G` into an index-register.
   (Index-registers are registers build from chain, pair, Fst, Snd.) *)
simproc_setup qregister_conversion_to_register (\<open>qregister_conversion x y\<close>) =
  \<open>fn m => fn ctxt => fn ct => SOME (Prog_Variables.qregister_conversion_to_register_conv ctxt ct) handle e => NONE\<close>

(* A hint to the simplifier with the meaning:
    - A is a term of the form x>>Q
    - Q,R are registers
    - Q \<le> R
    - The whole term should be rewritten into x'>>R for some x'
  Rewriting the term is done by the simproc TODO declared below.
*)
definition "register_conversion_hint R A = A" (* LEGACY *)
lemma register_conversion_hint_cong[cong]: "A=A' \<Longrightarrow> register_conversion_hint R A = register_conversion_hint R A'" by simp

(* Simproc that rewrites terms of the form `register_conversion_hint G (apply_qregister F a)` into
  `apply_qregister target (apply_qregister (qregister_conversion \<dots>) A)` for suitable \<dots> *)
simproc_setup register_conversion_hint (\<open>register_conversion_hint G (apply_qregister F a)\<close> | \<open>register_conversion_hint G (apply_qregister_space F S)\<close>) =
  \<open>fn m => fn ctxt => fn ct => let
    (* val _ = \<^print> ct *)
    val target = ct |> Thm.dest_arg1
    val conv = (Prog_Variables.apply_qregister_conversion_conv ctxt target |> Conv.arg_conv)
        then_conv Conv.rewr_conv @{thm register_conversion_hint_def[THEN eq_reflection]}
    in SOME (conv ct) handle e => NONE end\<close>

(* TODO: check if we keep this mechanism. *)
definition \<open>JOIN_REGISTERS F G FG \<equiv> True\<close>

(* TODO: check if we keep this mechanism. *)
definition \<open>REGISTER_SOLVE x \<equiv> x\<close>
lemma REGISTER_SOLVER_cong[cong]: \<open>REGISTER_SOLVE x = REGISTER_SOLVE x\<close>
  by (rule refl)

named_theorems join_registers

(* TODO: remove or move *)
(* Indicates to the simplifier that the (schematic) variable x should be instantiated as y *)
definition \<open>INSTANTIATE_VARIABLE x y = True\<close>
lemma INSTANTIATE_VARIABLE_cong[cong]: \<open>INSTANTIATE_VARIABLE x y = INSTANTIATE_VARIABLE x y\<close>
  by simp
lemma INSTANTIATE_VARIABLE_instantiate: \<open>INSTANTIATE_VARIABLE x x\<close>
  by (simp add: INSTANTIATE_VARIABLE_def)
setup \<open>
map_theory_simpset (fn ctxt => ctxt
    addSolver 
      Simplifier.mk_solver "INSTANTIATE_VARIABLE" (fn ctxt => 
        resolve_tac ctxt @{thms INSTANTIATE_VARIABLE_instantiate}))\<close>

(* 
(* TODO outdated doc comment *)

Simproc that proves a goal of the form \<open>JOIN_REGISTERS F G ?H ?L\<close> where
  F G are qregisters and H,L will be instantiated.
  (Strictly speaking, they will not be instantiated because simprocs cannot do that.
   Instead, the JOIN_REGISTERS term will be rewritten into (?H=\<dots> \<and> ?L=\<dots>).
   Strictly speaking, H,L do not need to be schematic therefore.)

  Both H, L will instantiated to \<open>(\<lambda>F. register_conversion_hint FG F)\<close> where FG is an upper bound (not proven!)
  for F,G (w.r.t., qregister_le).

  (We have two variables H,L because they may need different types.)
  (* TODO: Do they? Do we have cases where the types are different? Let's see in the end and possibly simplify. *)
*)
(* simproc_setup JOIN_REGISTERS (\<open>JOIN_REGISTERS F G H L\<close>) = \<open>fn _ => fn ctxt => fn ct => let
  val (((F,G),H),L) = ct |> Thm.dest_comb |> apfst Thm.dest_comb |> apfst (apfst Thm.dest_comb) |> apfst (apfst (apfst Thm.dest_arg))
  val F' = Thm.term_of F val G' = Thm.term_of G
  val index = Prog_Variables.is_index_qregister F' andalso Prog_Variables.is_index_qregister G'
  val FG_option = if index then NONE else Prog_Variables.join_registers ctxt F' G' |> Option.map (Thm.cterm_of ctxt)
  in case FG_option of
    NONE => NONE
    | SOME FG =>
        SOME \<^instantiate>\<open>FG and F and G and H and L and 'f=\<open>Thm.ctyp_of_cterm F\<close> and 'g=\<open>Thm.ctyp_of_cterm G\<close> and
              'h=\<open>Thm.ctyp_of_cterm H |> Thm.dest_funT |> fst\<close> and 'l=\<open>Thm.ctyp_of_cterm L |> Thm.dest_funT |> fst\<close> and
              'fg=\<open>Thm.ctyp_of_cterm FG\<close> in
              lemma \<open>JOIN_REGISTERS (F::'f) (G::'g) (H::'h\<Rightarrow>'h) (L::'l\<Rightarrow>'l) \<equiv>
              H = (\<lambda>F. register_conversion_hint (FG::'fg) F) \<and> L = (\<lambda>F. register_conversion_hint FG F)\<close>
              by (auto simp add: JOIN_REGISTERS_def register_conversion_hint_def id_def)\<close> (* |> \<^print> *)
end\<close> *)
simproc_setup JOIN_REGISTERS (\<open>JOIN_REGISTERS F G FG\<close>) = \<open>fn _ => fn ctxt => fn ct => let
  val ((F,G),FG) = ct |> Thm.dest_comb |> apfst Thm.dest_comb |> apfst (apfst Thm.dest_arg)
  val F' = Thm.term_of F val G' = Thm.term_of G
  val FG_option = Prog_Variables.join_registers ctxt F' G' |> Option.map (Thm.cterm_of ctxt)
  (* val _ = \<^print> ("JOIN_REGISTERS", Option.map Thm.typ_of_cterm FG_option, Thm.typ_of_cterm FG) *)
  in case FG_option of
    NONE => NONE
    | SOME FG' =>
        SOME \<^instantiate>\<open>FG and FG' and F and G and 'f=\<open>Thm.ctyp_of_cterm F\<close> and 'g=\<open>Thm.ctyp_of_cterm G\<close> and
              'fg=\<open>Thm.ctyp_of_cterm FG\<close> and 'fg'=\<open>Thm.ctyp_of_cterm FG'\<close> in
              lemma \<open>JOIN_REGISTERS (F::'f) (G::'g) (FG::'fg) \<equiv> INSTANTIATE_VARIABLE FG (FG'::'fg')\<close>
              by (auto simp add: JOIN_REGISTERS_def INSTANTIATE_VARIABLE_def)\<close> (* |> \<^print> *)
end\<close>

(* TODO move to .ML *)
ML \<open>
(* ct is of the form REGISTER_SOLVE (X :: bool) *)
fun register_solve_simproc_of_tac ctxt tac ct = let
    val goal = ct |> Thm.dest_arg |> Thm.apply \<^cterm>\<open>Trueprop\<close>
(* val _ = goal |> Thm.term_of |> \<^print> *)
    val thm = SOME (Goal.prove_internal ctxt [] goal (fn _ => tac))
           (* handle _ => NONE *)
(* val _ = \<^print> thm *)
    val lemma = @{lemma \<open>X \<Longrightarrow> REGISTER_SOLVE X \<equiv> True\<close> by (simp add: REGISTER_SOLVE_def)}
    val eq = Option.map (fn thm => lemma OF [thm]) thm
(* val _ = \<^print> eq *)
  in eq end

(* TODO: support cregisters as well *)
fun register_solve_le_simproc (_:morphism) ctxt ct =
  case Thm.term_of ct of
    \<^Const_>\<open>REGISTER_SOLVE _\<close> $ (\<^Const_>\<open>qregister_le _ _ _\<close> $ _ $ _) =>
      register_solve_simproc_of_tac ctxt (Prog_Variables.qregister_le_tac ctxt 1) ct
\<close>

(* TODO: support cregisters as well *)
simproc_setup register_solve_le (\<open>REGISTER_SOLVE (qregister_le Q R)\<close>) = register_solve_le_simproc

(* lemma register_conversion_hint_solve[simp]: 
  \<open>register_conversion_hint R (apply_qregister Q x) = apply_qregister R (apply_qregister (qregister_conversion Q R) x)\<close>
  if \<open>REGISTER_SOLVE (qregister_le Q R)\<close>
   *)

definition \<open>NOT_INDEX_REGISTER x = True\<close>
lemma NOT_INDEX_REGISTER_cong[cong]: \<open>NOT_INDEX_REGISTER x = NOT_INDEX_REGISTER x\<close>
  by simp

simproc_setup NOT_INDEX_REGISTER (\<open>NOT_INDEX_REGISTER R\<close>) = \<open>fn _ => fn ctxt => fn ct => let
  val R = Thm.dest_arg ct
  in
      if Prog_Variables.is_index_qregister (Thm.term_of R) |> \<^print>
      then NONE
      else SOME \<^instantiate>\<open>R and 'r=\<open>Thm.ctyp_of_cterm R\<close> in lemma \<open>NOT_INDEX_REGISTER (R::'r) \<equiv> True\<close> by (simp add: NOT_INDEX_REGISTER_def)\<close> |> \<^print>
  end
\<close>

section \<open>Cleanup\<close>

end
