theory QRHL_Core
  imports Complex_Main "HOL-Library.Adhoc_Overloading" BOLegacy Discrete_Distributions 
    Misc_Missing Prog_Variables (* Registers.Pure_States *)
"HOL-Eisbach.Eisbach"
  keywords "declare_variable_type" :: thy_decl
begin

hide_const (open) Real_Vector_Spaces.span
hide_const (open) Order.top
hide_const (open) Coset.kernel
no_notation Group.monoid.mult (infixl "\<otimes>\<index>" 70)
no_notation m_inv ("inv\<index> _" [81] 80)
hide_const (open) Coset.kernel
(* hide_const (open) Quantum.CNOT
hide_const (open) Quantum.pauliX
hide_const (open) Quantum.pauliZ
hide_const (open) Quantum.pauliZ
hide_const (open) Quantum.hadamard *)

section \<open>Miscellaneous\<close>

declare Inf_class.INF_image[simp]



(* TODO move into theory Predicates.thy *)
section \<open>Quantum predicates\<close>

type_synonym predicate = "qu2 subspace"

subsection \<open>Classical predicates\<close>
  
definition classical_subspace :: "bool \<Rightarrow> _ ell2 ccsubspace"  ("\<CC>\<ll>\<aa>[_]")
  where "\<CC>\<ll>\<aa>[b] = (if b then top else bot)"
syntax classical_subspace :: "bool \<Rightarrow> _ ell2 ccsubspace"  ("Cla[_]")
  \<comment> \<open>Easier to type syntax\<close>

lemma classical_true[simp]: "Cla[True] = top" unfolding classical_subspace_def by simp
lemma classical_false[simp]: "Cla[False] = bot" unfolding classical_subspace_def by simp
lemma classical_mono[simp]: "(Cla[a] \<le> Cla[b]) = (a \<longrightarrow> b)" 
  apply (cases a, auto, cases b, auto)
  using bot.extremum_uniqueI ccsubspace_top_not_bot by blast 
lemma classical_simp1[simp]: 
  shows "(Cla[b] \<le> A) = (b \<longrightarrow> A = top)"
  using top.extremum_unique by fastforce
lemma classical_inf[simp]: "Cla[x] \<sqinter> Cla[y] = Cla[x \<and> y]"
  by (simp add: classical_subspace_def)
lemma classical_sup[simp]: "Cla[x] \<squnion> Cla[y] = Cla[x \<or> y]"
  by (simp add: classical_subspace_def)
lemma classical_simp2[simp]:
  shows "(Cla[a] \<sqinter> B \<le> C) = (a \<longrightarrow> B \<le> C)"
  apply (cases a) by auto
lemma classical_sort[simp]:
  assumes "NO_MATCH Cla[x] A" 
  shows "A \<sqinter> Cla[b] = Cla[b] \<sqinter> A"
  by (simp add: classical_subspace_def)
lemma classical_geq_top[simp]: \<open>\<top> \<le> Cla[b] \<longleftrightarrow> b\<close>
  by (simp add: classical_subspace_def top_unique)

lemma Cla_split[split]: "P (Cla[Q]) = ((Q \<longrightarrow> P top) \<and> (\<not> Q \<longrightarrow> P bot))"
  by (cases Q, auto) 
lemma classical_ortho[simp]: "- Cla[b] = Cla[\<not> b]"
  by auto

lemma applyOp_Cla[simp]:
  assumes "unitary A"
  shows "A \<cdot> Cla[b] = Cla[b]"
  apply (cases b) using assms by auto

lemma Cla_plus[simp]: "Cla[x] + Cla[y] = Cla[x\<or>y]" 
  unfolding sup_ccsubspace_def[symmetric] by auto
lemma Cla_sup[simp]: "Cla[x] \<squnion> Cla[y] = Cla[x\<or>y]" 
  unfolding sup_ccsubspace_def[symmetric] by auto

lemma BINF_Cla[simp]: "(INF z\<in>Z. Cla[x z]) = Cla[\<forall>z\<in>Z. x z]"
proof (rule Inf_eqI)
  show "\<And>i. i \<in> (\<lambda>z. \<CC>\<ll>\<aa>[x z]) ` Z \<Longrightarrow> \<CC>\<ll>\<aa>[\<forall>z\<in>Z. x z] \<le> i" by auto
  fix y assume assm: "\<And>i. i \<in> (\<lambda>z. \<CC>\<ll>\<aa>[x z]) ` Z \<Longrightarrow> y \<le> i"
  show "y \<le> \<CC>\<ll>\<aa>[\<forall>z\<in>Z. x z]"
  proof (cases "\<forall>z\<in>Z. x z")
    case True thus ?thesis by auto
  next case False
    then obtain z where "\<not> x z" and "z\<in>Z" by auto
    hence "Cla[x z] = bot" by simp
    hence "bot \<in> (\<lambda>z. \<CC>\<ll>\<aa>[x z]) ` Z"
      using \<open>z \<in> Z\<close> by force
    hence "y \<le> bot" by (rule assm)
    thus ?thesis
      by (simp add: False)
  qed
qed

lemma BSUP_Cla[simp]: "(SUP z\<in>Z. Cla[x z]) = Cla[\<exists>z\<in>Z. x z]"
  by (smt (verit, ccfv_SIG) SUP_bot_conv(1) Sup_bot_conv(2) Sup_upper classical_subspace_def imageE order_antisym top_greatest)

lemma free_INF[simp]: "(INF x\<in>X. A) = Cla[X={}] + A"
  apply (cases "X={}") by auto

lemma eigenspace_Cla[simp]: "eigenspace b 0 = Cla[b=0]"
proof (cases "b=0")
  case True
  then show ?thesis 
    by (auto simp: eigenspace_def)
next
  case False
  have "eigenspace b 0 = kernel ((-b) *\<^sub>C id_cblinfun)"
    by (auto simp: eigenspace_def)
  also have "\<dots> = kernel id_cblinfun"
    using False apply (subst kernel_scaleC) by auto
  also have "\<dots> = 0"
    by simp
  also have "\<dots> = Cla[b=0]"
    using False by simp
  finally show ?thesis 
      by assumption
qed

lemma apply_qregister_fst: \<open>apply_qregister qFst a = a \<otimes>\<^sub>o id_cblinfun\<close>
  by (simp add: Laws_Quantum.Fst_def qFst.rep_eq)

lemma apply_qregister_snd: \<open>apply_qregister qSnd a = id_cblinfun \<otimes>\<^sub>o a\<close>
  by (simp add: Laws_Quantum.Snd_def qSnd.rep_eq)

lemma apply_qregister_qswap: \<open>apply_qregister qswap (a \<otimes>\<^sub>o b) = b \<otimes>\<^sub>o a\<close>
  by (simp add: qswap_def apply_qregister_pair apply_qregister_fst apply_qregister_snd
      comp_tensor_op)

lemma transform_qregister_swap_ell2: \<open>transform_qregister swap_ell2 = qswap\<close>
  apply (rule qregister_eqI_tensor_op)
  by (auto simp: apply_qregister_transform_qregister apply_qregister_qswap
      swap_tensor_op sandwich_apply)

definition index_flip_vector :: "qu2 ell2 \<Rightarrow> qu2 ell2" where \<open>index_flip_vector \<psi> = swap_ell2 *\<^sub>V \<psi>\<close>

definition swap_variables_vector :: "'a q2variable \<Rightarrow> 'a q2variable \<Rightarrow> qu2 ell2 \<Rightarrow> qu2 ell2" where
  \<open>swap_variables_vector Q R \<psi> = (apply_qregister \<lbrakk>Q,R\<rbrakk>\<^sub>q swap_ell2) *\<^sub>V \<psi>\<close>

definition index_flip_subspace :: "qu2 ell2 ccsubspace \<Rightarrow> qu2 ell2 ccsubspace"
  where \<open>index_flip_subspace S = swap_ell2 *\<^sub>S S\<close>

lemma index_flip_subspace_top[simp]: "index_flip_subspace top = top"
  by (simp add: index_flip_subspace_def)
lemma index_flip_subspace_bot[simp]: "index_flip_subspace bot = bot"
  by (simp add: index_flip_subspace_def)

lemma index_flip_subspace_INF[simp]: \<open>index_flip_subspace (INF i\<in>A. S i) = (INF i\<in>A. index_flip_subspace (S i))\<close>
  apply (cases \<open>A = {}\<close>)
   apply simp
  by (simp add: index_flip_subspace_def)

definition swap_variables_subspace :: "'a q2variable \<Rightarrow> 'a q2variable \<Rightarrow> qu2 ell2 ccsubspace \<Rightarrow> qu2 ell2 ccsubspace" where
  \<open>swap_variables_subspace Q R S = (apply_qregister \<lbrakk>Q,R\<rbrakk>\<^sub>q swap_ell2) *\<^sub>S S\<close>

lemma index_flip_subspace_zero[simp]: "index_flip_subspace 0 = 0"
  by simp
lemma index_flip_subspace_Cla[simp]: "index_flip_subspace (Cla[b]) = Cla[b]"
  by auto
lemma index_flip_subspace_inf[simp]: "index_flip_subspace (A\<sqinter>B) = (index_flip_subspace A) \<sqinter> (index_flip_subspace B)"
  by (simp add: index_flip_subspace_def)
lemma index_flip_subspace_plus[simp]: "index_flip_subspace (A+B) = (index_flip_subspace A) + (index_flip_subspace B)"
  by (simp add: index_flip_subspace_def)

(* TODO move to Prog_Variables *)
lemma qregister_unitary: \<open>qregister F \<Longrightarrow> unitary U \<Longrightarrow> unitary (apply_qregister F U)\<close>
  apply (transfer fixing: U) by (rule register_unitary)

lemma swap_variables_subspace_top[simp]: "qcompatible v w \<Longrightarrow> swap_variables_subspace v w top = top"
  by (simp add: swap_variables_subspace_def unitary_range qregister_unitary)
lemma swap_variables_subspace_bot[simp]: "swap_variables_subspace v w bot = bot"
  by (simp add: swap_variables_subspace_def)
lemma swap_variables_subspace_zero[simp]: "swap_variables_subspace v w 0 = 0"
  by simp
lemma swap_variables_subspace_Cla[simp]: "qcompatible v w \<Longrightarrow> swap_variables_subspace v w (Cla[b]) = Cla[b]"
  by auto
lemma swap_variables_subspace_inf[simp]: "swap_variables_subspace v w (A\<sqinter>B) = (swap_variables_subspace v w A) \<sqinter> (swap_variables_subspace v w B)"
  apply (cases \<open>qregister \<lbrakk>v, w\<rbrakk>\<^sub>q\<close>)
  by (simp_all add: swap_variables_subspace_def isometry_cblinfun_image_inf_distrib 
      unitary_isometry qregister_unitary non_qregister)
lemma swap_variables_subspace_plus[simp]: "swap_variables_subspace v w (A+B) = (swap_variables_subspace v w A) + (swap_variables_subspace v w B)"
  by (simp add: swap_variables_subspace_def)

subsection "Distinct quantum variables"

abbreviation (input) qvariables_local :: \<open>'a q2variable \<Rightarrow> 'b q2variable \<Rightarrow> bool\<close> where
  \<open>qvariables_local Q R \<equiv> qregister_le Q R\<close>

text \<open>The following constant \<open>DISTINCT_QVARS_GUARD\<close> is a marker that indicates that the simplifier
  should not attempt to solve the subgoal \<open>C\<close> (which is supposed to be of the form \<open>colocal_...\<close>)
  unless a quick check whether it can be solved succeeds. (The quick check simply checks whether
  no variable occurs in both arguments of the \<open>distinct_qvars_...\<close>.) This is to avoid spending potentially
  a lot of time on repeated failed colocality-proofs.

  To avoid this check (i.e., attempt simplification always), simply add \<open>DISTINCT_QVARS_GUARD_def\<close> to the simplifier.

  See also the simproc \<open>distinct_qvars_guard_simproc\<close> below.
  \<close>
definition [code del]: \<open>DISTINCT_QVARS_GUARD (C::bool) = C\<close>
lemma DISTINCT_QVARS_GUARD_cong[cong]: \<open>DISTINCT_QVARS_GUARD x = DISTINCT_QVARS_GUARD x\<close>
  by simp

definition operator_local :: "'b qupdate \<Rightarrow> ('a,'b) qregister \<Rightarrow> bool" where
  \<open>operator_local A F \<longleftrightarrow> A \<in> range (apply_qregister F)\<close>

definition predicate_local :: "'b subspace \<Rightarrow> ('a,'b) qregister \<Rightarrow> bool" where
  \<open>predicate_local S F \<longleftrightarrow> S \<in> range (apply_qregister_space F)\<close>

definition distinct_qvars_op_vars :: "('b,'b) l2bounded \<Rightarrow> ('a,'b) qregister \<Rightarrow> bool" where
  \<open>distinct_qvars_op_vars A F \<longleftrightarrow> A \<in> commutant (range (apply_qregister F))\<close>

definition distinct_qvars_pred_vars :: "'b ell2 ccsubspace \<Rightarrow> ('a,'b) qregister \<Rightarrow> bool" where
  \<open>distinct_qvars_pred_vars S F \<longleftrightarrow> distinct_qvars_op_vars (Proj S) F\<close>

definition distinct_qvars_op_pred :: "(qu2,qu2) l2bounded \<Rightarrow> predicate \<Rightarrow> bool" where
  \<open>distinct_qvars_op_pred A S \<longleftrightarrow> A o\<^sub>C\<^sub>L Proj S = Proj S o\<^sub>C\<^sub>L A\<close>

abbreviation (input) \<open>colocal_op_pred == distinct_qvars_op_pred\<close> (* Legacy *)
abbreviation (input) \<open>colocal_op_qvars == distinct_qvars_op_vars\<close> (* Legacy *)
abbreviation (input) \<open>colocal_pred_qvars == distinct_qvars_pred_vars\<close> (* Legacy *)

consts colocal :: "'a \<Rightarrow> 'b \<Rightarrow> bool" (* Legacy *)
adhoc_overloading colocal \<open>\<lambda>x y. distinct_qvars_pred_vars x y\<close> \<open>\<lambda>x y. distinct_qvars_op_vars x y\<close> \<open>\<lambda>x y. distinct_qvars_op_pred x y\<close>
(* Having non-eta reduced terms in the adhoc_overloading effectively makes the overloading input-only,
   as appropropriate for a legacy name *)

(* TODO move to Prog_Var *)
lemma apply_qregister_empty_qregister[simp]: \<open>apply_qregister empty_qregister A = one_dim_iso A *\<^sub>C id_cblinfun\<close>
  by (simp add: empty_qregister.rep_eq empty_var_def)

lemma distinct_qvars_op_vars_unit'[simp]: "distinct_qvars_op_vars A empty_qregister"
  by (simp add: distinct_qvars_op_vars_def commutant_def)

lemma distinct_qvars_pred_vars_unit'[simp]: "distinct_qvars_pred_vars A empty_qregister"
  by (simp add: distinct_qvars_pred_vars_def)

lemma distinct_qvars_op_vars_0[simp,intro]:
  shows \<open>distinct_qvars_op_vars 0 F\<close>
  by (simp add: distinct_qvars_op_vars_def commutant_def)

lemma distinct_qvars_op_vars_id[simp,intro]:
  shows \<open>distinct_qvars_op_vars id_cblinfun F\<close>
  by (simp add: distinct_qvars_op_vars_def commutant_def)

lemma distinct_qvars_pred_vars_top[simp,intro]:
  shows \<open>colocal_pred_qvars \<top> F\<close>
  by (simp add: distinct_qvars_pred_vars_def)

lemma distinct_qvars_pred_vars_bot[simp,intro]:
  shows \<open>distinct_qvars_pred_vars \<bottom> F\<close>
  by (simp add: distinct_qvars_pred_vars_def)

  (* TODO move to Prog_Variables *)
  (* TODO same for cregister *)
lemma qregister_raw_apply_qregister[simp]: \<open>qregister_raw (apply_qregister X) \<longleftrightarrow> qregister X\<close>
  apply transfer by simp

  
  (* TODO move to Prog_Variables *)
lemma apply_qregister_scaleC: \<open>apply_qregister X (c *\<^sub>C a) = c *\<^sub>C apply_qregister X a\<close>
  using clinear_apply_qregister[of X]
  by (rule clinear.scaleC)

lemma distinct_qvars_op_vars_non_qregister[simp]: \<open>distinct_qvars_op_vars A non_qregister\<close>
  by (simp add: distinct_qvars_op_vars_def commutant_def)

lemma distinct_qvars_pred_vars_non_qregister[simp]: \<open>distinct_qvars_pred_vars S non_qregister\<close>
  by (simp add: distinct_qvars_pred_vars_def)

lemma distinct_qvars_op_vars_pair[simp,intro]:
  assumes \<open>distinct_qvars_op_vars A F\<close>
  assumes \<open>distinct_qvars_op_vars A G\<close>
  shows \<open>distinct_qvars_op_vars A (qregister_pair F G)\<close>
proof (cases \<open>qregister \<lbrakk>F,G\<rbrakk>\<^sub>q\<close>)
  case True
  note [register] = this
  have \<open>clinear (\<lambda>B. A o\<^sub>C\<^sub>L apply_qregister \<lbrakk>F, G\<rbrakk>\<^sub>q B)\<close>
    apply (rule clinearI)
    by (auto simp: apply_qregister_plus cblinfun_compose_add_right apply_qregister_scaleC)
  moreover have \<open>clinear (\<lambda>B. apply_qregister \<lbrakk>F, G\<rbrakk>\<^sub>q B o\<^sub>C\<^sub>L A)\<close>
    apply (rule clinearI)
    by (auto simp: apply_qregister_plus cblinfun_compose_add_left apply_qregister_scaleC)
  moreover have \<open>continuous_map weak_star_topology weak_star_topology (\<lambda>B. A o\<^sub>C\<^sub>L apply_qregister \<lbrakk>F, G\<rbrakk>\<^sub>q B)\<close>
    using weak_star_cont_register continuous_map_left_comp_weak_star    
    apply (rule continuous_map_compose[unfolded o_def])
    by simp
  moreover have \<open>continuous_map weak_star_topology weak_star_topology (\<lambda>B. apply_qregister \<lbrakk>F, G\<rbrakk>\<^sub>q B o\<^sub>C\<^sub>L A)\<close>
    using weak_star_cont_register continuous_map_right_comp_weak_star    
    apply (rule continuous_map_compose[unfolded o_def])
    by simp
  ultimately have \<open>(\<lambda>B. A o\<^sub>C\<^sub>L apply_qregister \<lbrakk>F, G\<rbrakk>\<^sub>q B) = (\<lambda>B. apply_qregister \<lbrakk>F, G\<rbrakk>\<^sub>q B o\<^sub>C\<^sub>L A)\<close> for B
    apply (rule weak_star_clinear_eq_butterfly_ketI)
    using assms
     apply (auto simp add: apply_qregister_pair distinct_qvars_op_vars_def commutant_def 
        simp flip: tensor_ell2_ket tensor_butterfly)
      by (metis (no_types, lifting) Laws_Quantum.compatible_ac_rules(2))
  then show ?thesis
    apply (simp add: distinct_qvars_op_vars_def commutant_def)
    by metis
next
  case False
  then have [simp]: \<open>\<lbrakk>F,G\<rbrakk> = non_qregister\<close>
  using non_qregister by blast
  then show ?thesis
    by simp
qed

lemma distinct_qvars_pred_vars_pair[simp,intro]:
  assumes \<open>distinct_qvars_pred_vars S F\<close>
  assumes \<open>distinct_qvars_pred_vars S G\<close>
  shows \<open>distinct_qvars_pred_vars S (qregister_pair F G)\<close>
  using assms by (simp add: distinct_qvars_pred_vars_def distinct_qvars_op_vars_pair)

lemma colocal_op_qvars_apply_qregister[simp]:
  assumes \<open>qcompatible F G\<close>
  shows \<open>colocal_op_qvars (apply_qregister F S) G\<close>
  using assms
  by (simp add: distinct_qvars_op_vars_def commutant_def qcompatible_commute)

lemma distinct_qvars_pred_vars_apply_qregister_space[simp]:
  assumes [register]: \<open>qregister \<lbrakk>F,G\<rbrakk>\<close>
  shows \<open>distinct_qvars_pred_vars (apply_qregister_space F S) G\<close>
  by (simp add: distinct_qvars_pred_vars_def apply_qregister_space_def Proj_on_own_range)

lemma distinct_qvars_pred_vars_cla[simp]: \<open>qregister X \<Longrightarrow> distinct_qvars_pred_vars Cla[x] X\<close>
  by simp

lemma operator_local_Proj: \<open>operator_local (Proj S) F \<longleftrightarrow> predicate_local S F\<close>
proof (cases \<open>qregister F\<close>)
  case True
  note [register] = this
  have \<open>Proj (apply_qregister F (Proj T) *\<^sub>S \<top>) \<in> range (\<lambda>T. apply_qregister F T)\<close> for T
  proof -
    have \<open>Proj (apply_qregister F (Proj T) *\<^sub>S \<top>) = apply_qregister F (Proj T)\<close>
      apply (rule Proj_on_own_range)
      by simp
    also have \<open>\<dots> \<in> range (\<lambda>T. apply_qregister F T)\<close>
      by simp
    finally show ?thesis
      by -
  qed
  moreover have \<open>S \<in> range (\<lambda>x. apply_qregister F (Proj x) *\<^sub>S \<top>)\<close> 
    if \<open>Proj S = apply_qregister F A\<close> for A
  proof -
    from that have \<open>is_Proj A\<close>
      by (metis Proj_is_Proj True apply_qregister_is_Proj)
    have \<open>S = Proj S *\<^sub>S \<top>\<close>
      by simp
    also from that have \<open>\<dots> = apply_qregister F A *\<^sub>S \<top>\<close>
      by simp
    also from \<open>is_Proj A\<close> have \<open>\<dots> = apply_qregister F (Proj (A *\<^sub>S \<top>)) *\<^sub>S \<top>\<close>
      by (simp add: Proj_on_own_range)
    also have \<open>\<dots> \<in> range (\<lambda>x. apply_qregister F (Proj x) *\<^sub>S \<top>)\<close>
      by simp
    ultimately show ?thesis
      by (auto simp add: predicate_local_def operator_local_def apply_qregister_space_def)
  qed
  ultimately show ?thesis
    by (auto simp: predicate_local_def operator_local_def apply_qregister_space_def)
next
  case False
  then have [simp]: \<open>F = non_qregister\<close>
    by (simp add: non_qregister)
  then show ?thesis
    by (auto simp add: predicate_local_def operator_local_def Proj_inj)
qed


lemma operator_local_timesOp[intro!]: "operator_local A Q \<Longrightarrow> operator_local B Q \<Longrightarrow> operator_local (A o\<^sub>C\<^sub>L B) Q"
  apply (simp add: operator_local_def)
  by (smt (verit) image_iff qregister_compose rangeI)
lemma predicate_local_applyOpSpace[intro!]: 
  assumes \<open>operator_local A Q\<close> and \<open>predicate_local S Q\<close>
  shows \<open>predicate_local (A *\<^sub>S S) Q\<close>
proof -
  from assms(1)
  obtain A' where A_def: \<open>A = apply_qregister Q A'\<close>
    by (meson image_iff operator_local_def)
  from assms(2)
  obtain S' where S_def: \<open>S = apply_qregister_space Q S'\<close>
    by (meson image_iff predicate_local_def)
  show \<open>predicate_local (A *\<^sub>S S) Q\<close>
    by (simp add: A_def S_def predicate_local_def flip:  apply_qregister_space_image)
qed

subsection \<open>Lifting\<close>

abbreviation (input) \<open>liftOp == (\<lambda>A F. apply_qregister F A)\<close> (* LEGACY *)
abbreviation (input) \<open>liftSpace == (\<lambda>A F. apply_qregister_space F A)\<close> (* LEGACY *)

abbreviation variable_in (infix "\<in>\<^sub>\<qq>" 80) where "variable_in R S \<equiv> liftSpace S R" 
notation (input) variable_in (infix "\<in>\<^sub>q" 80)
abbreviation variable_is (infix "=\<^sub>\<qq>" 80) where "variable_is R \<psi> \<equiv> R \<in>\<^sub>q ccspan {\<psi>}" 
notation (input) variable_is (infix "=\<^sub>q" 80)

consts lift :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixl "\<guillemotright>" 90)
syntax lift :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixl ">>" 90)
adhoc_overloading
  lift liftOp \<open>(\<lambda>x. liftSpace x)\<close>

lemma predicate_localE:
  assumes "predicate_local S Q"
  shows "\<exists>S'. S=S'\<guillemotright>Q"
  using assms predicate_local_def by fastforce

lemma operator_localE:
  assumes "operator_local A Q"
  shows "\<exists>A'. A=A'\<guillemotright>Q"
  using assms operator_local_def by fastforce

lemma lift_predicate_local[intro!]: "qvariables_local R Q \<Longrightarrow> predicate_local (S\<guillemotright>R) Q"
  by (simp add: apply_qregister_space_conversion predicate_local_def)
lemma lift_operator_local[intro!]: "qvariables_local R Q \<Longrightarrow> operator_local (S\<guillemotright>R) Q"
  using operator_local_def qregister_apply_conversion by blast

lemma adjoint_lift[simp]: "adj (liftOp U Q) = liftOp (adj U) Q" 
  by (simp add: apply_qregister_adj)
lemma scaleC_lift[simp]: "c *\<^sub>C (A\<guillemotright>Q) = (c *\<^sub>C A) \<guillemotright> Q" for A :: "(_,_) bounded"
   by (simp add: apply_qregister_scaleC)
lemma norm_lift[simp]:
  "distinct_qvars Q \<Longrightarrow> norm (X\<guillemotright>Q) = norm X"
  by (simp add: register_norm)
(* TODO remove [simp]? *)
lemma imageOp_lift[simp]: "applyOpSpace (liftOp U Q) top = liftSpace (applyOpSpace U top) Q"
  apply (cases \<open>qregister Q\<close>)
  apply (metis Proj_top apply_qregister_space_image apply_qregister_of_id apply_qregister_space_def cblinfun_image_id)
  by (simp add: apply_qregister_space_def non_qregister non_qregister.rep_eq non_qregister_raw_def) 
lemma applyOpSpace_lift[simp]: "applyOpSpace (liftOp U Q) (liftSpace S Q) = liftSpace (applyOpSpace U S) Q"
   by (simp flip: apply_qregister_space_image)
lemma top_lift[simp]: "distinct_qvars Q \<Longrightarrow> liftSpace top Q = top"
  by (simp add: apply_qregister_space_def)
lemma bot_lift[simp]: "liftSpace bot Q = bot"
  apply (cases \<open>qregister Q\<close>)
  by (simp_all add: apply_qregister_space_def)
lemma unitary_lift[simp]: "distinct_qvars Q \<Longrightarrow> unitary (liftOp U Q) = unitary U"
  unfolding unitary_def
  apply (auto simp add: simp flip: qregister_compose)
  by (metis apply_qregister_inject' apply_qregister_of_id)+
lemma tensor_lift: 
  fixes A B :: "_ subspace"
  assumes "distinct_qvars (qregister_pair Q R)"
  shows "(A\<otimes>B)\<guillemotright>(qregister_pair Q R) = (A\<guillemotright>Q) \<sqinter> (B\<guillemotright>R)"
  using assms 
  by (simp_all add: Proj_on_own_range adj_Proj comp_tensor_op is_Proj_algebraic 
      tensor_op_adjoint assms apply_qregister_pair qcompatible_def tensor_ccsubspace_via_Proj
      compatible_proj_intersect[of \<open>apply_qregister Q\<close> \<open>apply_qregister R\<close>] apply_qregister_space_def
      flip: imageOp_lift)

lemma lift_eqSp[simp]: "distinct_qvars Q \<Longrightarrow> (S\<guillemotright>Q = T\<guillemotright>Q) = (S = T)" for S T :: "'a subspace" 
  by (metis Proj_inj Proj_is_Proj Proj_on_own_range apply_qregister_inject' apply_qregister_space_def apply_qregister_is_Proj')
lemma lift_eqOp[simp]: "distinct_qvars Q \<Longrightarrow> (S\<guillemotright>Q = T\<guillemotright>Q) = (S = T)" for S T :: "('a,'a) l2bounded" 
  by (rule apply_qregister_inject')
lemma lift_plusOp[simp]: "S\<guillemotright>Q + T\<guillemotright>Q = (S + T)\<guillemotright>Q" for S T :: "('a,'a) l2bounded"  
  by (simp add: apply_qregister_plus)
lemma lift_uminusOp[simp]: "- (T\<guillemotright>Q) = (- T)\<guillemotright>Q" for T :: "('a,'a) l2bounded"
  apply (subst scaleC_minus1_left[symmetric])
  apply (subst (2) scaleC_minus1_left[symmetric])
  by simp
lemma lift_minusOp[simp]: "S\<guillemotright>Q - T\<guillemotright>Q = (S - T)\<guillemotright>Q" for S T :: "('a,'a) l2bounded"  
  by (simp add: ordered_field_class.sign_simps(9))
lemma lift_timesOp[simp]: "S\<guillemotright>Q o\<^sub>C\<^sub>L T\<guillemotright>Q = (S o\<^sub>C\<^sub>L T)\<guillemotright>Q" for S T :: "('a,'a) l2bounded"  
   by (simp add: qregister_compose)
lemma lift_ortho[simp]: "distinct_qvars Q \<Longrightarrow> - (S\<guillemotright>Q) = (- S)\<guillemotright>Q" for S :: "'a ell2 ccsubspace"
  apply (simp add: apply_qregister_space_def Proj_ortho_compl
      flip: imageOp_lift)
  by (metis (no_types, lifting) Proj_is_Proj Proj_on_own_range apply_qregister_of_id apply_qregister_is_Proj' lift_minusOp range_cblinfun_code_def uminus_Span_code)
lemma lift_tensorOp: "distinct_qvars (qregister_pair Q R) \<Longrightarrow> (S\<guillemotright>Q) o\<^sub>C\<^sub>L (T\<guillemotright>R) = (S \<otimes>\<^sub>o T)\<guillemotright>qregister_pair Q R" for Q :: "'a q2variable" and R :: "'b q2variable" and S T :: "(_,_) l2bounded"
  by (simp add: apply_qregister_pair)
lemma lift_tensorSpace: "distinct_qvars (qregister_pair Q R) \<Longrightarrow> (S\<guillemotright>Q) = (S \<otimes> top)\<guillemotright>qregister_pair Q R" for Q :: "'a q2variable" and R :: "'b q2variable" and S :: "_ subspace" 
  by (metis distinct_qvarsR inf_top.right_neutral tensor_lift top_lift)
lemma lift_id_cblinfun[simp]: "distinct_qvars Q \<Longrightarrow> id_cblinfun\<guillemotright>Q = id_cblinfun" for Q
  by simp

lemmas INF_lift = apply_qregister_space_INF[symmetric]

lemma Cla_inf_lift: "Cla[b] \<sqinter> (S\<guillemotright>Q) = (if b then S else bot)\<guillemotright>Q" by auto
lemma Cla_plus_lift: "distinct_qvars Q \<Longrightarrow> Cla[b] + (S\<guillemotright>Q) = (if b then top else S)\<guillemotright>Q" by auto
lemma Cla_sup_lift: "distinct_qvars Q \<Longrightarrow> Cla[b] \<squnion> (S\<guillemotright>Q) = (if b then top else S)\<guillemotright>Q" by auto
lemma Proj_lift[simp]: "Proj (S\<guillemotright>Q) = (Proj S)\<guillemotright>Q"
  for Q::"'a q2variable"
   by (metis Proj_is_Proj Proj_on_own_range Proj_range imageOp_lift apply_qregister_is_Proj')
lemma kernel_lift[simp]: "distinct_qvars Q \<Longrightarrow> kernel (A\<guillemotright>Q) = (kernel A)\<guillemotright>Q" for Q
  by (simp add: apply_qregister_space_kernel)
lemma eigenspace_lift[simp]: "distinct_qvars Q \<Longrightarrow> eigenspace a (A\<guillemotright>Q) = (eigenspace a A)\<guillemotright>Q" for Q
  unfolding eigenspace_def apply (subst lift_id_cblinfun[symmetric, of Q], assumption)
  apply (simp del: lift_id_cblinfun)
  by (metis (no_types, lifting) apply_qregister_of_id kernel_lift lift_minusOp scaleC_lift)

lemma lift_plus[simp]: "S\<guillemotright>Q + T\<guillemotright>Q = (S + T)\<guillemotright>Q" for S T :: "'a subspace"
  by (metis apply_qregister_space_plus)
lemma lift_sup[simp]: "S\<guillemotright>Q \<squnion> T\<guillemotright>Q = (S \<squnion> T)\<guillemotright>Q" for S T :: "'a subspace"  
  using lift_plus by auto
lemma lift_inf[simp]: "apply_qregister_space Q S \<sqinter> apply_qregister_space Q T = apply_qregister_space Q (S \<sqinter> T)" for S::"'a subspace"
  by (simp add: apply_qregister_space_inf)

lemma predicate_local_inf[intro!]: "predicate_local S Q \<Longrightarrow> predicate_local T Q \<Longrightarrow> predicate_local (S\<sqinter>T) Q"
  by (auto simp add: predicate_local_def)

(* TODO move to Prog_Var *)
(* TODO write lemma (proof in quicksheets 2023 p32)
lemma qregister_invertible_op:
assumes \<open>qregister F\<close>
shows \<open>F X invertible \<longleftrightarrow> X invertible\<close> *)

lemma lift_leq[simp]: "distinct_qvars Q \<Longrightarrow> (S\<guillemotright>Q \<le> T\<guillemotright>Q) = (S \<le> T)" for S::"'a subspace"
  by (rule apply_qregister_space_mono)

lemma top_leq_lift: "distinct_qvars Q \<Longrightarrow> top \<le> S\<guillemotright>Q \<longleftrightarrow> top \<le> S"
  apply (subst top_lift[symmetric], assumption) apply (subst lift_leq, assumption) by simp
lemma top_geq_lift: "distinct_qvars Q \<Longrightarrow> top \<ge> S\<guillemotright>Q \<longleftrightarrow> top \<ge> S" 
  apply (subst top_lift[symmetric], assumption) apply (subst lift_leq, assumption) by simp
lemma bot_leq_lift: "distinct_qvars Q \<Longrightarrow> bot \<le> S\<guillemotright>Q \<longleftrightarrow> bot \<le> S" 
  apply (subst bot_lift[symmetric]) apply (subst lift_leq, assumption) by simp
lemma bot_geq_lift: "distinct_qvars Q \<Longrightarrow> bot \<ge> S\<guillemotright>Q \<longleftrightarrow> bot \<ge> S" 
  apply (subst bot_lift[symmetric]) apply (subst lift_leq, assumption) by simp
lemma top_eq_lift: "distinct_qvars Q \<Longrightarrow> top = S\<guillemotright>Q \<longleftrightarrow> top = S" 
  apply (subst top_lift[symmetric], assumption) apply (subst lift_eqSp, assumption) by simp
lemma bot_eq_lift: "distinct_qvars Q \<Longrightarrow> bot = S\<guillemotright>Q \<longleftrightarrow> bot = S" 
  apply (subst bot_lift[symmetric]) apply (subst lift_eqSp, assumption) by simp
lemma top_eq_lift2: "distinct_qvars Q \<Longrightarrow> S\<guillemotright>Q = top \<longleftrightarrow> S = top" 
  apply (subst top_lift[symmetric], assumption) apply (subst lift_eqSp, assumption) by simp
lemma bot_eq_lift2: "distinct_qvars Q \<Longrightarrow> S\<guillemotright>Q = bot \<longleftrightarrow> S = bot" 
  apply (subst bot_lift[symmetric]) apply (subst lift_eqSp, assumption) by simp


lemma colocal_op_commute:
  assumes "colocal_op_qvars A Q"
  shows "A o\<^sub>C\<^sub>L B\<guillemotright>Q = B\<guillemotright>Q o\<^sub>C\<^sub>L A"
  using assms by (simp add: distinct_qvars_op_vars_def commutant_def)

(* lemma remove_qvar_unit_op:
  "(remove_qvar_unit_op \<cdot> A \<cdot> remove_qvar_unit_op* )\<guillemotright>Q = A\<guillemotright>(qregister_pair Q \<lbrakk>\<rbrakk>)"
for A::"(_,_)l2bounded" and Q::"'a q2variable"
 *)


lemma colocal_op_pred_lift1[simp,intro!]:
 "colocal_pred_qvars S Q \<Longrightarrow> colocal_op_pred (U\<guillemotright>Q) S"
for Q :: "'a q2variable" and U :: "('a,'a) l2bounded" and S :: predicate
   by (simp add: colocal_op_commute distinct_qvars_op_pred_def distinct_qvars_pred_vars_def)


lemma lift_extendR:
  assumes "distinct_qvars \<lbrakk>Q,R\<rbrakk>"
  shows "U\<guillemotright>Q = (U \<otimes>\<^sub>o id_cblinfun)\<guillemotright>\<lbrakk>Q,R\<rbrakk>"
  apply (subst apply_qregister_pair)
  apply (simp add: assms)
  using assms distinct_qvarsR by force

lemma lift_extendL:
  assumes "distinct_qvars (qregister_pair Q R)"
  shows "U\<guillemotright>Q = (id_cblinfun \<otimes>\<^sub>o U)\<guillemotright>(qregister_pair R Q)"
  apply (subst apply_qregister_pair)
   apply (simp add: assms distinct_qvars_swap)
  using assms distinct_qvarsR by fastforce

lemma move_sup_meas_rule:
  fixes Q::"'a q2variable"
  assumes "distinct_qvars Q"
  assumes "(Proj C)\<guillemotright>Q \<cdot> A \<le> B"
  shows "A \<le> (B\<sqinter>C\<guillemotright>Q) \<squnion> (- C)\<guillemotright>Q"
  apply (rule ccsubspace_supI_via_Proj) 
  using Proj_image_leq[of "C\<guillemotright>Q"] assms by simp

(* lemma span_lift: "distinct_qvars Q \<Longrightarrow> ccspan G \<guillemotright> Q = ccspan {lift_vector \<psi> Q \<psi>' | \<psi> \<psi>'. \<psi>\<in>G \<and> \<psi>' \<in> lift_rest Q}"
   *)

(* TODO move *)
lemma apply_qregister_space_transform_qregister:
  assumes [simp]: \<open>unitary U\<close>
  shows \<open>apply_qregister_space (transform_qregister U) S = U *\<^sub>S S\<close>
  by (simp add: apply_qregister_transform_qregister apply_qregister_space_def Proj_sandwich)

lemma index_flip_subspace_lift[simp]: "index_flip_subspace (S\<guillemotright>Q) = S \<guillemotright> index_flip_qvar Q"
  apply (cases \<open>qregister Q\<close>)
  by (simp_all add: index_flip_subspace_def index_flip_qvar_def apply_qregister_space_transform_qregister
      flip: transform_qregister_swap_ell2)

(* lemma swap_variables_subspace_lift[simp]: "swap_variables_subspace v w (S\<guillemotright>Q) = S \<guillemotright> swap_variables_vars v w Q" *)

lemma apply_qregister_qFst: \<open>apply_qregister qFst a = a \<otimes>\<^sub>o id_cblinfun\<close>
  by (simp add: Laws_Quantum.Fst_def qFst.rep_eq)

lemma apply_qregister_qSnd: \<open>apply_qregister qSnd b = id_cblinfun \<otimes>\<^sub>o b\<close>
  by (simp add: Laws_Quantum.Snd_def qSnd.rep_eq)

(* TODO move *)
lemma apply_qregister_space_qFst: \<open>apply_qregister_space qFst S = S \<otimes>\<^sub>S \<top>\<close>
  by (simp add: apply_qregister_space_def tensor_ccsubspace_via_Proj apply_qregister_qFst flip: imageOp_lift)

(* TODO move to Prog_Vars *)
lemma apply_qregister_space_qSnd: \<open>apply_qregister_space qSnd S = \<top> \<otimes>\<^sub>S S\<close>
  by (simp add: apply_qregister_space_def tensor_ccsubspace_via_Proj apply_qregister_qSnd flip: imageOp_lift)


lemma ket_less_specific:
  assumes "qregister \<lbrakk>X,Y\<rbrakk>"
  shows "ccspan {ket (x,y)}\<guillemotright>qregister_pair X Y \<le> ccspan {ket y}\<guillemotright>Y"
proof -
  have \<open>apply_qregister_space \<lbrakk>X, Y\<rbrakk>\<^sub>q (ccspan {|(x, y)\<rangle>}) = apply_qregister_space \<lbrakk>X, Y\<rbrakk>\<^sub>q (ccspan {|x\<rangle>} \<otimes>\<^sub>S ccspan {|y\<rangle>})\<close>
    by (simp add: tensor_ccsubspace_ccspan tensor_ell2_ket)
  also have \<open>\<dots> \<le> apply_qregister_space \<lbrakk>X, Y\<rbrakk>\<^sub>q (\<top> \<otimes>\<^sub>S ccspan {|y\<rangle>})\<close>
    by (smt (verit) assms distinct_qvarsL dual_order.trans inf.bounded_iff inf.cobounded2 tensor_lift top_greatest top_leq_lift)
  also have \<open>\<dots> = ccspan {|y\<rangle>} \<guillemotright> (qregister_chain \<lbrakk>X, Y\<rbrakk>\<^sub>q qSnd)\<close>
    by (metis assms distinct_qvarsL inf.absorb_iff2 qregister_chain_pair_Snd tensor_lift top.extremum top_lift)
  also have \<open>\<dots> = ccspan {ket y}\<guillemotright>Y\<close>
    by (metis assms qregister_chain_pair_Snd)
  finally show ?thesis
    by -
qed


lemma comm_op_twice[simp]: "distinct_qvars Q \<Longrightarrow> comm_op\<guillemotright>Q \<cdot> (comm_op\<guillemotright>Q \<cdot> S) = (S::_ ccsubspace)"
  apply (subst adjoint_swap_ell2[symmetric])
  by (simp del: adjoint_swap_ell2 flip: adjoint_lift cblinfun_compose_assoc add: cblinfun_assoc_left)

(* TODO use qregister_chain_apply_space instead *)
(* lemma apply_qregister_space_chain: \<open>apply_qregister_space (qregister_chain F G) S = apply_qregister_space F (apply_qregister_space G S)\<close> *)

lemma translate_to_index_registers_classical_subspace[translate_to_index_registers]:
  \<open>TTIR_APPLY_QREGISTER_SPACE (Cla[b]) \<lbrakk>\<rbrakk>\<^sub>q (Cla[b])\<close>
  by (auto simp: TTIR_APPLY_QREGISTER_SPACE_def)

(* TODO move *)
(* TODO: this should be applied in normalize_register_conv *)
(* TODO: keep qregister_chain_pair or this  *)
(* TODO: better name *)
lemma pair_chain_fst_snd:
  shows \<open>\<lbrakk>qregister_chain F A, qregister_chain F B\<rbrakk>\<^sub>q = qregister_chain F \<lbrakk>A, B\<rbrakk>\<^sub>q\<close>
  apply (rule sym)
  by (rule qregister_chain_pair)

(* TODO move *)
lemma apply_qregister_space_id[simp]: \<open>apply_qregister_space qregister_id S = S\<close>
  by (simp add: apply_qregister_space_def)


ML \<open>
fun resolve_inst_tac ctxt inst rules = FIRST' (map (fn rule => let
  val inst_rule = [infer_instantiate ctxt inst rule]
                  handle THM _ => []
  in resolve_tac ctxt inst_rule end
) rules)
\<close>





section \<open>Measurements\<close>

(* TODO: We have the WOT now, can use that one in the def, maybe... *)
(* TODO: Why not rephrase this in terms of is_Proj + projs orthogonal? Much easier. *)
(* definition "is_measurement M \<longleftrightarrow> ((\<forall>i. is_Proj (M i)) 
       \<and> (\<exists>P. (\<forall>\<psi> \<phi>. (\<Sum>\<^sub>\<infinity> i. \<phi> \<bullet>\<^sub>C (M i *\<^sub>V \<psi>)) = \<phi> \<bullet>\<^sub>C (P *\<^sub>V \<psi>)) \<and> P \<le> id_cblinfun))" *)
definition \<open>is_measurement M \<longleftrightarrow> ((\<forall>i. is_Proj (M i)) \<and> (\<forall>i j. i\<noteq>j \<longrightarrow> M i o\<^sub>C\<^sub>L M j = 0))\<close>
lemma is_measurement_0[simp]: "is_measurement (\<lambda>_. 0)"
  unfolding is_measurement_def
  by (auto intro: exI[of _ 0])


typedef ('a,'b) measurement = "{M::'a\<Rightarrow>('b,'b) l2bounded. is_measurement M}"
  morphisms mproj Abs_measurement
  by (rule exI[of _ "\<lambda>i. 0"], simp)
setup_lifting type_definition_measurement

lift_definition mtotal :: "('a,'b) measurement \<Rightarrow> bool" is
  "\<lambda>M. (SUP x. M x *\<^sub>S \<top>) = \<top>".

lemma is_Proj_mproj[simp]: "is_Proj (mproj M i)"
  using mproj[of M] unfolding is_measurement_def by auto

lift_definition computational_basis :: "('a, 'a) measurement" is
  "\<lambda>i. selfbutterket i"
  by (simp add: is_measurement_def butterfly_is_Proj)

lemma mproj_computational_basis[simp]: "mproj computational_basis x = selfbutterket x"
  unfolding computational_basis.rep_eq by simp

lemma mtotal_computational_basis [simp]: "mtotal computational_basis"
  apply transfer
  by (auto simp: butterfly_eq_proj SUP_ccspan UNION_singleton_eq_range)

lift_definition binary_measurement :: "('a,'a) l2bounded \<Rightarrow> (bit,'a) measurement" is
  "\<lambda>(P::('a,'a) l2bounded) (b::bit). (if is_Proj P then (if b=1 then P else id_cblinfun-P) else 0)"
proof (rename_tac P, case_tac "is_Proj P")
  fix P :: "('a ell2, 'a ell2) bounded"
  assume [simp]: "is_Proj P"
  show "is_measurement (\<lambda>b::bit. if is_Proj P then if b = 1 then P else id_cblinfun - P else 0)"
    by (auto simp: is_measurement_def cblinfun_compose_minus_right cblinfun_compose_minus_left
        is_Proj_idempotent)
next
  fix P :: "('a ell2, 'a ell2) bounded"
  assume [simp]: "\<not> is_Proj P"
  show "is_measurement (\<lambda>b. if is_Proj P then if b = 1 then P else id_cblinfun - P else 0)"
    by simp
qed

lemma binary_measurement_true[simp]: "is_Proj P \<Longrightarrow> mproj (binary_measurement P) 1 = P"
  apply transfer by simp

lemma binary_measurement_false[simp]: "is_Proj P \<Longrightarrow> mproj (binary_measurement P) 0 = id_cblinfun-P"
  unfolding binary_measurement.rep_eq by auto

lemma mtotal_binary_measurement[simp]: "mtotal (binary_measurement P) = is_Proj P"
  apply (transfer fixing: P)
  apply (auto simp: UNIV_bit)
  by (metis Proj_on_own_range add.commute complemented_lattice_class.sup_compl_top plus_ccsubspace_def range_cblinfun_code_def uminus_Span_code)

section \<open>Quantum predicates (ctd.)\<close>

subsection \<open>Subspace division\<close>

definition space_div :: "'b ell2 ccsubspace \<Rightarrow> 'a ell2 \<Rightarrow> ('a,'b) qregister \<Rightarrow> 'b ell2 ccsubspace"
                    ("_ \<div> _\<guillemotright>_" [89,89,89] 90) where
  [code del]: \<open>space_div A \<psi> Q = (if \<psi> = 0 then \<top> else SUP a. apply_qregister Q a *\<^sub>S (A \<sqinter> (Q =\<^sub>q \<psi>)))\<close>
  (* \<open>space_div A \<psi> Q = ccspan {apply_qregister Q a \<phi>\<psi> | a \<phi>\<psi>. \<phi>\<psi> \<in> space_as_set (A \<sqinter> (Q =\<^sub>q \<psi>))}\<close> (* Equivalent but less compact *) *)
  (* \<open>space_div A \<psi> Q = (SUP a. apply_qregister Q a *\<^sub>S A)\<close> (* Wrong. "ccspan {EPR} \<div> ket0" should be 0 but isn't *) *)
  (* \<open>space_div A \<psi> Q = Abs_clinear_space {\<phi>| \<phi> a. apply_qregister Q a *\<^sub>V \<phi> \<in> space_as_set A}\<close> (* Not right. E.g., a=0 makes this the whole space *) *)

lemma space_div_non_qregister[simp]: \<open>space_div A \<psi> non_qregister = (if \<psi>=0 then \<top> else \<bottom>)\<close>
  by (simp add: space_div_def)

lemma space_div_zero1[simp]: \<open>space_div 0 \<psi> Q = 0\<close> if \<open>\<psi> \<noteq> 0\<close>
  using that by (simp add: space_div_def)

lemma space_div_zero2[simp]: \<open>space_div S 0 Q = \<top>\<close>
  by (simp add: space_div_def)

lemma space_div_lift:
  assumes [simp]: \<open>qregister FG\<close>
  shows \<open>space_div (apply_qregister_space FG A') \<psi> (qregister_chain FG G')
           = apply_qregister_space FG (space_div A' \<psi> G')\<close>
  apply (cases \<open>\<psi> = 0\<close>)
  by (simp_all add: space_div_def apply_qregister_space_SUP)

lift_definition space_div_unlifted :: "('a*'b) ell2 ccsubspace \<Rightarrow> 'b ell2 \<Rightarrow> 'a ell2 ccsubspace" is
  "\<lambda>S \<psi>. {\<phi>. \<phi> \<otimes>\<^sub>s \<psi> \<in> space_as_set S}"
proof (rename_tac S \<psi>, rule closed_csubspace.intro)
  fix S :: \<open>('a \<times> 'b) ell2 ccsubspace\<close> and \<psi>
  show \<open>csubspace {\<phi>. \<phi> \<otimes>\<^sub>s \<psi> \<in> space_as_set S}\<close>
    apply (rule complex_vector.subspaceI)
    by (auto simp: tensor_ell2_add1 tensor_ell2_scaleC1
        complex_vector.subspace_add complex_vector.subspace_scale)
  show \<open>closed {\<phi>. \<phi> \<otimes>\<^sub>s \<psi> \<in> space_as_set S}\<close>
  proof -
    have \<open>{\<phi>. \<phi> \<otimes>\<^sub>s \<psi> \<in> space_as_set S} = (\<lambda>\<phi>. \<phi> \<otimes>\<^sub>s \<psi>) -` space_as_set S\<close>
      by auto
    moreover have \<open>closed ((\<lambda>\<phi>. \<phi> \<otimes>\<^sub>s \<psi>) -` space_as_set S)\<close>
      apply (rule continuous_closed_vimage)
      by (simp_all add: bounded_cbilinear.isCont[OF bounded_cbilinear_tensor_ell2])
    ultimately show \<open>closed {\<phi>. \<phi> \<otimes>\<^sub>s \<psi> \<in> space_as_set S}\<close>
      by simp
  qed
qed

lemma space_div_unlifted_zero1[simp]: \<open>space_div_unlifted 0 \<psi> = 0\<close> if \<open>\<psi> \<noteq> 0\<close>
  apply (rule space_as_set_inject[THEN iffD1])
  using that tensor_ell2_nonzero by (auto simp add: space_div_unlifted.rep_eq)

lemma space_div_unlifted_zero2[simp]: \<open>space_div_unlifted S 0 = \<top>\<close>
  by (simp add: space_div_unlifted_def top_ccsubspace.abs_eq)


lemma space_div_space_div_unlifted: 
  assumes \<open>qcompatible Q R\<close>
  shows "space_div (S\<guillemotright>\<lbrakk>R,Q\<rbrakk>) \<psi> Q = (space_div_unlifted S \<psi>)\<guillemotright>R"
proof (cases \<open>\<psi> = 0\<close>)
  case True
  have [simp]: \<open>qregister R\<close>
    using assms qcompatible_register2 by blast
  then show ?thesis
    using True by simp
next
  case False
  have [simp]: \<open>qcompatible R Q\<close>
    using assms qcompatible_sym by blast
  have \<open>space_div S \<psi> qSnd = space_div_unlifted S \<psi> \<guillemotright> qFst\<close>
  proof (rule antisym)
    show \<open>S \<div> \<psi>\<guillemotright>qSnd \<le> (space_div_unlifted S \<psi>) \<guillemotright> qFst\<close>
    proof (simp only: space_div_def False if_False, rule SUP_least)
      fix a
      have \<open>S \<sqinter> (qSnd =\<^sub>q \<psi>) \<le> (space_div_unlifted S \<psi>) \<guillemotright> qFst\<close>
      proof (rule ccsubspace_leI_unit)
        fix \<phi> assume \<open>\<phi> \<in> space_as_set (S \<sqinter> (qSnd =\<^sub>q \<psi>))\<close>
        then have \<phi>S: \<open>\<phi> \<in> space_as_set S\<close> and \<open>\<phi> \<in> space_as_set (qSnd =\<^sub>q \<psi>)\<close>
          by simp_all
        then have \<open>\<phi> \<in> space_as_set (\<top> \<otimes>\<^sub>S ccspan {\<psi>})\<close>
          by (simp add: apply_qregister_space_qSnd)
        then obtain \<gamma> where \<phi>_decomp: \<open>\<phi> = \<gamma> \<otimes> \<psi>\<close>
          apply atomize_elim
          apply (rule tensor_ccsubspace_right1dim_member)
          by simp
        then have \<open>\<gamma> \<in> space_as_set (space_div_unlifted S \<psi>)\<close>
          using \<phi>S space_div_unlifted.rep_eq by auto
        then show \<open>\<phi> \<in> space_as_set (space_div_unlifted S \<psi> \<guillemotright> qFst)\<close>
          by (simp add: \<phi>_decomp apply_qregister_space_qFst tensor_ell2_in_tensor_ccsubspace)
      qed
      then have \<open>(a\<guillemotright>qSnd) *\<^sub>S (S \<sqinter> (qSnd =\<^sub>q \<psi>)) \<le> (a\<guillemotright>qSnd) *\<^sub>S (space_div_unlifted S \<psi> \<guillemotright> qFst)\<close>
        by (simp add: cblinfun_image_mono)
      also have \<open>\<dots> \<le> space_div_unlifted S \<psi> \<guillemotright> qFst\<close>
        by (simp add: apply_qregister_space_qFst apply_qregister_qSnd tensor_ccsubspace_mono
            flip: tensor_ccsubspace_image)
      ultimately show \<open>(a\<guillemotright>qSnd) *\<^sub>S (S \<sqinter> (qSnd =\<^sub>q \<psi>)) \<le> space_div_unlifted S \<psi> \<guillemotright> qFst\<close>
        by simp
    qed
    show \<open>(space_div_unlifted S \<psi>) \<guillemotright> qFst \<le> S \<div> \<psi>\<guillemotright>qSnd\<close>
    proof -
      have \<open>\<gamma> \<otimes>\<^sub>s \<phi> \<in> space_as_set (S \<div> \<psi>\<guillemotright>qSnd)\<close>
        if \<open>\<gamma> \<in> space_as_set (space_div_unlifted S \<psi>)\<close> for \<gamma> \<phi>
      proof -
        from that
        have \<open>\<gamma> \<otimes>\<^sub>s \<psi> \<in> space_as_set S\<close>
          by (simp add: space_div_unlifted.rep_eq)
        then have *: \<open>\<gamma> \<otimes>\<^sub>s \<psi> \<in> space_as_set (S \<sqinter> (qSnd =\<^sub>q \<psi>))\<close>
          by (metis IntI UNIV_I apply_qregister_space_qSnd ccspan_superset insert_subset space_as_set_inf space_as_set_top tensor_ell2_in_tensor_ccsubspace)
        define a where \<open>a = butterfly \<phi> \<psi> /\<^sub>R ((norm \<psi>)\<^sup>2)\<close>
        from \<open>\<psi> \<noteq> 0\<close> have \<open>a *\<^sub>V \<psi> = \<phi>\<close>
          by (simp add: a_def scaleR_scaleC power2_norm_eq_cinner)
        then have \<open>\<gamma> \<otimes>\<^sub>s \<phi> = (a\<guillemotright>qSnd) *\<^sub>V (\<gamma> \<otimes>\<^sub>s \<psi>)\<close>
          by (simp add: apply_qregister_qSnd tensor_op_ell2)
        also have \<open>\<dots> \<in> space_as_set ((a\<guillemotright>qSnd) *\<^sub>S (S \<sqinter> (qSnd =\<^sub>q \<psi>)))\<close>
          using "*" cblinfun_apply_in_image' by blast
        also have \<open>\<dots> \<le> space_as_set (S \<div> \<psi>\<guillemotright>qSnd)\<close>
          apply (simp add: space_div_def
              flip: less_eq_ccsubspace.rep_eq)
          by (meson Sup_upper range_eqI)
        finally show ?thesis
          by -
      qed
      then show ?thesis
        by (auto intro!: ccspan_leqI 
          simp add: apply_qregister_space_qFst tensor_ccsubspace_def)
    qed
  qed
  then show \<open>space_div (S\<guillemotright>\<lbrakk>R,Q\<rbrakk>) \<psi> Q = (space_div_unlifted S \<psi>)\<guillemotright>R\<close>
    using space_div_lift[where FG=\<open>\<lbrakk>R,Q\<rbrakk>\<close> and A'=S and \<psi>=\<psi> and G'=qSnd]
    by (metis \<open>qregister \<lbrakk>R, Q\<rbrakk>\<^sub>q\<close> qregister_chain_apply_space qregister_chain_pair_Fst qregister_chain_pair_Snd)
qed

lemma qcomplement_exists:
  fixes F :: \<open>('a,'b) qregister\<close>
  assumes \<open>qregister F\<close>
  shows \<open>\<forall>\<^sub>\<tau> 'c::type = qregister_decomposition_basis F.
          \<exists>G :: ('c,'b) qregister. qcomplements F G\<close>
proof -
  have *: \<open>(\<exists>G :: 'c qupdate \<Rightarrow> 'b qupdate. complements (apply_qregister F) G)
    \<longleftrightarrow> (\<exists>G :: ('c,'b) qregister. qcomplements F G)\<close>
    apply (rule Ex_iffI[where f=Abs_qregister and g=apply_qregister])
    by (auto simp: qcomplements_def complements_def Abs_qregister_inverse
        Abs_qregister_inverse Laws_Quantum.compatible_register2)
  show ?thesis
    apply (subst *[symmetric])
    apply (rule complement_exists)
    using assms by simp
qed

lemma distinct_qvars_op_vars_complement:
  assumes \<open>qcomplements Q R\<close>
  assumes \<open>distinct_qvars_op_vars A Q\<close>
  shows \<open>operator_local A R\<close>
  using assms apply (auto simp add: distinct_qvars_op_vars_def operator_local_def)
  by (simp add: qcomplements.rep_eq register_range_complement_commutant)


lemma distinct_qvars_pred_vars_complement:
  assumes \<open>qcomplements Q R\<close>
  assumes \<open>distinct_qvars_pred_vars A Q\<close>
  shows \<open>predicate_local A R\<close>
  using assms(1) assms(2) distinct_qvars_op_vars_complement distinct_qvars_pred_vars_def operator_local_Proj by blast

lemma iso_qregister_operator_local:
  assumes \<open>iso_qregister Q\<close>
  shows \<open>operator_local A Q\<close>
proof -
  from assms obtain J where \<open>qregister_chain Q J = qregister_id\<close>
    unfolding iso_qregister_def by auto
  then have \<open>A = apply_qregister Q (apply_qregister J A)\<close>
    by (metis TTIR_APPLY_QREGISTER_def eq_id_iff qregister_id.rep_eq translate_to_index_registers_apply)
  then show ?thesis
    by (simp add: operator_local_def)
qed


lemma iso_qregister_predicate_local:
  assumes \<open>iso_qregister Q\<close>
  shows \<open>predicate_local S Q\<close>
  using assms iso_qregister_operator_local operator_local_Proj by blast

lemma leq_space_div[simp]: 
  fixes A B :: \<open>'b ell2 ccsubspace\<close> and Q :: \<open>('a, 'b) qregister\<close>
  assumes \<open>qregister Q\<close> and \<open>distinct_qvars_pred_vars A Q\<close>
  shows "(A \<le> B \<div> \<psi>\<guillemotright>Q) \<longleftrightarrow> (A \<sqinter> ccspan {\<psi>}\<guillemotright>Q \<le> B)"
proof -
  from qcomplement_exists[OF \<open>qregister Q\<close>]
  have \<open>\<forall>\<^sub>\<tau> 'g::type = qregister_decomposition_basis Q.
        (A \<le> B \<div> \<psi>\<guillemotright>Q) \<longleftrightarrow> (A \<sqinter> ccspan {\<psi>}\<guillemotright>Q \<le> B)\<close>
  proof (rule with_type_mp)
    assume \<open>\<exists>R. qcomplements Q R\<close>
    then obtain R :: \<open>('c, 'b) qregister\<close> where \<open>qcomplements Q R\<close>
      by auto
    then have \<open>qcomplements R Q\<close>
      by (meson complements_sym qcomplements.rep_eq)
    from \<open>qcomplements Q R\<close> have \<open>iso_qregister \<lbrakk>Q,R\<rbrakk>\<close>
      by (simp add: qcomplements_def')
    from \<open>qcomplements R Q\<close> have \<open>iso_qregister \<lbrakk>R,Q\<rbrakk>\<close>
      by (simp add: qcomplements_def')
    have [simp]: \<open>qregister \<lbrakk>R,Q\<rbrakk>\<close>
      using \<open>iso_qregister \<lbrakk>R, Q\<rbrakk>\<^sub>q\<close> iso_qregister_def by blast
    have [simp]: \<open>qregister \<lbrakk>Q,R\<rbrakk>\<close>
      by (simp add: qcompatible_sym)
    from \<open>distinct_qvars_pred_vars A Q\<close> \<open>qcomplements Q R\<close>
    have \<open>predicate_local A R\<close>
      using distinct_qvars_pred_vars_complement by auto
    then obtain A' where A_def: \<open>A = A'\<guillemotright>R\<close>
      using predicate_localE by blast
    from \<open>iso_qregister \<lbrakk>R,Q\<rbrakk>\<close>
    have \<open>predicate_local B \<lbrakk>R,Q\<rbrakk>\<close>
      using iso_qregister_predicate_local by blast
    then obtain B' where B_def: \<open>B = B'\<guillemotright>\<lbrakk>R,Q\<rbrakk>\<close>
      using predicate_localE by blast

    have \<open>A \<le> B \<div> \<psi>\<guillemotright>Q \<longleftrightarrow> A'\<guillemotright>R \<le> space_div_unlifted B' \<psi> \<guillemotright> R\<close>
      by (simp add: A_def B_def space_div_space_div_unlifted)
    also have \<open>\<dots> \<longleftrightarrow> A' \<le> space_div_unlifted B' \<psi>\<close>
      using \<open>qregister \<lbrakk>R, Q\<rbrakk>\<^sub>q\<close> distinct_qvarsL lift_leq by blast
    also have \<open>\<dots> \<longleftrightarrow> A'\<guillemotright>qFst \<sqinter> qSnd =\<^sub>q \<psi> \<le> B'\<close>
    proof (rule iffI)
      show \<open>A' \<le> space_div_unlifted B' \<psi>\<close> if \<open>A'\<guillemotright>qFst \<sqinter> qSnd =\<^sub>q \<psi> \<le> B'\<close>
       proof (rule ccsubspace_leI_unit)
        fix \<phi>
        assume \<open>\<phi> \<in> space_as_set A'\<close>
        then have \<open>\<phi> \<otimes> \<psi> \<in> space_as_set (A'\<guillemotright>qFst \<sqinter> qSnd =\<^sub>q \<psi>)\<close>
          by (auto intro!: tensor_ell2_in_tensor_ccsubspace ccspan_superset'
              simp add: apply_qregister_space_qFst apply_qregister_space_qSnd)
        also from that have \<open>\<dots> \<subseteq> space_as_set B'\<close>
          by (simp add: less_eq_ccsubspace.rep_eq)
        finally show \<open>\<phi> \<in> space_as_set (space_div_unlifted B' \<psi>)\<close>
          by (simp add: space_div_unlifted.rep_eq)
      qed
      show \<open>A'\<guillemotright>qFst \<sqinter> qSnd =\<^sub>q \<psi> \<le> B'\<close> if \<open>A' \<le> space_div_unlifted B' \<psi>\<close>
      proof (rule ccsubspace_leI_unit)
        fix \<phi> assume \<open>\<phi> \<in> space_as_set (A'\<guillemotright>qFst \<sqinter> qSnd =\<^sub>q \<psi>)\<close>
        then have \<phi>A: \<open>\<phi> \<in> space_as_set (A'\<guillemotright>qFst)\<close> and \<phi>\<psi>: \<open>\<phi> \<in> space_as_set (qSnd =\<^sub>q \<psi>)\<close>
          by auto
        from \<phi>\<psi> obtain \<gamma> where \<phi>_decomp: \<open>\<phi> = \<gamma> \<otimes> \<psi>\<close>
          apply atomize_elim
          apply (rule tensor_ccsubspace_right1dim_member)
          by (simp add: apply_qregister_space_qSnd)
        from \<phi>A that have \<open>\<phi> \<in> space_as_set (space_div_unlifted B' \<psi> \<guillemotright> qFst)\<close>
          using less_eq_ccsubspace.rep_eq by force
        then have \<open>\<gamma> \<in> space_as_set (space_div_unlifted B' \<psi>)\<close>
          by (metis UNIV_I \<phi>_decomp apply_qregister_space_qFst space_div_unlifted_zero2 tensor_ell2_mem_tensor_ccsubspace_left top_ccsubspace.rep_eq)
        then show \<open>\<phi> \<in> space_as_set B'\<close>
          by (simp add: space_div_unlifted.rep_eq \<phi>_decomp)
      qed
    qed
    also have \<open>\<dots> \<longleftrightarrow> A \<sqinter> Q =\<^sub>q \<psi> \<le> B\<close>
      apply (subst asm_rl[of \<open>Q =\<^sub>q \<psi> = (qSnd =\<^sub>q \<psi>) \<guillemotright> \<lbrakk>R,Q\<rbrakk>\<close>])
       apply (simp add: qregister_chain_pair_Snd flip: qregister_chain_apply_space_simp)
      apply (subst asm_rl[of \<open>A = A' \<guillemotright> qFst \<guillemotright> \<lbrakk>R,Q\<rbrakk>\<close>])
       apply (simp add: A_def apply_qregister_space_qFst assms(1) tensor_lift)
      by (simp add: B_def)
    finally show \<open>(A \<le> B \<div> \<psi>\<guillemotright>Q) = (A \<sqinter> Q =\<^sub>q \<psi> \<le> B)\<close>
      by -
  qed
  from this[cancel_with_type]
  show \<open>A \<le> B \<div> \<psi>\<guillemotright>Q \<longleftrightarrow> A \<sqinter> ccspan {\<psi>}\<guillemotright>Q \<le> B\<close>
    by simp
qed

lemma top_div[simp]: "top \<div> \<psi>\<guillemotright>Q = top" if \<open>qregister Q\<close>
proof -
  from qcomplement_exists[OF that]
  have \<open>\<forall>\<^sub>\<tau> 'g::type = qregister_decomposition_basis Q.
        top \<div> \<psi>\<guillemotright>Q = top\<close>
  proof (rule with_type_mp)
    assume \<open>\<exists>R. qcomplements Q R\<close>
    then obtain R :: \<open>('c, 'b) qregister\<close> where \<open>qcomplements Q R\<close>
      by auto
    then have [simp]: \<open>qregister \<lbrakk>Q, R\<rbrakk>\<^sub>q\<close>
      using iso_qregister_def qcomplements_def' by blast
    have \<open>top\<guillemotright>\<lbrakk>R,Q\<rbrakk> \<div> \<psi>\<guillemotright>Q = top\<close>
      apply (simp add: space_div_space_div_unlifted space_div_unlifted_def flip: top_ccsubspace_def)
      using \<open>qregister \<lbrakk>Q, R\<rbrakk>\<^sub>q\<close> qcompatible_register2 top_lift by blast
    then show \<open>top \<div> \<psi>\<guillemotright>Q = top\<close>
      by (simp add: distinct_qvars_swap)
  qed
  from this[cancel_with_type]
  show ?thesis
    by simp
qed
lemma bot_div[simp]: "bot \<div> \<psi>\<guillemotright>Q = (if \<psi>=0 then top else bot)" if \<open>\<psi> \<noteq> 0\<close>
  using space_div_zero1 by auto
lemma Cla_div[simp]: "Cla[e] \<div> \<psi>\<guillemotright>Q = (if \<psi>=0 then top else Cla[e])" if \<open>qregister Q\<close>
  using that by auto

(* lemma space_div_add_extend_lift_as_var_concat_hint:
  fixes S :: "_ subspace"
  shows "NO_MATCH ((variable_concat a b),b) (Q,R) \<Longrightarrow> (space_div (S\<guillemotright>Q) \<psi> R) = (space_div (extend_lift_as_var_concat_hint (S\<guillemotright>Q) R)) \<psi> R"
  unfolding extend_lift_as_var_concat_hint_def by simp *)

lemma translate_to_index_registers_space_div[translate_to_index_registers]:
  fixes F :: \<open>('a,'b) qregister\<close>
  assumes \<open>TTIR_APPLY_QREGISTER_SPACE A' F A\<close>
  assumes \<open>TTIR_LUB F G FG F' G'\<close>
  shows \<open>TTIR_APPLY_QREGISTER_SPACE (space_div A' \<psi> G)
          FG (apply_qregister_space F' A \<div> \<psi>\<guillemotright>G')\<close>
  using assms by (simp add: space_div_lift TTIR_APPLY_QREGISTER_SPACE_def TTIR_LUB_def)

subsection \<open>Quantum equality\<close>


definition quantum_equality_full :: "('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c::complex_inner) \<Rightarrow> ('a,'d) qregister \<Rightarrow> ('b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c) \<Rightarrow> ('b,'d) qregister \<Rightarrow> 'd subspace" where
  [code del]: "quantum_equality_full U Q V R = 
                 (eigenspace 1 (swap_ell2 o\<^sub>C\<^sub>L (V* o\<^sub>C\<^sub>L U) \<otimes>\<^sub>o (U* o\<^sub>C\<^sub>L V))) \<guillemotright> qregister_pair Q R"
  for Q :: "('a,'d) qregister" and R :: "('b,'d) qregister"
  and U V :: "_ \<Rightarrow>\<^sub>C\<^sub>L 'c"

abbreviation "quantum_equality" (infix "\<equiv>\<qq>" 100)
  where "quantum_equality X Y \<equiv> quantum_equality_full id_cblinfun X id_cblinfun Y"
syntax quantum_equality :: "'a q2variable \<Rightarrow> 'a q2variable \<Rightarrow> predicate" (infix "==q" 100)
syntax "_quantum_equality" :: "variable_list_args \<Rightarrow> variable_list_args \<Rightarrow> predicate" ("Qeq'[_=_']")
translations
  "_quantum_equality a b" \<rightharpoonup> "CONST quantum_equality (_qvariables a) (_qvariables b)"

lemma quantum_equality_non_qregister1[simp]: \<open>quantum_equality_full U non_qregister V R = \<bottom>\<close>
  by (simp add: quantum_equality_full_def)

lemma quantum_equality_non_qregister2[simp]: \<open>quantum_equality_full U Q V non_qregister = \<bottom>\<close>
  by (simp add: quantum_equality_full_def)

lemma apply_qregister_space_quantum_equality:
  \<open>apply_qregister_space S (quantum_equality_full U Q V R)
     = quantum_equality_full U (qregister_chain S Q) V (qregister_chain S R)\<close>
  by (simp add: quantum_equality_full_def flip: qregister_chain_pair)

lemma quantum_equality_full_not_compatible:
  assumes \<open>\<not> qcompatible Q R\<close>
  shows \<open>quantum_equality_full U Q V R = 0\<close>
  using assms by (simp add: quantum_equality_full_def non_qregister)


lemma quantum_equality_sym:
  (* assumes [simp]: "distinct_qvars (qregister_pair Q R)" *)
  shows "quantum_equality_full U Q V R = quantum_equality_full V R U Q"
proof (cases \<open>qcompatible Q R\<close>)
  case True
  have dist: "distinct_qvars (qregister_pair R Q)"
    using True by (rule distinct_qvars_swap)
  have [simp]: \<open>qregister (qregister_pair Q R)\<close>
    using True by blast
  have [simp]: \<open>qregister (qregister_pair R Q)\<close>
    by (simp add: dist)
  have a: "comm_op \<cdot> ((V* \<cdot> U) \<otimes>\<^sub>o (U* \<cdot> V)) \<cdot> comm_op* = (U* \<cdot> V) \<otimes>\<^sub>o (V* \<cdot> U)" by simp
  have op_eq: "((comm_op o\<^sub>C\<^sub>L (V* \<cdot> U) \<otimes>\<^sub>o (U* \<cdot> V))\<guillemotright>qregister_pair Q R) =
               ((comm_op o\<^sub>C\<^sub>L (U* \<cdot> V) \<otimes>\<^sub>o (V* \<cdot> U))\<guillemotright>qregister_pair R Q)"
    apply (subst qregister_pair_chain_swap[of Q R, symmetric])
    apply (subst qregister_chain_apply)
    apply (simp add: apply_qregister_qswap apply_qregister_transform_qregister sandwich_apply
        flip: transform_qregister_swap_ell2 cblinfun_compose_assoc)
    by (rule swap_ell2_commute_tensor_op)
  show ?thesis
    apply (subst quantum_equality_full_def)
    apply (subst quantum_equality_full_def)
    apply (subst eigenspace_lift[symmetric, OF True])
    apply (subst eigenspace_lift[symmetric, OF dist])
    using op_eq by simp
next
  case False
  then have \<open>\<not> qcompatible R Q\<close>
    using qcompatible_sym by blast
  with False
  show ?thesis
    by (simp add: quantum_equality_full_not_compatible)
qed

lift_definition qregister_tensor :: \<open>('a,'b) qregister \<Rightarrow> ('c,'d) qregister \<Rightarrow> ('a\<times>'c, 'b\<times>'d) qregister\<close> is
  \<open>\<lambda>F G. if qregister_raw F \<and> qregister_raw G then Laws_Quantum.register_tensor F G else non_qregister_raw\<close>
  by (auto simp: non_qregister_raw Laws_Quantum.register_tensor_is_register)

lemma qcompatible_raw_non_qregister_raw_left[simp]: \<open>\<not> qcompatible_raw non_qregister_raw F\<close>
  using non_qregister_raw qcompatible_raw_def by blast

lemma qcompatible_raw_non_qregister_raw_right[simp]: \<open>\<not> qcompatible_raw F non_qregister_raw\<close>
  using non_qregister_raw qcompatible_raw_def by blast

lemma qregister_pair_chain_left: \<open>qcompatible F G \<Longrightarrow> \<lbrakk>qregister_chain F H, G\<rbrakk>\<^sub>q = qregister_chain \<lbrakk>F, G\<rbrakk> (qregister_tensor H qregister_id)\<close>
  unfolding qcompatible_def
  apply transfer
  by (simp add: register_tensor_is_register pair_o_tensor non_qregister_raw)
lemma qregister_pair_chain_right: \<open>qcompatible F G \<Longrightarrow> \<lbrakk>F, qregister_chain G H\<rbrakk>\<^sub>q = qregister_chain \<lbrakk>F, G\<rbrakk> (qregister_tensor qregister_id H)\<close>
  unfolding qcompatible_def
  apply transfer
  by (simp add: register_tensor_is_register pair_o_tensor non_qregister_raw)

lemma qregister_tensor_non_qregister_left[simp]: \<open>qregister_tensor non_qregister F = non_qregister\<close>
  apply transfer by (auto simp: non_qregister_raw)
lemma qregister_tensor_non_qregister_right[simp]: \<open>qregister_tensor F non_qregister = non_qregister\<close>
  apply transfer by (auto simp: non_qregister_raw)

lemma qregister_tensor_apply:
  \<open>apply_qregister (qregister_tensor F G) (a \<otimes>\<^sub>o b) = apply_qregister F a \<otimes>\<^sub>o apply_qregister G b\<close>
  apply (cases \<open>qregister F\<close>; cases \<open>qregister G\<close>)
     apply (auto simp: non_qregister)
  apply transfer
  by simp

lemma qregister_tensor_transform_qregister:
  assumes [simp]: \<open>unitary U\<close> \<open>unitary V\<close>
  shows \<open>qregister_tensor (transform_qregister U) (transform_qregister V)
            = transform_qregister (U \<otimes>\<^sub>o V)\<close>
  apply (rule qregister_eqI_tensor_op)
  by (simp add: qregister_tensor_apply apply_qregister_transform_qregister unitary_tensor_op sandwich_tensor_op)

lemma transform_qregister_non_unitary: \<open>\<not> unitary U \<Longrightarrow> transform_qregister U = non_qregister\<close>
  apply (transfer fixing: U) by simp

lemma transform_qregister_id: \<open>transform_qregister id_cblinfun = qregister_id\<close>
  apply (rule apply_qregister_inject[THEN iffD1])
  by (auto intro!: ext simp add: apply_qregister_transform_qregister)

(* TODO _id2 (other side) *)
lemma qregister_tensor_transform_qregister_id1:
  \<open>qregister_tensor (transform_qregister U) qregister_id
            = transform_qregister (U \<otimes>\<^sub>o id_cblinfun)\<close>
proof (cases \<open>unitary U\<close>)
  case True
  note [simp] = True
  have \<open>qregister_tensor (transform_qregister U) qregister_id
      = qregister_tensor (transform_qregister U) (transform_qregister id_cblinfun)\<close>
    by (simp add: transform_qregister_id)
  also have \<open>\<dots> = transform_qregister (U \<otimes>\<^sub>o id_cblinfun)\<close>
    by (simp add: qregister_tensor_transform_qregister)
  finally show ?thesis
    by -
next
  case False
  then show ?thesis
    by (simp add: transform_qregister_non_unitary)
qed

lemma qregister_chain_transform_qregister:
  assumes [simp]: \<open>unitary U\<close> \<open>unitary V\<close>
  shows \<open>qregister_chain (transform_qregister U) (transform_qregister V) = transform_qregister (U o\<^sub>C\<^sub>L V)\<close>
  by (auto intro!: ext apply_qregister_inject[THEN iffD1]
      simp: apply_qregister_transform_qregister sandwich_compose
      simp flip: cblinfun_apply_cblinfun_compose)


lemma quantum_equality_transform_register_left:
  fixes W :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
  assumes [simp]: \<open>unitary W\<close>
  shows \<open>quantum_equality_full (U o\<^sub>C\<^sub>L W) Q V R = 
         quantum_equality_full U (qregister_chain Q (transform_qregister (W*))) V R\<close>
proof (cases \<open>qcompatible Q R\<close>)
  case True
  have \<open>swap_ell2 o\<^sub>C\<^sub>L (V* o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L W) \<otimes>\<^sub>o (W* o\<^sub>C\<^sub>L U* o\<^sub>C\<^sub>L V)
         = sandwich (W* \<otimes>\<^sub>o id_cblinfun) *\<^sub>V (swap_ell2 o\<^sub>C\<^sub>L (V* o\<^sub>C\<^sub>L U) \<otimes>\<^sub>o (U* o\<^sub>C\<^sub>L V))\<close>
    apply (rule tensor_ell2_extensionality)
    by (simp add: cblinfun_apply_cblinfun_compose tensor_op_ell2 sandwich_apply tensor_op_adjoint)
  then have \<open>eigenspace 1 (swap_ell2 o\<^sub>C\<^sub>L (V* o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L W) \<otimes>\<^sub>o (W* o\<^sub>C\<^sub>L U* o\<^sub>C\<^sub>L V)) =
    (W* \<otimes>\<^sub>o id_cblinfun) *\<^sub>S eigenspace 1 (swap_ell2 o\<^sub>C\<^sub>L (V* o\<^sub>C\<^sub>L U) \<otimes>\<^sub>o (U* o\<^sub>C\<^sub>L V))\<close>
    apply (subst cblinfun_image_eigenspace_isometry)
    by simp_all
  with True show ?thesis
    by (simp add: quantum_equality_full_def adj_cblinfun_compose qregister_pair_chain_left
        qregister_tensor_transform_qregister_id1 apply_qregister_space_transform_qregister
        unitary_tensor_op
        flip: cblinfun_compose_assoc)
next
  case False
  have \<open>\<not> qcompatible (qregister_chain Q (transform_qregister (W*))) R\<close>
  proof (rule notI)
    assume \<open>qcompatible (qregister_chain Q (transform_qregister (W*))) R\<close>
    then have \<open>qcompatible (qregister_chain (qregister_chain Q (transform_qregister (W*))) (transform_qregister W)) R\<close>
      by simp
    also have \<open>qregister_chain (qregister_chain Q (transform_qregister (W*))) (transform_qregister W) = Q\<close>
      by (simp add: qregister_chain_assoc qregister_chain_transform_qregister transform_qregister_id)
    finally show False
      using False by simp
  qed
  with False show ?thesis
    by (simp add: quantum_equality_full_not_compatible)
qed

lemma quantum_equality_transform_register_right:
  fixes W :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
  assumes \<open>unitary W\<close>
  shows \<open>quantum_equality_full U Q (V o\<^sub>C\<^sub>L W) R = 
         quantum_equality_full U Q V (qregister_chain R (transform_qregister (W*)))\<close>
  apply (subst quantum_equality_sym)
  apply (subst (2) quantum_equality_sym)
  using assms by (rule quantum_equality_transform_register_left)

lemma distinct_qvars_pred_vars_quantum_equality[simp]:
  assumes [register]: \<open>qregister \<lbrakk>F,H\<rbrakk>\<close> \<open>qregister \<lbrakk>G,H\<rbrakk>\<close>
  shows \<open>distinct_qvars_pred_vars (quantum_equality_full U F V G) H\<close>
proof (cases \<open>qregister \<lbrakk>F,G\<rbrakk>\<close>)
  case True
  note [register] = this
  show ?thesis
    by (simp add: quantum_equality_full_def)
next
  case False
  then have \<open>\<lbrakk>F,G\<rbrakk> = non_qregister\<close>
    by (simp add: non_qregister)
  then show ?thesis 
    by (simp add: quantum_equality_full_def apply_qregister_space_def)
qed

lemma predicate_local[intro!]: 
  assumes "qvariables_local (qregister_pair Q R) S"
  shows "predicate_local (quantum_equality_full U Q V R) S"
   by (simp add: assms lift_predicate_local quantum_equality_full_def)

lemma applyOpSpace_colocal:
  "colocal U S \<Longrightarrow> unitary U \<Longrightarrow> U \<cdot> S = S" for U :: "(qu2,qu2) l2bounded" and S :: predicate
  by (metis Proj_range cblinfun_compose_image distinct_qvars_op_pred_def unitary_range)

lemma applyOpSpace_colocal_simp[simp]:
  "DISTINCT_QVARS_GUARD (colocal U S) \<Longrightarrow> unitary U \<Longrightarrow> U \<cdot> S = S" for U :: "(qu2,qu2) l2bounded" and S :: predicate
  by (simp add: applyOpSpace_colocal DISTINCT_QVARS_GUARD_def)

lemma qeq_collect:
 "quantum_equality_full U Q1 V Q2 = quantum_equality_full (V*\<cdot>U) Q1 id_cblinfun Q2"
 for U :: "('a,'b) l2bounded" and V :: "('c,'b) l2bounded"
  unfolding quantum_equality_full_def by auto

lemma qeq_collect_guarded[simp]:
  fixes U :: "('a,'b) l2bounded" and V :: "('c,'b) l2bounded"
  assumes "NO_MATCH id_cblinfun V"
  shows "quantum_equality_full U Q1 V Q2 = quantum_equality_full (V*\<cdot>U) Q1 id_cblinfun Q2"
  by (fact qeq_collect)


(* Proof in paper *)
lemma Qeq_mult1[simp]:
  fixes U::"('a,'a) l2bounded" and U2 :: "'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c::complex_inner"
  assumes [simp]: \<open>unitary U\<close>
  shows "U\<guillemotright>Q1 *\<^sub>S quantum_equality_full U1 Q1 U2 Q2 = quantum_equality_full (U1 o\<^sub>C\<^sub>L U*) Q1 U2 Q2"
proof (cases \<open>qcompatible Q1 Q2\<close>)
  case True
  have \<open>U\<guillemotright>Q1 *\<^sub>S quantum_equality_full U1 Q1 U2 Q2
      = apply_qregister \<lbrakk>Q1, Q2\<rbrakk>\<^sub>q (U \<otimes>\<^sub>o id_cblinfun) *\<^sub>S
          apply_qregister_space \<lbrakk>Q1, Q2\<rbrakk>\<^sub>q (eigenspace 1 (swap_ell2 o\<^sub>C\<^sub>L (U2* o\<^sub>C\<^sub>L U1) \<otimes>\<^sub>o (U1* o\<^sub>C\<^sub>L U2)))\<close>
    unfolding quantum_equality_full_def using True lift_extendR by fastforce
  also have \<open>\<dots> = apply_qregister_space \<lbrakk>Q1, Q2\<rbrakk>\<^sub>q ((U \<otimes>\<^sub>o id_cblinfun) *\<^sub>S
                 eigenspace 1 (swap_ell2 o\<^sub>C\<^sub>L (U2* o\<^sub>C\<^sub>L U1) \<otimes>\<^sub>o (U1* o\<^sub>C\<^sub>L U2)))\<close>
    by simp
  also have \<open>\<dots> = apply_qregister_space \<lbrakk>Q1, Q2\<rbrakk>\<^sub>q
           (eigenspace 1 (swap_ell2 o\<^sub>C\<^sub>L (U2* o\<^sub>C\<^sub>L (U1 o\<^sub>C\<^sub>L U*)) \<otimes>\<^sub>o ((U1 o\<^sub>C\<^sub>L U*)* o\<^sub>C\<^sub>L U2)))\<close>
  proof -
    have \<open>(U \<otimes>\<^sub>o id_cblinfun) *\<^sub>S eigenspace 1 (swap_ell2 o\<^sub>C\<^sub>L (U2* o\<^sub>C\<^sub>L U1) \<otimes>\<^sub>o (U1* o\<^sub>C\<^sub>L U2))
        = kernel (swap_ell2 o\<^sub>C\<^sub>L (U2* o\<^sub>C\<^sub>L U1) \<otimes>\<^sub>o (U1* o\<^sub>C\<^sub>L U2) o\<^sub>C\<^sub>L U* \<otimes>\<^sub>o id_cblinfun - U* \<otimes>\<^sub>o id_cblinfun)\<close>
      by (simp add: eigenspace_def cblinfun_image_kernel_unitary unitary_tensor_op
          tensor_op_adjoint cblinfun_compose_minus_left)
    also have \<open>\<dots> = kernel ((U \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L (swap_ell2 o\<^sub>C\<^sub>L (U2* o\<^sub>C\<^sub>L U1) \<otimes>\<^sub>o (U1* o\<^sub>C\<^sub>L U2) o\<^sub>C\<^sub>L U* \<otimes>\<^sub>o id_cblinfun - U* \<otimes>\<^sub>o id_cblinfun))\<close>
      apply (rule kernel_cblinfun_compose)
      by (simp add: unitary_tensor_op kernel_compl_adj_range)
    also have \<open>\<dots> = eigenspace 1 ((U \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L swap_ell2 o\<^sub>C\<^sub>L (U2* o\<^sub>C\<^sub>L U1) \<otimes>\<^sub>o (U1* o\<^sub>C\<^sub>L U2) o\<^sub>C\<^sub>L U* \<otimes>\<^sub>o id_cblinfun)\<close>
      by (simp add: eigenspace_def cblinfun_compose_minus_right comp_tensor_op cblinfun_compose_assoc)
    also have \<open>\<dots> = eigenspace 1 (swap_ell2 o\<^sub>C\<^sub>L (U2* o\<^sub>C\<^sub>L (U1 o\<^sub>C\<^sub>L U*)) \<otimes>\<^sub>o ((U1 o\<^sub>C\<^sub>L U*)* o\<^sub>C\<^sub>L U2))\<close>
      apply (simp add: comp_tensor_op flip: cblinfun_compose_assoc swap_ell2_commute_tensor_op)
      by (simp add: comp_tensor_op cblinfun_compose_assoc)
    finally show ?thesis
      by simp
  qed
  also have \<open>\<dots> = quantum_equality_full (U1 o\<^sub>C\<^sub>L U*) Q1 U2 Q2\<close>
    by (simp add: quantum_equality_full_def)
  finally show ?thesis
    by -
next
  case False
  then show ?thesis
    by (simp add: non_qregister quantum_equality_full_def)
qed

(* Proof in paper *)
lemma Qeq_mult2[simp]:
  fixes U::"('a,'a) l2bounded" and U1 :: "'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c::complex_inner"
  assumes \<open>unitary U\<close>
  shows "U\<guillemotright>Q2 *\<^sub>S quantum_equality_full U1 Q1 U2 Q2 = quantum_equality_full U1 Q1 (U2 o\<^sub>C\<^sub>L U*) Q2"
proof (cases \<open>qcompatible Q1 Q2\<close>)
  case True
  show ?thesis
    apply (simp add: quantum_equality_sym[of U1])
    using assms by (rule Qeq_mult1)
next
  case False
  then show ?thesis
    by (simp add: non_qregister quantum_equality_full_def)
qed

lemma qFst_eq_vector_decompose:
  \<open>\<psi> \<in> space_as_set (qFst =\<^sub>q \<phi>) \<longleftrightarrow> (\<exists>\<psi>'. \<psi> = \<phi> \<otimes>\<^sub>s \<psi>')\<close>
proof (rule iffI)
  assume \<open>\<psi> \<in> space_as_set (qFst =\<^sub>q \<phi>)\<close>
  then have \<open>\<psi> \<in> space_as_set (ccspan {\<phi>} \<otimes>\<^sub>S \<top>)\<close>
    by (simp add: apply_qregister_space_qFst)
  then show \<open>\<exists>\<psi>'. \<psi> = \<phi> \<otimes>\<^sub>s \<psi>'\<close>
    by (rule tensor_ccsubspace_left1dim_member)
next
  assume \<open>\<exists>\<psi>'. \<psi> = \<phi> \<otimes>\<^sub>s \<psi>'\<close>
  then obtain \<psi>' where \<psi>_def: \<open>\<psi> = \<phi> \<otimes>\<^sub>s \<psi>'\<close>
    by auto
  then show \<open>\<psi> \<in> space_as_set (qFst =\<^sub>q \<phi>)\<close>
    by (simp add: apply_qregister_space_qFst ccspan_superset' tensor_ell2_in_tensor_ccsubspace)
qed

lemma qSnd_eq_vector_decompose:
  \<open>\<psi> \<in> space_as_set (qSnd =\<^sub>q \<phi>) \<longleftrightarrow> (\<exists>\<psi>'. \<psi> = \<psi>' \<otimes>\<^sub>s \<phi>)\<close>
proof (rule iffI)
  assume \<open>\<psi> \<in> space_as_set (qSnd =\<^sub>q \<phi>)\<close>
  then have \<open>\<psi> \<in> space_as_set (\<top> \<otimes>\<^sub>S ccspan {\<phi>})\<close>
    by (simp add: apply_qregister_space_qSnd)
  then show \<open>\<exists>\<psi>'. \<psi> = \<psi>' \<otimes>\<^sub>s \<phi>\<close>
    by (rule tensor_ccsubspace_right1dim_member)
next
  assume \<open>\<exists>\<psi>'. \<psi> = \<psi>' \<otimes>\<^sub>s \<phi>\<close>
  then obtain \<psi>' where \<psi>_def: \<open>\<psi> = \<psi>' \<otimes>\<^sub>s \<phi>\<close>
    by auto
  then show \<open>\<psi> \<in> space_as_set (qSnd =\<^sub>q \<phi>)\<close>
    by (simp add: apply_qregister_space_qSnd ccspan_superset' tensor_ell2_in_tensor_ccsubspace)
qed

(* Proof in paper *)
lemma quantum_eq_unique[simp]:
  fixes Q :: "('a,'d) qregister" and R :: "('b,'d) qregister"
    and U :: "'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c::chilbert_space" and V :: "'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c"
    and \<psi> :: "'a ell2"
  assumes [simp]: \<open>qregister \<lbrakk>Q,R\<rbrakk>\<close>
  assumes \<open>isometry U\<close> and \<open>isometry (V*)\<close>
  shows \<open>quantum_equality_full U Q V R \<sqinter> Q =\<^sub>q \<psi>   =  Q =\<^sub>q \<psi> \<sqinter> R =\<^sub>q (V* *\<^sub>V U *\<^sub>V \<psi>)\<close>
proof -
  have \<open>quantum_equality_full U qFst V qSnd \<sqinter> qFst =\<^sub>q \<psi>   =  qFst =\<^sub>q \<psi> \<sqinter> qSnd =\<^sub>q (V* *\<^sub>V U *\<^sub>V \<psi>)\<close>
  proof (intro antisym inf.boundedI)
    show \<open>quantum_equality_full U qFst V qSnd \<sqinter> qFst =\<^sub>q \<psi>  \<le>  qFst =\<^sub>q \<psi>\<close>
      by simp
    show \<open>qFst =\<^sub>q \<psi> \<sqinter> qSnd =\<^sub>q (V* *\<^sub>V U *\<^sub>V \<psi>)  \<le>  qFst =\<^sub>q \<psi>\<close>
      by simp
    show \<open>quantum_equality_full U qFst V qSnd \<sqinter> qFst =\<^sub>q \<psi>  \<le>  qSnd =\<^sub>q (V* *\<^sub>V U *\<^sub>V \<psi>)\<close>
    proof (rule ccsubspace_leI_unit)
      fix \<phi>
      assume \<open>\<phi> \<in> space_as_set (quantum_equality_full U qFst V qSnd \<sqinter> qFst =\<^sub>q \<psi>)\<close>
      then have qeq: \<open>\<phi> \<in> space_as_set (quantum_equality_full U qFst V qSnd)\<close> and fst: \<open>\<phi> \<in> space_as_set (qFst =\<^sub>q \<psi>)\<close>
        by auto
      from qeq have \<phi>_inv: \<open>swap_ell2 *\<^sub>V ((V* o\<^sub>C\<^sub>L U) \<otimes>\<^sub>o (U* o\<^sub>C\<^sub>L V)) *\<^sub>V \<phi> = \<phi>\<close>
        using eigenspace_memberD[where e=1] by (force simp add: quantum_equality_full_def)
      from fst obtain \<phi>' where \<phi>_def: \<open>\<phi> = \<psi> \<otimes>\<^sub>s \<phi>'\<close>
        by (auto simp: qFst_eq_vector_decompose)
      have \<open>\<phi> = (U* *\<^sub>V V *\<^sub>V \<phi>') \<otimes>\<^sub>s (V* *\<^sub>V U *\<^sub>V \<psi>)\<close>
        apply (subst \<phi>_inv[symmetric])
        by (simp add: \<phi>_def tensor_op_ell2)
      also have \<open>\<dots> \<in> space_as_set (qSnd =\<^sub>q (V* *\<^sub>V U *\<^sub>V \<psi>))\<close>
        by (simp add: apply_qregister_space_qSnd tensor_ell2_in_tensor_ccsubspace ccspan_superset')
      finally show \<open>\<phi> \<in> space_as_set (qSnd =\<^sub>q (V* *\<^sub>V U *\<^sub>V \<psi>))\<close>
        by -
    qed
    show \<open>qFst =\<^sub>q \<psi> \<sqinter> qSnd =\<^sub>q (V* *\<^sub>V U *\<^sub>V \<psi>)  \<le>  quantum_equality_full U qFst V qSnd\<close>
    proof (rule ccsubspace_leI_unit)
      fix \<phi>
      assume \<open>\<phi> \<in> space_as_set (qFst =\<^sub>q \<psi> \<sqinter> qSnd =\<^sub>q (V* *\<^sub>V U *\<^sub>V \<psi>))\<close>
      then have \<open>\<phi> \<in> space_as_set (ccspan {\<psi> \<otimes>\<^sub>s V* *\<^sub>V U *\<^sub>V \<psi>})\<close>
        by (simp add: tensor_ccsubspace_ccspan flip: tensor_lift)
      then obtain c where \<phi>_def: \<open>\<phi> = c *\<^sub>C (\<psi> \<otimes>\<^sub>s V* *\<^sub>V U *\<^sub>V \<psi>)\<close>
        by (auto simp add: ccspan_finite complex_vector.span_singleton)
      from \<open>isometry (V*)\<close> have [simp]: \<open>V *\<^sub>V V* *\<^sub>V x = x\<close> for x
        by (simp add: isometry_def flip: cblinfun_apply_cblinfun_compose cblinfun_compose_assoc)
      from \<open>isometry U\<close> have [simp]: \<open>U* *\<^sub>V U *\<^sub>V x = x\<close> for x
        by (simp add: isometry_def flip: cblinfun_apply_cblinfun_compose cblinfun_compose_assoc)
      have \<open>(swap_ell2 o\<^sub>C\<^sub>L (V* o\<^sub>C\<^sub>L U) \<otimes>\<^sub>o (U* o\<^sub>C\<^sub>L V)) *\<^sub>V \<phi> = \<phi>\<close>
        by (simp add: \<phi>_def cblinfun.scaleC_right tensor_op_ell2)
      then show \<open>\<phi> \<in> space_as_set (quantum_equality_full U qFst V qSnd)\<close>
        by (simp add: quantum_equality_full_def eigenspace_memberI)
    qed
  qed
  then have \<open>(quantum_equality_full U qFst V qSnd \<sqinter> qFst =\<^sub>q \<psi>) \<guillemotright> \<lbrakk>Q,R\<rbrakk>
             = (qFst =\<^sub>q \<psi> \<sqinter> qSnd =\<^sub>q (V* *\<^sub>V U *\<^sub>V \<psi>)) \<guillemotright> \<lbrakk>Q,R\<rbrakk>\<close>
    by (rule arg_cong[where f=\<open>apply_qregister_space _\<close>])
  then show ?thesis
    by (simp add: apply_qregister_space_inf apply_qregister_space_quantum_equality 
        qregister_chain_pair_Fst 
        flip: qregister_chain_apply_space
        del: lift_inf)
qed

(* Proof in paper, Lemma 34, p.25 *)
lemma quantum_eq_add_state:
  fixes U :: "'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2" and V :: "'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2" and \<psi> :: "'d ell2"
    and Q :: "('a,'m) qregister" and R :: "('b,'m) qregister" and T :: "('d,'m) qregister"
  assumes [register]: \<open>qregister \<lbrakk>Q,R,T\<rbrakk>\<close>
  assumes \<open>norm \<psi> = 1\<close>
  shows \<open>quantum_equality_full U Q V R  \<sqinter>  T =\<^sub>q \<psi>
             = quantum_equality_full (U \<otimes>\<^sub>o id_cblinfun) \<lbrakk>Q,T\<rbrakk> (tensor_ell2_right \<psi> o\<^sub>C\<^sub>L V) R\<close>
proof -
  have [simp]: \<open>qregister_chain \<lbrakk>T, Q, R\<rbrakk>\<^sub>q \<lbrakk>\<lbrakk>#2\<rbrakk>\<^sub>q, \<lbrakk>#1\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q = \<lbrakk>Q,T\<rbrakk>\<close>
    apply (rule qregister_eqI_tensor_op)
    by (simp add: apply_qregister_pair qregister_compose qregister_chain_pair
        flip: qregister_chain_apply 
        del: lift_timesOp qregister_chain_apply_simp)
  have [simp]: \<open>\<lbrakk>#2, #3.\<rbrakk>\<^sub>q = qSnd\<close>
    apply (rule qregister_eqI_tensor_op)
    by (simp add: apply_qregister_pair qregister_compose qregister_chain_pair
        apply_qregister_snd apply_qregister_fst qregister_chain_apply comp_tensor_op
        del: lift_timesOp qregister_chain_apply_simp)
  have trafo213: \<open>\<lbrakk>\<lbrakk>\<lbrakk>#2\<rbrakk>\<^sub>q, \<lbrakk>#1\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q, \<lbrakk>#3.\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q = transform_qregister (assoc_ell2 o\<^sub>C\<^sub>L (swap_ell2 \<otimes>\<^sub>o id_cblinfun))\<close>
    apply (intro qregister_eqI_separating separating_tensor' separating_UNIV)
         apply (auto intro!: separating_UNIV)[5]
    by (auto intro!: equal_ket 
        simp: apply_qregister_qFst apply_qregister_qSnd apply_qregister_pair qregister_chain_apply
        comp_tensor_op tensor_op_ell2 apply_qregister_transform_qregister sandwich_apply
        assoc_ell2'_tensor assoc_ell2_tensor tensor_op_adjoint
        simp flip: tensor_ell2_ket)

  have \<open>quantum_equality_full U \<lbrakk>#2\<rbrakk> V \<lbrakk>#3.\<rbrakk>  \<sqinter>  \<lbrakk>#1\<rbrakk> =\<^sub>q \<psi>
             = quantum_equality_full (U \<otimes>\<^sub>o id_cblinfun) \<lbrakk>#2,#1\<rbrakk> (tensor_ell2_right \<psi> o\<^sub>C\<^sub>L V) \<lbrakk>#3.\<rbrakk>\<close>
  proof (intro antisym ccsubspace_leI_unit)
    fix x :: \<open>('d \<times> 'a \<times> 'b) ell2\<close> (* assume \<open>norm x = 1\<close> *)
    assume \<open>x \<in> space_as_set (quantum_equality_full U \<lbrakk>#2\<rbrakk> V \<lbrakk>#3.\<rbrakk> \<sqinter> \<lbrakk>#1\<rbrakk> =\<^sub>q \<psi>)\<close>
    then have qeq: \<open>x \<in> space_as_set (quantum_equality_full U \<lbrakk>#2\<rbrakk> V \<lbrakk>#3.\<rbrakk>)\<close>
      and x1: \<open>x \<in> space_as_set (\<lbrakk>#1\<rbrakk> =\<^sub>q \<psi>)\<close>
      by simp_all
    from x1 obtain x' where x_def: \<open>x = \<psi> \<otimes>\<^sub>s x'\<close>
      using qFst_eq_vector_decompose by blast
    from qeq have x_inv: \<open>(id_cblinfun \<otimes>\<^sub>o (swap_ell2 o\<^sub>C\<^sub>L (V* o\<^sub>C\<^sub>L U) \<otimes>\<^sub>o (U* o\<^sub>C\<^sub>L V))) *\<^sub>V x = x\<close>
      using eigenspace_memberD[where e=1]
      by (auto simp add: quantum_equality_full_def apply_qregister_space_qSnd
          simp flip: eigenspace_tensor_id_left)

    have x'_decomp: \<open>x' = (\<Sum>\<^sub>\<infinity>(a,b). Rep_ell2 x' (a,b) *\<^sub>C ket (a,b))\<close>
      by (simp add: cond_case_prod_eta ell2_decompose_infsum)

    have aux1: \<open>X *\<^sub>V x = (\<Sum>\<^sub>\<infinity>(a,b). X *\<^sub>V \<psi> \<otimes>\<^sub>s Rep_ell2 x' (a, b) *\<^sub>C |(a, b)\<rangle>)\<close> for X
      unfolding x_def apply (subst x'_decomp)
      by (simp add: case_prod_unfold summable_on_tensor_ell2_right ell2_decompose_summable
          infsum_tensor_ell2_right
          flip: infsum_cblinfun_apply)


    have \<open>(sandwich (assoc_ell2 o\<^sub>C\<^sub>L swap_ell2 \<otimes>\<^sub>o id_cblinfun) *\<^sub>V
             (swap_ell2 o\<^sub>C\<^sub>L
              (V* o\<^sub>C\<^sub>L tensor_ell2_right \<psi>* o\<^sub>C\<^sub>L U \<otimes>\<^sub>o id_cblinfun) \<otimes>\<^sub>o
              ((U \<otimes>\<^sub>o id_cblinfun)* o\<^sub>C\<^sub>L (tensor_ell2_right \<psi> o\<^sub>C\<^sub>L V)))) *\<^sub>V x
        = (id_cblinfun \<otimes>\<^sub>o (swap_ell2 o\<^sub>C\<^sub>L (V* o\<^sub>C\<^sub>L U) \<otimes>\<^sub>o (U* o\<^sub>C\<^sub>L V))) *\<^sub>V x\<close>
      apply (subst (2) aux1) apply (subst aux1)
      by (simp add: tensor_ell2_scaleC2
          cblinfun_apply_cblinfun_compose cblinfun.scaleC_right sandwich_apply 
          assoc_ell2'_tensor assoc_ell2_tensor tensor_op_adjoint tensor_op_ell2
          cdot_square_norm \<open>norm \<psi> = 1\<close>
          flip: tensor_ell2_ket)
    also have \<open>\<dots> = x\<close>
      by (simp add: x_inv)
    finally show \<open>x \<in> space_as_set (quantum_equality_full (U \<otimes>\<^sub>o id_cblinfun) \<lbrakk>#2,#1\<rbrakk> (tensor_ell2_right \<psi> o\<^sub>C\<^sub>L V) \<lbrakk>#3.\<rbrakk>)\<close>
      by (simp add: quantum_equality_full_def trafo213 apply_qregister_space_transform_qregister
          cblinfun_image_eigenspace_isometry eigenspace_memberI)
  next
    fix x
    assume \<open>x \<in> space_as_set (quantum_equality_full (U \<otimes>\<^sub>o id_cblinfun) \<lbrakk>#2,#1\<rbrakk> (tensor_ell2_right \<psi> o\<^sub>C\<^sub>L V) \<lbrakk>#3.\<rbrakk>)\<close>
    then have x_inv: \<open>(sandwich (assoc_ell2 o\<^sub>C\<^sub>L swap_ell2 \<otimes>\<^sub>o id_cblinfun) *\<^sub>V (swap_ell2 o\<^sub>C\<^sub>L
              (V* o\<^sub>C\<^sub>L tensor_ell2_right \<psi>* o\<^sub>C\<^sub>L U \<otimes>\<^sub>o id_cblinfun) \<otimes>\<^sub>o
              ((U \<otimes>\<^sub>o id_cblinfun)* o\<^sub>C\<^sub>L (tensor_ell2_right \<psi> o\<^sub>C\<^sub>L V)))) *\<^sub>V x = x\<close>
      using eigenspace_memberD[where e=1]
      by (auto simp add: quantum_equality_full_def trafo213
          apply_qregister_space_transform_qregister cblinfun_image_eigenspace_isometry)
    have x_decomp: \<open>x = (\<Sum>\<^sub>\<infinity>(a,b,c). Rep_ell2 x (a,b,c) *\<^sub>C ket (a,b,c))\<close>
      by (simp add: cond_case_prod_eta ell2_decompose_infsum)
    have aux2: \<open>X *\<^sub>V x = (\<Sum>\<^sub>\<infinity>(a,b,c). X *\<^sub>V Rep_ell2 x (a,b,c) *\<^sub>C |(a,b,c)\<rangle>)\<close> for X
      unfolding x_def apply (subst x_decomp)
      by (simp add: case_prod_unfold summable_on_tensor_ell2_right ell2_decompose_summable
          infsum_tensor_ell2_right
          flip: infsum_cblinfun_apply)


    have x1: \<open>x \<in> space_as_set (\<lbrakk>#1\<rbrakk> =\<^sub>q \<psi>)\<close>
      apply (subst x_inv[symmetric])
      apply (subst aux2)
      using qFst_eq_vector_decompose 
      by (auto intro!: infsum_in_closed_csubspaceI  complex_vector.subspace_scale 
          simp: cblinfun.scaleC_right sandwich_apply assoc_ell2'_tensor tensor_op_adjoint
          tensor_ell2_scaleC2 tensor_op_ell2 assoc_ell2_tensor
          simp flip: tensor_ell2_ket)
    from x1 obtain x' where x_def: \<open>x = \<psi> \<otimes>\<^sub>s x'\<close>
      using qFst_eq_vector_decompose by blast
    have x'_decomp: \<open>x' = (\<Sum>\<^sub>\<infinity>(a,b). Rep_ell2 x' (a,b) *\<^sub>C ket (a,b))\<close>
      by (simp add: cond_case_prod_eta ell2_decompose_infsum)
    have aux3: \<open>X *\<^sub>V x = (\<Sum>\<^sub>\<infinity>(a,b). X *\<^sub>V \<psi> \<otimes>\<^sub>s Rep_ell2 x' (a, b) *\<^sub>C |(a, b)\<rangle>)\<close> for X
      unfolding x_def apply (subst x'_decomp)
      by (simp add: case_prod_unfold summable_on_tensor_ell2_right ell2_decompose_summable
          infsum_tensor_ell2_right
          flip: infsum_cblinfun_apply)

    have \<open>(id_cblinfun \<otimes>\<^sub>o (swap_ell2 o\<^sub>C\<^sub>L (V* o\<^sub>C\<^sub>L U) \<otimes>\<^sub>o (U* o\<^sub>C\<^sub>L V))) *\<^sub>V x = x\<close>
      apply (subst (2) x_inv[symmetric])
      apply (subst aux3)
      apply (subst aux3)
      by (auto intro!: 
          simp: cblinfun.scaleC_right sandwich_apply assoc_ell2'_tensor tensor_op_adjoint
          tensor_ell2_scaleC2 tensor_op_ell2 assoc_ell2_tensor \<open>norm \<psi> = 1\<close> cdot_square_norm 
          simp flip: tensor_ell2_ket)
    then have qeq': \<open>x \<in> space_as_set (quantum_equality_full (V* o\<^sub>C\<^sub>L U) \<lbrakk>#2\<rbrakk>\<^sub>q id_cblinfun \<lbrakk>#3.\<rbrakk>\<^sub>q)\<close>
      by (simp add: quantum_equality_full_def apply_qregister_space_qSnd eigenspace_memberI
          flip: eigenspace_tensor_id_left)

    from x1 qeq' show \<open>x \<in> space_as_set (quantum_equality_full U \<lbrakk>#2\<rbrakk> V \<lbrakk>#3.\<rbrakk> \<sqinter> \<lbrakk>#1\<rbrakk> =\<^sub>q \<psi>)\<close>
      by simp
  qed
  then have \<open>(quantum_equality_full U \<lbrakk>#2\<rbrakk> V \<lbrakk>#3.\<rbrakk>  \<sqinter>  \<lbrakk>#1\<rbrakk> =\<^sub>q \<psi>) \<guillemotright> \<lbrakk>T,Q,R\<rbrakk>
             = (quantum_equality_full (U \<otimes>\<^sub>o id_cblinfun) \<lbrakk>#2,#1\<rbrakk> (tensor_ell2_right \<psi> o\<^sub>C\<^sub>L V) \<lbrakk>#3.\<rbrakk>) \<guillemotright> \<lbrakk>T,Q,R\<rbrakk>\<close>
    by (rule arg_cong[where f=\<open>apply_qregister_space _\<close>])
  then show ?thesis
    by (simp add: apply_qregister_space_inf apply_qregister_space_quantum_equality 
        qregister_chain_pair_Fst qregister_chain_pair_Snd
        flip: qregister_chain_apply_space qregister_chain_assoc
        del: lift_inf qregister_chain_apply_space_simp)
qed

lemma swap_variables_subspace_quantum_equality[simp]: 
  "swap_variables_subspace v w (quantum_equality_full U Q V R) = 
      quantum_equality_full U (swap_variables_qvars v w Q) V (swap_variables_qvars v w R)"
proof (cases \<open>qregister \<lbrakk>v,w\<rbrakk>\<close>)
  case True
  then show ?thesis
    by (simp add: swap_variables_subspace_def swap_variables_qvars_def
        apply_qregister_space_transform_qregister
        flip: apply_qregister_space_quantum_equality)
next
  case False
  then show ?thesis
    by (simp add: non_qregister swap_variables_subspace_def swap_variables_qvars_def
        transform_qregister_non_unitary)
qed

(* We flip the lhs/rhs of the quantum equality in addition to changing the indices.
   This is because quantum equalities are typically written with 1-variables on the left and 2-variables on the right. *)
lemma index_flip_subspace_quantum_equality[simp]: 
  "index_flip_subspace (quantum_equality_full U Q V R) = 
      quantum_equality_full V (index_flip_qvar R) U (index_flip_qvar Q)"
  apply (subst (2) quantum_equality_sym)
  using swap_variables_subspace_quantum_equality[where v=qFst and w=qSnd]
  by (auto simp add: swap_variables_subspace_def swap_variables_qvars_def
      index_flip_subspace_def index_flip_qvar_def transform_qregister_swap_ell2
      del: swap_variables_subspace_quantum_equality)

lemma quantum_equality_full_swap_left:
  (* assumes "distinct_qvars (qregister_pair (qregister_pair Q R) S)" *)
  shows "quantum_equality_full U (qregister_pair Q R) V S
       = quantum_equality_full (U o\<^sub>C\<^sub>L swap_ell2) (qregister_pair R Q) V S"
  using quantum_equality_transform_register_left[where W=swap_ell2
      and Q=\<open>\<lbrakk>Q,R\<rbrakk>\<close> and U=\<open>U o\<^sub>C\<^sub>L swap_ell2\<close> and V=V and R=S]
  by (simp add: cblinfun_compose_assoc transform_qregister_swap_ell2)

lemma quantum_equality_full_swap_right:
  (* assumes "distinct_qvars (qregister_pair (qregister_pair Q R) S)" *)
  shows "quantum_equality_full U Q V (qregister_pair R S)
       = quantum_equality_full U Q (V o\<^sub>C\<^sub>L comm_op) (qregister_pair S R)"
  using quantum_equality_transform_register_right[where W=swap_ell2
      and V=\<open>V o\<^sub>C\<^sub>L swap_ell2\<close> and R=\<open>\<lbrakk>R,S\<rbrakk>\<close> and U=U and Q=Q]
  by (simp add: cblinfun_compose_assoc transform_qregister_swap_ell2)

lemma quantum_equality_fixes_swap:
  \<open>space_as_set (quantum_equality_full U Q V R)
         = {\<psi>. apply_qregister \<lbrakk>Q,R\<rbrakk>\<^sub>q (swap_ell2 o\<^sub>C\<^sub>L (V* o\<^sub>C\<^sub>L U) \<otimes>\<^sub>o (U* o\<^sub>C\<^sub>L V)) \<psi> = \<psi>}\<close>
proof (cases \<open>qcompatible Q R\<close>)
  case True
  then show ?thesis
    by (simp add: quantum_equality_full_def eigenspace_def kernel.rep_eq
        apply_qregister_space_kernel apply_qregister_minus vimage_def cblinfun.diff_left
        del: kernel_lift)
next
  case False
  then show ?thesis
    by (simp add: non_qregister quantum_equality_full_not_compatible)
qed

lemma quantum_equality_merge:
  fixes Q1 :: \<open>('a,'m) qregister\<close> and R1 :: \<open>('b,'m) qregister\<close> and Q2 R2
  fixes U1 :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'j ell2\<close>
  assumes [register]: "qregister \<lbrakk>Q1,R1,Q2,R2\<rbrakk>"
  shows "quantum_equality_full U1 Q1 V1 R1 \<sqinter> quantum_equality_full U2 Q2 V2 R2 
    \<le> quantum_equality_full (U1 \<otimes>\<^sub>o U2) (qregister_pair Q1 Q2) (V1 \<otimes>\<^sub>o V2) (qregister_pair R1 R2)"
proof (rule ccsubspace_leI, rule subsetI)
  fix x :: "'m ell2"
  assume "x \<in> space_as_set (quantum_equality_full U1 Q1 V1 R1 \<sqinter> quantum_equality_full U2 Q2 V2 R2)"
  then have x1: \<open>apply_qregister \<lbrakk>Q1, R1\<rbrakk>\<^sub>q (swap_ell2 o\<^sub>C\<^sub>L (V1* o\<^sub>C\<^sub>L U1) \<otimes>\<^sub>o (U1* o\<^sub>C\<^sub>L V1)) x = x\<close>
    and x2: \<open>apply_qregister \<lbrakk>Q2, R2\<rbrakk>\<^sub>q (swap_ell2 o\<^sub>C\<^sub>L (V2* o\<^sub>C\<^sub>L U2) \<otimes>\<^sub>o (U2* o\<^sub>C\<^sub>L V2)) x = x\<close>
    by (simp_all add: quantum_equality_fixes_swap)
  then have x12: "((comm_op o\<^sub>C\<^sub>L (V1* o\<^sub>C\<^sub>L U1) \<otimes>\<^sub>o (U1* o\<^sub>C\<^sub>L V1)) \<otimes>\<^sub>o (comm_op o\<^sub>C\<^sub>L (V2* o\<^sub>C\<^sub>L U2) \<otimes>\<^sub>o (U2* o\<^sub>C\<^sub>L V2))) \<guillemotright> \<lbrakk>\<lbrakk>Q1,R1\<rbrakk>, \<lbrakk>Q2,R2\<rbrakk>\<rbrakk> *\<^sub>V x = x"
    by (simp add: apply_qregister_pair)

  define t :: \<open>('a\<times>'b) \<times> ('c\<times>'d) \<Rightarrow> _\<close> where \<open>t = (\<lambda>((q1,q2),(r1,r2)). ((q1,r1),(q2,r2)))\<close>
  have \<open>bij t\<close>
    apply (rule o_bij[where g=\<open>\<lambda>((q1,r1),(q2,r2)). ((q1,q2),(r1,r2))\<close>])
    by (auto intro!: ext simp: t_def)
  define T :: \<open>(('a\<times>'b) \<times> ('c\<times>'d)) ell2 \<Rightarrow>\<^sub>C\<^sub>L _\<close> where \<open>T = classical_operator (Some o t)\<close>
  have ex_T: \<open>classical_operator_exists (Some o t)\<close>
    using \<open>bij t\<close> bij_betw_imp_inj_on classical_operator_exists_inj inj_map_total by blast
  have [simp]: \<open>unitary T\<close>
    using \<open>bij t\<close> by (simp add: T_def unitary_classical_operator)
  have applyT: \<open>T *\<^sub>V ket ((q1,q2),(r1,r2)) = ket ((q1,r1),(q2,r2))\<close> for q1 q2 r1 r2
    using ex_T by (simp add: T_def classical_operator_ket t_def)
  have applyTadj: \<open>T* *\<^sub>V ket ((q1,r1),(q2,r2)) = ket ((q1,q2),(r1,r2))\<close> for q1 q2 r1 r2
    using arg_cong[OF applyT, where f=\<open>cblinfun_apply (T*)\<close>]
    by (simp flip: cblinfun_apply_cblinfun_compose)
  have sandwichT: \<open>sandwich T *\<^sub>V (aa \<otimes>\<^sub>o ba) \<otimes>\<^sub>o ab \<otimes>\<^sub>o bb = (aa \<otimes>\<^sub>o ab) \<otimes>\<^sub>o ba \<otimes>\<^sub>o bb\<close> for aa ba ab bb
    apply (auto intro!: equal_ket cinner_ket_eqI simp: sandwich_apply applyTadj
        simp flip: cinner_adj_left[of T])
    by (simp add: tensor_op_ell2 flip: tensor_ell2_ket)

    have QR12_T: \<open>\<lbrakk>\<lbrakk>Q1,R1\<rbrakk>, \<lbrakk>Q2,R2\<rbrakk>\<rbrakk> = qregister_chain \<lbrakk>\<lbrakk>Q1,Q2\<rbrakk>, \<lbrakk>R1,R2\<rbrakk>\<rbrakk> (transform_qregister T)\<close>
      apply (intro qregister_eqI_separating separating_tensor')
             apply (rule separating_UNIV refl)+
      apply (auto simp: apply_qregister_transform_qregister sandwichT apply_qregister_pair)
      by (metis (no_types, lifting) assms lift_cblinfun_comp(2) qcompatible3' qcompatible_commute)

  have \<open>(comm_op o\<^sub>C\<^sub>L (((V1 \<otimes>\<^sub>o V2)* o\<^sub>C\<^sub>L (U1 \<otimes>\<^sub>o U2)) \<otimes>\<^sub>o ((U1 \<otimes>\<^sub>o U2)* o\<^sub>C\<^sub>L (V1 \<otimes>\<^sub>o V2)))) \<guillemotright> \<lbrakk>\<lbrakk>Q1,Q2\<rbrakk>, \<lbrakk>R1,R2\<rbrakk>\<rbrakk>
          = ((comm_op o\<^sub>C\<^sub>L (V1* o\<^sub>C\<^sub>L U1) \<otimes>\<^sub>o (U1* o\<^sub>C\<^sub>L V1)) \<otimes>\<^sub>o (comm_op o\<^sub>C\<^sub>L (V2*\<cdot>U2) \<otimes>\<^sub>o (U2*\<cdot>V2))) \<guillemotright> \<lbrakk>\<lbrakk>Q1,R1\<rbrakk>, \<lbrakk>Q2,R2\<rbrakk>\<rbrakk>\<close>
    apply (auto intro!: equal_ket cinner_ket_eqI
        simp add: QR12_T apply_qregister_transform_qregister sandwich_apply applyTadj tensor_op_adjoint
        simp flip: cinner_adj_left[of T])
    by (simp add: tensor_op_ell2 flip: tensor_ell2_ket)

  with x12 show \<open>x \<in> space_as_set (quantum_equality_full (U1 \<otimes>\<^sub>o U2) \<lbrakk>Q1, Q2\<rbrakk>\<^sub>q (V1 \<otimes>\<^sub>o V2) \<lbrakk>R1, R2\<rbrakk>\<^sub>q)\<close>
    by (simp add: quantum_equality_fixes_swap)
qed

lemma translate_to_index_registers_qeq[translate_to_index_registers]:
  fixes F :: \<open>('a,'b) qregister\<close>
  assumes \<open>TTIR_LUB F G FG F' G'\<close>
  shows \<open>TTIR_APPLY_QREGISTER_SPACE (quantum_equality_full U F V G)
          FG (quantum_equality_full U F' V G')\<close>
  using assms 
  by (simp add: quantum_equality_full_def TTIR_APPLY_QREGISTER_SPACE_def TTIR_LUB_def
      flip: qregister_chain_pair)


section \<open>Common quantum objects\<close>

lemma adjoint_CNOT[simp]: "CNOT* = CNOT"
  by simp

lemma CNOT_CNOT[simp]: "CNOT \<cdot> CNOT = id_cblinfun"
  apply (rule equal_ket)
  by auto

(* definition [code del]: "CNOT = classical_operator (Some o (\<lambda>(x::bit,y). (x,y+x)))" for CNOT *)
lemma unitaryCNOT[simp]: "unitary CNOT"
  apply (rule unitaryI)
  by simp_all

(* definition [code del]: "pauliX = classical_operator (Some o (\<lambda>x::bit. x+1))" *)
lemma unitaryX[simp]: "unitary pauliX"
  by (simp add: unitary_def)

lemmas adjoint_X[simp] = pauliX_adjoint

lemmas X_X[simp] = pauliXX

lemmas adjoint_H[simp] = hada_adj

lemma H_H[simp]: "hadamard o\<^sub>C\<^sub>L hadamard = id_cblinfun"
  by eval

lemma unitaryH[simp]: "unitary hadamard"
  apply (rule unitaryI)
  by simp_all

lemma unitaryZ[simp]: "unitary pauliZ"
  by (simp add: unitary_def)

lemmas adjoint_Z[simp] = pauliZ_adjoint

lemmas Z_Z[simp] = pauliZZ

definition "matrix_pauliY = mat_of_rows_list 2 [ [0, - imaginary_unit], [imaginary_unit, 0] ]"
definition pauliY :: \<open>(bit, bit) matrix\<close> where [code del]: "pauliY = cblinfun_of_mat matrix_pauliY"
lemma mat_of_cblinfun_pauliY[simp, code]: "mat_of_cblinfun pauliY = matrix_pauliY"
  apply (auto simp add: pauliY_def matrix_pauliY_def)
  apply (subst cblinfun_of_mat_inverse)
  by (auto)
lemma adjoint_Y[simp]: "pauliY* = pauliY"
  by eval
lemma Y_Y[simp]: "pauliY o\<^sub>C\<^sub>L pauliY = id_cblinfun"
  by eval

abbreviation EPR :: "(bit*bit) ell2" where \<open>EPR \<equiv> \<beta>00\<close>
lemmas EPR_normalized = norm_\<beta>00

definition "Uoracle f = classical_operator (Some o (\<lambda>(x,y::_::group_add). (x, y + (f x))))"

lemma unitary_Uoracle[simp]: "unitary (Uoracle f)"
  unfolding Uoracle_def
  apply (rule unitary_classical_operator, rule bijI)
   apply (simp add: inj_on_def)
  apply (auto simp: image_def)
  by (metis diff_add_cancel)

lemma Uoracle_adjoint: "(Uoracle f)* = classical_operator (Some o (\<lambda>(x,y::_::group_add). (x, y - (f x))))" 
      (is "_ = classical_operator (Some o ?pi)")
proof -
  define \<pi> where "\<pi> = ?pi"
  have [simp]: "surj \<pi>"
    apply (auto simp: \<pi>_def image_def)
    by (metis add_diff_cancel)

  define \<pi>2 where "\<pi>2 = (\<lambda>(x,y). (x, y + (f x)))"
  have "\<pi>2 o \<pi> = id"
    unfolding \<pi>_def \<pi>2_def by auto
  with \<open>surj \<pi>\<close> have [simp]: "surj \<pi>2"
    by (metis fun.set_map surj_id)
  have "\<pi> o \<pi>2 = id"
    unfolding \<pi>_def \<pi>2_def by auto
  then have [simp]: "inj \<pi>2"
    using \<open>\<pi>2 \<circ> \<pi> = id\<close> inj_iff inv_unique_comp by blast

  have "Hilbert_Choice.inv \<pi>2 = \<pi>"
    using inv_unique_comp
    using \<open>\<pi> \<circ> \<pi>2 = id\<close> \<open>\<pi>2 \<circ> \<pi> = id\<close> by blast

  then have "inv_map (Some o \<pi>2) = Some o \<pi>"
    by (subst inv_map_total, simp_all)

  then have "(classical_operator (Some \<circ> \<pi>2))* = classical_operator (Some o \<pi>)"
    apply (subst classical_operator_adjoint)
    by simp_all

  then show ?thesis
    unfolding \<pi>_def \<pi>2_def Uoracle_def by auto
qed

lemma Uoracle_selfadjoint[simp]: "(Uoracle f)* = Uoracle f" for f :: "_ \<Rightarrow> _::xor_group"
  unfolding Uoracle_adjoint unfolding Uoracle_def by simp

lemma Uoracle_selfinverse[simp]: "Uoracle f \<cdot> Uoracle f = id_cblinfun" for f :: "_ \<Rightarrow> _::xor_group"
  apply (subst Uoracle_selfadjoint[symmetric]) apply (rule isometryD) by simp

lemma applyOp_Uoracle[simp]:
  shows "Uoracle f \<cdot> ket (x, y) = ket (x, y + f x)"
  unfolding Uoracle_def
  apply (subst classical_operator_ket)
  by (auto simp: inj_on_def intro: classical_operator_exists_inj)

lemma applyOp_Uoracle'[simp]:
  shows "Uoracle f \<cdot> (ket x \<otimes>\<^sub>s ket y) = ket x \<otimes>\<^sub>s ket (y + f x)"
  by (simp flip: ket_product)


lemma Uoracle_twice[simp]: 
  fixes f :: "_ \<Rightarrow> _::xor_group"
  assumes "distinct_qvars Q"
  shows "Uoracle f\<guillemotright>Q \<cdot> (Uoracle f\<guillemotright>Q *\<^sub>S S) = (S::_ ccsubspace)"
  apply (subst Uoracle_selfadjoint[symmetric])
  using assms by (simp del: Uoracle_selfadjoint flip: adjoint_lift cblinfun_compose_assoc add: cblinfun_assoc_left)


definition "proj_classical_set S = Proj (ccspan {ket s|s. s\<in>S})"

lemma is_Proj_proj_classical_set[simp]: "is_Proj (proj_classical_set S)"
  unfolding proj_classical_set_def by simp


section \<open>Misc\<close>

lemma bij_add_const[simp]: "bij (\<lambda>x. x+(y::_::ab_group_add))" 
  apply (rule bijI') apply simp
  apply (rename_tac z) apply (rule_tac x="z-y" in exI)
  by auto

lemma bij_bit_of_bool[simp]: "bij (\<lambda>x. of_bool (f x) :: bit) \<longleftrightarrow> bij f"
proof rule
  have bij_of_bool: "bij (of_bool :: _ \<Rightarrow> bit)"
    by (smt (verit, best) add_bit_eq_xor bijI' diff_add_cancel of_bool_eq_iff xor_bit_def)
  then show "bij (\<lambda>x. of_bool (f x) :: bit)" if "bij f"
    using Fun.bij_comp[of f of_bool] that unfolding o_def by simp
  show "bij f" if "bij (\<lambda>x. of_bool (f x) :: bit)"
    using that bij_of_bool
    by (smt (verit, best) bijI' bij_pointE)
qed

lemma bij_equal_bit[simp]: "bij (\<lambda>x::bit. x=y)" 
  apply (rule bijI') apply simp by (meson bit_neq)


declare imp_conjL[simp]

typedef infinite = "UNIV::nat set" ..
lemma infinite_infinite[simp]: "infinite (UNIV::infinite set)"
  by (metis (full_types) Abs_infinite_inverse UNIV_I ex_new_if_finite finite_imageI image_eqI infinite_UNIV_nat)
(* derive universe infinite *)
declare infinite_UNIV_listI[simp]

section "ML Code"

ML_file \<open>qrhl.ML\<close>

section "Simprocs"

simproc_setup distinct_qvars_guard_simproc (\<open>DISTINCT_QVARS_GUARD t\<close>) = QRHL.distinct_qvars_guard_simproc

end
