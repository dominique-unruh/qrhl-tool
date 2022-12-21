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
  
definition classical_subspace :: "bool \<Rightarrow> predicate"  ("\<CC>\<ll>\<aa>[_]")
  where "\<CC>\<ll>\<aa>[b] = (if b then top else bot)"
syntax classical_subspace :: "bool \<Rightarrow> predicate"  ("Cla[_]")

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

(* TODO move *)
definition \<open>Uswap = classical_operator (\<lambda>(x,y). Some(y,x))\<close> for Uswap

definition index_flip_vector :: "qu2 ell2 \<Rightarrow> qu2 ell2" where \<open>index_flip_vector \<psi> = Uswap *\<^sub>V \<psi>\<close>

axiomatization swap_variables_vector :: "'a q2variable \<Rightarrow> 'a q2variable \<Rightarrow> qu2 ell2 \<Rightarrow> qu2 ell2"

definition index_flip_subspace :: "qu2 ell2 ccsubspace \<Rightarrow> qu2 ell2 ccsubspace"
  where \<open>index_flip_subspace S = Uswap *\<^sub>S S\<close>

lemma index_flip_subspace_INF[simp]: \<open>index_flip_subspace (INF i\<in>A. S i) = (INF i\<in>A. index_flip_subspace (S i))\<close>
  by (cheat index_flip_subspace_INF)

axiomatization swap_variables_subspace :: "'a q2variable \<Rightarrow> 'a q2variable \<Rightarrow> qu2 ell2 ccsubspace \<Rightarrow> qu2 ell2 ccsubspace"

lemma index_flip_subspace_top[simp]: "index_flip_subspace top = top"
  by (cheat index_flip_subspace_top)
lemma index_flip_subspace_bot[simp]: "index_flip_subspace bot = bot"
  by (cheat index_flip_subspace_bot)
lemma index_flip_subspace_zero[simp]: "index_flip_subspace 0 = 0"
  by simp
lemma index_flip_subspace_Cla[simp]: "index_flip_subspace (Cla[b]) = Cla[b]"
  by auto
lemma index_flip_subspace_inf[simp]: "index_flip_subspace (A\<sqinter>B) = (index_flip_subspace A) \<sqinter> (index_flip_subspace B)"
  by (cheat index_flip_subspace_inf)
lemma index_flip_subspace_plus[simp]: "index_flip_subspace (A+B) = (index_flip_subspace A) + (index_flip_subspace B)"
  by (cheat index_flip_subspace_plus)

lemma swap_variables_subspace_top[simp]: "swap_variables_subspace v w top = top"
  by (cheat swap_variables_subspace_top)
lemma swap_variables_subspace_bot[simp]: "swap_variables_subspace v w bot = bot"
  by (cheat swap_variables_subspace_bot)
lemma swap_variables_subspace_zero[simp]: "swap_variables_subspace v w 0 = 0"
  by simp
lemma swap_variables_subspace_Cla[simp]: "swap_variables_subspace v w (Cla[b]) = Cla[b]"
  by auto
lemma swap_variables_subspace_inf[simp]: "swap_variables_subspace v w (A\<sqinter>B) = (swap_variables_subspace v w A) \<sqinter> (swap_variables_subspace v w B)"
  by (cheat swap_variables_subspace_inf)
lemma swap_variables_subspace_plus[simp]: "swap_variables_subspace v w (A+B) = (swap_variables_subspace v w A) + (swap_variables_subspace v w B)"
  by (cheat swap_variables_subspace_plus)

subsection "Distinct quantum variables"

abbreviation (input) qvariables_local :: \<open>'a q2variable \<Rightarrow> 'b q2variable \<Rightarrow> bool\<close> where
  \<open>qvariables_local Q R \<equiv> Qqcompatible (QCOMPLEMENT (QREGISTER_of R)) Q\<close>

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

axiomatization operator_local :: "(qu2,qu2) l2bounded \<Rightarrow> 'a q2variable \<Rightarrow> bool" 

axiomatization predicate_local :: "predicate \<Rightarrow> 'a q2variable \<Rightarrow> bool"

axiomatization distinct_qvars_pred_vars :: "predicate \<Rightarrow> 'a q2variable \<Rightarrow> bool"

axiomatization distinct_qvars_op_vars :: "(qu2,qu2) l2bounded \<Rightarrow> 'a q2variable \<Rightarrow> bool"

axiomatization distinct_qvars_op_pred :: "(qu2,qu2) l2bounded \<Rightarrow> predicate \<Rightarrow> bool"

abbreviation (input) \<open>colocal_op_pred == distinct_qvars_op_pred\<close> (* Legacy *)
abbreviation (input) \<open>colocal_op_qvars == distinct_qvars_op_vars\<close> (* Legacy *)
abbreviation (input) \<open>colocal_pred_qvars == distinct_qvars_pred_vars\<close> (* Legacy *)

consts colocal :: "'a \<Rightarrow> 'b \<Rightarrow> bool" (* Legacy *)
adhoc_overloading colocal \<open>\<lambda>x y. distinct_qvars_pred_vars x y\<close> \<open>\<lambda>x y. distinct_qvars_op_vars x y\<close> \<open>\<lambda>x y. distinct_qvars_op_pred x y\<close>
(* Having non-eta reduced terms in the adhoc_overloading effectively makes the overloading input-only,
   as appropropriate for a legacy name *)

lemma colocal_pred_qvars_unit[simp]: "colocal_pred_qvars A \<lbrakk>\<rbrakk>"
  by (cheat colocal_pred_qvars_unit)
lemma colocal_pred_qvars_unit'[simp]: "colocal_pred_qvars A empty_qregister"
  by (cheat colocal_pred_qvars_unit)

lemma colocal_op_qvars_unit[simp]: "colocal_op_qvars A \<lbrakk>\<rbrakk>"
  by (cheat colocal_op_qvars_unit)
lemma colocal_op_qvars_unit'[simp]: "colocal_op_qvars A empty_qregister"
  by (cheat colocal_op_qvars_unit)

lemma colocal_pred_qvars_top[simp,intro]:
  assumes \<open>qregister F\<close>
  shows \<open>colocal_pred_qvars \<top> F\<close>
  sorry

lemma colocal_pred_qvars_bot[simp,intro]:
  assumes \<open>qregister F\<close>
  shows \<open>colocal_pred_qvars \<bottom> F\<close>
  sorry

lemma colocal_pred_qvars_pair[simp,intro]:
  assumes \<open>qcompatible F G\<close>
  assumes \<open>colocal_pred_qvars S F\<close>
  assumes \<open>colocal_pred_qvars S G\<close>
  shows \<open>colocal_pred_qvars S (qregister_pair F G)\<close>
  sorry

lemma colocal_pred_qvars_apply_qregister_space[simp]:
  assumes \<open>qcompatible F G\<close>
  shows \<open>colocal_pred_qvars (apply_qregister_space F S) G\<close>
  sorry

lemma colocal_op_qvars_apply_qregister[simp]:
  assumes \<open>qcompatible F G\<close>
  shows \<open>colocal_op_qvars (apply_qregister F S) G\<close>
  sorry

lemma distinct_qvars_pred_vars_top[simp]: \<open>qregister X \<Longrightarrow> distinct_qvars_pred_vars top X\<close>
  sorry
lemma distinct_qvars_pred_vars_bot[simp]: \<open>qregister X \<Longrightarrow> distinct_qvars_pred_vars bot X\<close>
  sorry
lemma distinct_qvars_pred_vars_cla[simp]: \<open>qregister X \<Longrightarrow> distinct_qvars_pred_vars Cla[x] X\<close>
  by simp


lemma predicate_local_inf[intro!]: "predicate_local S Q \<Longrightarrow> predicate_local T Q \<Longrightarrow> predicate_local (S\<sqinter>T) Q"
  by (cheat predicate_local_inf)
lemma predicate_local_applyOpSpace[intro!]: "operator_local A Q \<Longrightarrow> predicate_local S Q \<Longrightarrow> predicate_local (A\<cdot>S) Q"
  by (cheat predicate_local_applyOpSpace)
lemma operator_local_timesOp[intro!]: "operator_local A Q \<Longrightarrow> operator_local B Q \<Longrightarrow> operator_local (A\<cdot>B) Q"
  by (cheat operator_local_timesOp)

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
  by (cheat predicate_localE)

lemma operator_localE:
  assumes "operator_local S Q"
  shows "\<exists>S'. S=S'\<guillemotright>Q"
  by (cheat operator_localE)

lemma lift_predicate_local[intro!]: "qvariables_local R Q \<Longrightarrow> predicate_local (S\<guillemotright>R) Q"
  by (cheat lift_predicate_local)
lemma lift_operator_local[intro!]: "qvariables_local R Q \<Longrightarrow> operator_local (S\<guillemotright>R) Q"
  by (cheat lift_operator_local)

lemma adjoint_lift[simp]: "adj (liftOp U Q) = liftOp (adj U) Q" 
  by (cheat adjoint_lift)
lemma scaleC_lift[simp]: "c *\<^sub>C (A\<guillemotright>Q) = (c *\<^sub>C A) \<guillemotright> Q" for A :: "(_,_) bounded"
  by (cheat scaleC_lift)
lemma norm_lift[simp]:
  "distinct_qvars Q \<Longrightarrow> norm (X\<guillemotright>Q) = norm X"
  by (cheat norm_lift)
lemma imageOp_lift[simp]: "applyOpSpace (liftOp U Q) top = liftSpace (applyOpSpace U top) Q"
  apply (cases \<open>qregister Q\<close>) defer
  unfolding apply_qregister_space_def
  apply (simp add: non_qregister non_qregister.rep_eq non_qregister_raw_def) 
  by (cheat imageOp_lift)
lemma applyOpSpace_lift[simp]: "applyOpSpace (liftOp U Q) (liftSpace S Q) = liftSpace (applyOpSpace U S) Q"
  by (cheat applyOpSpace_lift)
lemma top_lift[simp]: "distinct_qvars Q \<Longrightarrow> liftSpace top Q = top"
  by (cheat top_lift)
lemma bot_lift[simp]: "liftSpace bot Q = bot"
  by (cheat bot_lift)
lemma unitary_lift[simp]: "distinct_qvars Q \<Longrightarrow> unitary (liftOp U Q) = unitary U"
  by (cheat unitary_lift)
lemma tensor_lift: 
  fixes A B :: "_ subspace"
  assumes "distinct_qvars (qregister_pair Q R)"
  shows "(A\<otimes>B)\<guillemotright>(qregister_pair Q R) = (A\<guillemotright>Q) \<sqinter> (B\<guillemotright>R)"
  by (cheat tensor_lift)

lemma lift_inf[simp]: "S\<guillemotright>Q \<sqinter> T\<guillemotright>Q = (S \<sqinter> T)\<guillemotright>Q" for S::"'a subspace"
  by (cheat lift_inf)
lemma lift_leq[simp]: "distinct_qvars Q \<Longrightarrow> (S\<guillemotright>Q \<le> T\<guillemotright>Q) = (S \<le> T)" for S::"'a subspace"
  by (cheat lift_leq)
lemma lift_eqSp[simp]: "distinct_qvars Q \<Longrightarrow> (S\<guillemotright>Q = T\<guillemotright>Q) = (S = T)" for S T :: "'a subspace" 
  by (cheat lift_eqSp)
lemma lift_eqOp[simp]: "distinct_qvars Q \<Longrightarrow> (S\<guillemotright>Q = T\<guillemotright>Q) = (S = T)" for S T :: "('a,'a) l2bounded" 
  by (cheat TODO11)
lemma lift_plus[simp]: "S\<guillemotright>Q + T\<guillemotright>Q = (S + T)\<guillemotright>Q" for S T :: "'a subspace"  
  by (cheat TODO11)
lemma lift_sup[simp]: "S\<guillemotright>Q \<squnion> T\<guillemotright>Q = (S \<squnion> T)\<guillemotright>Q" for S T :: "'a subspace"  
  by (cheat TODO11)
lemma lift_plusOp[simp]: "S\<guillemotright>Q + T\<guillemotright>Q = (S + T)\<guillemotright>Q" for S T :: "('a,'a) l2bounded"  
  by (cheat TODO11)
lemma lift_uminusOp[simp]: "- (T\<guillemotright>Q) = (- T)\<guillemotright>Q" for T :: "('a,'a) l2bounded"  
  (* unfolding uminus_l2bounded_def by simp *)
  by (cheat lift_uminusOp)
lemma lift_minusOp[simp]: "S\<guillemotright>Q - T\<guillemotright>Q = (S - T)\<guillemotright>Q" for S T :: "('a,'a) l2bounded"  
  (* unfolding minus_l2bounded_def by simp *)
  by (cheat lift_minusOp)
lemma lift_timesOp[simp]: "S\<guillemotright>Q \<cdot> T\<guillemotright>Q = (S \<cdot> T)\<guillemotright>Q" for S T :: "('a,'a) l2bounded"  
  by (cheat TODO11)
lemma lift_ortho[simp]: "distinct_qvars Q \<Longrightarrow> - (S\<guillemotright>Q) = (- S)\<guillemotright>Q" for Q :: "'a q2variable" and S :: "'a ell2 ccsubspace"
  by (cheat TODO11)
lemma lift_tensorOp: "distinct_qvars (qregister_pair Q R) \<Longrightarrow> (S\<guillemotright>Q) \<cdot> (T\<guillemotright>R) = (S \<otimes>\<^sub>o T)\<guillemotright>qregister_pair Q R" for Q :: "'a q2variable" and R :: "'b q2variable" and S T :: "(_,_) l2bounded" 
  by (cheat TODO11)
lemma lift_tensorSpace: "distinct_qvars (qregister_pair Q R) \<Longrightarrow> (S\<guillemotright>Q) = (S \<otimes> top)\<guillemotright>qregister_pair Q R" for Q :: "'a q2variable" and R :: "'b q2variable" and S :: "_ subspace" 
  by (cheat TODO11)
lemma lift_id_cblinfun[simp]: "distinct_qvars Q \<Longrightarrow> id_cblinfun\<guillemotright>Q = id_cblinfun" for Q
  by (cheat TODO11)
lemma INF_lift: "(INF x. S x\<guillemotright>Q) = (INF x. S x)\<guillemotright>Q" for Q::"'a q2variable" and S::"'b \<Rightarrow> 'a subspace"
  by (cheat TODO11)
lemma Cla_inf_lift: "Cla[b] \<sqinter> (S\<guillemotright>Q) = (if b then S else bot)\<guillemotright>Q" by auto
lemma Cla_plus_lift: "distinct_qvars Q \<Longrightarrow> Cla[b] + (S\<guillemotright>Q) = (if b then top else S)\<guillemotright>Q" by auto
lemma Cla_sup_lift: "distinct_qvars Q \<Longrightarrow> Cla[b] \<squnion> (S\<guillemotright>Q) = (if b then top else S)\<guillemotright>Q" by auto
lemma Proj_lift[simp]: "Proj (S\<guillemotright>Q) = (Proj S)\<guillemotright>Q"
  for Q::"'a q2variable"
  by (cheat Proj_lift)
lemma kernel_lift[simp]: "distinct_qvars Q \<Longrightarrow> kernel (A\<guillemotright>Q) = (kernel A)\<guillemotright>Q" for Q
  by (cheat TODO11)
lemma eigenspace_lift[simp]: "distinct_qvars Q \<Longrightarrow> eigenspace a (A\<guillemotright>Q) = (eigenspace a A)\<guillemotright>Q" for Q
  unfolding eigenspace_def apply (subst lift_id_cblinfun[symmetric, of Q], assumption)
  apply (simp del: lift_id_cblinfun)
  by (metis (no_types, lifting) apply_qregister_of_id kernel_lift lift_minusOp scaleC_lift)

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
  by (cheat colocal_op_commute)

lemma remove_qvar_unit_op:
  "(remove_qvar_unit_op \<cdot> A \<cdot> remove_qvar_unit_op*)\<guillemotright>Q = A\<guillemotright>(qregister_pair Q \<lbrakk>\<rbrakk>)"
for A::"(_,_)l2bounded" and Q::"'a q2variable"
  by (cheat TODO12)


lemma colocal_op_pred_lift1[simp,intro!]:
 "colocal_pred_qvars S Q \<Longrightarrow> colocal_op_pred (U\<guillemotright>Q) S"
for Q :: "'a q2variable" and U :: "('a,'a) l2bounded" and S :: predicate
  by (cheat TODO12)


lemma lift_extendR:
  assumes "distinct_qvars \<lbrakk>Q,R\<rbrakk>"
  shows "U\<guillemotright>Q = (U \<otimes>\<^sub>o id_cblinfun)\<guillemotright>\<lbrakk>Q,R\<rbrakk>"
  apply (subst apply_qregister_pair)
  using assms qregister_pair_iff_compatible apply blast
  by (metis apply_qregister_of_id assms cblinfun_compose_id_right distinct_qvarsR)

lemma lift_extendL:
  assumes "distinct_qvars (qregister_pair Q R)"
  shows "U\<guillemotright>Q = (id_cblinfun \<otimes>\<^sub>o U)\<guillemotright>(qregister_pair R Q)"
  apply (subst apply_qregister_pair)
  using assms distinct_qvars_swap qregister_pair_iff_compatible apply blast
  by (metis apply_qregister_of_id assms cblinfun_compose_id_left distinct_qvarsR)

lemma move_sup_meas_rule:
  fixes Q::"'a q2variable"
  assumes "distinct_qvars Q"
  assumes "(Proj C)\<guillemotright>Q \<cdot> A \<le> B"
  shows "A \<le> (B\<sqinter>C\<guillemotright>Q) \<squnion> (- C)\<guillemotright>Q"
  apply (rule ccsubspace_supI_via_Proj) 
  using Proj_image_leq[of "C\<guillemotright>Q"] assms by simp

lemma span_lift: "distinct_qvars Q \<Longrightarrow> ccspan G \<guillemotright> Q = ccspan {lift_vector \<psi> Q \<psi>' | \<psi> \<psi>'. \<psi>\<in>G \<and> \<psi>' \<in> lift_rest Q}"
  by (cheat span_lift)

lemma index_flip_subspace_lift[simp]: "index_flip_subspace (S\<guillemotright>Q) = S \<guillemotright> index_flip_qvar Q"
  by (cheat index_flip_subspace_lift)

lemma swap_variables_subspace_lift[simp]: "swap_variables_subspace v w (S\<guillemotright>Q) = S \<guillemotright> swap_variables_vars v w Q"
  by (cheat index_flip_subspace_lift)

lemma apply_qregister_qFst: \<open>apply_qregister qFst a = a \<otimes>\<^sub>o id_cblinfun\<close>
  by (simp add: Laws_Quantum.Fst_def qFst.rep_eq)

lemma apply_qregister_qSnd: \<open>apply_qregister qSnd b = id_cblinfun \<otimes>\<^sub>o b\<close>
  by (simp add: Laws_Quantum.Snd_def qSnd.rep_eq)

(* TODO move *)
lemma apply_qregister_space_qFst: \<open>apply_qregister_space qFst S = S \<otimes>\<^sub>S \<top>\<close>
  by (simp add: apply_qregister_space_def tensor_ccsubspace_via_Proj apply_qregister_qFst flip: imageOp_lift)

(* TODO move *)
lemma apply_qregister_space_qSnd: \<open>apply_qregister_space qSnd S = \<top> \<otimes>\<^sub>S S\<close>
  by (simp add: apply_qregister_space_def tensor_ccsubspace_via_Proj apply_qregister_qSnd flip: imageOp_lift)

(* TODO move *)
lemma tensor_ccsubspace_ccspan: \<open>ccspan X \<otimes>\<^sub>S ccspan Y = ccspan {x \<otimes>\<^sub>s y | x y. x \<in> X \<and> y \<in> Y}\<close>
  apply (simp add: tensor_ccsubspace_def)
  sorry

lemma ket_less_specific:
  assumes "qregister \<lbrakk>X,Y\<rbrakk>"
  shows "ccspan {ket (x,y)}\<guillemotright>qregister_pair X Y \<le> ccspan {ket y}\<guillemotright>Y"
proof -
  have \<open>apply_qregister_space \<lbrakk>X, Y\<rbrakk>\<^sub>q (ccspan {|(x, y)\<rangle>}) = apply_qregister_space \<lbrakk>X, Y\<rbrakk>\<^sub>q (ccspan {|x\<rangle>} \<otimes>\<^sub>S ccspan {|y\<rangle>})\<close>
    by (simp add: tensor_ccsubspace_ccspan tensor_ell2_ket)
  also have \<open>\<dots> \<le> apply_qregister_space \<lbrakk>X, Y\<rbrakk>\<^sub>q (\<top> \<otimes>\<^sub>S ccspan {|y\<rangle>})\<close>
    by (smt (verit) assms distinct_qvarsL dual_order.trans inf.bounded_iff inf.cobounded2 tensor_lift top_greatest top_leq_lift)
  also have \<open>\<dots> = ccspan {|y\<rangle>} \<guillemotright> (qregister_chain \<lbrakk>X, Y\<rbrakk>\<^sub>q qSnd)\<close>
    by (metis assms distinct_qvarsL inf.absorb_iff2 qregister_chain_pair_Snd qregister_pair_iff_compatible tensor_lift top.extremum top_lift)
  also have \<open>\<dots> = ccspan {ket y}\<guillemotright>Y\<close>
    by (metis assms qregister_chain_pair_Snd qregister_pair_iff_compatible)
  finally show ?thesis
    by -
qed


lemma comm_op_twice[simp]: "distinct_qvars Q \<Longrightarrow> comm_op\<guillemotright>Q \<cdot> (comm_op\<guillemotright>Q \<cdot> S) = (S::_ ccsubspace)"
  apply (subst adjoint_swap_ell2[symmetric])
  by (simp del: adjoint_swap_ell2 flip: adjoint_lift cblinfun_compose_assoc add: cblinfun_assoc_left)

lemma translate_to_index_registers_compose[translate_to_index_registers]:
  assumes \<open>qregister FG \<and> F = qregister_chain FG F' \<and> G = qregister_chain FG G'\<close>
  shows \<open>cblinfun_compose (apply_qregister F A') (apply_qregister G B') \<equiv>
          apply_qregister FG (cblinfun_compose (apply_qregister F' A') 
                                               (apply_qregister G' B'))\<close>
  using assms by simp

lemma translate_to_index_registers_plus_op[translate_to_index_registers]:
  assumes \<open>qregister FG \<and> F = qregister_chain FG F' \<and> G = qregister_chain FG G'\<close>
  shows \<open>plus (apply_qregister F A') (apply_qregister G B') \<equiv>
          apply_qregister FG (plus (apply_qregister F' A') 
                                               (apply_qregister G' B'))\<close>
  using assms by simp

lemma translate_to_index_registers_minus_op[translate_to_index_registers]:
  assumes \<open>qregister FG \<and> F = qregister_chain FG F' \<and> G = qregister_chain FG G'\<close>
  shows \<open>minus (apply_qregister F A') (apply_qregister G B') \<equiv>
          apply_qregister FG (minus (apply_qregister F' A') 
                                   (apply_qregister G' B'))\<close>
  using assms by simp

lemma translate_to_index_registers_cblinfun_image[translate_to_index_registers]:
  assumes \<open>qregister FG \<and> F = qregister_chain FG F' \<and> G = qregister_chain FG G'\<close>
  shows \<open>cblinfun_image (apply_qregister F A') (apply_qregister_space G B') \<equiv>
          apply_qregister_space FG (cblinfun_image (apply_qregister F' A') 
                                   (apply_qregister_space G' B'))\<close>
  using assms apply (simp flip: applyOpSpace_lift)
  sorry


lemma translate_to_index_registers_eq_op[translate_to_index_registers]:
  assumes \<open>qregister FG \<and> F = qregister_chain FG F' \<and> G = qregister_chain FG G'\<close>
  shows \<open>(apply_qregister F A') = (apply_qregister G B') \<equiv>
         (apply_qregister F' A') = (apply_qregister G' B')\<close>
  using assms by simp


(* TODO move *)
lemma apply_qregister_space_chain: \<open>apply_qregister_space (qregister_chain F G) S = apply_qregister_space F (apply_qregister_space G S)\<close>
  sorry

lemma translate_to_index_registers_inf[translate_to_index_registers]:
  assumes \<open>qregister FG \<and> F = qregister_chain FG F' \<and> G = qregister_chain FG G'\<close>
  shows \<open>inf (apply_qregister_space F A') (apply_qregister_space G B') \<equiv>
          apply_qregister_space FG (inf (apply_qregister_space F' A') (apply_qregister_space G' B'))\<close>
  using assms by (auto simp add: apply_qregister_space_chain)

lemma translate_to_index_registers_sup[translate_to_index_registers]:
  assumes \<open>qregister FG \<and> F = qregister_chain FG F' \<and> G = qregister_chain FG G'\<close>
  shows \<open>sup (apply_qregister_space F A') (apply_qregister_space G B') \<equiv>
          apply_qregister_space FG (sup (apply_qregister_space F' A') (apply_qregister_space G' B'))\<close>
  using assms by (auto simp add: apply_qregister_space_chain)

lemma translate_to_index_registers_plus_space[translate_to_index_registers]:
  assumes \<open>qregister FG \<and> F = qregister_chain FG F' \<and> G = qregister_chain FG G'\<close>
  shows \<open>plus (apply_qregister_space F A') (apply_qregister_space G B') \<equiv>
          apply_qregister_space FG (plus (apply_qregister_space F' A') (apply_qregister_space G' B'))\<close>
  using assms by (auto simp add: apply_qregister_space_chain)

lemma translate_to_index_registers_leq[translate_to_index_registers]:
  assumes \<open>qregister FG \<and> F = qregister_chain FG F' \<and> G = qregister_chain FG G'\<close>
  shows \<open>(apply_qregister_space F A') \<le> (apply_qregister_space G B') \<equiv>
          (apply_qregister_space F' A') \<le> (apply_qregister_space G' B')\<close>
  using assms by (auto simp add: apply_qregister_space_chain)

lemma translate_to_index_registers_eq_space[translate_to_index_registers]:
  assumes \<open>qregister FG \<and> F = qregister_chain FG F' \<and> G = qregister_chain FG G'\<close>
  shows \<open>(apply_qregister_space F A') = (apply_qregister_space G B') \<equiv>
          (apply_qregister_space F' A') = (apply_qregister_space G' B')\<close>
  using assms by (auto simp add: apply_qregister_space_chain)

lemma translate_to_index_registers_apply_space[translate_to_index_registers]:
  shows \<open>apply_qregister_space F (apply_qregister_space F' A') \<equiv> apply_qregister_space (qregister_chain F F') A'\<close>
  by (simp add: apply_qregister_space_chain)

lemma tmp1: 
  assumes \<open>qregister_le F FG \<and> qregister_le G FG\<close>
  assumes \<open>qregister_conversion F FG = F'\<close>
  assumes \<open>qregister_conversion G FG = G'\<close>
  shows \<open>qregister FG \<and> F = qregister_chain FG F' \<and> G = qregister_chain FG G'\<close>
  by (metis assms(1) assms(2) assms(3) qregister_chain_conversion qregister_le_def)

ML \<open>
fun TODO_NAME_tac ctxt =
  resolve_tac ctxt @{thms tmp1}
  THEN' Prog_Variables.qregister_lub_tac ctxt
  THEN' CONVERSION (Prog_Variables.qregister_conversion_to_register_conv ctxt |> Conv.arg1_conv |> HOLogic.Trueprop_conv)
  THEN' resolve_tac ctxt @{thms refl}
  THEN' CONVERSION (Prog_Variables.qregister_conversion_to_register_conv ctxt |> Conv.arg1_conv |> HOLogic.Trueprop_conv)
  THEN' resolve_tac ctxt @{thms refl}
\<close>


(* TODO move *)
(* TODO: this should be applied in normalize_register_conv *)
lemma pair_fst_snd[simp]:
  shows \<open>\<lbrakk>qFst, qSnd\<rbrakk>\<^sub>q = qregister_id\<close>
  sorry

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
  sorry


ML \<open>
fun resolve_inst_tac ctxt inst rules = FIRST' (map (fn rule => let
  val inst_rule = [infer_instantiate ctxt inst rule]
                  handle THM _ => []
  in resolve_tac ctxt inst_rule end
) rules)
\<close>


thm eq_reflection

ML \<open>
(* Works on first subgoal *)
fun translate_to_index_registers_tac1 ctxt = let
  val rules = \<^named_theorems>\<open>translate_to_index_registers\<close> |> Proof_Context.get_thms ctxt
  in
    FIRST' [
      resolve_tac ctxt rules,
      TODO_NAME_tac ctxt,
      resolve_tac ctxt [
        @{lemma \<open>apply_qregister F A \<equiv> apply_qregister F A\<close> by simp},
        @{lemma \<open>apply_qregister_space F A \<equiv> apply_qregister_space F A\<close> by simp},
        @{lemma \<open>A \<equiv> apply_qregister_space qregister_id A\<close> by simp},
        @{lemma \<open>A \<equiv> apply_qregister qregister_id A\<close> by simp},
        @{lemma \<open>A \<equiv> A\<close> by simp}
      ]
    ]
  end

(* Works on all goals *)
fun translate_to_index_registers_tac ctxt = REPEAT (translate_to_index_registers_tac1 ctxt 1)
\<close>


ML \<open>
(* Expects goal X.
   Translates it into X' which has the toplevel constructor rewritten to have only index registers directly below it.
   E.g.: apply_register F A + apply_register G B \<equiv> apply_register FG (apply_register F' A + apply_register G' B)
         where F', G' are index-registers
   Or: apply_register F A = apply_register G B \<equiv> apply_register F' A \<equiv> apply_register G' B

   Only operates on the toplevel constructor!

   May fail it is does not know how to get rid of non-index-registers. (Not implemented!)
*)
fun translate_to_index_registers_conv_top ctxt ct = let
  val T = Thm.ctyp_of_cterm ct |> Thm.typ_of
  (* val T = Thm.typ_of cT *)
  val goal = Thm.apply (Thm.apply (Thm.cterm_of ctxt \<^Const>\<open>Pure.eq T\<close>) ct)
                       (Thm.cterm_of ctxt (Var(("rhs",Thm.maxidx_of_cterm ct + 1), T)))
  val tac = translate_to_index_registers_tac ctxt
  val thm = Goal.prove_internal ctxt [] goal (K tac)
  in thm end

fun translate_to_index_registers_conv ctxt ct = 
  if Term.is_schematic (Thm.term_of ct) then error "schematic vars in translate_to_index_registers_conv not yet supported"
  else Conv.bottom_conv (Conv.try_conv o translate_to_index_registers_conv_top) ctxt ct
\<close>



(* TODO move to Prog_Variables *)
method_setup translate_to_index_registers = \<open>
  Scan.succeed (fn ctxt => SIMPLE_METHOD (CONVERSION (translate_to_index_registers_conv ctxt) 1))
\<close>


section \<open>Measurements\<close>

definition "is_measurement M \<longleftrightarrow> ((\<forall>i. is_Proj (M i)) 
       \<and> (\<exists>P. (\<forall>\<psi> \<phi>. (\<Sum>\<^sub>\<infinity> i. \<phi> \<bullet>\<^sub>C (M i *\<^sub>V \<psi>)) = \<phi> \<bullet>\<^sub>C (P *\<^sub>V \<psi>)) \<and> P \<le> id_cblinfun))"
lemma is_measurement_0[simp]: "is_measurement (\<lambda>_. 0)"
  unfolding is_measurement_def
  by (auto intro: exI[of _ 0])


typedef ('a,'b) measurement = "{M::'a\<Rightarrow>('b,'b) l2bounded. is_measurement M}"
  morphisms mproj Abs_measurement
  by (rule exI[of _ "\<lambda>i. 0"], simp)
setup_lifting type_definition_measurement

lift_definition mtotal :: "('a,'b) measurement \<Rightarrow> bool" is
  "\<lambda>M. \<forall>\<psi> \<phi>. (\<Sum>\<^sub>\<infinity> i. \<phi> \<bullet>\<^sub>C (M i *\<^sub>V \<psi>)) = (\<phi> \<bullet>\<^sub>C \<psi>)".

lemma is_Proj_mproj[simp]: "is_Proj (mproj M i)"
  using mproj[of M] unfolding is_measurement_def by auto

lift_definition computational_basis :: "('a, 'a) measurement" is
  "\<lambda>i. proj (ket i)"
  by (cheat computational_basis)

lemma mproj_computational_basis[simp]: "mproj computational_basis x = proj (ket x)"
  unfolding computational_basis.rep_eq by simp

lemma mtotal_computational_basis [simp]: "mtotal computational_basis"
  by (cheat mtotal_computational_basis)

lift_definition binary_measurement :: "('a,'a) l2bounded \<Rightarrow> (bit,'a) measurement" is
  "\<lambda>(P::('a,'a) l2bounded) (b::bit). (if is_Proj P then (if b=1 then P else id_cblinfun-P) else 0)"
proof (rename_tac P, case_tac "is_Proj P")
  fix P :: "('a ell2, 'a ell2) bounded"
  assume [simp]: "is_Proj P"
  show "is_measurement (\<lambda>b::bit. if is_Proj P then if b = 1 then P else id_cblinfun - P else 0)"
    apply simp
    unfolding is_measurement_def apply (auto intro!: exI[of _ id_cblinfun] simp: UNIV_bit cinner_add_right[symmetric])
    by (metis id_cblinfun_apply cblinfun.add_left diff_add_cancel)
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
  apply (transfer fixing: P) apply (cases "is_Proj P") apply (auto simp: UNIV_bit)
  apply (metis id_cblinfun_apply cblinfun.add_left cinner_add_right diff_add_cancel)
  by (rule exI[of _ "ket undefined"], rule exI[of _ "ket undefined"], simp)


section \<open>Quantum predicates (ctd.)\<close>

subsection \<open>Subspace division\<close>

consts space_div :: "predicate \<Rightarrow> 'a ell2 \<Rightarrow> 'a q2variable \<Rightarrow> predicate"
                    ("_ \<div> _\<guillemotright>_" [89,89,89] 90)
lemma leq_space_div[simp]: "colocal A Q \<Longrightarrow> (A \<le> B \<div> \<psi>\<guillemotright>Q) = (A \<sqinter> ccspan {\<psi>}\<guillemotright>Q \<le> B)"
  by (cheat TODO14)

definition space_div_unlifted :: "('a*'b) ell2 ccsubspace \<Rightarrow> 'b ell2 \<Rightarrow> 'a ell2 ccsubspace" where
  [code del]: "space_div_unlifted S \<psi> = Abs_clinear_space {\<phi>. \<phi> \<otimes>\<^sub>s \<psi> \<in> space_as_set S}"

lemma space_div_space_div_unlifted: "space_div (S\<guillemotright>(qregister_pair Q R)) \<psi> R = (space_div_unlifted S \<psi>)\<guillemotright>Q"
  by (cheat space_div_space_div_unlifted)

lemma top_div[simp]: "top \<div> \<psi>\<guillemotright>Q = top" 
  by (cheat top_div)
lemma bot_div[simp]: "bot \<div> \<psi>\<guillemotright>Q = bot" 
  by (cheat bot_div)
lemma Cla_div[simp]: "Cla[e] \<div> \<psi>\<guillemotright>Q = Cla[e]" by simp

(* lemma space_div_add_extend_lift_as_var_concat_hint:
  fixes S :: "_ subspace"
  shows "NO_MATCH ((variable_concat a b),b) (Q,R) \<Longrightarrow> (space_div (S\<guillemotright>Q) \<psi> R) = (space_div (extend_lift_as_var_concat_hint (S\<guillemotright>Q) R)) \<psi> R"
  unfolding extend_lift_as_var_concat_hint_def by simp *)

subsection \<open>Quantum equality\<close>

(* TODO: 'c doesn't have to be ell2 *)
definition quantum_equality_full :: "('a,'c) l2bounded \<Rightarrow> ('a,'d) qregister \<Rightarrow> ('b,'c) l2bounded \<Rightarrow> ('b,'d) qregister \<Rightarrow> 'd subspace" where
  [code del]: "quantum_equality_full U Q V R = 
                 (eigenspace 1 (swap_ell2 o\<^sub>C\<^sub>L (V* o\<^sub>C\<^sub>L U) \<otimes>\<^sub>o (U* o\<^sub>C\<^sub>L V))) \<guillemotright> qregister_pair Q R"
  for Q :: "('a,'d) qregister" and R :: "('b,'d) qregister"
  and U V :: "(_,'c) l2bounded"

abbreviation "quantum_equality" :: "'a q2variable \<Rightarrow> 'a q2variable \<Rightarrow> predicate" (infix "\<equiv>\<qq>" 100)
  where "quantum_equality X Y \<equiv> quantum_equality_full id_cblinfun X id_cblinfun Y"
syntax quantum_equality :: "'a q2variable \<Rightarrow> 'a q2variable \<Rightarrow> predicate" (infix "==q" 100)
syntax "_quantum_equality" :: "variable_list_args \<Rightarrow> variable_list_args \<Rightarrow> predicate" ("Qeq'[_=_']")
translations
  "_quantum_equality a b" \<rightharpoonup> "CONST quantum_equality (_qvariables a) (_qvariables b)"

lemma quantum_equality_sym:
  assumes "distinct_qvars (qregister_pair Q R)"
  shows "quantum_equality_full U Q V R = quantum_equality_full V R U Q"
proof -
  have dist: "distinct_qvars (qregister_pair R Q)"
    using assms by (rule distinct_qvars_swap)
  have [simp]: \<open>qregister (qregister_pair Q R)\<close>
    using assms by blast
  have [simp]: \<open>qregister (qregister_pair R Q)\<close>
    by (simp add: dist)
  have [simp]: \<open>qcompatible Q R\<close>
    using assms qregister_pair_iff_compatible by blast
  have a: "comm_op \<cdot> ((V* \<cdot> U) \<otimes>\<^sub>o (U* \<cdot> V)) \<cdot> comm_op* = (U* \<cdot> V) \<otimes>\<^sub>o (V* \<cdot> U)" by simp
  have op_eq: "((comm_op o\<^sub>C\<^sub>L (V* \<cdot> U) \<otimes>\<^sub>o (U* \<cdot> V))\<guillemotright>qregister_pair Q R) =
               ((comm_op o\<^sub>C\<^sub>L (U* \<cdot> V) \<otimes>\<^sub>o (V* \<cdot> U))\<guillemotright>qregister_pair R Q)"
    using qregister_pair_chain_swap[of Q R, symmetric]
    sorry
  show ?thesis
    apply (subst quantum_equality_full_def)
    apply (subst quantum_equality_full_def)
    apply (subst eigenspace_lift[symmetric, OF assms])
    apply (subst eigenspace_lift[symmetric, OF dist])
    using op_eq by simp
qed

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
  by (cheat predicate_local)

lemma applyOpSpace_colocal:
  "colocal U S \<Longrightarrow> unitary U \<Longrightarrow> U \<cdot> S = S" for U :: "(qu2,qu2) l2bounded" and S :: predicate
  by (cheat TODO14)

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
  "unitary U \<Longrightarrow> U\<guillemotright>Q1 \<cdot> quantum_equality_full U1 Q1 U2 Q2 = quantum_equality_full (U1\<cdot>U*) Q1 U2 Q2"
 for U::"('a,'a) l2bounded" and U2 :: "('b,'c) l2bounded"  
  by (cheat TODO14)

(* Proof in paper *)
lemma Qeq_mult2[simp]:
  "unitary U \<Longrightarrow> U\<guillemotright>Q2 \<cdot> quantum_equality_full U1 Q1 U2 Q2 = quantum_equality_full U1 Q1 (U2\<cdot>U*) Q2"
 for U::"('a,'a) l2bounded" and U1 :: "('b,'c) l2bounded"  
  by (cheat TODO14)

(* Proof in paper *)
lemma quantum_eq_unique[simp]: "distinct_qvars (qregister_pair Q R) \<Longrightarrow>
  isometry U \<Longrightarrow> isometry (adj V) \<Longrightarrow> 
  quantum_equality_full U Q V R \<sqinter> ccspan{\<psi>}\<guillemotright>Q
  = liftSpace (ccspan{\<psi>}) Q \<sqinter> liftSpace (ccspan{V* \<cdot> U \<cdot> \<psi>}) R"
  for Q::"'a q2variable" and R::"'b q2variable"
    and U::"('a,'c) l2bounded" and V::"('b,'c) l2bounded"
    and \<psi>::"'a ell2"
  by (cheat TODO14)

(* Proof in paper *)
lemma
  quantum_eq_add_state: 
    "distinct_qvars (qregister_pair Q (qregister_pair R T)) \<Longrightarrow> norm \<psi> = 1 \<Longrightarrow>
    quantum_equality_full U Q V R \<sqinter> ccspan {\<psi>}\<guillemotright>T
             = quantum_equality_full (U \<otimes>\<^sub>o id_cblinfun) (qregister_pair Q T) (addState \<psi> \<cdot> V) R"
    for U :: "('a,'c) l2bounded" and V :: "('b,'c) l2bounded" and \<psi> :: "'d ell2"
    and Q :: "'a q2variable"    and R :: "'b q2variable"    and T :: "'d q2variable"
  by (cheat TODO14)


(* We flip the lhs/rhs of the quantum equality in addition to changing the indices.
   This is because quantum equalities are typically written with 1-variables on the left and 2-variables on the right. *)
lemma index_flip_subspace_quantum_equality[simp]: 
  "index_flip_subspace (quantum_equality_full U Q V R) = 
      quantum_equality_full V (index_flip_qvar R) U (index_flip_qvar Q)"
  by (cheat index_flip_subspace_quantum_equality)

lemma swap_variables_subspace_quantum_equality[simp]: 
  "swap_variables_subspace v w (quantum_equality_full U Q V R) = 
      quantum_equality_full U (swap_variables_qvars v w Q) V (swap_variables_qvars v w R)"
  by (cheat swap_variables_subspace_quantum_equality)

lemma quantum_equality_full_swap_left:
  assumes [simp]: "distinct_qvars (qregister_pair (qregister_pair Q R) S)"
  shows "quantum_equality_full U (qregister_pair Q R) V S
       = quantum_equality_full (U \<cdot> comm_op) (qregister_pair R Q) V S"
  sorry
(* proof -
  have "quantum_equality_full U (variable_concat Q R) V S
      = quantum_equality_full (U\<cdot>comm_op* ) (variable_concat R Q) (V\<cdot>id_cblinfun* ) S"
    apply (rule quantum_equality_reorder)
    using assms apply (auto simp: distinct_qvars_split1 intro!: qvar_trafo_comm_op qvar_trafo_id)
    using distinct_qvarsR distinct_qvars_swap by blast+
  also have "\<dots> = quantum_equality_full (U\<cdot>comm_op) (variable_concat R Q) V S"
    by simp
  finally show ?thesis by -
qed *)

lemma quantum_equality_full_swap_right:
  assumes [simp]: "distinct_qvars (qregister_pair (qregister_pair Q R) S)"
  shows "quantum_equality_full U Q V (qregister_pair R S)
       = quantum_equality_full U Q (V\<cdot>comm_op) (qregister_pair S R)"
    sorry
(* proof -
  have "quantum_equality_full U Q V (variable_concat R S)
      = quantum_equality_full (U\<cdot>id_cblinfun* ) Q (V\<cdot>comm_op* ) (variable_concat S R)"
    apply (rule quantum_equality_reorder)
    using assms apply (auto simp: distinct_qvars_split1 distinct_qvars_split2 intro!: qvar_trafo_comm_op qvar_trafo_id)
    using distinct_qvarsR distinct_qvars_swap by blast+
  also have "\<dots> = quantum_equality_full U Q (V\<cdot>comm_op) (variable_concat S R)"
    by simp
  finally show ?thesis by -
qed *)


lemma quantum_equality_merge:
  assumes "distinct_qvars (qregister_pair (qregister_pair Q1 R1) (qregister_pair Q2 R2))"
  shows "quantum_equality_full U1 Q1 V1 R1 \<sqinter> quantum_equality_full U2 Q2 V2 R2 
    \<le> quantum_equality_full (U1 \<otimes>\<^sub>o U2) (qregister_pair Q1 Q2) (V1 \<otimes>\<^sub>o V2) (qregister_pair R1 R2)"
  sorry
(* proof (rule ccsubspace_leI, rule subsetI)
  fix x :: "mem2 ell2"
  assume "x \<in> space_as_set (quantum_equality_full U1 Q1 V1 R1 \<sqinter> quantum_equality_full U2 Q2 V2 R2)"
  then have x1: "x \<in> space_as_set (quantum_equality_full U1 Q1 V1 R1)"
    and x2: "x \<in> space_as_set (quantum_equality_full U2 Q2 V2 R2)"
    by auto
  define QR1 QR2 QR12' Q12 R12 QR12 where "QR1 = variable_concat Q1 R1" and "QR2 = variable_concat Q2 R2"
    and "QR12' = variable_concat QR1 QR2" and "Q12 = variable_concat Q1 Q2" and "R12 = variable_concat R1 R2"
    and "QR12 = variable_concat Q12 R12"

  have [simp]: "distinct_qvars QR1"
    using assms unfolding QR1_def 
    using distinct_qvarsL by blast
  have [simp]: "distinct_qvars QR2"
    using assms unfolding QR2_def
    using distinct_qvarsR by blast
  have [simp]: "distinct_qvars QR12'"
    unfolding QR12'_def QR1_def QR2_def
    using assms by (auto intro: distinct_qvars_swap simp: distinct_qvars_split1 distinct_qvars_split2)
  have [simp]: "distinct_qvars (variable_concat Q12 R12)"
    using assms unfolding Q12_def R12_def
    by (auto intro: distinct_qvars_swap simp: distinct_qvars_split1 distinct_qvars_split2)
  include no_notation_blinfun_apply
  obtain T where qvar_trafo_T: "qvar_trafo T QR12 QR12'"
    and apply_T[simp]: "T *\<^sub>V ((q1\<otimes>q2)\<otimes>(r1\<otimes>r2)) = (q1\<otimes>r1)\<otimes>(q2\<otimes>r2)" for q1 q2 r1 r2 :: "_ ell2"
    apply atomize_elim apply (rule exI) apply (rule all_simps(2)[THEN iffD1], rule allI)+
    unfolding QR12_def Q12_def R12_def
    apply (rule qvar_trafo_ex_trans)
     apply (rule qvar_trafo_ex_assoc1)
    using assms apply (auto intro: distinct_qvars_swap simp: distinct_qvars_split1 distinct_qvars_split2)[1]
    apply (rule qvar_trafo_ex_trans)
     apply (rule qvar_trafo_ex_tensorR)
    using assms apply (auto intro: distinct_qvars_swap simp: distinct_qvars_split1 distinct_qvars_split2)[1]
      apply (rule qvar_trafo_ex_assoc2)
    using assms apply (auto intro: distinct_qvars_swap distinct_qvarsL distinct_qvarsR simp: distinct_qvars_split1 distinct_qvars_split2)[2]
    apply (rule qvar_trafo_ex_trans)
     apply (rule qvar_trafo_ex_tensorR)
    using assms apply (auto intro: distinct_qvars_swap distinct_qvarsL distinct_qvarsR simp: distinct_qvars_split1 distinct_qvars_split2)[1]
      apply (rule qvar_trafo_ex_tensorL)
    using assms apply (auto intro: distinct_qvars_swap distinct_qvarsL distinct_qvarsR simp: distinct_qvars_split1 distinct_qvars_split2)[1]
       apply (rule qvar_trafo_ex_comm)
    using assms apply (auto intro: distinct_qvars_swap distinct_qvarsL distinct_qvarsR simp: distinct_qvars_split1 distinct_qvars_split2)[3]
    apply (rule qvar_trafo_ex_trans)
     apply (rule qvar_trafo_ex_tensorR)
    using assms apply (auto intro: distinct_qvars_swap simp: distinct_qvars_split1 distinct_qvars_split2)[1]
      apply (rule qvar_trafo_ex_assoc1)
    using assms apply (auto intro: distinct_qvars_swap distinct_qvarsL distinct_qvarsR simp: distinct_qvars_split1 distinct_qvars_split2)[2]
    unfolding  QR12'_def QR1_def QR2_def
    apply (rule qvar_trafo_ex_assoc2)
    using assms by (auto intro: distinct_qvars_swap simp: distinct_qvars_split1 distinct_qvars_split2)[1]

  have apply_T_adj[simp]: "T* *\<^sub>V ((q1\<otimes>q2)\<otimes>(r1\<otimes>r2)) = (q1\<otimes>r1)\<otimes>(q2\<otimes>r2)" (is "?lhs=?rhs") for q1 q2 r1 r2
  proof -
    note apply_T[simp del]
    from qvar_trafo_T have [simp]: "isometry T"
      using qvar_trafo_unitary unitary_twosided_isometry by blast
    have "?lhs = T* *\<^sub>V (T *\<^sub>V (q1\<otimes>r1)\<otimes>(q2\<otimes>r2))"
      by (subst apply_T, simp)
    also have "\<dots> = ?rhs"
      by (simp add: cblinfun_apply_cblinfun_compose[symmetric])
    finally show ?thesis by -
  qed

  from x1 have x1': "(comm_op \<cdot> (V1*\<cdot>U1)\<otimes>(U1*\<cdot>V1)) \<guillemotright> QR1 *\<^sub>V x = x"
    unfolding quantum_equality_full_def QR1_def[symmetric]
    apply (subst (asm) eigenspace_lift[symmetric], simp)
    by (frule eigenspace_memberD, simp)
  from x2 have x2': "(comm_op \<cdot> (V2*\<cdot>U2)\<otimes>(U2*\<cdot>V2)) \<guillemotright> QR2 *\<^sub>V x = x"
    unfolding quantum_equality_full_def QR2_def[symmetric]
    apply (subst (asm) eigenspace_lift[symmetric], simp)
    by (frule eigenspace_memberD, simp)

  have x12: "((comm_op \<cdot> (V1*\<cdot>U1)\<otimes>(U1*\<cdot>V1)) \<otimes> (comm_op \<cdot> (V2*\<cdot>U2)\<otimes>(U2*\<cdot>V2))) \<guillemotright> QR12' *\<^sub>V x = x"
    unfolding QR12'_def apply (subst lift_tensorOp[symmetric])
    unfolding QR12'_def[symmetric] apply simp
    by (simp add: x1' x2')

  have same_op: "(comm_op \<cdot> (((V1 \<otimes> V2)* o\<^sub>C\<^sub>L (U1 \<otimes> U2)) \<otimes> ((U1 \<otimes> U2)* o\<^sub>C\<^sub>L (V1 \<otimes> V2))))\<guillemotright>QR12
      = ((comm_op \<cdot> (V1*\<cdot>U1)\<otimes>(U1*\<cdot>V1)) \<otimes> (comm_op \<cdot> (V2*\<cdot>U2)\<otimes>(U2*\<cdot>V2))) \<guillemotright> QR12'"
    apply (subst qvar_trafo_l2bounded[OF qvar_trafo_T])
    apply (subst lift_eqOp, simp)
    apply (rule equal_ket)
    by (auto simp: ket_product tensorOp_applyOp_distr)

  have "(comm_op \<cdot> (((V1 \<otimes> V2)* o\<^sub>C\<^sub>L (U1 \<otimes> U2)) \<otimes> ((U1 \<otimes> U2)* o\<^sub>C\<^sub>L (V1 \<otimes> V2))))\<guillemotright>QR12 *\<^sub>V x = x"
    apply (subst same_op) by (rule x12)

  then show "x \<in> space_as_set (quantum_equality_full (U1 \<otimes> U2) Q12 (V1 \<otimes> V2) R12)"
    unfolding quantum_equality_full_def QR12_def
    apply (subst eigenspace_lift[symmetric], simp)
    apply (rule eigenspace_memberI)
    by simp
qed *)

lemma translate_to_index_registers_qeq[translate_to_index_registers]:
  fixes F :: \<open>('a,'b) qregister\<close>
  assumes \<open>qregister FG \<and> F = qregister_chain FG F' \<and> G = qregister_chain FG G'\<close>
  shows \<open>quantum_equality_full U F V G \<equiv>
          apply_qregister_space FG (quantum_equality_full U F' V G')\<close>
  using assms 
  by (simp add: quantum_equality_full_def flip: apply_qregister_space_chain qregister_chain_pair)

schematic_goal TODO_REMOVE:
  assumes [simp,register]: "declared_qvars \<lbrakk>q1,r1,q2,r2\<rbrakk>"
  shows \<open>quantum_equality_full (id_cblinfun) \<lbrakk>q1, r1\<rbrakk>\<^sub>q id_cblinfun \<lbrakk>q2, r2\<rbrakk>\<^sub>q \<equiv> x\<close>
  apply translate_to_index_registers
  oops

section \<open>Common quantum objects\<close>

(* definition [code del]: "CNOT = classical_operator (Some o (\<lambda>(x::bit,y). (x,y+x)))" for CNOT *)
lemma unitaryCNOT[simp]: "unitary CNOT"
  sorry

lemma adjoint_CNOT[simp]: "CNOT* = CNOT"
  by simp

lemma CNOT_CNOT[simp]: "CNOT \<cdot> CNOT = id_cblinfun"
  using unitaryCNOT unfolding unitary_def adjoint_CNOT by simp

(* definition [code del]: "pauliX = classical_operator (Some o (\<lambda>x::bit. x+1))" *)
lemma unitaryX[simp]: "unitary pauliX"
  by (simp add: unitary_def)

lemmas adjoint_X[simp] = pauliX_adjoint

lemmas X_X[simp] = pauliXX

lemma unitaryH[simp]: "unitary hadamard"
  by (cheat TODO14)
lemmas adjoint_H[simp] = hada_adj

lemma H_H[simp]: "hadamard \<cdot> hadamard = id_cblinfun"
  using unitaryH unfolding unitary_def by simp

lemma unitaryZ[simp]: "unitary pauliZ"
  by (simp add: unitary_def)

lemmas adjoint_Z[simp] = pauliZ_adjoint

lemmas Z_Z[simp] = pauliZZ

consts pauliY :: "(bit,bit) l2bounded"
lemma unitaryY[simp]: "unitary pauliY"
  by (cheat TODO15)
lemma Y_Y[simp]: "pauliY \<cdot> pauliY = id_cblinfun"
  by (cheat TODO15)
lemma adjoint_Y[simp]: "pauliY* = pauliY"
  by (cheat TODO15)

consts EPR :: "(bit*bit) ell2" 
lemma EPR_normalized[simp]: "norm EPR = 1"
  by (cheat TODO15)

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
