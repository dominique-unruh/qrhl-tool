theory QRHL_Core
  imports Complex_Main "HOL-Library.Adhoc_Overloading" BOLegacy Discrete_Distributions 
    Misc_Missing Prog_Variables (* Registers.Pure_States *)
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

(* lemma swap_variables_vars_concat[simp]: 
  "swap_variables_vars v w (variable_concat Q R)
   = variable_concat (swap_variables_vars v w Q) (swap_variables_vars v w R)"
  by (cheat swap_variables_vars_concat)
 *)

(* lemma swap_variables_vars_unit[simp]: 
  "swap_variables_vars v w variable_unit = variable_unit"
  by (cheat swap_variables_vars_unit) *)

(* lemma swap_variables_vars_singleton1[simp]: 
  "swap_variables_vars v w (variable_singleton v) = variable_singleton w"
  by (cheat swap_variables_vars_singleton1) *)

(* lemma swap_variables_vars_singleton2[simp]: 
  "swap_variables_vars v w (variable_singleton w) = variable_singleton v"
  by (cheat swap_variables_vars_singleton2)

lemma swap_variables_vars_singleton3[simp]: 
  "NO_MATCH v z \<Longrightarrow> NO_MATCH w z \<Longrightarrow> distinct_qvars \<lbrakk>v,z\<rbrakk> \<Longrightarrow> distinct_qvars \<lbrakk>w,z\<rbrakk> \<Longrightarrow> swap_variables_vars v w (variable_singleton z) = variable_singleton z"
  by (cheat swap_variables_vars_singleton2)
 *)

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

abbreviation \<open>colocal_op_pred == distinct_qvars_op_pred\<close> (* Legacy *)
abbreviation \<open>colocal_op_qvars == distinct_qvars_op_vars\<close> (* Legacy *)
abbreviation \<open>colocal_pred_qvars == distinct_qvars_pred_vars\<close> (* Legacy *)

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

(* lemma colocal_pred_qvars[simp, intro!]:
  assumes "distinct_qvars Q"
  assumes "colocal_pred_qvars_str S (set (variable_names Q))"
  shows "colocal_pred_qvars S Q"
  by (cheat colocal_pred_qvars) *)

(* lemma colocal_op_qvars[simp, intro!]:
  assumes "distinct_qvars Q"
  assumes "colocal_op_qvars_str U (set (variable_names Q))"
  shows "colocal_op_qvars U Q"
  by (cheat colocal_op_qvars) *)

lemma predicate_local_inf[intro!]: "predicate_local S Q \<Longrightarrow> predicate_local T Q \<Longrightarrow> predicate_local (S\<sqinter>T) Q"
  by (cheat predicate_local_inf)
lemma predicate_local_applyOpSpace[intro!]: "operator_local A Q \<Longrightarrow> predicate_local S Q \<Longrightarrow> predicate_local (A\<cdot>S) Q"
  by (cheat predicate_local_applyOpSpace)
lemma operator_local_timesOp[intro!]: "operator_local A Q \<Longrightarrow> operator_local B Q \<Longrightarrow> operator_local (A\<cdot>B) Q"
  by (cheat operator_local_timesOp)

subsection \<open>Lifting\<close>

abbreviation (input) \<open>liftOp == (\<lambda>A F. apply_qregister F A)\<close>
abbreviation (input) \<open>liftSpace == (\<lambda>A F. apply_qregister_space F A)\<close>

(* definition liftOp :: "('a,'a) l2bounded \<Rightarrow> 'a q2variable \<Rightarrow> (qu2,qu2) l2bounded" 
  (* Convention: If not distinct_qvars Q, then liftOp A Q := 0 *)
  where "liftOp A x = (if register x then x A else 0)" *)
(* definition
  (* Convention: If not distinct_qvars Q, then liftOp A Q := bot *)
  liftSpace :: "'a subspace \<Rightarrow> ('a,'b) qregister \<Rightarrow> 'b subspace"
  where \<open>liftSpace S x = apply_qregister x (Proj S) *\<^sub>S \<top>\<close> *)
(* definition
  (* lift_vector \<psi> Q \<psi>' = \<psi> \<otimes> \<psi>' where \<psi> is interpreted as a vector over Q, and \<psi>' as a vector over the complement of Q *)
  lift_vector :: "'a::default ell2 \<Rightarrow> 'a q2variable \<Rightarrow> ('a, qu \<times> qu) complement_domain ell2 \<Rightarrow> qu2 ell2" 
  where \<open>lift_vector \<psi> Q \<psi>' = (Q(\<psi>) \<otimes>\<^sub>p (complement Q)(\<psi>'))\<close> *)

abbreviation variable_in (infix "\<in>\<^sub>\<qq>" 80) where "variable_in R S \<equiv> liftSpace S R" 
notation (input) variable_in (infix "\<in>\<^sub>q" 80)
abbreviation variable_is (infix "=\<^sub>\<qq>" 80) where "variable_is R \<psi> \<equiv> R \<in>\<^sub>q ccspan {\<psi>}" 
notation (input) variable_is (infix "=\<^sub>q" 80)

consts lift :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" ("_\<guillemotright>_"  [91,91] 90)
syntax lift :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" ("_>>_"  [91,91] 90)
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
lemma lift_tensorOp: "distinct_qvars (qregister_pair Q R) \<Longrightarrow> (S\<guillemotright>Q) \<cdot> (T\<guillemotright>R) = (S \<otimes> T)\<guillemotright>qregister_pair Q R" for Q :: "'a q2variable" and R :: "'b q2variable" and S T :: "(_,_) l2bounded" 
  by (cheat TODO11)
lemma lift_tensorSpace: "distinct_qvars (qregister_pair Q R) \<Longrightarrow> (S\<guillemotright>Q) = (S \<otimes> top)\<guillemotright>qregister_pair Q R" for Q :: "'a q2variable" and R :: "'b q2variable" and S :: "_ subspace" 
  by (cheat TODO11)
lemma lift_id_cblinfun[simp]: "distinct_qvars Q \<Longrightarrow> id_cblinfun\<guillemotright>Q = id_cblinfun" for Q :: "'a q2variable"
  by (cheat TODO11)
lemma INF_lift: "(INF x. S x\<guillemotright>Q) = (INF x. S x)\<guillemotright>Q" for Q::"'a q2variable" and S::"'b \<Rightarrow> 'a subspace"
  by (cheat TODO11)
lemma Cla_inf_lift: "Cla[b] \<sqinter> (S\<guillemotright>Q) = (if b then S else bot)\<guillemotright>Q" by auto
lemma Cla_plus_lift: "distinct_qvars Q \<Longrightarrow> Cla[b] + (S\<guillemotright>Q) = (if b then top else S)\<guillemotright>Q" by auto
lemma Cla_sup_lift: "distinct_qvars Q \<Longrightarrow> Cla[b] \<squnion> (S\<guillemotright>Q) = (if b then top else S)\<guillemotright>Q" by auto
lemma Proj_lift[simp]: "Proj (S\<guillemotright>Q) = (Proj S)\<guillemotright>Q"
  for Q::"'a q2variable"
  by (cheat Proj_lift)
lemma kernel_lift[simp]: "distinct_qvars Q \<Longrightarrow> kernel (A\<guillemotright>Q) = (kernel A)\<guillemotright>Q" for Q::"'a q2variable"
  by (cheat TODO11)
lemma eigenspace_lift[simp]: "distinct_qvars Q \<Longrightarrow> eigenspace a (A\<guillemotright>Q) = (eigenspace a A)\<guillemotright>Q" for Q::"'a q2variable"
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
  shows "U\<guillemotright>Q = (U\<otimes>id_cblinfun)\<guillemotright>\<lbrakk>Q,R\<rbrakk>"
  apply (subst apply_qregister_pair)
  using assms qregister_pair_iff_compatible apply blast
  by (metis apply_qregister_of_id assms cblinfun_compose_id_right distinct_qvarsR)

lemma lift_extendL:
  assumes "distinct_qvars (qregister_pair Q R)"
  shows "U\<guillemotright>Q = (id_cblinfun\<otimes>U)\<guillemotright>(qregister_pair R Q)"
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

(* lemma applyOp_lift: "distinct_qvars Q \<Longrightarrow> A\<guillemotright>Q \<cdot> lift_vector \<psi> Q \<psi>' = lift_vector (A\<cdot>\<psi>) Q \<psi>'"
  by (cheat applyOp_lift) *)

lemma span_lift: "distinct_qvars Q \<Longrightarrow> ccspan G \<guillemotright> Q = ccspan {lift_vector \<psi> Q \<psi>' | \<psi> \<psi>'. \<psi>\<in>G \<and> \<psi>' \<in> lift_rest Q}"
  by (cheat span_lift)

(* lemma lift_vector_inj:
  assumes "r \<in> lift_rest Q"
  assumes "r \<noteq> 0"
  assumes "lift_vector \<psi>1 Q r = lift_vector \<psi>2 Q r"
  shows "\<psi>1 = \<psi>2"
  by (cheat lift_vector_inj) *)


(* lemma applyOpSpace_eq':
  fixes S :: "_ ccsubspace" and A B :: "(_,_) bounded"
  assumes [simp]: "distinct_qvars Q"
  assumes "predicate_local S Q"
  assumes "operator_local A Q"
  assumes "operator_local B Q"
  assumes AB: "\<And>x \<psi>'. x \<in> G \<Longrightarrow> \<psi>' \<in> lift_rest Q \<Longrightarrow> A \<cdot> (lift_vector x Q \<psi>') = B \<cdot> (lift_vector x Q \<psi>')"
  assumes S_spanG: "ccspan G \<guillemotright> Q \<ge> S"
  shows "A \<cdot> S = B \<cdot> S"
proof -
  obtain S' where S: "S = S'\<guillemotright>Q"
    apply atomize_elim using \<open>predicate_local S Q\<close> by (rule predicate_localE)
  obtain A' where A: "A = A'\<guillemotright>Q"
    apply atomize_elim using \<open>operator_local A Q\<close> by (rule operator_localE)
  obtain B' where B: "B = B'\<guillemotright>Q"
    apply atomize_elim using \<open>operator_local B Q\<close> by (rule operator_localE)

  have A'B': "A' \<cdot> x = B' \<cdot> x" if "x \<in> G" for x
    using AB[OF that] unfolding A B 
    apply (simp add: applyOp_lift)
    apply (rule lift_vector_inj)
    using lift_rest_nonempty[folded some_in_eq, of Q] by auto

  have S'_spanG: "S' \<le> ccspan G"
    using S_spanG unfolding S by simp

  have "A' \<cdot> S' = B' \<cdot> S'"
    using A'B' S'_spanG cblinfun_image_eq by blast

  then show ?thesis
    unfolding S A B by simp
qed *)

lemma index_flip_subspace_lift[simp]: "index_flip_subspace (S\<guillemotright>Q) = S \<guillemotright> index_flip_qvar Q"
  by (cheat index_flip_subspace_lift)

lemma swap_variables_subspace_lift[simp]: "swap_variables_subspace v w (S\<guillemotright>Q) = S \<guillemotright> swap_variables_vars v w Q"
  by (cheat index_flip_subspace_lift)


lemma ket_less_specific:
  assumes "distinct_qvars (qregister_pair X Y)"
  shows "ccspan {ket (x,y)}\<guillemotright>qregister_pair X Y \<le> ccspan {ket y}\<guillemotright>Y"
proof -
  have "ccspan {ket (x,y)}\<guillemotright>qregister_pair X Y = ccspan {x' \<otimes> y' | x' y'. x'\<in>{ket x} \<and> y'\<in>{ket y}}\<guillemotright>qregister_pair X Y"
    unfolding ket_product by simp
  also have "\<dots> = ccspan {ket x}\<guillemotright>X \<sqinter> ccspan {ket y}\<guillemotright>Y"
    apply (subst span_tensor[symmetric])
    apply (subst tensor_lift)
    using assms by auto
  also have "\<dots> \<le> ccspan {ket y}\<guillemotright>Y"
    by simp
  finally show ?thesis
    by -
qed


lemma comm_op_twice[simp]: "distinct_qvars Q \<Longrightarrow> comm_op\<guillemotright>Q \<cdot> (comm_op\<guillemotright>Q \<cdot> S) = (S::_ ccsubspace)"
  apply (subst adj_comm_op[symmetric])
  by (simp del: adj_comm_op flip: adjoint_lift cblinfun_compose_assoc add: cblinfun_assoc_left)


(*
subsection "Rewriting quantum variable lifting"

(* TODO: use new constant conjugate for A\<cdot>B\<cdot>A* expressions to avoid duplication *)

(* Means that operator A can be used to transform an expression \<dots>\<guillemotright>Q into \<dots>\<guillemotright>R *)
(* TODO: we could have "register A" in here, we'd lose qvar_trafo_adj then. It the latter useful? *)
definition "qvar_trafo A Q R \<longleftrightarrow> register Q \<and> register R \<and> iso_register A \<and> (\<forall>C::(_,_)l2bounded. C\<guillemotright>Q = (A C)\<guillemotright>R)" 

lemma qvar_trafo_id[simp]: "distinct_qvars Q \<Longrightarrow> qvar_trafo id Q Q"
  unfolding qvar_trafo_def by auto

lemma qvar_trafo_adj[simp]: assumes "qvar_trafo A Q R" shows "qvar_trafo (inv A) R Q"
  by (metis (no_types, lifting) Laws_Quantum.iso_register_inv Laws_Quantum.iso_register_inv_comp2 assms qvar_trafo_def surj_f_inv_f surj_iff)

lemma assoc_op_lift: "(assoc' A)\<guillemotright>(variable_concat (variable_concat Q R) T)
     = A\<guillemotright>(variable_concat Q (variable_concat R T))" for A::"('a*'b*'c,_)l2bounded" 
  by (cheat assoc_op_lift)
lemma assoc_op_lift': "(assoc A)\<guillemotright>(variable_concat Q (variable_concat R T))
     = A\<guillemotright>(variable_concat (variable_concat Q R) T)" for A::"(('a*'b)*'c,_)l2bounded" 
  by (cheat assoc_op_lift')
lemma comm_op_lift: "(swap A)\<guillemotright>(variable_concat Q R)
     = A\<guillemotright>(variable_concat R Q)" for A::"('a*'b,_)l2bounded" 
  by (cheat comm_op_lift)
lemma lift_tensor_id: "distinct_qvars (variable_concat Q R) \<Longrightarrow> distinct_qvars (variable_concat Q R) \<Longrightarrow>
   (\<And>D::(_,_) l2bounded. (A D)\<guillemotright>Q = D\<guillemotright>Q') \<Longrightarrow> (\<And>D::(_,_) l2bounded. (A' D)\<guillemotright>R = D\<guillemotright>R') \<Longrightarrow> 
  ((Laws_Quantum.register_tensor A A') C)\<guillemotright>variable_concat Q R = C\<guillemotright>variable_concat Q' R'"
  for A :: "'a update \<Rightarrow> 'b update" and A' :: "'c update \<Rightarrow> 'd update" 
    and C::"(_,_) l2bounded" and Q R :: "_ q2variable"
  by (cheat lift_tensor_id)

lemma comm_op_sym:
  "comm_op \<guillemotright> variable_concat Q R = comm_op \<guillemotright> variable_concat R Q"
  (* using comm_op_lift[where A=comm_op and Q=Q and R=R] by simp *)
  by (cheat comm_op_sym)


lemma qvar_trafo_assoc_op[simp]:
  assumes "distinct_qvars (variable_concat Q (variable_concat R T))"
  shows "qvar_trafo assoc' (variable_concat Q (variable_concat R T))  (variable_concat (variable_concat Q R) T)"
proof (unfold qvar_trafo_def, auto)
  show "distinct_qvars (variable_concat Q (variable_concat R T))" and "distinct_qvars (variable_concat (variable_concat Q R) T)"
    using assms by (auto intro: distinct_qvars_swap simp: distinct_qvars_split1 distinct_qvars_split2)
  show "C\<guillemotright>variable_concat Q (variable_concat R T) = (assoc' C)\<guillemotright>variable_concat (variable_concat Q R) T" for C::"(_,_)l2bounded"
    by (rule assoc_op_lift[symmetric])
qed


lemma qvar_trafo_comm_op[simp]:
  assumes "distinct_qvars (variable_concat Q R)"
  shows "qvar_trafo swap (variable_concat Q R) (variable_concat R Q)"
proof (unfold qvar_trafo_def, auto simp del: adj_comm_op)
  show "distinct_qvars (variable_concat Q R)" and "distinct_qvars (variable_concat R Q)"
    using assms by (auto intro: distinct_qvars_swap)
  show "C\<guillemotright>variable_concat Q R = (swap C)\<guillemotright>variable_concat R Q" for C::"(_,_)l2bounded"
    by (rule comm_op_lift[symmetric])
qed

lemma qvar_trafo_l2bounded:
  fixes C::"(_,_) l2bounded"
  assumes "qvar_trafo A Q R"
  shows "C\<guillemotright>Q = (A C)\<guillemotright>R"
  using assms unfolding qvar_trafo_def by auto

lemma qvar_trafo_subspace:
  fixes S::"'a subspace"
  assumes "qvar_trafo A Q R"
  shows "S\<guillemotright>Q = (A (Proj S) *\<^sub>S \<top>)\<guillemotright>R"
  by (metis (no_types, lifting) Proj_range assms imageOp_lift qvar_trafo_l2bounded)

lemma qvar_trafo_mult:
  assumes "qvar_trafo A Q R"
    and "qvar_trafo B R S"
  shows "qvar_trafo (B o A) Q S"
  by (smt (verit, ccfv_SIG) Laws_Quantum.iso_register_comp assms(1) assms(2) comp_eq_dest_lhs qvar_trafo_def)

lemma qvar_trafo_tensor:
  assumes "distinct_qvars (variable_concat Q Q')"
    and "distinct_qvars (variable_concat R R')"
    and "qvar_trafo A Q R"
    and "qvar_trafo A' Q' R'"
  shows "qvar_trafo (Laws_Quantum.register_tensor A A') (variable_concat Q Q') (variable_concat R R')"
proof (unfold qvar_trafo_def, (rule conjI[rotated])+, rule allI)
  show "distinct_qvars (variable_concat Q Q')" and "distinct_qvars (variable_concat R R')"
    using assms unfolding qvar_trafo_def by auto
  show "C\<guillemotright>variable_concat Q Q' = ((Laws_Quantum.register_tensor A A') C)\<guillemotright>variable_concat R R'" for C::"(_,_)l2bounded"
    apply (rule lift_tensor_id[symmetric])
    using assms unfolding qvar_trafo_def
    by auto
  show \<open>Laws_Quantum.iso_register (A \<otimes>\<^sub>r A')\<close>
    by (metis Laws_Quantum.iso_register_tensor_is_iso_register assms(3) assms(4) qvar_trafo_def)
qed
*)

abbreviation (input) \<open>reorder_variables_hint \<equiv> (\<lambda>A F. register_conversion_hint F A)\<close>
lemmas reorder_variables_hint_def = register_conversion_hint_def

(*
lemma reorder_variables_hint_remove_aux: "reorder_variables_hint x R \<equiv> x" \<comment> \<open>Auxiliary lemma used by reorder_variables_hint_conv\<close>
  unfolding reorder_variables_hint_def by simp

(* Tells the simplifier the following:
    - A is of the form x\<guillemotright>Q
    - Q,R are both explicit distinct variable terms
    - the term should be rewritten into x'\<guillemotright>(variable_concat Q' R) for some Q', x'
*)
definition "extend_lift_as_var_concat_hint A R = A"
lemma extend_lift_as_var_concat_hint_cong[cong]: "A=A' \<Longrightarrow> extend_lift_as_var_concat_hint A R = extend_lift_as_var_concat_hint A' R" by simp
lemma extend_lift_as_var_concat_hint_remove_aux: "extend_lift_as_var_concat_hint A R \<equiv> A"
  by (simp add: extend_lift_as_var_concat_hint_def)


(* A hint to the simplifier with the meaning:
     - x is a term of the form x'>>Q (where x' is of type subspace or l2bounded)
     - qvar_trafo A Q R holds (i.e., should be produced as a precondition when rewriting)
     - the whole term should be rewritten into y'>>R for some y' 
  Rewriting the term is done by the simplifier rules declared below.
*)
definition "variable_renaming_hint x (A::'a update \<Rightarrow> 'b update) (R::'b q2variable) = x"
lemma variable_renaming_hint_cong[cong]: "x=x' \<Longrightarrow> variable_renaming_hint x A R = variable_renaming_hint x' A R" by simp

(* A copy of qvars_trafo that is protected from unintentional rewriting *)
definition "qvar_trafo_protected = qvar_trafo"
lemma qvar_trafo_protected_cong[cong]: "qvar_trafo_protected A Q R = qvar_trafo_protected A Q R" ..

lemma variable_renaming_hint_subspace[simp]:
  fixes S::"_ subspace"
  assumes "qvar_trafo_protected A Q R"
  shows "variable_renaming_hint (S\<guillemotright>Q) A R = (S\<guillemotright>A)\<guillemotright>R"
  using assms unfolding variable_renaming_hint_def qvar_trafo_protected_def
  by (metis (no_types, lifting) Laws_Quantum.iso_register_is_register liftSpace_def qvar_trafo_def qvar_trafo_subspace)

lemma variable_renaming_hint_l2bounded[simp]:
  fixes S::"(_,_) l2bounded"
  assumes "qvar_trafo_protected A Q R"
  shows "variable_renaming_hint (S\<guillemotright>Q) A R = (S\<guillemotright>A)\<guillemotright>R"
  using assms unfolding variable_renaming_hint_def qvar_trafo_protected_def
(* XXX *)
  apply (simp add: Laws_Quantum.iso_register_is_register liftOp_def qvar_trafo_def)
  by meson


lemma extend_space_lift_aux: \<comment> \<open>Auxiliary lemma for extend_lift_conv\<close>
  fixes Q :: "'q qvariable" and R :: "'r qvariable"
    and S :: "'q subspace"
  assumes "distinct_qvars (register_pair Q R)"
  shows "liftSpace S Q \<equiv> (S\<otimes>top)\<guillemotright>(register_pair Q R)"
  apply (rule eq_reflection)
  using assms by (rule lift_tensorSpace)


lemma extend_l2bounded_lift_aux: \<comment> \<open>Auxiliary lemma for extend_lift_conv\<close>
  fixes Q :: "'q::universe variables" and R :: "'r::universe variables"
    and S :: "('q,'q) l2bounded"
  assumes "distinct_qvars (variable_concat Q R)"
  shows "S\<guillemotright>Q \<equiv> (S\<otimes>id_cblinfun)\<guillemotright>(variable_concat Q R)"
  apply (rule eq_reflection)
  using assms lift_extendR by blast

lemma trafo_lift_space_aux: \<comment> \<open>Auxiliary lemma for sort_lift_conv\<close>
  fixes S::"_ subspace"
  assumes "qvar_trafo_protected A Q R"
  shows "S\<guillemotright>Q \<equiv> (A\<cdot>S)\<guillemotright>R"
  apply (rule eq_reflection)
  using assms unfolding qvar_trafo_protected_def by (rule qvar_trafo_subspace)

lemma trafo_lift_l2bounded_aux: \<comment> \<open>Auxiliary lemma for sort_lift_conv\<close>
  fixes S::"(_,_) l2bounded"
  assumes "qvar_trafo_protected A Q R"
  shows "S\<guillemotright>Q \<equiv> (A\<cdot>S\<cdot>A* )\<guillemotright>R"
  apply (rule eq_reflection)
  using assms unfolding qvar_trafo_protected_def by (rule qvar_trafo_l2bounded)

lemma trafo_lift_space_bw_aux: \<comment> \<open>Auxiliary lemma for reorder_lift_conv\<close>
  fixes S::"_ subspace"
  assumes "qvar_trafo_protected A Q R"
  shows "S\<guillemotright>R \<equiv> (A*\<cdot>S)\<guillemotright>Q"
  apply (rule eq_reflection)
  using qvar_trafo_adj[OF assms[unfolded qvar_trafo_protected_def]]
  using qvar_trafo_subspace by blast

lemma trafo_lift_l2bounded_bw_aux: \<comment> \<open>Auxiliary lemma for reorder_lift_conv\<close>
  fixes S::"(_,_) l2bounded"
  assumes "qvar_trafo_protected A Q R"
  shows "S\<guillemotright>R \<equiv> (A*\<cdot>S\<cdot>A)\<guillemotright>Q"
  apply (rule eq_reflection)
  using qvar_trafo_l2bounded[OF qvar_trafo_adj[OF assms[unfolded qvar_trafo_protected_def]]]
  by simp
  




(* A hint to the simplifier with the meaning:
     - x is a term of the form x'>>Q (where x' is of type subspace or l2bounded)
     - colocal Q R holds (i.e., should be produced as a precondition when rewriting)
     - the whole term should be rewritten into y'>>variable_concat Q R for some y'
  Rewriting the term is done by the variable_rewriting simproc.
 *)
(* TODO: we might not need this if we reimplement the various conversions *)
definition "variable_extension_hint x (R::_ variables) = x"


lemma variable_extension_hint_subspace[simp]:
  fixes S::"_ subspace"
  assumes "distinct_qvars (variable_concat Q R)"
  shows "variable_extension_hint (S\<guillemotright>Q) R = (S\<otimes>top)\<guillemotright>variable_concat Q R"
  unfolding variable_extension_hint_def 
  using assms by (rule lift_tensorSpace)

lemma variable_extension_hint_l2bounded[simp]:
  fixes S::"(_,_) l2bounded"
  assumes "distinct_qvars (variable_concat Q R)"
  shows "variable_extension_hint (S\<guillemotright>Q) R = (S\<otimes>id_cblinfun)\<guillemotright>variable_concat Q R"
  unfolding variable_extension_hint_def 
  using assms
  using extend_l2bounded_lift_aux by blast

*)

lemma join_registers_template_op:
  assumes \<open>JOIN_REGISTERS F G X Y\<close>
  shows \<open>op (apply_qregister F A) (apply_qregister G B) = op (X (apply_qregister F A)) (Y (apply_qregister G B))\<close>
  using assms unfolding JOIN_REGISTERS_def by simp

lemma join_registers_template_space:
  assumes \<open>JOIN_REGISTERS F G X Y\<close>
  shows \<open>op (apply_qregister_space F A) (apply_qregister_space G B) = op (X (apply_qregister_space F A)) (Y (apply_qregister_space G B))\<close>
  using assms unfolding JOIN_REGISTERS_def by simp

lemma join_registers_template_op_space:
  assumes \<open>JOIN_REGISTERS F G X Y\<close>
  shows \<open>op (apply_qregister F A) (apply_qregister_space G B) = op (X (apply_qregister F A)) (Y (apply_qregister_space G B))\<close>
  using assms unfolding JOIN_REGISTERS_def by simp

lemmas join_registers_eq_op[join_registers] = join_registers_template_op[where op=\<open>(=)\<close>]
lemmas join_registers_plus_op[join_registers] = join_registers_template_op[where op=\<open>plus\<close>]
lemmas join_registers_minus_op[join_registers] = join_registers_template_op[where op=\<open>minus\<close>]
lemmas join_registers_cblinfun_compose[join_registers] = join_registers_template_op[where op=\<open>(o\<^sub>C\<^sub>L)\<close>]
lemmas join_registers_inf[join_registers] = join_registers_template_space[where op=\<open>inf\<close>]
lemmas join_registers_sup[join_registers] = join_registers_template_space[where op=\<open>sup\<close>]
lemmas join_registers_plus_space[join_registers] = join_registers_template_space[where op=\<open>plus\<close>]
lemmas join_registers_cblinfun_image[join_registers] = join_registers_template_op_space[where op=\<open>cblinfun_image\<close>]
lemmas join_registers_le_space[join_registers] = join_registers_template_space[where op=\<open>less_eq\<close>]
lemmas join_registers_eq_space[join_registers] = join_registers_template_space[where op=\<open>(=)\<close>]

(*

(* Hint for the simplifier, meaning that:
    - x is of the form x'>>Q
    - colocal Q \<lbrakk>\<rbrakk> holds
    - the whole expression should be rewritten to y'>>Q' where Q' is a sorted variable list
  Rewriting the term is done by the variable_rewriting simproc.
 *)
definition "sort_variables_hint x = x"

lemma join_variables_hint_subspace_conv_aux:
  "join_variables_hint (S\<guillemotright>Q) R \<equiv> sort_variables_hint (variable_extension_hint (S\<guillemotright>Q) R')" for S::"_ subspace"
  unfolding join_variables_hint_def variable_extension_hint_def sort_variables_hint_def by simp

lemma join_variables_hint_l2bounded_conv_aux:
  "join_variables_hint (S\<guillemotright>Q) R \<equiv> sort_variables_hint (variable_extension_hint (S\<guillemotright>Q) R')" for S::"(_,_) l2bounded"
  unfolding join_variables_hint_def variable_extension_hint_def sort_variables_hint_def by simp

lemma sort_variables_hint_subspace_conv_aux:
  "sort_variables_hint (S\<guillemotright>Q) \<equiv> variable_renaming_hint (S\<guillemotright>Q) A R'" for S::"_ subspace"
  unfolding variable_renaming_hint_def sort_variables_hint_def by simp

lemma sort_variables_hint_l2bounded_conv_aux:
  "sort_variables_hint (S\<guillemotright>Q) \<equiv> variable_renaming_hint (S\<guillemotright>Q) A R'" for S::"(_,_) l2bounded"
  unfolding variable_renaming_hint_def sort_variables_hint_def by simp

lemma sort_variables_hint_remove_aux: "sort_variables_hint x \<equiv> x" 
  unfolding sort_variables_hint_def by simp


(* For convenience in ML code *)
definition [simp]: "comm_op_pfx = assoc_op* \<cdot> (comm_op\<otimes>id_cblinfun) \<cdot> assoc_op"
definition [simp]: "id_tensor A = id_cblinfun\<otimes>A"
definition [simp]: "assoc_op_adj = assoc_op*"
definition [simp]: "remove_qvar_unit_op2 = remove_qvar_unit_op \<cdot> comm_op"
definition [simp]: "qvar_trafo_mult (Q::'b::universe variables) (B::('b,'c)l2bounded) (A::('a,'b)l2bounded) = timesOp B A"


lemma qvar_trafo_protected_mult[simp]: 
  "qvar_trafo_protected A Q R \<Longrightarrow> qvar_trafo_protected B R S \<Longrightarrow> qvar_trafo_protected (qvar_trafo_mult R B A) Q S"
  unfolding qvar_trafo_protected_def apply simp by (rule qvar_trafo_mult)

lemma qvar_trafo_protected_adj_assoc_op[simp]:
  "distinct_qvars (variable_concat Q (variable_concat R T)) \<Longrightarrow>
    qvar_trafo_protected assoc_op_adj (variable_concat (variable_concat Q R) T)
                                      (variable_concat Q (variable_concat R T))"
  unfolding qvar_trafo_protected_def by simp 

lemma qvar_trafo_protected_assoc_op[simp]:
  "distinct_qvars (variable_concat Q (variable_concat R T)) \<Longrightarrow>
    qvar_trafo_protected assoc_op (variable_concat Q (variable_concat R T))
                                  (variable_concat (variable_concat Q R) T)"
  unfolding qvar_trafo_protected_def by simp 

lemma qvar_trafo_protected_comm_op_pfx[simp]:
  assumes [simp]: "distinct_qvars (variable_concat Q (variable_concat R T))"
  shows "qvar_trafo_protected comm_op_pfx
         (variable_concat Q (variable_concat R T))
         (variable_concat R (variable_concat Q T))"
proof -
  have [simp]: "distinct_qvars (variable_concat Q R)" 
   and [simp]: "distinct_qvars (variable_concat (variable_concat R Q) T)"
   and [simp]: "distinct_qvars (variable_concat (variable_concat Q R) T)"
   and [simp]: "distinct_qvars (variable_concat R (variable_concat Q T)) "
   and [simp]: "distinct_qvars T" 
    using assms by (auto simp: distinct_qvars_split1 distinct_qvars_split2 intro: distinct_qvars_swap distinct_qvarsL)
  show ?thesis
  unfolding qvar_trafo_protected_def comm_op_pfx_def
  apply (rule qvar_trafo_mult[where R="variable_concat (variable_concat Q R) T"])
   apply simp
  apply (rule qvar_trafo_mult[where R="variable_concat (variable_concat R Q) T"])
   apply (rule qvar_trafo_tensor)
  by simp_all
qed

lemma qvar_trafo_protected_remove_qvar_unit_op[simp]:
  assumes "distinct_qvars Q"
  shows "qvar_trafo_protected (remove_qvar_unit_op) (variable_concat Q \<lbrakk>\<rbrakk>) Q"
  unfolding qvar_trafo_protected_def qvar_trafo_def
  by (auto simp: assms remove_qvar_unit_op)

lemma qvar_trafo_protected_remove_qvar_unit_op2[simp]:
  assumes [simp]: "distinct_qvars Q"
  shows "qvar_trafo_protected (remove_qvar_unit_op2) (variable_concat \<lbrakk>\<rbrakk> Q) Q"
  unfolding qvar_trafo_protected_def remove_qvar_unit_op2_def
  apply (rule qvar_trafo_mult)
   apply (rule qvar_trafo_comm_op)
   apply simp
  unfolding qvar_trafo_def
  by (auto simp: remove_qvar_unit_op)


lemma qvar_trafo_protected_id_tensor[simp]:
  assumes [simp]: "distinct_qvars (variable_concat Q R)" and [simp]: "distinct_qvars (variable_concat Q R')"
    and "qvar_trafo_protected A R R'"
  shows "qvar_trafo_protected (id_tensor A) (variable_concat Q R) (variable_concat Q R')"
  unfolding qvar_trafo_protected_def id_tensor_def
  apply (rule qvar_trafo_tensor)
     apply simp_all[2]
   apply (rule qvar_trafo_id)
  using assms(2) apply (rule distinct_qvarsL) 
  using assms(3) unfolding qvar_trafo_protected_def by assumption

lemma qvar_trafo_protected_comm_op[simp]:
  assumes [simp]: "distinct_qvars (variable_concat Q R)"
  shows "qvar_trafo_protected comm_op (variable_concat Q R) (variable_concat R Q)"
  unfolding qvar_trafo_protected_def by simp                                                  

subsubsection \<open>For manually showing existence of qvar_trafo's\<close>

lemma qvar_trafo_ex_tensorL:
  fixes q r s t
  fixes B :: "_ \<Rightarrow>\<^sub>C\<^sub>L _"
  assumes "distinct_qvars (variable_concat Q R)"
  assumes "qvar_trafo B Q S \<and> B *\<^sub>V q = s"
  assumes "distinct_qvars (variable_concat S R)"
  defines "D == (B \<otimes> id_cblinfun)"
  shows "qvar_trafo D (variable_concat Q R) (variable_concat S R) \<and> D *\<^sub>V (q\<otimes>r) = (s\<otimes>r)"
  unfolding D_def apply (rule conjI)
   apply (rule qvar_trafo_tensor[rotated 2])
  using assms apply simp
     apply (rule qvar_trafo_id)
  using assms apply (auto intro: distinct_qvarsL distinct_qvarsR)[1]
  using assms apply simp
  using assms apply (auto intro: distinct_qvarsL distinct_qvarsR)[1]
  by (simp add: assms tensorOp_applyOp_distr cblinfun.scaleC_left)

lemma qvar_trafo_ex_tensorR:
  fixes q r s t u
  assumes "distinct_qvars (variable_concat Q R)"
  assumes "qvar_trafo B R T \<and> B *\<^sub>V r = t"
  assumes "distinct_qvars (variable_concat Q T)"
  defines "D == (id_cblinfun \<otimes> B)"
  shows "qvar_trafo D (variable_concat Q R) (variable_concat Q T) \<and> D *\<^sub>V (q\<otimes>r) = (q\<otimes>t)"
  unfolding D_def apply (rule conjI)
   apply (rule qvar_trafo_tensor[rotated 2])
      apply (rule qvar_trafo_id)
  using assms apply (auto intro: distinct_qvarsL distinct_qvarsR)[1]
  using assms apply simp
  using assms apply (auto intro: distinct_qvarsL distinct_qvarsR)[1]
  using assms unfolding qvar_trafo_def apply simp
  by (simp add: assms tensorOp_applyOp_distr)

lemma qvar_trafo_ex_assoc1:
  fixes Q :: "'q::universe variables" and R :: "'r::universe variables" and S :: "'s::universe variables" and T :: "'t::universe variables"
  fixes q r s :: "_ ell2"
  assumes "distinct_qvars (variable_concat Q (variable_concat R S))"
  shows "qvar_trafo (assoc_op* ) (variable_concat (variable_concat Q R) S) (variable_concat Q (variable_concat R S)) \<and> (assoc_op* ) *\<^sub>V ((q\<otimes>r)\<otimes>s) = (q\<otimes>(r\<otimes>s))"
  apply (rule conjI)
   apply (rule qvar_trafo_adj)
   apply (rule qvar_trafo_assoc_op)
  using assms apply simp
  using assms by simp


lemma qvar_trafo_ex_assoc2:
  fixes Q :: "'q::universe variables" and R :: "'r::universe variables" and S :: "'s::universe variables" and T :: "'t::universe variables"
  fixes q r s :: "_ ell2"
  assumes "distinct_qvars (variable_concat Q (variable_concat R S))"
  shows "qvar_trafo assoc_op (variable_concat Q (variable_concat R S)) (variable_concat (variable_concat Q R) S) \<and> assoc_op *\<^sub>V (q\<otimes>(r\<otimes>s)) = ((q\<otimes>r)\<otimes>s)"
  apply (rule conjI)
   apply (rule qvar_trafo_assoc_op)
  using assms by simp_all

lemma qvar_trafo_ex_comm:
  fixes Q :: "'q::universe variables" and R :: "'r::universe variables" and T :: "'t::universe variables"
  fixes q r :: "_ ell2"
  assumes [simp]: "distinct_qvars (variable_concat Q R)"
  shows "qvar_trafo comm_op (variable_concat Q R) (variable_concat R Q) \<and> comm_op *\<^sub>V (q\<otimes>r) = (r\<otimes>q)"
  apply (rule conjI)
   apply (rule qvar_trafo_comm_op, simp)
  by auto


lemma qvar_trafo_ex_id:
  assumes "distinct_qvars Q"
  shows "qvar_trafo id_cblinfun Q Q \<and> id_cblinfun *\<^sub>V \<psi> = \<psi>"
  using assms by auto

lemma qvar_trafo_ex_trans:
  assumes "qvar_trafo A Q R \<and> A *\<^sub>V \<psi> = \<phi>"
  assumes "qvar_trafo B R S \<and> B *\<^sub>V \<phi> = \<tau>"
  defines "C == B o\<^sub>C\<^sub>L A"
  shows "qvar_trafo C Q S \<and> C *\<^sub>V \<psi> = \<tau>"
  unfolding C_def apply (rule conjI)
   apply (rule qvar_trafo_mult)
  using assms by (auto)

*)


(*
subsection \<open>Rewriting quantum variable lifting, alternative approach\<close>

definition "qvar_trafo' A Q R \<longleftrightarrow> distinct_qvars Q \<and> distinct_qvars R \<and> isometry A \<and> (\<forall>C::(_,_)l2bounded. C\<guillemotright>Q = A\<cdot>(C\<guillemotright>R)\<cdot>A* )"
  for A::"(qu2,qu2) l2bounded"

lemma qvar_trafo'_unitary: assumes "qvar_trafo' A Q R" shows "unitary A"
proof -
  have colocalQ: "distinct_qvars Q" and colocalR: "distinct_qvars R" using assms unfolding qvar_trafo'_def by auto
  have "A \<cdot> A* = id_cblinfun"
  proof -
    have "id_cblinfun\<guillemotright>Q = A \<cdot> id_cblinfun\<guillemotright>R \<cdot> A*"
      using assms unfolding qvar_trafo'_def by auto 
    then show ?thesis 
      apply (subst (asm) lift_id_cblinfun, simp add: colocalQ)
      apply (subst (asm) lift_id_cblinfun, simp add: colocalR)
      by simp
  qed
  moreover have "isometry A"
    using assms unfolding qvar_trafo'_def by auto
  ultimately show ?thesis
    using isometry_def unitary_def by blast
qed

lemma qvar_trafo'_concat:
  fixes Q R Q' R'
  defines "QR \<equiv> variable_concat Q R" and "QR' \<equiv> variable_concat Q' R'"
  assumes "qvar_trafo' A Q Q'"
    and "qvar_trafo' A R R'"
  assumes [simp]: "distinct_qvars QR"
    and  [simp]: "distinct_qvars QR'"
  shows "qvar_trafo' A QR QR'"
proof -
  have "isometry A"
    using assms(3) unfolding qvar_trafo'_def by simp
  define f1 f2 where "f1 C = C\<guillemotright>QR" and "f2 C = A \<cdot> C\<guillemotright>QR' \<cdot> A*" for C :: "(_,_)bounded"
  define tensors where "tensors = {C1 \<otimes> C2| (C1::('a,'a) l2bounded) (C2::('b,'b) l2bounded). True}"
  have "bounded_clinear f1"
  proof (rule bounded_clinear_intro)
    fix X :: "(('a \<times> 'b) ell2, ('a \<times> 'b) ell2) bounded"
      and Y :: "(('a \<times> 'b) ell2, ('a \<times> 'b) ell2) bounded"
      and c :: complex
    show "f1 (X + Y) = f1 X + f1 Y"
      by (simp add: f1_def) 
    show "f1 (c *\<^sub>C X) = c *\<^sub>C f1 X"
      by (simp add: f1_def) 
    show "norm (f1 X) \<le> norm X * 1"
      unfolding f1_def by simp
  qed
  have "bounded_clinear f2"
  proof (rule bounded_clinear_intro)
    fix X :: "(('a \<times> 'b) ell2, ('a \<times> 'b) ell2) bounded"
      and Y :: "(('a \<times> 'b) ell2, ('a \<times> 'b) ell2) bounded"
      and c :: complex
    show "f2 (X + Y) = f2 X + f2 Y"
      by (simp add: f2_def bounded_cbilinear.add_left bounded_cbilinear.add_right bounded_cbilinear_cblinfun_compose flip: lift_plusOp)
    show "f2 (c *\<^sub>C X) = c *\<^sub>C f2 X"
      apply (simp add: f2_def)
      by (metis cblinfun_compose_scaleC_left cblinfun_compose_scaleC_right scaleC_lift)
    have "norm (f2 X) \<le> norm (A \<cdot> X\<guillemotright>QR') * norm (A* )"
      unfolding f2_def by (rule norm_cblinfun_compose)
    also have "\<dots> \<le> norm A * norm (X\<guillemotright>QR') * norm (A* )"
      apply (rule mult_right_mono)
       apply (rule norm_cblinfun_compose)
      by simp
    also have "\<dots> = norm A * norm X * norm (A* )"
      by simp
    finally show "norm (f2 X) \<le> norm X * (norm A * norm (A* ))"
      unfolding f2_def 
      by (simp add: mult.assoc mult.left_commute)
  qed
  have "f1 (C1 \<otimes> C2) = f2 (C1 \<otimes> C2)" for C1 C2
  proof -
    have "(C1\<otimes>C2)\<guillemotright>QR = C1\<guillemotright>Q \<cdot> C2\<guillemotright>R"
      unfolding assms apply (subst lift_tensorOp[symmetric]) using assms by auto
    also have "\<dots> = (A \<cdot> C1\<guillemotright>Q' \<cdot> A* ) \<cdot> (A \<cdot> C2\<guillemotright>R' \<cdot> A* )"
      using assms unfolding qvar_trafo'_def by metis
    also have "\<dots> = A \<cdot> C1\<guillemotright>Q' \<cdot> (A* \<cdot> A) \<cdot> C2\<guillemotright>R' \<cdot> A*"
      by (simp add: cblinfun_compose_assoc)
    also have "\<dots> = A \<cdot> C1\<guillemotright>Q' \<cdot> C2\<guillemotright>R' \<cdot> A*"
      apply (subst isometryD)
      using qvar_trafo'_unitary
      using assms(3) unitary_isometry by auto 
    also have "\<dots> = A \<cdot> (C1\<otimes>C2)\<guillemotright>QR' \<cdot> A*"
      unfolding assms apply (subst lift_tensorOp[symmetric])
      using assms apply blast
      by (auto simp: cblinfun_compose_assoc)
    finally show ?thesis 
      unfolding f1_def f2_def by simp
  qed
  then have f1_f2_tensors: "f1 C = f2 C" if "C \<in> tensors" for C
    using that unfolding tensors_def by auto
  have "f1 = f2"
    apply (rule ext)
    using \<open>bounded_clinear f1\<close> \<open>bounded_clinear f2\<close> f1_f2_tensors
    apply (rule equal_span'[where f=f1 and G=tensors])
    using span_tensors tensors_def
    by auto
  then show ?thesis
    unfolding f1_def f2_def qvar_trafo'_def using assms(5-6) \<open>isometry A\<close> apply auto by metis
qed

lemma qvar_trafo'_l2bounded:
  fixes C::"(_,_) l2bounded"
  assumes "qvar_trafo' A Q R"
  shows "C\<guillemotright>Q = A \<cdot> C\<guillemotright>R \<cdot> A*"
  using assms unfolding qvar_trafo'_def by auto

lemma qvar_trafo'_subspace:
  fixes S::"'a::universe subspace"
  assumes "qvar_trafo' A Q R"
  shows "S\<guillemotright>Q = A \<cdot>(S\<guillemotright>R)"
proof -
  define C where "C = Proj S"
  have "S\<guillemotright>Q = (Proj S \<cdot> top)\<guillemotright>Q" by simp
  also have "\<dots> = (Proj S)\<guillemotright>Q \<cdot> top" by simp
  also have "\<dots> = (A \<cdot> Proj S\<guillemotright>R \<cdot> A* ) \<cdot> top"
    apply (subst qvar_trafo'_l2bounded) using assms by auto
  also have "\<dots> = (A \<cdot> Proj (S\<guillemotright>R) \<cdot> A* ) \<cdot> top"
    using Proj_lift assms qvar_trafo'_def by fastforce
  also have "\<dots> = (Proj (A \<cdot> S\<guillemotright>R)) \<cdot> top"
    apply (subst Proj_sandwich[unfolded sandwich_apply])
    using assms by (simp_all add: qvar_trafo'_unitary)
  also have "\<dots> = A \<cdot> S\<guillemotright>R" by auto
  ultimately show ?thesis by simp
qed

lemma qvar_trafo'_colocal:
  assumes "colocal_op_qvars A Q"
  assumes "unitary A"
  shows "qvar_trafo' A Q Q"
proof -
  from \<open>colocal_op_qvars A Q\<close> have "distinct_qvars Q"
    unfolding distinct_qvars_def apply transfer by auto
  moreover have "C\<guillemotright>Q = A o\<^sub>C\<^sub>L C\<guillemotright>Q o\<^sub>C\<^sub>L A*" for C
  proof -
    from \<open>unitary A\<close> have "C\<guillemotright>Q = C\<guillemotright>Q o\<^sub>C\<^sub>L A o\<^sub>C\<^sub>L A*"
      by (simp add: cblinfun_compose_assoc)
    also from \<open>colocal_op_qvars A Q\<close> have "\<dots> = A o\<^sub>C\<^sub>L C\<guillemotright>Q o\<^sub>C\<^sub>L A*"
      by (subst colocal_op_commute, simp_all)
    finally show ?thesis by -
  qed
  ultimately show ?thesis
    unfolding qvar_trafo'_def
    using assms by auto
qed

lemma qvar_trafo'_comm_op:
  assumes "distinct_qvars (variable_concat Q R)"
  shows "qvar_trafo' (comm_op\<guillemotright>variable_concat Q R) Q R"
proof -
  define QR where "QR = variable_concat Q R"
  from assms have dist_RQ: "distinct_qvars (variable_concat R Q)"
    using distinct_qvars_swap by auto
  from assms have "distinct_qvars Q" and "distinct_qvars R"
    using dist_RQ distinct_qvarsR by blast+
  have "C\<guillemotright>Q = comm_op\<guillemotright>QR \<cdot> C\<guillemotright>R o\<^sub>C\<^sub>L (comm_op\<guillemotright>QR)*" for C
  proof -
    thm comm_op_lift[symmetric]
    have "C\<guillemotright>Q = (C \<otimes> id_cblinfun)\<guillemotright>QR"
      apply (subst lift_extendR) by (auto intro: assms simp: QR_def)
    also have "\<dots> = (comm_op \<cdot> (id_cblinfun \<otimes> C) \<cdot> comm_op* ) \<guillemotright> QR"
      by (simp add: comm_op_lift)
    also have "\<dots> = comm_op\<guillemotright>QR \<cdot> (id_cblinfun \<otimes> C)\<guillemotright>QR \<cdot> (comm_op\<guillemotright>QR)*"
      by (simp add: QR_def assms)
    also have "\<dots> = comm_op\<guillemotright>QR \<cdot> C\<guillemotright>R \<cdot> (comm_op\<guillemotright>QR)*"
      unfolding QR_def apply (subst lift_extendL[symmetric, where U=C])
      using dist_RQ by simp_all
    finally show ?thesis
      by auto
  qed
  with assms \<open>distinct_qvars Q\<close> \<open>distinct_qvars R\<close> show ?thesis
    unfolding qvar_trafo'_def QR_def by auto
qed

lemma qvar_trafo'_comm_op':
  assumes "distinct_qvars (variable_concat Q R)"
  shows "qvar_trafo' (comm_op\<guillemotright>variable_concat R Q) Q R"
  using qvar_trafo'_comm_op
  by (simp add: qvar_trafo'_comm_op assms comm_op_sym)


lemma comm_op_space_lifted[simp]:
  fixes Q R :: "_ variables" and S :: "_ subspace"
  assumes "distinct_qvars (variable_concat Q R)"
  shows "comm_op\<guillemotright>(variable_concat Q R) \<cdot> S\<guillemotright>R = S\<guillemotright>Q"
  using assms qvar_trafo'_comm_op qvar_trafo'_subspace by fastforce

lemma comm_op_space_lifted'[simp]:
  fixes Q R :: "_ variables" and S :: "_ subspace"
  assumes "distinct_qvars (variable_concat Q R)"
  shows "comm_op\<guillemotright>(variable_concat Q R) \<cdot> S\<guillemotright>Q = S\<guillemotright>R"
  by (metis assms comm_op_space_lifted comm_op_sym distinct_qvars_swap)

*)

section \<open>Measurements\<close>

definition "is_measurement M \<longleftrightarrow> ((\<forall>i. is_Proj (M i)) 
       \<and> (\<exists>P. (\<forall>\<psi> \<phi>. (\<Sum>\<^sub>\<infinity> i. \<langle>\<phi>, M i *\<^sub>V \<psi>\<rangle>) = \<langle>\<phi>, P *\<^sub>V \<psi>\<rangle>) \<and> P \<le> id_cblinfun))"
lemma is_measurement_0[simp]: "is_measurement (\<lambda>_. 0)"
  unfolding is_measurement_def
  by (auto intro: exI[of _ 0])


typedef ('a,'b) measurement = "{M::'a\<Rightarrow>('b,'b) l2bounded. is_measurement M}"
  morphisms mproj Abs_measurement
  by (rule exI[of _ "\<lambda>i. 0"], simp)
setup_lifting type_definition_measurement

lift_definition mtotal :: "('a,'b) measurement \<Rightarrow> bool" is
  "\<lambda>M. \<forall>\<psi> \<phi>. (\<Sum>\<^sub>\<infinity> i. \<langle>\<phi>, M i *\<^sub>V \<psi>\<rangle>) = \<langle>\<phi>, \<psi>\<rangle>".

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
  [code del]: "space_div_unlifted S \<psi> = Abs_clinear_space {\<phi>. \<phi>\<otimes>\<psi> \<in> space_as_set S}"

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
definition quantum_equality_full :: "('a,'c) l2bounded \<Rightarrow> 'a q2variable \<Rightarrow> ('b,'c) l2bounded \<Rightarrow> 'b q2variable \<Rightarrow> predicate" where
  [code del]: "quantum_equality_full U Q V R = 
                 (eigenspace 1 (comm_op \<cdot> (V*\<cdot>U)\<otimes>(U*\<cdot>V))) \<guillemotright> qregister_pair Q R"
  for Q :: "'a q2variable" and R :: "'b q2variable"
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
  have a: "comm_op \<cdot> ((V* \<cdot> U) \<otimes> (U* \<cdot> V)) \<cdot> comm_op* = (U* \<cdot> V) \<otimes> (V* \<cdot> U)" by simp
  have op_eq: "((comm_op \<cdot> (V* \<cdot> U) \<otimes> (U* \<cdot> V))\<guillemotright>qregister_pair Q R) =
               ((comm_op \<cdot> (U* \<cdot> V) \<otimes> (V* \<cdot> U))\<guillemotright>qregister_pair R Q)"
    using qregister_pair_chain_swap[of Q R, symmetric]
    sorry
  show ?thesis
    apply (subst quantum_equality_full_def)
    apply (subst quantum_equality_full_def)
    apply (subst eigenspace_lift[symmetric, OF assms])
    apply (subst eigenspace_lift[symmetric, OF dist])
    using op_eq by simp
qed

(* 
lemma qvar_trafo'_quantum_equality_full:
  fixes Q Q' U V R R'
  defines "QR \<equiv> variable_concat Q R" and "QR' \<equiv> variable_concat Q' R'"
  assumes "qvar_trafo' CO QR' QR"
  shows "CO \<cdot> quantum_equality_full U Q V R = quantum_equality_full U Q' V R'"
  unfolding quantum_equality_full_def QR_def[symmetric] QR'_def[symmetric]
  apply (subst qvar_trafo'_subspace[where Q=QR'])
  using assms by auto
 *)

lemma predicate_local[intro!]: 
  assumes "qvariables_local (qregister_pair Q R) S"
  shows "predicate_local (quantum_equality_full U Q V R) S"
  by (cheat predicate_local)

(* lemma colocal_quantum_equality_full[simp,intro!]:
  "colocal_qvars_qvars_str (variable_concat Q1 Q2) Q3 \<Longrightarrow> 
    colocal_pred_qvars_str (quantum_equality_full U1 Q1 U2 Q2) Q3"
for Q1::"'a q2variable" and Q2::"'b q2variable" and Q3::"string set"
and U1 U2::"(_,'d)l2bounded" 
  by (cheat TODO14) *)

(* (* TODO can probably be removed because it's a special case of colocal_quantum_equality_full *)
lemma colocal_quantum_eq[simp,intro!]: 
  "colocal_qvars_qvars_str (variable_concat Q1 Q2) R \<Longrightarrow> colocal_pred_qvars_str (Q1 \<equiv>\<qq> Q2) R"
  for Q1 Q2 :: "'c q2variable" and R :: "string set"
  by (cheat TODO14) *)

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
             = quantum_equality_full (U \<otimes> id_cblinfun) (qregister_pair Q T) (addState \<psi> \<cdot> V) R"
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

(* lemma quantum_equality_reorder:
  fixes U :: "('a,'c) l2bounded" and V :: "('b,'c) l2bounded"
  fixes Q :: "'a q2variable" and R :: "'b q2variable"
  assumes trafoQ: "qvar_trafo A Q Q'"
  assumes trafoR: "qvar_trafo B R R'"
  assumes [simp]: "distinct_qvars (variable_concat Q R)"
  assumes [simp]: "distinct_qvars (variable_concat Q' R')"
  shows "quantum_equality_full U Q V R = quantum_equality_full (U\<cdot>A* ) Q' (V\<cdot>B* ) R'"
proof -
  define QR QR' where "QR = variable_concat Q R" and "QR' = variable_concat Q' R'"
  with trafoQ trafoR have trafoQR: "qvar_trafo (A\<otimes>B) QR QR'"
    by (simp add: qvar_trafo_tensor)
  define VB UA where "VB = V \<cdot> B*" and "UA = U \<cdot> A*"

  have ABcomm: "(A\<otimes>B) \<cdot> comm_op = comm_op \<cdot> (B\<otimes>A)"
  proof -
    have "(A\<otimes>B) \<cdot> comm_op = (comm_op \<cdot> comm_op) \<cdot> ((A\<otimes>B) \<cdot> comm_op)"
      by simp
    also have "\<dots> = comm_op \<cdot> (B\<otimes>A)"
      apply (subst cblinfun_compose_assoc)
      apply (subst cblinfun_compose_assoc[symmetric], subst comm_op_swap)
      by rule
    finally show ?thesis
      by -
  qed

  from trafoQR have "(comm_op \<cdot> (V* \<cdot> U) \<otimes> (U* \<cdot> V))\<guillemotright>QR =
    ((A\<otimes>B) \<cdot> (comm_op \<cdot> (V* \<cdot> U) \<otimes> (U* \<cdot> V)) \<cdot> (A\<otimes>B)* ) \<guillemotright> QR'" (is "_ = liftOp ?rhs _")
    using qvar_trafo_l2bounded by blast
  also have "?rhs = comm_op \<cdot> ((B\<otimes>A) \<cdot> ((V* \<cdot> U) \<otimes> (U* \<cdot> V)) \<cdot> (A\<otimes>B)* )"
    apply (subst cblinfun_compose_assoc[symmetric])+
    apply (subst ABcomm)
    apply (subst cblinfun_compose_assoc)+ by rule
  also have "\<dots> = comm_op \<cdot> (VB* \<cdot> UA) \<otimes> (UA* \<cdot> VB)"
    unfolding VB_def UA_def
    by (simp add: cblinfun_compose_assoc)
  finally show "quantum_equality_full U Q V R = quantum_equality_full UA Q' VB R'"
    unfolding quantum_equality_full_def QR_def QR'_def
    apply (subst eigenspace_lift[symmetric], simp)+
    by simp
qed *)

lemma quantum_equality_full_swap_left:
  assumes [simp]: "distinct_qvars (qregister_pair (qregister_pair Q R) S)"
  shows "quantum_equality_full U (qregister_pair Q R) V S
       = quantum_equality_full (U\<cdot>comm_op) (qregister_pair R Q) V S"
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
    \<le> quantum_equality_full (U1\<otimes>U2) (qregister_pair Q1 Q2) (V1\<otimes>V2) (qregister_pair R1 R2)"
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

(* consts hadamard :: "(bit,bit) l2bounded" *)
lemma unitaryH[simp]: "unitary hadamard"
  by (cheat TODO14)
lemmas adjoint_H[simp] = hada_adj

lemma H_H[simp]: "hadamard \<cdot> hadamard = id_cblinfun"
  using unitaryH unfolding unitary_def by simp

(* definition "hadamard' = sqrt2 \<cdot> hadamard"
lemma H_H': "hadamard = (1/sqrt2) \<cdot> hadamard'" unfolding hadamard'_def by simp
lemma [simp]: "isometry (1 / sqrt2 \<cdot> hadamard')"
  unfolding hadamard'_def by simp *)


(* definition [code del]: "pauliZ = hadamard \<cdot> pauliX \<cdot> hadamard" *)
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

(* definition[code del]: "EPR' = timesScalarVec sqrt2 EPR"

lemma EPR_EPR': "EPR = timesScalarVec (1/sqrt2) EPR'"
  unfolding EPR'_def by simp

lemma norm_EPR'[simp]: "cmod (1/sqrt2) * norm EPR' = 1"
  unfolding EPR'_def using EPR_normalized apply auto
  by (metis divide_cancel_right nonzero_mult_div_cancel_right norm_divide norm_eq_zero norm_one sqrt2_neq0) *)

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
  shows "Uoracle f \<cdot> (ket x \<otimes> ket y) = ket x \<otimes> ket (y + f x)"
  by (simp flip: ket_product)


lemma Uoracle_twice[simp]: 
  fixes f :: "_ \<Rightarrow> _::xor_group"
  assumes "distinct_qvars Q"
  shows "Uoracle f\<guillemotright>Q \<cdot> (Uoracle f\<guillemotright>Q \<cdot> S) = (S::_ ccsubspace)"
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

(* simproc_setup "variable_rewriting" 
  ("join_variables_hint a b" | "sort_variables_hint a" |
   "reorder_variables_hint a b" | "extend_lift_as_var_concat_hint A R") = 
  QRHL.variable_rewriting_simproc *)

simproc_setup distinct_qvars_guard_simproc (\<open>DISTINCT_QVARS_GUARD t\<close>) = QRHL.distinct_qvars_guard_simproc

end
