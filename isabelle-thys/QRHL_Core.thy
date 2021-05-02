theory QRHL_Core
  imports Complex_Main "HOL-Library.Adhoc_Overloading" BOLegacy Discrete_Distributions 
    Universe Misc_Missing Prog_Variables
  keywords "declare_variable_type" :: thy_decl
begin

hide_const (open) Real_Vector_Spaces.span
no_notation Group.monoid.mult (infixl "\<otimes>\<index>" 70)

section \<open>Miscellaneous\<close>

declare Inf_class.INF_image[simp]



(* TODO move into theory Predicates.thy *)
section \<open>Quantum predicates\<close>

type_synonym predicate = "mem2 subspace"

subsection \<open>Classical predicates\<close>
  
definition classical_subspace :: "bool \<Rightarrow> predicate"  ("\<CC>\<ll>\<aa>[_]")
  where "\<CC>\<ll>\<aa>[b] = (if b then top else bot)"
syntax classical_subspace :: "bool \<Rightarrow> predicate"  ("Cla[_]")

lemma classical_true[simp]: "Cla[True] = top" unfolding classical_subspace_def by simp
lemma classical_false[simp]: "Cla[False] = bot" unfolding classical_subspace_def by simp
lemma classical_mono[simp]: "(Cla[a] \<le> Cla[b]) = (a \<longrightarrow> b)" 
  apply (cases a, auto, cases b, auto)
  using bot.extremum_uniqueI clinear_space_top_not_bot by blast 
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
  have "eigenspace b 0 = kernel ((-b) *\<^sub>C idOp)"
    by (auto simp: eigenspace_def)
  also have "\<dots> = kernel idOp"
    using False apply (subst kernel_scalar_times) by auto
  also have "\<dots> = 0"
    by simp
  also have "\<dots> = Cla[b=0]"
    using False by simp
  finally show ?thesis 
      by assumption
qed

lift_definition index_flip_vector :: "mem2 ell2 \<Rightarrow> mem2 ell2" is
  "\<lambda>\<psi>. \<psi> o index_flip_mem2"
  by (cheat index_flip_vector)

lift_definition swap_variables_vector :: "'a::universe variable \<Rightarrow> 'a variable \<Rightarrow> mem2 ell2 \<Rightarrow> mem2 ell2" is
  "\<lambda>v w \<psi>. \<psi> o swap_variables_mem2 v w"
  by (cheat swap_variables_vector)

lift_definition index_flip_subspace :: "mem2 ell2 ccsubspace \<Rightarrow> mem2 ell2 ccsubspace" is
  "\<lambda>S. index_flip_vector ` S"
  by (cheat index_flip_subspace)

lift_definition swap_variables_subspace :: "'a::universe variable \<Rightarrow> 'a variable \<Rightarrow> mem2 ell2 ccsubspace \<Rightarrow> mem2 ell2 ccsubspace" is
  "\<lambda>v w S. swap_variables_vector v w ` S"
  by (cheat swap_variables_subspace)


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

lemma swap_variables_vars_concat[simp]: 
  "swap_variables_vars v w (variable_concat Q R)
   = variable_concat (swap_variables_vars v w Q) (swap_variables_vars v w R)"
  by (cheat swap_variables_vars_concat)

lemma swap_variables_vars_unit[simp]: 
  "swap_variables_vars v w variable_unit = variable_unit"
  by (cheat swap_variables_vars_unit)

lemma swap_variables_vars_singleton1[simp]: 
  "swap_variables_vars v w (variable_singleton v) = variable_singleton w"
  by (cheat swap_variables_vars_singleton1)

lemma swap_variables_vars_singleton2[simp]: 
  "swap_variables_vars v w (variable_singleton w) = variable_singleton v"
  by (cheat swap_variables_vars_singleton2)

lemma swap_variables_vars_singleton3[simp]: 
  "NO_MATCH v z \<Longrightarrow> NO_MATCH w z \<Longrightarrow> distinct_qvars \<lbrakk>v,z\<rbrakk> \<Longrightarrow> distinct_qvars \<lbrakk>w,z\<rbrakk> \<Longrightarrow> swap_variables_vars v w (variable_singleton z) = variable_singleton z"
  by (cheat swap_variables_vars_singleton2)

subsection "Distinct quantum variables"

consts predicate_local_raw :: "predicate \<Rightarrow> variable_raw set \<Rightarrow> bool"
lemma predicate_local_raw_top: "predicate_local_raw top {}" 
  by (cheat predicate_local_raw_top)
lemma predicate_local_raw_bot: "predicate_local_raw bot {}" 
  by (cheat predicate_local_raw_bot)
lemma predicate_local_raw_inter: "predicate_local_raw A Q \<Longrightarrow> predicate_local_raw B Q \<Longrightarrow> predicate_local_raw (A\<sqinter>B) Q" 
  by (cheat predicate_local_raw_inter)
lemma predicate_local_raw_plus: "predicate_local_raw A Q \<Longrightarrow> predicate_local_raw B Q \<Longrightarrow> predicate_local_raw (A+B) Q" 
  by (cheat predicate_local_raw_plus)
lemma predicate_local_raw_sup: "predicate_local_raw A Q \<Longrightarrow> predicate_local_raw B Q \<Longrightarrow> predicate_local_raw (sup A B) Q" 
  by (cheat predicate_local_raw_sup)
lemma predicate_local_raw_ortho: "predicate_local_raw A Q \<Longrightarrow> predicate_local_raw (- A) Q" 
  by (cheat predicate_local_raw_ortho)
lemma predicate_local_raw_mono: "Q \<subseteq> Q' \<Longrightarrow> predicate_local_raw A Q \<Longrightarrow> predicate_local_raw A Q'"
  by (cheat predicate_local_raw_mono)
consts operator_local_raw :: "(mem2,mem2)l2bounded \<Rightarrow> variable_raw set \<Rightarrow> bool"
lemma predicate_local_raw_apply_op: "operator_local_raw U Q \<Longrightarrow> predicate_local_raw A Q \<Longrightarrow> predicate_local_raw (U\<cdot>A) Q" 
  by (cheat predicate_local_raw_apply_op)
lemma operator_local_raw_mono: "Q \<subseteq> Q' \<Longrightarrow> operator_local_raw A Q \<Longrightarrow> operator_local_raw A Q'" 
  by (cheat operator_local_raw_mono)

definition "qvariables_local R Q \<longleftrightarrow> set (raw_variables R) \<subseteq> set (raw_variables Q) \<and> distinct_qvars R \<and> distinct_qvars Q"

lift_definition predicate_local :: "predicate \<Rightarrow> 'a::universe variables \<Rightarrow> bool"
  is  "\<lambda>A (vs,_). distinct (flatten_tree vs) \<and> predicate_local_raw A (set (flatten_tree vs))" .

lift_definition operator_local :: "(mem2,mem2) l2bounded \<Rightarrow> 'a::universe variables \<Rightarrow> bool" 
  is  "\<lambda>A (vs,_). distinct (flatten_tree vs) \<and> operator_local_raw A (set (flatten_tree vs))" .

lift_definition colocal_pred_qvars :: "predicate \<Rightarrow> 'a::universe variables \<Rightarrow> bool"
  is "\<lambda>A (vs,_). distinct (flatten_tree vs) \<and> (\<exists>vs'. set (flatten_tree vs) \<inter> vs' = {} \<and> predicate_local_raw A vs')" .

lift_definition colocal_pred_qvars_str :: "predicate \<Rightarrow> string set \<Rightarrow> bool"
  is "\<lambda>A vs. (\<exists>vs'. vs \<inter> variable_raw_name ` vs' = {} \<and> predicate_local_raw A vs')" .

lift_definition colocal_op_qvars :: "(mem2,mem2) l2bounded \<Rightarrow> 'a::universe variables \<Rightarrow> bool"
  is "\<lambda>A (vs,_). distinct (flatten_tree vs) \<and> (\<exists>vs'. set (flatten_tree vs) \<inter> vs' = {} \<and> operator_local_raw A vs')" .

lift_definition colocal_op_qvars_str :: "(mem2,mem2) l2bounded \<Rightarrow> string set \<Rightarrow> bool"
  is "\<lambda>A vs. (\<exists>vs'. vs \<inter> variable_raw_name ` vs' = {} \<and> operator_local_raw A vs')" .

lift_definition colocal_op_pred :: "(mem2,mem2) l2bounded \<Rightarrow> predicate \<Rightarrow> bool"
  is "\<lambda>A B. \<exists>vs1 vs2. vs1 \<inter> vs2 = {} \<and> operator_local_raw A vs1 \<and> predicate_local_raw B vs2" .

lift_definition colocal_qvars_qvars_str :: "'a::universe variables \<Rightarrow> string set \<Rightarrow> bool"
  is "\<lambda>(vs,_) vs'. distinct (flatten_tree vs) \<and> variable_raw_name ` set (flatten_tree vs) \<inter> vs' = {}" .

consts colocal :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
adhoc_overloading colocal colocal_pred_qvars colocal_op_pred colocal_op_qvars (* colocal_qvars_qvars *)

lemma colocal_pred_qvars_unit[simp]: "colocal_pred_qvars A \<lbrakk>\<rbrakk>"
  by (cheat colocal_pred_qvars_unit)

lemma colocal_op_qvars_unit[simp]: "colocal_op_qvars A \<lbrakk>\<rbrakk>"
  by (cheat colocal_op_qvars_unit)

lemma colocal_qvars_qvars_str[simp, intro!]:
  assumes "distinct_qvars Q"
  assumes "set (variable_names Q) \<inter> R = {}"
  shows "colocal_qvars_qvars_str Q R"
  by (cheat colocal_qvars_qvars_str)

lemma colocal_pred_qvars[simp, intro!]:
  assumes "distinct_qvars Q"
  assumes "colocal_pred_qvars_str S (set (variable_names Q))"
  shows "colocal_pred_qvars S Q"
  by (cheat colocal_pred_qvars)

lemma colocal_op_qvars[simp, intro!]:
  assumes "distinct_qvars Q"
  assumes "colocal_op_qvars_str U (set (variable_names Q))"
  shows "colocal_op_qvars U Q"
  by (cheat colocal_op_qvars)

lemma colocal_top[simp]: "colocal_pred_qvars_str top Q"
  using [[transfer_del_const pcr_ccsubspace]]
  unfolding distinct_qvars_def apply transfer 
  by (auto intro: predicate_local_raw_top exI[of _ "{}"])
lemma colocal_bot[simp]: "colocal_pred_qvars_str bot Q"
  using [[transfer_del_const pcr_ccsubspace]]
  unfolding distinct_qvars_def apply transfer
  by (auto intro: predicate_local_raw_bot exI[of _ "{}"])

lemma colocal_inf[simp, intro!]: 
  assumes "colocal_pred_qvars_str A Q" and "colocal_pred_qvars_str B Q" 
  shows "colocal_pred_qvars_str (A \<sqinter> B) Q"
proof -
  from assms
  obtain vsA vsB where "Q \<inter> variable_raw_name ` vsA = {}" and "predicate_local_raw A vsA"
    and "Q \<inter> variable_raw_name ` vsB = {}" and "predicate_local_raw B vsB"
    apply atomize_elim unfolding colocal_pred_qvars_str.rep_eq by auto
  then have "\<exists>vs'. Q \<inter> variable_raw_name ` vs' = {} \<and> predicate_local_raw (A \<sqinter> B) vs'"
    apply (rule_tac exI[of _ "vsA \<union> vsB"])
    by (auto intro: predicate_local_raw_mono intro!: predicate_local_raw_inter)
  then show ?thesis
    unfolding colocal_pred_qvars_str.rep_eq by simp
qed

lemma colocal_Inf[simp, intro!]: 
  assumes "\<And>A. A\<in>AA \<Longrightarrow> colocal_pred_qvars_str A Q" 
  shows "colocal_pred_qvars_str (Inf AA) Q"
  by (cheat colocal_Inf)

lemma colocal_plus[simp, intro!]: 
  fixes A :: "_ subspace"
  assumes "colocal_pred_qvars_str A Q" and "colocal_pred_qvars_str B Q" shows "colocal_pred_qvars_str (A + B) Q" 
proof -
  from assms
  obtain vsA vsB where "Q \<inter> variable_raw_name ` vsA = {}" and "predicate_local_raw A vsA"
    and "Q \<inter> variable_raw_name ` vsB = {}" and "predicate_local_raw B vsB"
    apply atomize_elim unfolding colocal_pred_qvars_str.rep_eq by auto
  then have "\<exists>vs'. Q \<inter> variable_raw_name ` vs' = {} \<and> predicate_local_raw (A + B) vs'"
    apply (rule_tac exI[of _ "vsA \<union> vsB"])
    by (auto intro: predicate_local_raw_mono intro!: predicate_local_raw_sup)
  then show ?thesis
    unfolding colocal_pred_qvars_str.rep_eq by simp
qed

lemma colocal_sup[simp,intro!]: "colocal_pred_qvars_str A Q \<Longrightarrow> colocal_pred_qvars_str B Q \<Longrightarrow> colocal_pred_qvars_str (A \<squnion> B) Q"
  by (simp flip: plus_ccsubspace_def)
lemma colocal_Cla[simp]: "colocal_pred_qvars_str (Cla[b]) Q"
  by (cases b; simp)

lemma colocal_pred_qvars_mult[simp,intro!]:
  assumes "colocal_op_qvars_str U Q" and "colocal_pred_qvars_str S Q" shows "colocal_pred_qvars_str (U\<cdot>S) Q"
proof -
  from assms
  obtain vsU vsS where "Q \<inter> variable_raw_name ` vsU = {}" and "operator_local_raw U vsU"
    and "Q \<inter> variable_raw_name ` vsS = {}" and "predicate_local_raw S vsS"
    apply atomize_elim unfolding colocal_pred_qvars_str.rep_eq colocal_op_qvars_str.rep_eq by auto
  then have "\<exists>vs'. Q \<inter> variable_raw_name ` vs' = {} \<and> predicate_local_raw (U \<cdot> S) vs'"
    apply (rule_tac exI[of _ "vsU \<union> vsS"])
    by (auto intro: predicate_local_raw_mono operator_local_raw_mono intro!: predicate_local_raw_apply_op)
  then show ?thesis
    unfolding colocal_pred_qvars_str.rep_eq by simp
qed

lemma colocal_ortho[simp]: "colocal_pred_qvars_str (- S) Q = colocal_pred_qvars_str S Q"
proof -
  have "colocal_pred_qvars_str (- S) Q" if "colocal_pred_qvars_str S Q" for S
  proof -
    from that
    obtain vsS where "Q \<inter> variable_raw_name ` vsS = {}" and "predicate_local_raw S vsS"
      apply atomize_elim unfolding colocal_pred_qvars_str.rep_eq by auto
    then have "\<exists>vs'. Q \<inter> variable_raw_name ` vs' = {} \<and> predicate_local_raw (- S) vs'"
      apply (rule_tac exI[of _ vsS])
      by (auto intro: intro!: predicate_local_raw_ortho)
    then show ?thesis
      unfolding colocal_pred_qvars_str.rep_eq by simp
  qed
  from this[where S=S] this[where S="- S"]
  show ?thesis 
    by auto
qed

lemma predicate_local_inf[intro!]: "predicate_local S Q \<Longrightarrow> predicate_local T Q \<Longrightarrow> predicate_local (S\<sqinter>T) Q"
  by (cheat predicate_local_inf)
lemma predicate_local_applyOpSpace[intro!]: "operator_local A Q \<Longrightarrow> predicate_local S Q \<Longrightarrow> predicate_local (A\<cdot>S) Q"
  by (cheat predicate_local_applyOpSpace)
lemma qvariables_localI[intro!]: "set (raw_variables R) \<subseteq> set (raw_variables Q) \<Longrightarrow> distinct_qvars R \<Longrightarrow> distinct_qvars Q
\<Longrightarrow> qvariables_local R Q"
  unfolding qvariables_local_def by simp
lemma operator_local_timesOp[intro!]: "operator_local A Q \<Longrightarrow> operator_local B Q \<Longrightarrow> operator_local (A\<cdot>B) Q"
  by (cheat operator_local_timesOp)

subsection \<open>Lifting\<close>

axiomatization
  (* Convention: If not distinct_qvars Q, then liftOp A Q := 0 *)
  liftOp :: "('a,'a) l2bounded \<Rightarrow> 'a::universe variables \<Rightarrow> (mem2,mem2) l2bounded" and
  (* Convention: If not distinct_qvars Q, then liftOp A Q := bot *)
  liftSpace :: "'a subspace \<Rightarrow> 'a::universe variables \<Rightarrow> predicate" and
  (* lift_vector \<psi> Q \<psi>' = \<psi> \<otimes> \<psi>' where \<psi> is interpreted as a vector over Q, and \<psi>' as a vector over the complement of Q *)
  lift_vector :: "'a ell2 \<Rightarrow> 'a variables \<Rightarrow> mem2 ell2 \<Rightarrow> mem2 ell2" and
  (* lift_rest Q is the set of valid \<psi>' in lift_vector *)
  lift_rest :: "'a variables \<Rightarrow> mem2 ell2 set"

consts lift :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" ("_\<guillemotright>_"  [91,91] 90)
syntax lift :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" ("_>>_"  [91,91] 90)
adhoc_overloading
  lift liftOp liftSpace

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
  assumes "distinct_qvars (variable_concat Q R)"
  shows "(A\<otimes>B)\<guillemotright>(variable_concat Q R) = (A\<guillemotright>Q) \<sqinter> (B\<guillemotright>R)"
  by (cheat tensor_lift)

lemma lift_inf[simp]: "S\<guillemotright>Q \<sqinter> T\<guillemotright>Q = (S \<sqinter> T)\<guillemotright>Q" for S::"'a::universe subspace"
  by (cheat lift_inf)
lemma lift_leq[simp]: "distinct_qvars Q \<Longrightarrow> (S\<guillemotright>Q \<le> T\<guillemotright>Q) = (S \<le> T)" for S::"'a::universe subspace"
  by (cheat lift_leq)
lemma lift_eqSp[simp]: "distinct_qvars Q \<Longrightarrow> (S\<guillemotright>Q = T\<guillemotright>Q) = (S = T)" for S T :: "'a::universe subspace" 
  by (cheat lift_eqSp)
lemma lift_eqOp[simp]: "distinct_qvars Q \<Longrightarrow> (S\<guillemotright>Q = T\<guillemotright>Q) = (S = T)" for S T :: "('a::universe,'a) l2bounded" 
  by (cheat TODO11)
lemma lift_plus[simp]: "S\<guillemotright>Q + T\<guillemotright>Q = (S + T)\<guillemotright>Q" for S T :: "'a::universe subspace"  
  by (cheat TODO11)
lemma lift_sup[simp]: "S\<guillemotright>Q \<squnion> T\<guillemotright>Q = (S \<squnion> T)\<guillemotright>Q" for S T :: "'a::universe subspace"  
  by (cheat TODO11)
lemma lift_plusOp[simp]: "S\<guillemotright>Q + T\<guillemotright>Q = (S + T)\<guillemotright>Q" for S T :: "('a::universe,'a) l2bounded"  
  by (cheat TODO11)
lemma lift_uminusOp[simp]: "- (T\<guillemotright>Q) = (- T)\<guillemotright>Q" for T :: "('a::universe,'a) l2bounded"  
  (* unfolding uminus_l2bounded_def by simp *)
  by (cheat lift_uminusOp)
lemma lift_minusOp[simp]: "S\<guillemotright>Q - T\<guillemotright>Q = (S - T)\<guillemotright>Q" for S T :: "('a::universe,'a) l2bounded"  
  (* unfolding minus_l2bounded_def by simp *)
  by (cheat lift_minusOp)
lemma lift_timesOp[simp]: "S\<guillemotright>Q \<cdot> T\<guillemotright>Q = (S \<cdot> T)\<guillemotright>Q" for S T :: "('a::universe,'a) l2bounded"  
  by (cheat TODO11)
lemma lift_ortho[simp]: "distinct_qvars Q \<Longrightarrow> - (S\<guillemotright>Q) = (- S)\<guillemotright>Q" for Q :: "'a::universe variables" and S :: "'a ell2 ccsubspace"
  by (cheat TODO11)
lemma lift_tensorOp: "distinct_qvars (variable_concat Q R) \<Longrightarrow> (S\<guillemotright>Q) \<cdot> (T\<guillemotright>R) = (S \<otimes> T)\<guillemotright>variable_concat Q R" for Q :: "'a::universe variables" and R :: "'b::universe variables" and S T :: "(_,_) l2bounded" 
  by (cheat TODO11)
lemma lift_tensorSpace: "distinct_qvars (variable_concat Q R) \<Longrightarrow> (S\<guillemotright>Q) = (S \<otimes> top)\<guillemotright>variable_concat Q R" for Q :: "'a::universe variables" and R :: "'b::universe variables" and S :: "_ subspace" 
  by (cheat TODO11)
lemma lift_idOp[simp]: "distinct_qvars Q \<Longrightarrow> idOp\<guillemotright>Q = idOp" for Q :: "'a::universe variables"
  by (cheat TODO11)
lemma INF_lift: "(INF x. S x\<guillemotright>Q) = (INF x. S x)\<guillemotright>Q" for Q::"'a::universe variables" and S::"'b \<Rightarrow> 'a subspace"
  by (cheat TODO11)
lemma Cla_inf_lift: "Cla[b] \<sqinter> (S\<guillemotright>Q) = (if b then S else bot)\<guillemotright>Q" by auto
lemma Cla_plus_lift: "distinct_qvars Q \<Longrightarrow> Cla[b] + (S\<guillemotright>Q) = (if b then top else S)\<guillemotright>Q" by auto
lemma Cla_sup_lift: "distinct_qvars Q \<Longrightarrow> Cla[b] \<squnion> (S\<guillemotright>Q) = (if b then top else S)\<guillemotright>Q" by auto
lemma Proj_lift[simp]: "Proj (S\<guillemotright>Q) = (Proj S)\<guillemotright>Q"
  for Q::"'a::universe variables"
  by (cheat Proj_lift)
lemma kernel_lift[simp]: "distinct_qvars Q \<Longrightarrow> kernel (A\<guillemotright>Q) = (kernel A)\<guillemotright>Q" for Q::"'a::universe variables"
  by (cheat TODO11)
lemma eigenspace_lift[simp]: "distinct_qvars Q \<Longrightarrow> eigenspace a (A\<guillemotright>Q) = (eigenspace a A)\<guillemotright>Q" for Q::"'a::universe variables"
  unfolding eigenspace_def apply (subst lift_idOp[symmetric, of Q], assumption) by (simp del: lift_idOp)

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
  "(remove_qvar_unit_op \<cdot> A \<cdot> remove_qvar_unit_op*)\<guillemotright>Q = A\<guillemotright>(variable_concat Q \<lbrakk>\<rbrakk>)"
for A::"(_,_)l2bounded" and Q::"'a::universe variables"
  by (cheat TODO12)


lemma colocal_op_pred_lift1[simp,intro!]:
 "colocal_pred_qvars S Q \<Longrightarrow> colocal_op_pred (U\<guillemotright>Q) S"
for Q :: "'a::universe variables" and U :: "('a,'a) l2bounded" and S :: predicate
  by (cheat TODO12)

lemma colocal_op_qvars_lift1[simp,intro!]:
  "colocal_qvars_qvars_str Q R \<Longrightarrow> colocal_op_qvars_str (U\<guillemotright>Q) R"
for Q :: "'a::universe variables" and R :: "string set" and U :: "('a,'a) l2bounded"  
  by (cheat TODO12)

lemma colocal_pred_qvars_lift1[simp,intro!]:
  "colocal_qvars_qvars_str Q R \<Longrightarrow> colocal_pred_qvars_str (S\<guillemotright>Q) R"
for Q :: "'a::universe variables" and R :: "string set"
  by (cheat TODO12)

lemma lift_extendR:
  assumes "distinct_qvars (variable_concat Q R)"
  shows "U\<guillemotright>Q = (U\<otimes>idOp)\<guillemotright>(variable_concat Q R)"
  by (metis assms distinct_qvarsR lift_idOp lift_tensorOp times_idOp1)

lemma lift_extendL:
  assumes "distinct_qvars (variable_concat Q R)"
  shows "U\<guillemotright>Q = (idOp\<otimes>U)\<guillemotright>(variable_concat R Q)"
  by (metis assms distinct_qvarsR distinct_qvars_swap lift_idOp lift_tensorOp times_idOp2)

(* TODO: rename: plus \<rightarrow> sup *)
lemma move_plus_meas_rule:
  fixes Q::"'a::universe variables"
  assumes "distinct_qvars Q"
  assumes "(Proj C)\<guillemotright>Q \<cdot> A \<le> B"
  shows "A \<le> (B\<sqinter>C\<guillemotright>Q) \<squnion> (- C)\<guillemotright>Q"
  apply (rule move_plus) 
  using Proj_leq[of "C\<guillemotright>Q"] assms by simp

lemma applyOp_lift: "distinct_qvars Q \<Longrightarrow> A\<guillemotright>Q \<cdot> lift_vector \<psi> Q \<psi>' = lift_vector (A\<cdot>\<psi>) Q \<psi>'"
  by (cheat applyOp_lift)

lemma span_lift: "distinct_qvars Q \<Longrightarrow> ccspan G \<guillemotright> Q = ccspan {lift_vector \<psi> Q \<psi>' | \<psi> \<psi>'. \<psi>\<in>G \<and> \<psi>' \<in> lift_rest Q}"
  by (cheat span_lift)

lemma lift_rest_nonempty: "lift_rest Q - {0} \<noteq> {}"
  by (cheat lift_rest_nonempty)

lemma lift_vector_inj:
  assumes "r \<in> lift_rest Q"
  assumes "r \<noteq> 0"
  assumes "lift_vector \<psi>1 Q r = lift_vector \<psi>2 Q r"
  shows "\<psi>1 = \<psi>2"
  by (cheat lift_vector_inj)


lemma applyOpSpace_eq':
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
    using A'B' S'_spanG by (rule applyOpSpace_eq)

  then show ?thesis
    unfolding S A B by simp
qed

lemma index_flip_subspace_lift[simp]: "index_flip_subspace (S\<guillemotright>Q) = S \<guillemotright> index_flip_vars Q"
  by (cheat index_flip_subspace_lift)

lemma swap_variables_subspace_lift[simp]: "swap_variables_subspace v w (S\<guillemotright>Q) = S \<guillemotright> swap_variables_vars v w Q"
  by (cheat index_flip_subspace_lift)


lemma ket_less_specific:
  assumes "distinct_qvars (variable_concat X Y)"
  shows "ccspan {ket (x,y)}\<guillemotright>variable_concat X Y \<le> ccspan {ket y}\<guillemotright>Y"
proof -
  have "ccspan {ket (x,y)}\<guillemotright>variable_concat X Y = ccspan {x' \<otimes> y' | x' y'. x'\<in>{ket x} \<and> y'\<in>{ket y}}\<guillemotright>variable_concat X Y"
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
  by (simp del: adj_comm_op flip: adjoint_lift cblinfun_apply_assoc_clinear_space)


subsection "Rewriting quantum variable lifting"

(* TODO: use new constant conjugate for A\<cdot>B\<cdot>A* expressions to avoid duplication *)

(* Means that operator A can be used to transform an expression \<dots>\<guillemotright>Q into \<dots>\<guillemotright>R *)
definition "qvar_trafo A Q R \<longleftrightarrow> distinct_qvars Q \<and> distinct_qvars R \<and> (\<forall>C::(_,_)l2bounded. C\<guillemotright>Q = (A\<cdot>C\<cdot>A*)\<guillemotright>R)" for A::"('a::universe,'b::universe) l2bounded"

lemma qvar_trafo_id[simp]: "distinct_qvars Q \<Longrightarrow> qvar_trafo idOp Q Q" unfolding qvar_trafo_def by auto

(* Auxiliary lemma, will be removed after generalizing to qvar_trafo_unitary *)
lemma qvar_trafo_coiso: assumes "qvar_trafo A Q R" shows "A \<cdot> A* = idOp"
proof -
  have colocalQ: "distinct_qvars Q" and colocalR: "distinct_qvars R" using assms unfolding qvar_trafo_def by auto
  have "idOp\<guillemotright>Q = (A \<cdot> idOp \<cdot> A*)\<guillemotright>R"
    using assms unfolding qvar_trafo_def by auto 
  hence "idOp\<guillemotright>R = (A \<cdot> A*)\<guillemotright>R" using colocalR colocalQ by auto
  hence "idOp = A \<cdot> A*" apply (subst lift_eqOp[symmetric])
    using colocalR by auto
  then show ?thesis ..
qed

lemma qvar_trafo_adj[simp]: assumes "qvar_trafo A Q R" shows "qvar_trafo (A*) R Q"
proof (unfold qvar_trafo_def, auto)
  show colocalQ: "distinct_qvars Q" and colocalR: "distinct_qvars R" using assms unfolding qvar_trafo_def by auto
  show "C\<guillemotright>R = (A* \<cdot> C \<cdot> A)\<guillemotright>Q" for C::"(_,_)l2bounded"
  proof -
    have "(A* \<cdot> C \<cdot> A)\<guillemotright>Q = (A \<cdot> (A* \<cdot> C \<cdot> A) \<cdot> A*)\<guillemotright>R"
      using assms unfolding qvar_trafo_def by auto 
    also have "\<dots> = ((A \<cdot> A*) \<cdot> C \<cdot> (A \<cdot> A*)*)\<guillemotright>R"
      by (simp add: cblinfun_apply_assoc)
    also have "\<dots> = C\<guillemotright>R" apply (subst qvar_trafo_coiso[OF assms])+ by auto 
    finally show ?thesis ..
  qed
qed

lemma qvar_trafo_unitary:
  assumes "qvar_trafo A Q R"
  shows "unitary A"
proof -
  have "qvar_trafo (A*) R Q"
    using assms by (rule qvar_trafo_adj)
  hence "(A*) \<cdot> (A*)* = idOp" by (rule qvar_trafo_coiso)
  hence "A* \<cdot> A = idOp" by simp
  also have "A \<cdot> A* = idOp"
    using assms by (rule qvar_trafo_coiso)
  ultimately show ?thesis unfolding unitary_def by simp
qed

hide_fact qvar_trafo_coiso (* Subsumed by qvar_trafo_unitary *)

lemma assoc_op_lift: "(assoc_op \<cdot> A \<cdot> assoc_op*)\<guillemotright>(variable_concat (variable_concat Q R) T)
     = A\<guillemotright>(variable_concat Q (variable_concat R T))" for A::"('a::universe*'b::universe*'c::universe,_)l2bounded" 
  by (cheat assoc_op_lift)
lemma assoc_op_lift': "(assoc_op* \<cdot> A \<cdot> assoc_op)\<guillemotright>(variable_concat Q (variable_concat R T))
     = A\<guillemotright>(variable_concat (variable_concat Q R) T)" for A::"(('a::universe*'b::universe)*'c::universe,_)l2bounded" 
  by (cheat assoc_op_lift')
lemma comm_op_lift: "(comm_op \<cdot> A \<cdot> comm_op*)\<guillemotright>(variable_concat Q R)
     = A\<guillemotright>(variable_concat R Q)" for A::"('a::universe*'b::universe,_)l2bounded" 
  by (cheat comm_op_lift)
lemma lift_tensor_id: "distinct_qvars (variable_concat Q R) \<Longrightarrow> distinct_qvars (variable_concat Q R) \<Longrightarrow>
   (\<And>D::(_,_) l2bounded. (A \<cdot> D \<cdot> A*)\<guillemotright>Q = D\<guillemotright>Q') \<Longrightarrow> (\<And>D::(_,_) l2bounded. (A' \<cdot> D \<cdot> A'*)\<guillemotright>R = D\<guillemotright>R') \<Longrightarrow> 
  ((A\<otimes>A') \<cdot> C \<cdot> (A\<otimes>A')*)\<guillemotright>variable_concat Q R = C\<guillemotright>variable_concat Q' R'"
  for A :: "('a::universe,'b::universe) l2bounded" and A' :: "('c::universe,'d::universe) l2bounded" and C::"(_,_) l2bounded" and Q R :: "_ variables"
  by (cheat lift_tensor_id)

lemma comm_op_sym:
  "comm_op \<guillemotright> variable_concat Q R = comm_op \<guillemotright> variable_concat R Q"
  using comm_op_lift[where A=comm_op and Q=Q and R=R] by simp



lemma qvar_trafo_assoc_op[simp]:
  assumes "distinct_qvars (variable_concat Q (variable_concat R T))"
  shows "qvar_trafo assoc_op (variable_concat Q (variable_concat R T))  (variable_concat (variable_concat Q R) T)"
proof (unfold qvar_trafo_def, auto)
  show "distinct_qvars (variable_concat Q (variable_concat R T))" and "distinct_qvars (variable_concat (variable_concat Q R) T)"
    using assms by (auto intro: distinct_qvars_swap simp: distinct_qvars_split1 distinct_qvars_split2)
  show "C\<guillemotright>variable_concat Q (variable_concat R T) = (assoc_op \<cdot> C \<cdot> assoc_op*)\<guillemotright>variable_concat (variable_concat Q R) T" for C::"(_,_)l2bounded"
    by (rule assoc_op_lift[symmetric])
qed


lemma qvar_trafo_comm_op[simp]:
  assumes "distinct_qvars (variable_concat Q R)"
  shows "qvar_trafo comm_op (variable_concat Q R) (variable_concat R Q)"
proof (unfold qvar_trafo_def, auto simp del: adj_comm_op)
  show "distinct_qvars (variable_concat Q R)" and "distinct_qvars (variable_concat R Q)"
    using assms by (auto intro: distinct_qvars_swap)
  show "C\<guillemotright>variable_concat Q R = (comm_op \<cdot> C \<cdot> comm_op*)\<guillemotright>variable_concat R Q" for C::"(_,_)l2bounded"
    by (rule comm_op_lift[symmetric])
qed

lemma qvar_trafo_l2bounded:
  fixes C::"(_,_) l2bounded"
  assumes "qvar_trafo A Q R"
  shows "C\<guillemotright>Q = (A\<cdot>C\<cdot>A*)\<guillemotright>R"
  using assms unfolding qvar_trafo_def by auto

lemma qvar_trafo_subspace:
  fixes S::"'a::universe subspace"
  assumes "qvar_trafo A Q R"
  shows "S\<guillemotright>Q = (A\<cdot>S)\<guillemotright>R"
proof -
  define C where "C = Proj S"
  have "S\<guillemotright>Q = (Proj S \<cdot> top)\<guillemotright>Q" by simp
  also have "\<dots> = (Proj S)\<guillemotright>Q \<cdot> top" by simp
  also have "\<dots> = (A \<cdot> Proj S \<cdot> A*)\<guillemotright>R \<cdot> top"
    apply (subst qvar_trafo_l2bounded) using assms by auto
  also have "\<dots> = (Proj (A\<cdot>S))\<guillemotright>R \<cdot> top"
    apply (subst Proj_times)
    using assms by (simp_all add: qvar_trafo_unitary)
  also have "\<dots> = (Proj (A\<cdot>S) \<cdot> top)\<guillemotright>R" by auto
  also have "\<dots> = (A\<cdot>S)\<guillemotright>R" by auto
  ultimately show ?thesis by simp
qed

lemma qvar_trafo_mult:
  assumes "qvar_trafo A Q R"
    and "qvar_trafo B R S"
  shows "qvar_trafo (B\<cdot>A) Q S"
proof (unfold qvar_trafo_def, auto)
  show colocalQ: "distinct_qvars Q" and colocalS: "distinct_qvars S" using assms unfolding qvar_trafo_def by auto
  show "C\<guillemotright>Q = (B \<cdot> A \<cdot> C \<cdot> (A* \<cdot> B*))\<guillemotright>S" for C::"(_,_) l2bounded"
  proof -
    have "C\<guillemotright>Q = (A \<cdot> C \<cdot> A*)\<guillemotright>R" apply (rule qvar_trafo_l2bounded) using assms by simp
    also have "\<dots> = (B \<cdot> (A \<cdot> C \<cdot> A*) \<cdot> B*)\<guillemotright>S" apply (rule qvar_trafo_l2bounded) using assms by simp
    also have "\<dots> = (B \<cdot> A \<cdot> C \<cdot> (A* \<cdot> B*))\<guillemotright>S" using cblinfun_apply_assoc by metis
    finally show ?thesis .
  qed
qed

lemma qvar_trafo_tensor:
  assumes "distinct_qvars (variable_concat Q Q')"
    and "distinct_qvars (variable_concat R R')"
    and "qvar_trafo A Q R"
    and "qvar_trafo A' Q' R'"
  shows "qvar_trafo (A\<otimes>A') (variable_concat Q Q') (variable_concat R R')"
proof (unfold qvar_trafo_def, (rule conjI[rotated])+, rule allI)
  show "distinct_qvars (variable_concat Q Q')" and "distinct_qvars (variable_concat R R')"
    using assms unfolding qvar_trafo_def by auto
  show "C\<guillemotright>variable_concat Q Q' = ((A \<otimes> A') \<cdot> C \<cdot> (A \<otimes> A')*)\<guillemotright>variable_concat R R'" for C::"(_,_)l2bounded"
    apply (rule lift_tensor_id[symmetric])
    using assms unfolding qvar_trafo_def by auto
qed


(* A hint to the simplifier with the meaning:
    - A is a term of the form x>>Q
    - R is an explicit distinct varterm containing all variables in Q
    - Q is an explicit distinct varterm
    - The whole term should be rewritten into x'>>R for some x'
  Rewriting the term is done by the simproc variable_rewriting_simproc declared below.
*)
definition "reorder_variables_hint A R = A"
lemma [cong]: "A=A' \<Longrightarrow> reorder_variables_hint A R = reorder_variables_hint A' R" by simp

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
definition "variable_renaming_hint x (A::('a,'b) l2bounded) (R::'b::universe variables) = x"
lemma variable_renaming_hint_cong[cong]: "x=x' \<Longrightarrow> variable_renaming_hint x A R = variable_renaming_hint x' A R" by simp

(* A copy of qvars_trafo that is protected from unintentional rewriting *)
definition "qvar_trafo_protected = qvar_trafo"
lemma qvar_trafo_protected_cong[cong]: "qvar_trafo_protected A Q R = qvar_trafo_protected A Q R" ..

lemma variable_renaming_hint_subspace[simp]:
  fixes S::"_ subspace"
  assumes "qvar_trafo_protected A Q R"
  shows "variable_renaming_hint (S\<guillemotright>Q) A R = (A\<cdot>S)\<guillemotright>R"
  using assms unfolding variable_renaming_hint_def qvar_trafo_protected_def by (rule qvar_trafo_subspace)

lemma variable_renaming_hint_l2bounded[simp]:
  fixes S::"(_,_) l2bounded"
  assumes "qvar_trafo_protected A Q R"
  shows "variable_renaming_hint (S\<guillemotright>Q) A R = (A\<cdot>S\<cdot>A*)\<guillemotright>R"
  using assms unfolding variable_renaming_hint_def qvar_trafo_protected_def by (rule qvar_trafo_l2bounded)


lemma extend_space_lift_aux: \<comment> \<open>Auxiliary lemma for extend_lift_conv\<close>
  fixes Q :: "'q::universe variables" and R :: "'r::universe variables"
    and S :: "'q subspace"
  assumes "distinct_qvars (variable_concat Q R)"
  shows "S\<guillemotright>Q \<equiv> (S\<otimes>top)\<guillemotright>(variable_concat Q R)"
  apply (rule eq_reflection)
  using assms by (rule lift_tensorSpace)


lemma extend_l2bounded_lift_aux: \<comment> \<open>Auxiliary lemma for extend_lift_conv\<close>
  fixes Q :: "'q::universe variables" and R :: "'r::universe variables"
    and S :: "('q,'q) l2bounded"
  assumes "distinct_qvars (variable_concat Q R)"
  shows "S\<guillemotright>Q \<equiv> (S\<otimes>idOp)\<guillemotright>(variable_concat Q R)"
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
  shows "S\<guillemotright>Q \<equiv> (A\<cdot>S\<cdot>A*)\<guillemotright>R"
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
  shows "variable_extension_hint (S\<guillemotright>Q) R = (S\<otimes>idOp)\<guillemotright>variable_concat Q R"
  unfolding variable_extension_hint_def 
  using assms
  using extend_l2bounded_lift_aux by blast

(* Hint for the simplifier, meaning that:
    - x is of the form x'\<guillemotright>Q
    - colocal Q [], colocal R [] holds
    - the whole expression should be rewritten to x'\<guillemotright>Q\<otimes>R' such that Q\<otimes>R' has the same variables as Q\<otimes>R (duplicates removed)
  Rewriting the term is done by the simplifier rules declared below.
*)
definition "join_variables_hint x (R::'a::universe variables) = x"

lemma add_join_variables_hint: 
  fixes Q :: "'a::universe variables" and R :: "'b::universe variables" 
    and S :: "'a subspace" and T :: "'b subspace"
    and A :: "('a,'a) l2bounded" and B :: "('b,'b) l2bounded"
  shows "NO_MATCH (a,a) (Q,R) \<Longrightarrow> S\<guillemotright>Q \<sqinter> T\<guillemotright>R = join_variables_hint (S\<guillemotright>Q) R \<sqinter> join_variables_hint (T\<guillemotright>R) Q"
    and "NO_MATCH (a,a) (Q,R) \<Longrightarrow> S\<guillemotright>Q + T\<guillemotright>R = join_variables_hint (S\<guillemotright>Q) R + join_variables_hint (T\<guillemotright>R) Q"
    and "NO_MATCH (a,a) (Q,R) \<Longrightarrow> S\<guillemotright>Q \<squnion> T\<guillemotright>R = join_variables_hint (S\<guillemotright>Q) R \<squnion> join_variables_hint (T\<guillemotright>R) Q"
    and "NO_MATCH (a,a) (Q,R) \<Longrightarrow> A\<guillemotright>Q \<cdot> T\<guillemotright>R = join_variables_hint (A\<guillemotright>Q) R \<cdot> join_variables_hint (T\<guillemotright>R) Q"
    and "NO_MATCH (a,a) (Q,R) \<Longrightarrow> (S\<guillemotright>Q \<le> T\<guillemotright>R) = (join_variables_hint (S\<guillemotright>Q) R \<le> join_variables_hint (T\<guillemotright>R) Q)"
    and "NO_MATCH (a,a) (Q,R) \<Longrightarrow> (S\<guillemotright>Q = T\<guillemotright>R) = (join_variables_hint (S\<guillemotright>Q) R = join_variables_hint (T\<guillemotright>R) Q)"
    and "NO_MATCH (a,a) (Q,R) \<Longrightarrow> (A\<guillemotright>Q = B\<guillemotright>R) = (join_variables_hint (A\<guillemotright>Q) R = join_variables_hint (B\<guillemotright>R) Q)"
    and "NO_MATCH (a,a) (Q,R) \<Longrightarrow> (A\<guillemotright>Q + B\<guillemotright>R) = (join_variables_hint (A\<guillemotright>Q) R + join_variables_hint (B\<guillemotright>R) Q)"
    and "NO_MATCH (a,a) (Q,R) \<Longrightarrow> (A\<guillemotright>Q - B\<guillemotright>R) = (join_variables_hint (A\<guillemotright>Q) R - join_variables_hint (B\<guillemotright>R) Q)"
    and "NO_MATCH (a,a) (Q,R) \<Longrightarrow> (A\<guillemotright>Q \<cdot> B\<guillemotright>R) = (join_variables_hint (A\<guillemotright>Q) R \<cdot> join_variables_hint (B\<guillemotright>R) Q)"
  unfolding join_variables_hint_def by simp_all



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
definition [simp]: "comm_op_pfx = assoc_op* \<cdot> (comm_op\<otimes>idOp) \<cdot> assoc_op"
definition [simp]: "id_tensor A = idOp\<otimes>A"
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
  defines "D == (B \<otimes> idOp)"
  shows "qvar_trafo D (variable_concat Q R) (variable_concat S R) \<and> D *\<^sub>V (q\<otimes>r) = (s\<otimes>r)"
  unfolding D_def apply (rule conjI)
   apply (rule qvar_trafo_tensor[rotated 2])
  using assms apply simp
     apply (rule qvar_trafo_id)
  using assms apply (auto intro: distinct_qvarsL distinct_qvarsR)[1]
  using assms apply simp
  using assms apply (auto intro: distinct_qvarsL distinct_qvarsR)[1]
  by (simp add: assms tensorOp_applyOp_distr times_applyOp)

lemma qvar_trafo_ex_tensorR:
  fixes q r s t u
  assumes "distinct_qvars (variable_concat Q R)"
  assumes "qvar_trafo B R T \<and> B *\<^sub>V r = t"
  assumes "distinct_qvars (variable_concat Q T)"
  defines "D == (idOp \<otimes> B)"
  shows "qvar_trafo D (variable_concat Q R) (variable_concat Q T) \<and> D *\<^sub>V (q\<otimes>r) = (q\<otimes>t)"
  unfolding D_def apply (rule conjI)
   apply (rule qvar_trafo_tensor[rotated 2])
      apply (rule qvar_trafo_id)
  using assms apply (auto intro: distinct_qvarsL distinct_qvarsR)[1]
  using assms apply simp
  using assms apply (auto intro: distinct_qvarsL distinct_qvarsR)[1]
  using assms unfolding qvar_trafo_def apply simp
  by (simp add: assms tensorOp_applyOp_distr times_applyOp)

lemma qvar_trafo_ex_assoc1:
  fixes Q :: "'q::universe variables" and R :: "'r::universe variables" and S :: "'s::universe variables" and T :: "'t::universe variables"
  fixes q r s :: "_ ell2"
  assumes "distinct_qvars (variable_concat Q (variable_concat R S))"
  shows "qvar_trafo (assoc_op*) (variable_concat (variable_concat Q R) S) (variable_concat Q (variable_concat R S)) \<and> (assoc_op*) *\<^sub>V ((q\<otimes>r)\<otimes>s) = (q\<otimes>(r\<otimes>s))"
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
  by (auto simp: times_applyOp)


lemma qvar_trafo_ex_id:
  assumes "distinct_qvars Q"
  shows "qvar_trafo idOp Q Q \<and> idOp *\<^sub>V \<psi> = \<psi>"
  using assms by auto

lemma qvar_trafo_ex_trans:
  assumes "qvar_trafo A Q R \<and> A *\<^sub>V \<psi> = \<phi>"
  assumes "qvar_trafo B R S \<and> B *\<^sub>V \<phi> = \<tau>"
  defines "C == B o\<^sub>C\<^sub>L A"
  shows "qvar_trafo C Q S \<and> C *\<^sub>V \<psi> = \<tau>"
  unfolding C_def apply (rule conjI)
   apply (rule qvar_trafo_mult)
  using assms by (auto simp: times_applyOp)

subsection \<open>Rewriting quantum variable lifting, alternative approach\<close>

definition "qvar_trafo' A Q R \<longleftrightarrow> distinct_qvars Q \<and> distinct_qvars R \<and> isometry A \<and> (\<forall>C::(_,_)l2bounded. C\<guillemotright>Q = A\<cdot>(C\<guillemotright>R)\<cdot>A*)"
  for A::"(mem2,mem2) l2bounded"

lemma qvar_trafo'_unitary: assumes "qvar_trafo' A Q R" shows "unitary A"
proof -
  have colocalQ: "distinct_qvars Q" and colocalR: "distinct_qvars R" using assms unfolding qvar_trafo'_def by auto
  have "A \<cdot> A* = idOp"
  proof -
    have "idOp\<guillemotright>Q = A \<cdot> idOp\<guillemotright>R \<cdot> A*"
      using assms unfolding qvar_trafo'_def by auto 
    then show ?thesis 
      apply (subst (asm) lift_idOp, simp add: colocalQ)
      apply (subst (asm) lift_idOp, simp add: colocalR)
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
      by (simp add: f2_def cblinfun_apply_dist1 cblinfun_apply_dist2 flip: lift_plusOp)
    show "f2 (c *\<^sub>C X) = c *\<^sub>C f2 X"
      apply (simp add: f2_def)
      by (metis op_scalar_op scalar_op_op scaleC_lift)
    have "norm (f2 X) \<le> norm (A \<cdot> X\<guillemotright>QR') * norm (A*)"
      unfolding f2_def by (rule norm_mult_ineq_cblinfun)
    also have "\<dots> \<le> norm A * norm (X\<guillemotright>QR') * norm (A*)"
      apply (rule mult_right_mono)
       apply (rule norm_mult_ineq_cblinfun)
      by simp
    also have "\<dots> = norm A * norm X * norm (A*)"
      by simp
    finally show "norm (f2 X) \<le> norm X * (norm A * norm (A*))"
      unfolding f2_def 
      by (simp add: mult.assoc mult.left_commute)
  qed
  have "f1 (C1 \<otimes> C2) = f2 (C1 \<otimes> C2)" for C1 C2
  proof -
    have "(C1\<otimes>C2)\<guillemotright>QR = C1\<guillemotright>Q \<cdot> C2\<guillemotright>R"
      unfolding assms apply (subst lift_tensorOp[symmetric]) using assms by auto
    also have "\<dots> = (A \<cdot> C1\<guillemotright>Q' \<cdot> A*) \<cdot> (A \<cdot> C2\<guillemotright>R' \<cdot> A*)"
      using assms unfolding qvar_trafo'_def by metis
    also have "\<dots> = A \<cdot> C1\<guillemotright>Q' \<cdot> (A* \<cdot> A) \<cdot> C2\<guillemotright>R' \<cdot> A*"
      by (simp add: cblinfun_apply_assoc)
    also have "\<dots> = A \<cdot> C1\<guillemotright>Q' \<cdot> C2\<guillemotright>R' \<cdot> A*"
      apply (subst adjUU)
      using qvar_trafo'_unitary
      using assms(3) unitary_isometry by auto 
    also have "\<dots> = A \<cdot> (C1\<otimes>C2)\<guillemotright>QR' \<cdot> A*"
      unfolding assms apply (subst lift_tensorOp[symmetric])
      using assms by (auto simp: cblinfun_apply_assoc)
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
  also have "\<dots> = (A \<cdot> Proj S\<guillemotright>R \<cdot> A*) \<cdot> top"
    apply (subst qvar_trafo'_l2bounded) using assms by auto
  also have "\<dots> = (A \<cdot> Proj (S\<guillemotright>R) \<cdot> A*) \<cdot> top"
    using Proj_lift assms qvar_trafo'_def by fastforce
  also have "\<dots> = (Proj (A \<cdot> S\<guillemotright>R)) \<cdot> top"
    apply (subst Proj_times)
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
      by (simp add: assoc_right)
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
    have "C\<guillemotright>Q = (C \<otimes> idOp)\<guillemotright>QR"
      apply (subst lift_extendR) by (auto intro: assms simp: QR_def)
    also have "\<dots> = (comm_op \<cdot> (idOp \<otimes> C) \<cdot> comm_op*) \<guillemotright> QR"
      by (simp add: comm_op_lift)
    also have "\<dots> = comm_op\<guillemotright>QR \<cdot> (idOp \<otimes> C)\<guillemotright>QR \<cdot> (comm_op\<guillemotright>QR)*"
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
  by (metis adj_comm_op assms comm_op_lift comm_op_times_comm_op times_adjoint times_idOp1)


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



section \<open>Measurements\<close>

(* definition "infsetsums f M x = ((\<lambda>F. sum f F) \<longlongrightarrow> x) (finite_subsets_at_top M)"
definition "infsetsummable f M = (\<exists>x. infsetsums f M x)"
(* I think this is equal to infsetsum, except that infsetsum is only defined on second countable topologies *)
definition "infsetsum' f M = (if infsetsummable f M then THE x. infsetsums f M x else 0)" *)


definition "is_measurement M \<longleftrightarrow> ((\<forall>i. isProjector (M i)) 
       \<and> (\<exists>P. (\<forall>\<psi> \<phi>. (\<Sum>\<^sub>a i. \<langle>\<phi>, M i *\<^sub>V \<psi>\<rangle>) = \<langle>\<phi>, P *\<^sub>V \<psi>\<rangle>) \<and> loewner_leq P idOp))"
lemma is_measurement_0[simp]: "is_measurement (\<lambda>_. 0)"
  unfolding is_measurement_def by (auto intro: exI[of _ 0])


typedef ('a,'b) measurement = "{M::'a\<Rightarrow>('b,'b) l2bounded. is_measurement M}"
  morphisms mproj Abs_measurement
  by (rule exI[of _ "\<lambda>i. 0"], simp)
setup_lifting type_definition_measurement

lift_definition mtotal :: "('a,'b) measurement \<Rightarrow> bool" is
  "\<lambda>M. \<forall>\<psi> \<phi>. (\<Sum>\<^sub>a i. \<langle>\<phi>, M i *\<^sub>V \<psi>\<rangle>) = \<langle>\<phi>, \<psi>\<rangle>".

lemma isProjector_mproj[simp]: "isProjector (mproj M i)"
  using mproj[of M] unfolding is_measurement_def by auto

lift_definition computational_basis :: "('a, 'a) measurement" is
  "\<lambda>i. proj (ket i)"
  by (cheat computational_basis)

lemma mproj_computational_basis[simp]: "mproj computational_basis x = proj (ket x)"
  unfolding computational_basis.rep_eq by simp

lemma mtotal_computational_basis [simp]: "mtotal computational_basis"
  by (cheat mtotal_computational_basis)

lift_definition binary_measurement :: "('a,'a) l2bounded \<Rightarrow> (bit,'a) measurement" is
  "\<lambda>(P::('a,'a) l2bounded) (b::bit). (if isProjector P then (if b=1 then P else idOp-P) else 0)"
proof (rename_tac P, case_tac "isProjector P")
  fix P :: "('a ell2, 'a ell2) bounded"
  assume [simp]: "isProjector P"
  show "is_measurement (\<lambda>b::bit. if isProjector P then if b = 1 then P else idOp - P else 0)"
    apply simp
    unfolding is_measurement_def apply (auto intro!: exI[of _ idOp] simp: UNIV_bit cinner_add_right[symmetric])
    by (metis apply_idOp diff_add_cancel plus_cblinfun.rep_eq)
next
  fix P :: "('a ell2, 'a ell2) bounded"
  assume [simp]: "\<not> isProjector P"
  show "is_measurement (\<lambda>b. if isProjector P then if b = 1 then P else idOp - P else 0)"
    by simp
qed

lemma binary_measurement_true[simp]: "isProjector P \<Longrightarrow> mproj (binary_measurement P) 1 = P"
  apply transfer by simp

lemma binary_measurement_false[simp]: "isProjector P \<Longrightarrow> mproj (binary_measurement P) 0 = idOp-P"
  unfolding binary_measurement.rep_eq by auto

lemma mtotal_binary_measurement[simp]: "mtotal (binary_measurement P) = isProjector P"
  apply (transfer fixing: P) apply (cases "isProjector P") apply (auto simp: UNIV_bit)
  apply (metis apply_idOp cinner_add_right diff_add_cancel minus_cblinfun.rep_eq)
  by (rule exI[of _ "ket undefined"], rule exI[of _ "ket undefined"], simp)


section \<open>Quantum predicates (ctd.)\<close>

subsection \<open>Subspace division\<close>

consts space_div :: "predicate \<Rightarrow> 'a ell2 \<Rightarrow> 'a::universe variables \<Rightarrow> predicate"
                    ("_ \<div> _\<guillemotright>_" [89,89,89] 90)
lemma leq_space_div[simp]: "colocal A Q \<Longrightarrow> (A \<le> B \<div> \<psi>\<guillemotright>Q) = (A \<sqinter> ccspan {\<psi>}\<guillemotright>Q \<le> B)"
  by (cheat TODO14)

definition space_div_unlifted :: "('a*'b) ell2 ccsubspace \<Rightarrow> 'b ell2 \<Rightarrow> 'a ell2 ccsubspace" where
  [code del]: "space_div_unlifted S \<psi> = Abs_clinear_space {\<phi>. \<phi>\<otimes>\<psi> \<in> space_as_set S}"

lemma space_div_space_div_unlifted: "space_div (S\<guillemotright>(variable_concat Q R)) \<psi> R = (space_div_unlifted S \<psi>)\<guillemotright>Q"
  by (cheat space_div_space_div_unlifted)

lemma top_div[simp]: "top \<div> \<psi>\<guillemotright>Q = top" 
  by (cheat top_div)
lemma bot_div[simp]: "bot \<div> \<psi>\<guillemotright>Q = bot" 
  by (cheat bot_div)
lemma Cla_div[simp]: "Cla[e] \<div> \<psi>\<guillemotright>Q = Cla[e]" by simp

lemma space_div_add_extend_lift_as_var_concat_hint:
  fixes S :: "_ subspace"
  shows "NO_MATCH ((variable_concat a b),b) (Q,R) \<Longrightarrow> (space_div (S\<guillemotright>Q) \<psi> R) = (space_div (extend_lift_as_var_concat_hint (S\<guillemotright>Q) R)) \<psi> R"
  unfolding extend_lift_as_var_concat_hint_def by simp

subsection \<open>Quantum equality\<close>

(* TODO: 'c doesn't have to be ell2 *)
definition quantum_equality_full :: "('a,'c) l2bounded \<Rightarrow> 'a::universe variables \<Rightarrow> ('b,'c) l2bounded \<Rightarrow> 'b::universe variables \<Rightarrow> predicate" where
  [code del]: "quantum_equality_full U Q V R = 
                 (eigenspace 1 (comm_op \<cdot> (V*\<cdot>U)\<otimes>(U*\<cdot>V))) \<guillemotright> variable_concat Q R"
  for Q :: "'a::universe variables" and R :: "'b::universe variables"
  and U V :: "(_,'c) l2bounded"

abbreviation "quantum_equality" :: "'a::universe variables \<Rightarrow> 'a::universe variables \<Rightarrow> predicate" (infix "\<equiv>\<qq>" 100)
  where "quantum_equality X Y \<equiv> quantum_equality_full idOp X idOp Y"
syntax quantum_equality :: "'a::universe variables \<Rightarrow> 'a::universe variables \<Rightarrow> predicate" (infix "==q" 100)
syntax "_quantum_equality" :: "variable_list_args \<Rightarrow> variable_list_args \<Rightarrow> predicate" ("Qeq'[_=_']")
translations
  "_quantum_equality a b" \<rightharpoonup> "CONST quantum_equality (_variables a) (_variables b)"

lemma quantum_equality_sym:
  assumes "distinct_qvars (variable_concat Q R)"
  shows "quantum_equality_full U Q V R = quantum_equality_full V R U Q"
proof -
  have dist: "distinct_qvars (variable_concat R Q)"
    using assms by (rule distinct_qvars_swap)
  have a: "comm_op \<cdot> ((V* \<cdot> U) \<otimes> (U* \<cdot> V)) \<cdot> comm_op* = (U* \<cdot> V) \<otimes> (V* \<cdot> U)" by simp
  have op_eq: "((comm_op \<cdot> (V* \<cdot> U) \<otimes> (U* \<cdot> V))\<guillemotright>variable_concat Q R) =
               ((comm_op \<cdot> (U* \<cdot> V) \<otimes> (V* \<cdot> U))\<guillemotright>variable_concat R Q)"
    apply (subst comm_op_lift[symmetric])
    using a by (simp add: assoc_right)
  show ?thesis
    apply (subst quantum_equality_full_def)
    apply (subst quantum_equality_full_def)
    apply (subst eigenspace_lift[symmetric, OF assms])
    apply (subst eigenspace_lift[symmetric, OF dist])
    using op_eq by simp
qed


lemma qvar_trafo'_quantum_equality_full:
  fixes Q Q' U V R R'
  defines "QR \<equiv> variable_concat Q R" and "QR' \<equiv> variable_concat Q' R'"
  assumes "qvar_trafo' CO QR' QR"
  shows "CO \<cdot> quantum_equality_full U Q V R = quantum_equality_full U Q' V R'"
  unfolding quantum_equality_full_def QR_def[symmetric] QR'_def[symmetric]
  apply (subst qvar_trafo'_subspace[where Q=QR'])
  using assms by auto


lemma predicate_local[intro!]: 
  assumes "qvariables_local (variable_concat Q R) S"
  shows "predicate_local (quantum_equality_full U Q V R) S"
  by (cheat predicate_local)

lemma colocal_quantum_equality_full[simp,intro!]:
  "colocal_qvars_qvars_str (variable_concat Q1 Q2) Q3 \<Longrightarrow> 
    colocal_pred_qvars_str (quantum_equality_full U1 Q1 U2 Q2) Q3"
for Q1::"'a::universe variables" and Q2::"'b::universe variables" and Q3::"string set"
and U1 U2::"(_,'d)l2bounded" 
  by (cheat TODO14)

(* TODO can probably be removed because it's a special case of colocal_quantum_equality_full *)
lemma colocal_quantum_eq[simp,intro!]: 
  "colocal_qvars_qvars_str (variable_concat Q1 Q2) R \<Longrightarrow> colocal_pred_qvars_str (Q1 \<equiv>\<qq> Q2) R"
  for Q1 Q2 :: "'c::universe variables" and R :: "string set"
  by (cheat TODO14)

lemma applyOpSpace_colocal[simp]:
  "colocal U S \<Longrightarrow> unitary U \<Longrightarrow> U \<cdot> S = S" for U :: "(mem2,mem2) l2bounded" and S :: predicate
  by (cheat TODO14)

lemma qeq_collect:
 "quantum_equality_full U Q1 V Q2 = quantum_equality_full (V*\<cdot>U) Q1 idOp Q2"
 for U :: "('a::universe,'b::universe) l2bounded" and V :: "('c::universe,'b) l2bounded"
  unfolding quantum_equality_full_def by auto

lemma qeq_collect_guarded[simp]:
  fixes U :: "('a::universe,'b::universe) l2bounded" and V :: "('c::universe,'b) l2bounded"
  assumes "NO_MATCH idOp V"
  shows "quantum_equality_full U Q1 V Q2 = quantum_equality_full (V*\<cdot>U) Q1 idOp Q2"
  by (fact qeq_collect)

(* Proof in paper *)
lemma Qeq_mult1[simp]:
  "unitary U \<Longrightarrow> U\<guillemotright>Q1 \<cdot> quantum_equality_full U1 Q1 U2 Q2 = quantum_equality_full (U1\<cdot>U*) Q1 U2 Q2"
 for U::"('a::universe,'a) l2bounded" and U2 :: "('b::universe,'c::universe) l2bounded"  
  by (cheat TODO14)

(* Proof in paper *)
lemma Qeq_mult2[simp]:
  "unitary U \<Longrightarrow> U\<guillemotright>Q2 \<cdot> quantum_equality_full U1 Q1 U2 Q2 = quantum_equality_full U1 Q1 (U2\<cdot>U*) Q2"
 for U::"('a::universe,'a::universe) l2bounded" and U1 :: "('b::universe,'c::universe) l2bounded"  
  by (cheat TODO14)

(* Proof in paper *)
lemma quantum_eq_unique[simp]: "distinct_qvars (variable_concat Q R) \<Longrightarrow>
  isometry U \<Longrightarrow> isometry (adj V) \<Longrightarrow> 
  quantum_equality_full U Q V R \<sqinter> ccspan{\<psi>}\<guillemotright>Q
  = liftSpace (ccspan{\<psi>}) Q \<sqinter> liftSpace (ccspan{V* \<cdot> U \<cdot> \<psi>}) R"
  for Q::"'a::universe variables" and R::"'b::universe variables"
    and U::"('a,'c) l2bounded" and V::"('b,'c) l2bounded"
    and \<psi>::"'a ell2"
  by (cheat TODO14)

(* Proof in paper *)
lemma
  quantum_eq_add_state: 
    "distinct_qvars (variable_concat Q (variable_concat R T)) \<Longrightarrow> norm \<psi> = 1 \<Longrightarrow>
    quantum_equality_full U Q V R \<sqinter> ccspan {\<psi>}\<guillemotright>T
             = quantum_equality_full (U \<otimes> idOp) (variable_concat Q T) (addState \<psi> \<cdot> V) R"
    for U :: "('a::universe,'c) l2bounded" and V :: "('b::universe,'c) l2bounded" and \<psi> :: "'d::universe ell2"
    and Q :: "'a::universe variables"    and R :: "'b::universe variables"    and T :: "'d variables"
  by (cheat TODO14)


(* We flip the lhs/rhs of the quantum equality in addition to changing the indices.
   This is because quantum equalities are typically written with 1-variables on the left and 2-variables on the right. *)
lemma index_flip_subspace_quantum_equality[simp]: 
  "index_flip_subspace (quantum_equality_full U Q V R) = 
      quantum_equality_full V (index_flip_vars R) U (index_flip_vars Q)"
  by (cheat index_flip_subspace_quantum_equality)

lemma swap_variables_subspace_quantum_equality[simp]: 
  "swap_variables_subspace v w (quantum_equality_full U Q V R) = 
      quantum_equality_full U (swap_variables_vars v w Q) V (swap_variables_vars v w R)"
  by (cheat swap_variables_subspace_quantum_equality)

lemma quantum_equality_reorder:
  fixes U :: "('a::universe,'c) l2bounded" and V :: "('b::universe,'c) l2bounded"
  fixes Q :: "'a variables" and R :: "'b::universe variables"
  assumes trafoQ: "qvar_trafo A Q Q'"
  assumes trafoR: "qvar_trafo B R R'"
  assumes [simp]: "distinct_qvars (variable_concat Q R)"
  assumes [simp]: "distinct_qvars (variable_concat Q' R')"
  shows "quantum_equality_full U Q V R = quantum_equality_full (U\<cdot>A*) Q' (V\<cdot>B*) R'"
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
      apply (subst cblinfun_apply_assoc)
      apply (subst cblinfun_apply_assoc[symmetric], subst comm_op_swap)
      by rule
    finally show ?thesis
      by -
  qed

  from trafoQR have "(comm_op \<cdot> (V* \<cdot> U) \<otimes> (U* \<cdot> V))\<guillemotright>QR =
    ((A\<otimes>B) \<cdot> (comm_op \<cdot> (V* \<cdot> U) \<otimes> (U* \<cdot> V)) \<cdot> (A\<otimes>B)*) \<guillemotright> QR'" (is "_ = liftOp ?rhs _")
    using qvar_trafo_l2bounded by blast
  also have "?rhs = comm_op \<cdot> ((B\<otimes>A) \<cdot> ((V* \<cdot> U) \<otimes> (U* \<cdot> V)) \<cdot> (A\<otimes>B)*)"
    apply (subst cblinfun_apply_assoc[symmetric])+
    apply (subst ABcomm)
    apply (subst cblinfun_apply_assoc)+ by rule
  also have "\<dots> = comm_op \<cdot> (VB* \<cdot> UA) \<otimes> (UA* \<cdot> VB)"
    unfolding VB_def UA_def
    by (simp add: cblinfun_apply_assoc)
  finally show "quantum_equality_full U Q V R = quantum_equality_full UA Q' VB R'"
    unfolding quantum_equality_full_def QR_def QR'_def
    apply (subst eigenspace_lift[symmetric], simp)+
    by simp
qed

lemma quantum_equality_full_swap_left:
  assumes [simp]: "distinct_qvars (variable_concat (variable_concat Q R) S)"
  shows "quantum_equality_full U (variable_concat Q R) V S
       = quantum_equality_full (U\<cdot>comm_op) (variable_concat R Q) V S"
proof -
  have "quantum_equality_full U (variable_concat Q R) V S
      = quantum_equality_full (U\<cdot>comm_op*) (variable_concat R Q) (V\<cdot>idOp*) S"
    apply (rule quantum_equality_reorder)
    using assms apply (auto simp: distinct_qvars_split1 intro!: qvar_trafo_comm_op qvar_trafo_id)
    using distinct_qvarsR distinct_qvars_swap by blast+
  also have "\<dots> = quantum_equality_full (U\<cdot>comm_op) (variable_concat R Q) V S"
    by simp
  finally show ?thesis by -
qed

lemma quantum_equality_full_swap_right:
  assumes [simp]: "distinct_qvars (variable_concat (variable_concat Q R) S)"
  shows "quantum_equality_full U Q V (variable_concat R S)
       = quantum_equality_full U Q (V\<cdot>comm_op) (variable_concat S R)"
proof -
  have "quantum_equality_full U Q V (variable_concat R S)
      = quantum_equality_full (U\<cdot>idOp*) Q (V\<cdot>comm_op*) (variable_concat S R)"
    apply (rule quantum_equality_reorder)
    using assms apply (auto simp: distinct_qvars_split1 distinct_qvars_split2 intro!: qvar_trafo_comm_op qvar_trafo_id)
    using distinct_qvarsR distinct_qvars_swap by blast+
  also have "\<dots> = quantum_equality_full U Q (V\<cdot>comm_op) (variable_concat S R)"
    by simp
  finally show ?thesis by -
qed


lemma quantum_equality_merge:
  assumes "distinct_qvars (variable_concat (variable_concat Q1 R1) (variable_concat Q2 R2))"
  shows "quantum_equality_full U1 Q1 V1 R1 \<sqinter> quantum_equality_full U2 Q2 V2 R2 
    \<le> quantum_equality_full (U1\<otimes>U2) (variable_concat Q1 Q2) (V1\<otimes>V2) (variable_concat R1 R2)"
proof (rule ccsubspace_leI, rule subsetI)
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
      using qvar_trafo_unitary unitary_def' by blast
    have "?lhs = T* *\<^sub>V (T *\<^sub>V (q1\<otimes>r1)\<otimes>(q2\<otimes>r2))"
      by (subst apply_T, simp)
    also have "\<dots> = ?rhs"
      by (simp add: times_applyOp[symmetric])
    finally show ?thesis by -
  qed

  from x1 have x1': "(comm_op \<cdot> (V1*\<cdot>U1)\<otimes>(U1*\<cdot>V1)) \<guillemotright> QR1 *\<^sub>V x = x"
    unfolding quantum_equality_full_def QR1_def[symmetric]
    apply (subst (asm) eigenspace_lift[symmetric], simp)
    by (frule eigenspace_memberE, simp)
  from x2 have x2': "(comm_op \<cdot> (V2*\<cdot>U2)\<otimes>(U2*\<cdot>V2)) \<guillemotright> QR2 *\<^sub>V x = x"
    unfolding quantum_equality_full_def QR2_def[symmetric]
    apply (subst (asm) eigenspace_lift[symmetric], simp)
    by (frule eigenspace_memberE, simp)

  have x12: "((comm_op \<cdot> (V1*\<cdot>U1)\<otimes>(U1*\<cdot>V1)) \<otimes> (comm_op \<cdot> (V2*\<cdot>U2)\<otimes>(U2*\<cdot>V2))) \<guillemotright> QR12' *\<^sub>V x = x"
    unfolding QR12'_def apply (subst lift_tensorOp[symmetric])
    unfolding QR12'_def[symmetric] apply simp
    by (simp add: x1' x2' times_applyOp)

  have same_op: "(comm_op \<cdot> (((V1 \<otimes> V2)* o\<^sub>C\<^sub>L (U1 \<otimes> U2)) \<otimes> ((U1 \<otimes> U2)* o\<^sub>C\<^sub>L (V1 \<otimes> V2))))\<guillemotright>QR12
      = ((comm_op \<cdot> (V1*\<cdot>U1)\<otimes>(U1*\<cdot>V1)) \<otimes> (comm_op \<cdot> (V2*\<cdot>U2)\<otimes>(U2*\<cdot>V2))) \<guillemotright> QR12'"
    apply (subst qvar_trafo_l2bounded[OF qvar_trafo_T])
    apply (subst lift_eqOp, simp)
    apply (rule equal_ket)
    by (auto simp: ket_product times_applyOp tensorOp_applyOp_distr)

  have "(comm_op \<cdot> (((V1 \<otimes> V2)* o\<^sub>C\<^sub>L (U1 \<otimes> U2)) \<otimes> ((U1 \<otimes> U2)* o\<^sub>C\<^sub>L (V1 \<otimes> V2))))\<guillemotright>QR12 *\<^sub>V x = x"
    apply (subst same_op) by (rule x12)

  then show "x \<in> space_as_set (quantum_equality_full (U1 \<otimes> U2) Q12 (V1 \<otimes> V2) R12)"
    unfolding quantum_equality_full_def QR12_def
    apply (subst eigenspace_lift[symmetric], simp)
    apply (rule eigenspace_memberI)
    by simp
qed

section \<open>Common quantum objects\<close>

definition [code del]: "CNOT = classical_operator (Some o (\<lambda>(x::bit,y). (x,y+x)))"
lemma unitaryCNOT[simp]: "unitary CNOT"
  unfolding CNOT_def apply (rule unitary_classical_operator)
  apply (rule o_bij[where g="\<lambda>(x,y). (x,y+x)"]; rule ext)
  unfolding o_def id_def by auto

lemma adjoint_CNOT[simp]: "CNOT* = CNOT"
proof -
  define f where "f = (\<lambda>(x::bit,y). (x,y+x))"
  have[simp]: "f o f = id"
    unfolding f_def o_def id_def by fastforce
  have[simp]: "bij f"
    apply (rule o_bij[where g="f"]; rule ext) by auto
  then have[simp]: "inj f"
    by (rule bij_is_inj)
  have[simp]: "surj f"
    apply (rule bij_is_surj) by simp
  have inv_f[simp]: "Hilbert_Choice.inv f = f"
    apply (rule inv_unique_comp) by auto
  have [simp]: "inv_option (Some \<circ> f) = Some \<circ> f"
    apply (subst inv_option_Some) by simp_all
  show ?thesis
    unfolding CNOT_def
    apply (subst classical_operator_adjoint)
    unfolding f_def[symmetric]
    by auto
qed

lemma CNOT_CNOT[simp]: "CNOT \<cdot> CNOT = idOp"
  using unitaryCNOT unfolding unitary_def adjoint_CNOT by simp

definition [code del]: "pauliX = classical_operator (Some o (\<lambda>x::bit. x+1))"
lemma unitaryX[simp]: "unitary pauliX"
  unfolding pauliX_def apply (rule unitary_classical_operator)
  apply (rule o_bij[where g="\<lambda>x. x+1"]; rule ext)
  unfolding o_def id_def by auto

lemma adjoint_X[simp]: "pauliX* = pauliX"
proof -
  define f where "f = (\<lambda>x::bit. x+1)"
  have[simp]: "f o f = id"
    unfolding f_def o_def id_def by auto
  have[simp]: "bij f"
    apply (rule o_bij[where g="f"]; rule ext) by auto
  have[simp]: "inj f"
    apply (rule bij_is_inj) by simp
  have[simp]: "surj f"
    apply (rule bij_is_surj) by simp
  have inv_f[simp]: "Hilbert_Choice.inv f = f"
    apply (rule inv_unique_comp) by auto
  have [simp]: "inv_option (Some \<circ> f) = Some \<circ> f"
    apply (subst inv_option_Some) by simp_all
  show ?thesis
    unfolding pauliX_def
    apply (subst classical_operator_adjoint)
    unfolding f_def[symmetric]
    by auto
qed


lemma X_X[simp]: "pauliX \<cdot> pauliX = idOp"
  using unitaryX unfolding unitary_def adjoint_CNOT by simp

consts hadamard :: "(bit,bit) l2bounded"
lemma unitaryH[simp]: "unitary hadamard"
  by (cheat TODO14)
lemma adjoint_H[simp]: "hadamard* = hadamard"
  by (cheat TODO15)

lemma H_H[simp]: "hadamard \<cdot> hadamard = idOp"
  using unitaryH unfolding unitary_def by simp

(* definition "hadamard' = sqrt2 \<cdot> hadamard"
lemma H_H': "hadamard = (1/sqrt2) \<cdot> hadamard'" unfolding hadamard'_def by simp
lemma [simp]: "isometry (1 / sqrt2 \<cdot> hadamard')"
  unfolding hadamard'_def by simp *)


definition [code del]: "pauliZ = hadamard \<cdot> pauliX \<cdot> hadamard"
lemma unitaryZ[simp]: "unitary pauliZ"
  unfolding pauliZ_def by simp

lemma adjoint_Z[simp]: "pauliZ* = pauliZ"
  unfolding pauliZ_def apply simp apply (subst cblinfun_apply_assoc) by simp

lemma Z_Z[simp]: "pauliZ \<cdot> pauliZ = idOp"
  using unitaryZ unfolding unitary_def by simp

consts pauliY :: "(bit,bit) l2bounded"
lemma unitaryY[simp]: "unitary pauliY"
  by (cheat TODO15)
lemma Y_Y[simp]: "pauliY \<cdot> pauliY = idOp"
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

  then have "inv_option (Some o \<pi>2) = Some o \<pi>"
    by (subst inv_option_Some, simp_all)

  then have "(classical_operator (Some \<circ> \<pi>2))* = classical_operator (Some o \<pi>)"
    apply (subst classical_operator_adjoint)
    by simp_all

  then show ?thesis
    unfolding \<pi>_def \<pi>2_def Uoracle_def by auto
qed

lemma Uoracle_selfadjoint[simp]: "(Uoracle f)* = Uoracle f" for f :: "_ \<Rightarrow> _::xor_group"
  unfolding Uoracle_adjoint unfolding Uoracle_def by simp

lemma Uoracle_selfinverse[simp]: "Uoracle f \<cdot> Uoracle f = idOp" for f :: "_ \<Rightarrow> _::xor_group"
  apply (subst Uoracle_selfadjoint[symmetric]) apply (rule adjUU) by simp

lemma applyOp_Uoracle[simp]:
  shows "Uoracle f \<cdot> ket (x, y) = ket (x, y + f x)"
  unfolding Uoracle_def
  apply (subst classical_operator_basis)
  by (auto simp: inj_on_def intro: classical_operator_exists_inj)

lemma applyOp_Uoracle'[simp]:
  shows "Uoracle f \<cdot> (ket x \<otimes> ket y) = ket x \<otimes> ket (y + f x)"
  by (simp flip: ket_product)


lemma Uoracle_twice[simp]: 
  fixes f :: "_ \<Rightarrow> _::xor_group"
  assumes "distinct_qvars Q"
  shows "Uoracle f\<guillemotright>Q \<cdot> (Uoracle f\<guillemotright>Q \<cdot> S) = (S::_ ccsubspace)"
  apply (subst Uoracle_selfadjoint[symmetric])
  using assms by (simp del: Uoracle_selfadjoint flip: adjoint_lift cblinfun_apply_assoc_clinear_space)


definition "proj_classical_set S = Proj (ccspan {ket s|s. s\<in>S})"

lemma isProjector_proj_classical_set[simp]: "isProjector (proj_classical_set S)"
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
derive universe infinite
declare infinite_UNIV_listI[simp]

section "ML Code"

ML_file \<open>qrhl.ML\<close>

section "Simprocs"

simproc_setup "variable_rewriting" 
  ("join_variables_hint a b" | "sort_variables_hint a" | 
   "reorder_variables_hint a b" | "extend_lift_as_var_concat_hint A R") = 
  QRHL.variable_rewriting_simproc


end
