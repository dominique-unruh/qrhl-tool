theory Scratch
  imports QRHL
 (* "HOL-ex.Sketch_and_Explore" *) 
(* "HOL-Eisbach.Eisbach" *)
(* QRHL_Operations  *)
begin

no_notation eq_closure_of ("closure'_of\<index>")

ML "open Prog_Variables"

(* MOVE *)

lemma QREGISTER_of_qregister_id: \<open>QREGISTER_of qregister_id = QREGISTER_all\<close>
  apply (rule Rep_QREGISTER_inject[THEN iffD1])
  by (simp add: QREGISTER_of.rep_eq QREGISTER_all.rep_eq)

(* lemma closed_map_when_continuously_invertible:
  assumes cont: \<open>continuous_map Y X g\<close>
  assumes inv: \<open>\<And>x. x \<in> topspace X \<Longrightarrow> f x \<in> topspace Y \<and> g (f x) = x\<close>
    (* and Y: "\<And>y. y \<in> topspace Y \<Longrightarrow> g y \<in> topspace X \<and> f(g y) = y" *)
  shows \<open>closed_map X Y f\<close>
proof (unfold closed_map_def, intro allI impI)
  fix U
  assume \<open>closedin X U\<close>
  then have \<open>U \<subseteq> topspace X\<close>
  by (simp add: closedin_subset)
  with inv have \<open>g ` f ` U = U\<close>
    by (simp add: image_image subsetD)
  with \<open>closedin X U\<close> have \<open>closedin X (g ` f ` U)\<close>
    by simp
  with cont have \<open>closedin Y (topspace Y \<inter> g -` (g ` f ` U))\<close>
    using closedin_vimage by blast
  also have \<open>\<dots> = f ` U\<close>
  sledgehammer
  try0
  by -

    using \<open>U \<subseteq> topspace X\<close> inv by auto
  finally show \<open>closedin Y (f ` U)\<close>
    by -
qed *)

(* lemma \<open>limitin X id l F = (l \<in> topspace X \<and> (\<forall>U. openin X U \<longrightarrow> l \<in> U \<longrightarrow> F \<le> principal U))\<close>
  apply (simp add: limitin_def le_filter_def eventually_principal)
  by (metis (mono_tags, lifting) eventually_mono)
lemma \<open>(l \<in> topspace X \<and> (\<forall>U. openin X U \<longrightarrow> l \<in> U \<longrightarrow> F \<le> principal U))
= (l \<in> topspace X \<and> F \<le> nhdsin X l)\<close>
  sledgehammer
  try0
  by - *)

(* TODO used? *)
lemma filterlim_bot: \<open>filterlim f \<bottom> F \<longleftrightarrow> (F = \<bottom>)\<close>
proof -
  have \<open>F = \<bottom>\<close> if \<open>filtermap f F \<le> \<bottom>\<close>
  proof -
    from that have \<open>filtermap f F = \<bottom>\<close>
      by (simp add: le_bot)
    then have \<open>eventually (\<lambda>_. False) (filtermap f F)\<close>
      by simp
    then have \<open>eventually (\<lambda>_. False) F\<close>
      by (simp add: eventually_filtermap)
    then show \<open>F = \<bottom>\<close>
      using eventually_False by auto
  qed
  then show ?thesis
    by (auto simp add: filterlim_def)
qed


(* lemma \<open>filterlim f (nhdsin T l) F \<longleftrightarrow> limitin T f l F\<close>
  apply (cases \<open>l \<in> topspace T\<close>)
   apply (simp flip: filterlim_nhdsin_iff_limitin)
  apply (simp add: filterlim_bot limitin_def)
  apply (auto simp flip: filterlim_nhdsin_iff_limitin) *)

thm filterlim_nhdsin_iff_limitin

(* lemma
  shows \<open>closed A \<longleftrightarrow> (\<forall>F x. F \<le> nhds x \<longrightarrow> x \<in> U)\<close>
  apply (rule iffI)
try0
sledgehammer
subgoal by -
  sledgehammer
  try0
  by - *)

(* lemma \<open>limitin T f x \<bottom> = xxx\<close>
  apply (simp add: flip: filterlim_nhdsin_iff_limitin) *)

lemma closedin_if_converge_inside:
  fixes A :: \<open>'a set\<close>
  assumes AT: \<open>A \<subseteq> topspace T\<close>
  assumes xA: \<open>\<And>(F::'a filter) f x. F \<noteq> \<bottom> \<Longrightarrow> limitin T f x F \<Longrightarrow> range f \<subseteq> A \<Longrightarrow> x \<in> A\<close>
  shows \<open>closedin T A\<close>
proof (cases \<open>A = {}\<close>)
  case True
  then show ?thesis by simp
next
  case False
  then obtain a where \<open>a \<in> A\<close>
    by auto
  define Ac where \<open>Ac = topspace T - A\<close>
  have \<open>\<exists>U. openin T U \<and> x \<in> U \<and> U \<subseteq> Ac\<close> if \<open>x \<in> Ac\<close> for x
  proof (rule ccontr)
    assume \<open>\<nexists>U. openin T U \<and> x \<in> U \<and> U \<subseteq> Ac\<close>
    then have UA: \<open>U \<inter> A \<noteq> {}\<close> if \<open>openin T U\<close>and \<open>x \<in> U\<close> for U
      by (metis Ac_def Diff_mono Diff_triv openin_subset subset_refl that)
    have [simp]: \<open>x \<in> topspace T\<close>
      using that by (simp add: Ac_def)

    define F where \<open>F = nhdsin T x \<sqinter> principal A\<close>
    have \<open>F \<noteq> \<bottom>\<close>
      apply (subst filter_eq_iff)
      apply (auto intro!: exI[of _ \<open>\<lambda>_. False\<close>] simp: F_def eventually_inf eventually_principal
          eventually_nhdsin)
      by (meson UA disjoint_iff)

    define f where \<open>f y = (if y\<in>A then y else a)\<close> for y
    with \<open>a \<in> A\<close> have \<open>range f \<subseteq> A\<close>
      by force

    have \<open>\<forall>\<^sub>F y in F. f y \<in> U\<close> if \<open>openin T U\<close> and \<open>x \<in> U\<close> for U
    proof -
      have \<open>eventually (\<lambda>x. x \<in> U) (nhdsin T x)\<close>
        using eventually_nhdsin that by fastforce
      moreover have \<open>\<exists>R. (\<forall>x\<in>A. R x) \<and> (\<forall>x. x \<in> U \<longrightarrow> R x \<longrightarrow> f x \<in> U)\<close>
        apply (rule exI[of _ \<open>\<lambda>x. x \<in> A\<close>])
        by (simp add: f_def)
      ultimately show ?thesis
        by (auto simp add: F_def eventually_inf eventually_principal)
    qed
    then have \<open>limitin T f x F\<close>
      unfolding limitin_def by simp
    with \<open>F \<noteq> \<bottom>\<close> \<open>range f \<subseteq> A\<close> xA
    have \<open>x \<in> A\<close>
      by simp
    with that show False
      by (simp add: Ac_def)
  qed
  then have \<open>openin T Ac\<close>
    apply (rule_tac openin_subopen[THEN iffD2])
    by simp
  then show ?thesis
    by (simp add: Ac_def AT closedin_def)
qed


(* proof (rule ccontr)
  define Ac where \<open>Ac = topspace T - A\<close>
  assume \<open>\<not> closedin T A\<close>
  then have \<open>A \<noteq> {}\<close>
    using closedin_empty by blast
  then obtain a where \<open>a \<in> A\<close>
    by blast

  from \<open>\<not> closedin T A\<close> AT have \<open>\<not> openin T Ac\<close>
    by (simp add: Ac_def closedin_def)
  then obtain x where \<open>x \<in> Ac\<close> and overlap: \<open>openin T U \<Longrightarrow> x \<in> U \<Longrightarrow> U \<inter> (topspace T - Ac) \<noteq> {}\<close> for U
    unfolding Ac_def
    by (smt (verit, best) Diff_Diff_Int Diff_triv Int_Diff Int_absorb1 Int_absorb2 Int_lower2 openin_closedin_eq openin_subopen)
  then obtain f0 where \<open>f0 U \<in> U \<inter> (topspace T - Ac)\<close> if \<open>openin T U\<close> and \<open>x \<in> U\<close> for U
    apply atomize_elim
    apply (rule choice)
    by auto
  have \<open>\<forall>\<^sub>F y in nhdsin T x. y \<in> U\<close>


  define f where \<open>f U = (if openin T U \<and> x \<in> U then f0 U else a)\<close> for U

  have \<open>limitin T g x F\<close>
    apply (simp add: limitin_def)
  term nhds
  term is_filter *)

(* lemma closedin_if_converge_inside:
  assumes AT: \<open>A \<subseteq> topspace T\<close>
  assumes xA: \<open>\<And>F x. x \<in> topspace T \<Longrightarrow> F \<le> nhdsin T x \<Longrightarrow> x \<in> A\<close>
  shows \<open>closedin T A\<close>
proof (rule ccontr)
  define Ac where \<open>Ac = topspace T - A\<close>
  assume \<open>\<not> closedin T A\<close>
  with AT have \<open>\<not> openin T Ac\<close>
    by (simp add: Ac_def closedin_def)
  with xA show False
    by (metis Ac_def Diff_iff inf_sup_ord(2) openin_subopen)
qed *)

(* lemma closedin_if_converge_inside':
  assumes AT: \<open>A \<subseteq> topspace T\<close>
  assumes xA: \<open>\<And>F x. limitin T id x F \<Longrightarrow> x \<in> A\<close>
  shows \<open>closedin T A\<close>
  apply (rule closedin_if_converge_inside)
  using assms apply (simp add: filterlim_nhdsin_iff_limitin) *)

(* TODO: replace  *) thm continuous_map_left_comp_sot (* with this *)
lemma continuous_map_left_comp_sot[continuous_intros]: 
  assumes \<open>continuous_map T cstrong_operator_topology f\<close> 
  shows \<open>continuous_map T cstrong_operator_topology (\<lambda>x. b o\<^sub>C\<^sub>L f x)\<close> 
  by (fact continuous_map_compose[OF assms continuous_map_left_comp_sot, unfolded o_def])

(* TODO: replace  *) thm continuous_map_right_comp_sot (* with this *)
lemma continuous_map_right_comp_sot[continuous_intros]: 
  assumes \<open>continuous_map T cstrong_operator_topology f\<close> 
  shows \<open>continuous_map T cstrong_operator_topology (\<lambda>x. f x o\<^sub>C\<^sub>L a)\<close> 
  by (fact continuous_map_compose[OF assms continuous_map_right_comp_sot, unfolded o_def])

lemma sandwich_sot_continuous[continuous_intros]:
  assumes \<open>continuous_map T cstrong_operator_topology f\<close>
  shows \<open>continuous_map T cstrong_operator_topology (\<lambda>x. sandwich A (f x))\<close>
  unfolding sandwich_apply
  by (intro continuous_intros assms)


lemma commutant_tensor1': \<open>commutant (range (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a)) = range (\<lambda>b. b \<otimes>\<^sub>o id_cblinfun)\<close>
proof -
  have \<open>commutant (range (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a)) = commutant (sandwich swap_ell2 ` range (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun))\<close>
    by (metis (no_types, lifting) image_cong range_composition swap_tensor_op_sandwich)
  also have \<open>\<dots> = sandwich swap_ell2 ` commutant (range (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun))\<close>
    by (simp add: sandwich_unitary_complement)
       (* TODO: rename sandwich_unitary_complement \<rightarrow> sandwich_unitary_commutant *)
  also have \<open>\<dots> = sandwich swap_ell2 ` range (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a)\<close>
    by (simp add: commutant_tensor1)
  also have \<open>\<dots> = range (\<lambda>b. b \<otimes>\<^sub>o id_cblinfun)\<close>
    by force
  finally show ?thesis
    by -
qed


lemma closed_map_sot_tensor_op_id_right: 
  \<open>closed_map cstrong_operator_topology cstrong_operator_topology (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun :: ('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2)\<close>
proof (unfold closed_map_def, intro allI impI)
  fix U :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2) set\<close>
  assume closed_U: \<open>closedin cstrong_operator_topology U\<close>

  have aux1: \<open>range f \<subseteq> X \<longleftrightarrow> (\<forall>x. f x \<in> X)\<close> for f :: \<open>'x \<Rightarrow> 'y\<close> and X
    by blast

  have \<open>l \<in> (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) ` U\<close> if range: \<open>range (\<lambda>x. f x) \<subseteq> (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) ` U\<close>
    and limit: \<open>limitin cstrong_operator_topology f l F\<close> and \<open>F \<noteq> \<bottom>\<close> 
  for f and l :: \<open>('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2\<close> and F :: \<open>(('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2) filter\<close>
  proof -
    from range obtain f' where f'U: \<open>range f' \<subseteq> U\<close> and f_def: \<open>f y = f' y \<otimes>\<^sub>o id_cblinfun\<close> for y
      apply atomize_elim
      apply (subst aux1)
      apply (rule choice2)
      by auto
    have \<open>l \<in> commutant (range (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a))\<close>
    proof (rule commutant_memberI)
      fix c :: \<open>('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2\<close> 
      assume \<open>c \<in> range (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a)\<close>
      then obtain c' where c_def: \<open>c = id_cblinfun \<otimes>\<^sub>o c'\<close>
        by blast
      from limit have 1: \<open>limitin cstrong_operator_topology ((\<lambda>z. z o\<^sub>C\<^sub>L c) o f) (l o\<^sub>C\<^sub>L c) F\<close>
        apply(rule continuous_map_limit[rotated])
        by (simp add: continuous_map_right_comp_sot)
      from limit have 2: \<open>limitin cstrong_operator_topology ((\<lambda>z. c o\<^sub>C\<^sub>L z) o f) (c o\<^sub>C\<^sub>L l) F\<close>
        apply(rule continuous_map_limit[rotated])
        by (simp add: continuous_map_left_comp_sot)
      have 3: \<open>f x o\<^sub>C\<^sub>L c = c o\<^sub>C\<^sub>L f x\<close> for x
        by (simp add: f_def c_def comp_tensor_op)
      from 1 2 show \<open>l o\<^sub>C\<^sub>L c = c o\<^sub>C\<^sub>L l\<close>
        unfolding 3 o_def
        by (meson hausdorff_sot limitin_unique that(3))
    qed
    then have \<open>l \<in> range (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun)\<close>
      by (simp add: commutant_tensor1')
    then obtain l' where l_def: \<open>l = l' \<otimes>\<^sub>o id_cblinfun\<close>
      by blast
    have \<open>limitin cstrong_operator_topology f' l' F\<close>
    proof (rule limitin_cstrong_operator_topology[THEN iffD2], rule allI)
      fix \<psi> fix b :: 'b
      have \<open>((\<lambda>x. f x *\<^sub>V (\<psi> \<otimes>\<^sub>s |b\<rangle>)) \<longlongrightarrow> l *\<^sub>V (\<psi> \<otimes>\<^sub>s |b\<rangle>)) F\<close>
        using limitin_cstrong_operator_topology that(2) by auto
      then have \<open>((\<lambda>x. (f' x *\<^sub>V \<psi>) \<otimes>\<^sub>s |b\<rangle>) \<longlongrightarrow> (l' *\<^sub>V \<psi>) \<otimes>\<^sub>s |b\<rangle>) F\<close>
        by (simp add: f_def l_def tensor_op_ell2)
      then have \<open>((\<lambda>x. (tensor_ell2_right |b\<rangle>)* *\<^sub>V ((f' x *\<^sub>V \<psi>) \<otimes>\<^sub>s |b\<rangle>)) 
                  \<longlongrightarrow> (tensor_ell2_right |b\<rangle>)* *\<^sub>V ((l' *\<^sub>V \<psi>) \<otimes>\<^sub>s |b\<rangle>)) F\<close>
        apply (rule cblinfun.tendsto[rotated])
        by simp
      then show \<open>((\<lambda>x. f' x *\<^sub>V \<psi>) \<longlongrightarrow> l' *\<^sub>V \<psi>) F\<close>
        by (simp add: tensor_ell2_right_adj_apply)
    qed
    with closed_U f'U \<open>F \<noteq> \<bottom>\<close> have \<open>l' \<in> U\<close>
      by (simp add: limitin_closedin)
    then show \<open>l \<in> (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) ` U\<close>
      by (simp add: l_def)
  qed
  then show \<open>closedin cstrong_operator_topology ((\<lambda>a. a \<otimes>\<^sub>o id_cblinfun :: ('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2) ` U)\<close>
    apply (rule_tac closedin_if_converge_inside)
    by simp_all
qed

lemma closed_map_sot_unitary_sandwich:
  fixes U :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  assumes \<open>unitary U\<close> (* Probably holds under weaker assumptions. *)
  shows \<open>closed_map cstrong_operator_topology cstrong_operator_topology (\<lambda>x. sandwich U x)\<close>
  apply (rule closed_eq_continuous_inverse_map[where g=\<open>sandwich (U*)\<close>, THEN iffD2])
  using assms 
  by (auto intro!: continuous_intros
      simp add: sandwich_compose
      simp flip: cblinfun_apply_cblinfun_compose)

lemma closed_map_sot_register:
  assumes \<open>qregister F\<close>
  shows \<open>closed_map cstrong_operator_topology cstrong_operator_topology (apply_qregister F)\<close>
proof -
  have \<open>qregister_raw (apply_qregister F)\<close>
    by (simp add: assms)
  from register_decomposition[OF this]
  have \<open>\<forall>\<^sub>\<tau> 'c::type = qregister_decomposition_basis F. ?thesis\<close>
  proof (rule with_type_mp)
    assume \<open>\<exists>U :: ('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2. unitary U \<and> (\<forall>\<theta>. apply_qregister F \<theta> = sandwich U *\<^sub>V \<theta> \<otimes>\<^sub>o id_cblinfun)\<close>
    then obtain U :: \<open>('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close> where
      \<open>unitary U\<close> and FU: \<open>apply_qregister F \<theta> = sandwich U *\<^sub>V \<theta> \<otimes>\<^sub>o id_cblinfun\<close> for \<theta>
      by metis
    have \<open>closed_map cstrong_operator_topology cstrong_operator_topology (sandwich U o (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun))\<close>
      apply (rule closed_map_compose)
       apply (rule closed_map_sot_tensor_op_id_right)
      using \<open>unitary U\<close> by (rule closed_map_sot_unitary_sandwich)
    then show \<open>closed_map cstrong_operator_topology cstrong_operator_topology (apply_qregister F)\<close>
      by (simp add: FU[abs_def] o_def)
  qed
  from this[cancel_with_type]
  show ?thesis
    by -
qed

(* TODO: valid_qregister_range could be a corollary of this *)
lemma valid_qregister_range_pres_raw:
  assumes \<open>qregister_raw F\<close>
  assumes \<open>valid_qregister_range A\<close>
  shows \<open>valid_qregister_range (F ` A)\<close>
proof (rule valid_qregister_rangeI)
(* Things to prove first:

commutant (commutant A) = A \<longleftrightarrow> A SOT-closed (Double Commutant Thm, Conway Func IX.6.4)
DONE: double_commutant_theorem

registers preserve SOT-limits (quicksheets 2023, p62-63)
DONE: closed_map_sot_register

 *)
  show \<open>a \<in> F ` A \<Longrightarrow> a* \<in> F ` A\<close> for a
    by (smt (verit) assms image_iff register_adjoint valid_qregister_range_def)
  from \<open>valid_qregister_range A\<close>
  have *: \<open>A = commutant (commutant A)\<close>
    by (simp add: valid_qregister_range_def)
  show \<open>commutant (commutant (F ` A)) \<subseteq> F ` A\<close>
  proof (rule subsetI)
    fix a
    assume \<open>a \<in> commutant (commutant (F ` A))\<close>
    then have \<open>a o\<^sub>C\<^sub>L b = b o\<^sub>C\<^sub>L a\<close> if \<open>b \<in> commutant (F ` A)\<close> for b
      apply (subst (asm) commutant_def)
      using that by auto

    show \<open>a \<in> F ` A \<close>
      by -
  qed
qed

(* lemma valid_qregister_range_raw:
  assumes \<open>qregister_raw F\<close>
  shows \<open>valid_qregister_range (range F)\<close>
  by (simp add: assms valid_qregister_range_UNIV valid_qregister_range_pres_raw) *)

lift_definition QREGISTER_chain :: \<open>('a,'b) qregister \<Rightarrow> 'a QREGISTER \<Rightarrow> 'b QREGISTER\<close> is
  \<open>\<lambda>F \<GG>. if qregister_raw F then F ` \<GG> else empty_qregister_range\<close>
  by (auto simp add: valid_qregister_range_pres_raw non_qregister_raw valid_empty_qregister_range)

lift_definition QREGISTER_fst :: \<open>('a\<times>'b) QREGISTER\<close> is
  \<open>(\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) ` UNIV\<close>
  using valid_qregister_range[of qFst]
  apply simp
  sorry
lift_definition QREGISTER_snd :: \<open>('a\<times>'b) QREGISTER\<close> is
  \<open>(\<lambda>a. id_cblinfun \<otimes>\<^sub>o a) ` UNIV\<close>
  sorry

lemma QREGISTER_of_qregister_chain: \<open>QREGISTER_of (qregister_chain F G) = QREGISTER_chain F (QREGISTER_of G)\<close>
  sorry

lemma QREGISTER_of_qFst: \<open>QREGISTER_of qFst = QREGISTER_fst\<close>
  sorry
lemma QREGISTER_of_qSnd: \<open>QREGISTER_of qSnd = QREGISTER_snd\<close>
  sorry

lemma x2: \<open>QREGISTER_pair (QREGISTER_chain A F)
                      (QREGISTER_pair B
                          (QREGISTER_chain A G))
= QREGISTER_pair B (QREGISTER_chain A (QREGISTER_pair F G))\<close>
  sorry


lemma x3: \<open>QREGISTER_pair (QREGISTER_chain F G) (QREGISTER_chain F H)
= QREGISTER_chain F (QREGISTER_pair G H)\<close>
  sorry

lemma QREGISTER_pair_assoc: \<open>QREGISTER_pair (QREGISTER_pair F G) H = QREGISTER_pair F (QREGISTER_pair G H)\<close>
  sorry

lemma x4: \<open>QREGISTER_pair (QREGISTER_chain A F)
                      (QREGISTER_pair       (QREGISTER_chain A G) B)
= QREGISTER_pair B (QREGISTER_chain A (QREGISTER_pair F G))\<close>
  sorry

lemma QREGISTER_pair_unit_left: \<open>QREGISTER_pair QREGISTER_unit F = F\<close>
  sorry

lemma QREGISTER_pair_unit_right: \<open>QREGISTER_pair F QREGISTER_unit = F\<close>
  sorry


lemma QREGISTER_pair_all_left: \<open>QREGISTER_pair QREGISTER_all F = QREGISTER_all\<close>
  sorry

lemma QREGISTER_pair_all_right: \<open>QREGISTER_pair F QREGISTER_all = QREGISTER_all\<close>
  sorry

lemma QREGISTER_chain_id_left: \<open>QREGISTER_chain qregister_id F = F\<close>
  sorry

lemma QREGISTER_chain_all_right: \<open>QREGISTER_chain F QREGISTER_all = QREGISTER_of F\<close>
  sorry

lemma QREGISTER_pair_fst_snd: \<open>QREGISTER_pair QREGISTER_fst QREGISTER_snd = QREGISTER_all\<close>
  sorry
lemma QREGISTER_pair_snd_fst: \<open>QREGISTER_pair QREGISTER_snd QREGISTER_fst = QREGISTER_all\<close>
  sorry
lemma QREGISTER_chain_unit_left: \<open>QREGISTER_chain empty_qregister F = QREGISTER_unit\<close>
  sorry

lemma QREGISTER_chain_unit_right: \<open>QREGISTER_chain F QREGISTER_unit = QREGISTER_unit\<close>
  sorry

ML \<open>
(* Brings an INDEX-REGISTER into normal form. *)
local
  val rules = (map (fn thm => thm RS @{thm eq_reflection}) @{thms 
    x2 x3 QREGISTER_pair_assoc x4 QREGISTER_pair_unit_left QREGISTER_pair_unit_right
    QREGISTER_chain_id_left QREGISTER_chain_all_right
    QREGISTER_pair_all_left QREGISTER_pair_all_right
    QREGISTER_pair_fst_snd QREGISTER_pair_snd_fst
    QREGISTER_chain_unit_left QREGISTER_chain_unit_right})
in
fun INDEX_REGISTER_norm_conv ctxt = Raw_Simplifier.rewrite ctxt false rules
end
\<close>

ML \<open>
(* Converts "QREGISTER_of F" for index register F into an INDEX-REGISTER.
   An INDEX-REGISTER is a QREGISTER built from
  "QREGISTER_chain QREGISTER_pair QREGISTER_fst QREGISTER_snd qFst qSnd QREGISTER_all QREGISTER_unit".
(While keeping the structure of the index-register. That is, can be undone be QREGISTER_of_index_reg_reverse_conv.)
 *)
val QREGISTER_of_index_reg_conv =
  Misc.rewrite_with_prover (fn ctxt => distinct_vars_tac ctxt 1)
    (map (fn thm => thm RS @{thm eq_reflection})
          @{thms 
            QREGISTER_of_qregister_pair QREGISTER_of_qregister_chain QREGISTER_of_empty_qregister
            QREGISTER_of_qFst QREGISTER_of_qSnd QREGISTER_of_qregister_id})
\<close>


lemma z1:
  assumes \<open>qregister F\<close>
  assumes \<open>QCOMPLEMENT (QREGISTER_of F) = QREGISTER_of G\<close>
  assumes \<open>qregister G\<close>
  shows \<open>qcomplements F G\<close>
  sorry


lemma y2:
  \<open>QCOMPLEMENT (QREGISTER_pair (QREGISTER_chain qFst F) (QREGISTER_chain qSnd G))
    = QREGISTER_pair (QREGISTER_chain qFst (QCOMPLEMENT F)) (QREGISTER_chain qSnd (QCOMPLEMENT G))\<close>
  sorry
lemma y1:
  \<open>QCOMPLEMENT (QREGISTER_pair QREGISTER_fst (QREGISTER_chain qSnd F))
    = QREGISTER_chain qSnd (QCOMPLEMENT F)\<close>
  sorry
lemma y3:
  \<open>QCOMPLEMENT (QREGISTER_pair (QREGISTER_chain qFst F) QREGISTER_snd)
    = QREGISTER_chain qFst (QCOMPLEMENT F)\<close>
  sorry

lemma QCOMPLEMENT_snd: \<open>QCOMPLEMENT QREGISTER_snd = QREGISTER_fst\<close>
  sorry

lemma QCOMPLEMENT_fst: \<open>QCOMPLEMENT QREGISTER_fst = QREGISTER_snd\<close>
  sorry


ML \<open>
(* Rewrites QCOMPLEMENT (INDEX-QREGISTER) into an INDEX-QREGISTER *)
local
  val rules = (map (fn thm => thm RS @{thm eq_reflection}) @{thms 
      y1 y2 y3 QCOMPLEMENT_snd QCOMPLEMENT_fst})
in
fun QCOMPLEMENT_INDEX_REGISTER_conv ctxt = Raw_Simplifier.rewrite ctxt false rules
end
\<close>

ML \<open>
(* Opposite of QREGISTER_of_index_reg_conv *)
val QREGISTER_of_index_reg_reverse_conv =
  Misc.rewrite_with_prover (fn ctxt => distinct_vars_tac ctxt 1)
    (map (fn thm => thm RS @{thm sym} RS @{thm eq_reflection})
          @{thms 
            QREGISTER_of_qregister_pair QREGISTER_of_qregister_chain QREGISTER_of_empty_qregister
            QREGISTER_of_qFst QREGISTER_of_qSnd QREGISTER_of_qregister_id})\<close>


ML \<open>
fun qcomplements_tac ctxt =
  resolve_tac ctxt @{thms z1} (* Creates three subgoals *)
  THEN'
  distinct_vars_tac ctxt (* Solve first subgoal *)
  THEN'
  (* Second subgoal *)
  CONVERSION ((QREGISTER_of_index_reg_conv |> Misc.mk_ctxt_conv Conv.arg_conv |> Misc.mk_ctxt_conv Conv.arg1_conv |> Misc.concl_conv_Trueprop) ctxt)
  THEN'
  (* Second subgoal *)
  CONVERSION ((INDEX_REGISTER_norm_conv |> Misc.mk_ctxt_conv Conv.arg_conv |> Misc.mk_ctxt_conv Conv.arg1_conv |> Misc.concl_conv_Trueprop) ctxt)
  THEN'
  (* Second subgoal *)
  CONVERSION ((QCOMPLEMENT_INDEX_REGISTER_conv |> Misc.mk_ctxt_conv Conv.arg1_conv |> Misc.concl_conv_Trueprop) ctxt)
  THEN'
  (* Second subgoal *)
  CONVERSION ((QREGISTER_of_index_reg_reverse_conv |> Misc.mk_ctxt_conv Conv.arg1_conv |> Misc.concl_conv_Trueprop) ctxt)
  THEN'
  (* Solve second subgoal *)
  resolve_tac ctxt @{thms refl}
  THEN'
  distinct_vars_tac ctxt (* Solve third subgoal *)
\<close>

schematic_goal \<open>qcomplements \<lbrakk>\<lbrakk>#2\<rbrakk>\<^sub>q, \<lbrakk>#3\<rbrakk>\<^sub>q, \<lbrakk>#1\<rbrakk>\<^sub>q, \<lbrakk>#5.\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q (?X :: (?'x,_) qregister)\<close>
  by (tactic \<open>qcomplements_tac \<^context> 1\<close>)


(* END MOVE *)

ML \<open>
open Prog_Variables
\<close>


experiment
  fixes C :: "(bit, qu) qregister" and A :: "(bit, qu) qregister" and B :: "(bit, qu) qregister"
  assumes [register]: \<open>declared_qvars \<lbrakk>C, A, B\<rbrakk>\<close>
begin

ML \<open>
val config =
Prog_Variables.translate_to_index_registers_conv_options_trace false
Prog_Variables.translate_to_index_registers_conv_default_options
\<close>

ML \<open>
val ct = \<^cterm>\<open>

(((((((let P = apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q A) (mproj M z) *\<^sub>S \<top> in (let M = computational_basis in \<CC>\<ll>\<aa>[mtotal M] \<sqinter> (\<Sqinter>za. let P = apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q C) (mproj M za) *\<^sub>S \<top> in (\<CC>\<ll>\<aa>[z \<noteq> 1] + \<CC>\<ll>\<aa>[isometry pauliX] \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B) pauliX* *\<^sub>S ((\<CC>\<ll>\<aa>[za \<noteq> 1] + \<CC>\<ll>\<aa>[isometry pauliZ] \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B) pauliZ* *\<^sub>S (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B \<equiv>\<qq> qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q A \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B) pauliZ *\<^sub>S \<top>)))) \<sqinter> (\<CC>\<ll>\<aa>[za = 1] + qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B \<equiv>\<qq> qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q A) \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B) pauliX *\<^sub>S \<top>)))) \<sqinter> (\<CC>\<ll>\<aa>[z = 1] + (\<CC>\<ll>\<aa>[za \<noteq> 1] + \<CC>\<ll>\<aa>[isometry pauliZ] \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B) pauliZ* *\<^sub>S (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B \<equiv>\<qq> qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q A \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B) pauliZ *\<^sub>S \<top>)))) \<sqinter> (\<CC>\<ll>\<aa>[za = 1] + qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B \<equiv>\<qq> qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q A)) \<sqinter> P + - P)) \<sqinter> P + - P)) \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q C) hadamard *\<^sub>S \<top>))) \<sqinter> (apply_qregister \<lbrakk>qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q C, qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q A\<rbrakk>\<^sub>q CNOT *\<^sub>S \<top>)))) \<div> EPR\<guillemotright>\<lbrakk>qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q A, qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B\<rbrakk>\<^sub>q

\<close>
\<close>

ML \<open>Prog_Variables.translate_to_index_registers_conv \<^context>
  config
  ct
  |> Thm.rhs_of\<close>

end


lemmas prepare_for_code_add =
  (* qregister_of_cregister_Fst[symmetric] qregister_of_cregister_Snd[symmetric] *)
  (* qregister_of_cregister_pair[symmetric] qregister_of_cregister_chain[symmetric] *)
  apply_qregister_of_cregister permute_and_tensor1_cblinfun_code_prep
  same_outside_cregister_def

  apply_qregister_space_code_hack (* TODO think of something more efficient *)

  case_prod_beta if_distrib[of fst] if_distrib[of snd] prod_eq_iff

  div_leq_simp mod_mod_cancel

  getter_pair getter_chain setter_chain setter_pair setter_cFst setter_cSnd

  enum_index_prod_def fst_enum_nth snd_enum_nth enum_index_nth if_distrib[of enum_index]
  enum_nth_injective

  quantum_equality_full_def_let space_div_space_div_unlifted INF_lift Cla_inf_lift Cla_plus_lift Cla_sup_lift
  top_leq_lift top_geq_lift bot_leq_lift bot_geq_lift top_eq_lift bot_eq_lift top_eq_lift2 bot_eq_lift2

lemmas prepare_for_code_flip =
  qregister_of_cregister_Fst qregister_of_cregister_Snd
  qregister_of_cregister_pair qregister_of_cregister_chain
lemma xxx: \<open>apply_qregister_space \<lbrakk>\<lbrakk>#3\<rbrakk>\<^sub>q, \<lbrakk>#4.\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q (\<lbrakk>#1\<rbrakk>\<^sub>q \<equiv>\<qq> \<lbrakk>#2.\<rbrakk>\<^sub>q) = a\<close>
  apply (simp add: join_registers cong del: if_weak_cong add: prepare_for_code_add flip: prepare_for_code_flip)
  oops

lemma permute_and_tensor1_mat'_cong:
\<open>n=m \<Longrightarrow> a=b \<Longrightarrow> permute_and_tensor1_mat' n f g a = permute_and_tensor1_mat' m f g b\<close>
  by simp

definition "Proj_code = Proj"
lemma apply_qregister_space_code_hack': \<open>apply_qregister_space (qregister_of_cregister F) S = apply_qregister (qregister_of_cregister F) (Proj_code S) *\<^sub>S \<top>\<close>
  unfolding Proj_code_def by (rule apply_qregister_space_def)

ML \<open>
fun top_everywhere_conv conv ctxt = Conv.top_conv (fn ctxt => Conv.try_conv (conv ctxt)) ctxt
fun bottom_everywhere_conv conv ctxt = Conv.bottom_conv (fn ctxt => Conv.try_conv (conv ctxt)) ctxt
\<close>


lemma xxx:
\<open>apply_qregister_space \<lbrakk>\<lbrakk>#3\<rbrakk>\<^sub>q, \<lbrakk>#4.\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q (\<lbrakk>#1\<rbrakk>\<^sub>q \<equiv>\<qq> \<lbrakk>#2.\<rbrakk>\<^sub>q)
    \<le> apply_qregister_space \<lbrakk>\<lbrakk>#1\<rbrakk>\<^sub>q, \<lbrakk>#2\<rbrakk>\<^sub>q, \<lbrakk>#3\<rbrakk>\<^sub>q, \<lbrakk>#4.\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q
        (apply_qregister_space \<lbrakk>\<lbrakk>#1\<rbrakk>\<^sub>q, \<lbrakk>#2\<rbrakk>\<^sub>q, \<lbrakk>#3\<rbrakk>\<^sub>q, \<lbrakk>#4.\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q
          (apply_qregister_space \<lbrakk>\<lbrakk>#1\<rbrakk>\<^sub>q, \<lbrakk>#2\<rbrakk>\<^sub>q, \<lbrakk>#3\<rbrakk>\<^sub>q, \<lbrakk>#4.\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q
            (apply_qregister_space empty_qregister \<CC>\<ll>\<aa>[isometry CNOT] \<sqinter>
             apply_qregister_space \<lbrakk>\<lbrakk>#1\<rbrakk>\<^sub>q, \<lbrakk>#2\<rbrakk>\<^sub>q, \<lbrakk>#3\<rbrakk>\<^sub>q, \<lbrakk>#4.\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q
              (apply_qregister \<lbrakk>\<lbrakk>#3\<rbrakk>\<^sub>q, \<lbrakk>#1\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q (CNOT*) *\<^sub>S
               apply_qregister_space \<lbrakk>\<lbrakk>#1\<rbrakk>\<^sub>q, \<lbrakk>#2\<rbrakk>\<^sub>q, \<lbrakk>#3\<rbrakk>\<^sub>q, \<lbrakk>#4.\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q
                (apply_qregister_space \<lbrakk>\<lbrakk>#1\<rbrakk>\<^sub>q, \<lbrakk>#2\<rbrakk>\<^sub>q, \<lbrakk>#3\<rbrakk>\<^sub>q, \<lbrakk>#4.\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q
                  (apply_qregister_space empty_qregister \<CC>\<ll>\<aa>[isometry hadamard] \<sqinter>
                   apply_qregister_space \<lbrakk>\<lbrakk>#1\<rbrakk>\<^sub>q, \<lbrakk>#2\<rbrakk>\<^sub>q, \<lbrakk>#3\<rbrakk>\<^sub>q, \<lbrakk>#4.\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q
                    (apply_qregister \<lbrakk>#3\<rbrakk>\<^sub>q (hadamard*) *\<^sub>S
                      ( (top)))) \<sqinter>
                 apply_qregister_space \<lbrakk>\<lbrakk>#3\<rbrakk>\<^sub>q, \<lbrakk>#1\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q
                  (apply_qregister \<lbrakk>\<lbrakk>#1\<rbrakk>\<^sub>q, \<lbrakk>#2.\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q CNOT *\<^sub>S
                   apply_qregister_space empty_qregister \<top>)))) \<div> EPR\<guillemotright>\<lbrakk>\<lbrakk>#1\<rbrakk>\<^sub>q, \<lbrakk>#2\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q))\<close>

  apply (simp add: join_registers cong: permute_and_tensor1_mat'_cong cong del: if_weak_cong 
        add: prepare_for_code_add  flip: prepare_for_code_flip)
  oops

lemma apply_qregister_space_of_cregister:
  assumes \<open>cregister F\<close>
  shows \<open>apply_qregister_space (qregister_of_cregister F) a =
          permute_and_tensor1_cblinfun (getter F) (same_outside_cregister F) (Proj a) *\<^sub>S \<top>\<close>
  by (simp add: apply_qregister_of_cregister apply_qregister_space_def assms)

lemma qregister_to_cregister_conv_aux1: \<open>Q \<equiv> qregister_of_cregister F \<Longrightarrow> R \<equiv> qregister_of_cregister G \<Longrightarrow> \<lbrakk>Q,R\<rbrakk>\<^sub>q \<equiv> qregister_of_cregister \<lbrakk>F,G\<rbrakk>\<^sub>c\<close>
  by (simp add: Scratch.prepare_for_code_flip(3))

lemma qregister_to_cregister_conv_aux2: 
  \<open>Q \<equiv> qregister_of_cregister F \<Longrightarrow> R \<equiv> qregister_of_cregister G \<Longrightarrow> 
      qregister_chain Q R \<equiv> qregister_of_cregister (cregister_chain F G)\<close>
   by (simp add: Scratch.prepare_for_code_flip(4))

lemma qregister_of_cregister_empty: \<open>qregister_of_cregister empty_cregister = empty_qregister\<close>
  by (metis empty_cregister_is_register empty_qregisters_same qregister_qregister_of_cregister)

lemma qregister_of_cregister_id: \<open>qregister_of_cregister cregister_id = qregister_id\<close>
  by (metis cregister_chain_id cregister_id qregister_chain_id qregister_conversion_as_register qregister_of_cregister_chain qregister_qregister_of_cregister)

ML \<open>
fun qregister_to_cregister_conv_tac ctxt st =
  ((DETERM (resolve_tac ctxt @{thms qregister_to_cregister_conv_aux1 qregister_to_cregister_conv_aux2} 1)
    THEN qregister_to_cregister_conv_tac ctxt THEN qregister_to_cregister_conv_tac ctxt)
  ORELSE (DETERM (resolve_tac ctxt 
    @{thms qregister_of_cregister_Fst[symmetric, THEN eq_reflection]
           qregister_of_cregister_Snd[symmetric, THEN eq_reflection]
           qregister_of_cregister_empty[symmetric, THEN eq_reflection]
           qregister_of_cregister_id[symmetric, THEN eq_reflection]} 1))) st\<close>


ML \<open>
val qregister_to_cregister_conv = Misc.conv_from_tac
  (fn _ => fn t => Prog_Variables.is_index_qregister t orelse raise CTERM ("not an index qregister", [ct]))
  qregister_to_cregister_conv_tac\<close>

ML \<open>
fun apply_qregister_to_cregister_conv_tac ctxt =
  (DETERM (resolve_tac ctxt @{thms apply_qregister_of_cregister[THEN eq_reflection] apply_qregister_space_of_cregister[THEN eq_reflection]} 1))
  THEN Prog_Variables.distinct_vars_tac ctxt 1\<close>

(* schematic_goal \<open>apply_qregister (qregister_of_cregister \<lbrakk>\<lbrakk>#1\<rbrakk>\<^sub>c, \<lbrakk>#2\<rbrakk>\<^sub>c, \<lbrakk>#3\<rbrakk>\<^sub>c, \<lbrakk>#4.\<rbrakk>\<^sub>c\<rbrakk>\<^sub>c) A \<equiv> ?Q\<close>
  apply (tactic \<open>apply_qregister_to_cregister_conv_tac \<^context>\<close>)
  apply (tactic \<open>Prog_Variables.distinct_vars_tac \<^context> 1\<close>)  
  apply (rule apply_qregister_of_cregister[THEN eq_reflection] apply_qregister_space_of_cregister[THEN eq_reflection]) *)

ML \<open>
val apply_qregister_to_cregister_conv = Misc.conv_from_tac
  (fn _ => fn t => case t of \<^Const_>\<open>apply_qregister _ _\<close> $ (\<^Const_>\<open>qregister_of_cregister _ _\<close> $ _) $ _ => ()
                           | \<^Const_>\<open>apply_qregister_space _ _\<close> $ (\<^Const_>\<open>qregister_of_cregister _ _\<close> $ _) $ _ => ()
                           | _ => raise TERM ("not of the form `apply_qregister (qregister_of_cregister _) _`", [t]))
  apply_qregister_to_cregister_conv_tac\<close>

lemma cregister_lens_getter_conv_pair_aux:
  assumes \<open>cregister \<lbrakk>F,G\<rbrakk>\<^sub>c\<close>
  assumes \<open>getter F \<equiv> f\<close>
  assumes \<open>getter G \<equiv> g\<close>
  shows \<open>getter \<lbrakk>F,G\<rbrakk>\<^sub>c \<equiv> BNF_Def.convol f g\<close>
  by (simp add: Scratch.prepare_for_code_add(11) assms(1) assms(2) assms(3) BNF_Def.convol_def)

lemma cregister_lens_getter_conv_chain_aux:
  assumes \<open>cregister F\<close>
  assumes \<open>getter F \<equiv> f\<close>
  assumes \<open>getter G \<equiv> g\<close>
  shows \<open>getter (cregister_chain F G) \<equiv> g o f\<close>
  by (simp add: assms(1) assms(2) assms(3) getter_chain)

lemma cregister_lens_setter_conv_pair_aux:
  assumes \<open>cregister \<lbrakk>F,G\<rbrakk>\<^sub>c\<close>
  assumes \<open>setter F \<equiv> f\<close>
  assumes \<open>setter G \<equiv> g\<close>
  shows \<open>setter \<lbrakk>F,G\<rbrakk>\<^sub>c \<equiv> (\<lambda>(x,y). f x o g y)\<close>
  by (simp add: Scratch.prepare_for_code_add(14) assms(1) assms(2) assms(3))

lemma cregister_lens_setter_conv_chain_aux:
  assumes \<open>cregister F\<close>
  assumes \<open>cregister G\<close>
  assumes \<open>setter F \<equiv> sF\<close>
  assumes \<open>setter G \<equiv> sG\<close>
  assumes \<open>getter F \<equiv> gF\<close>
  shows \<open>setter (cregister_chain F G) \<equiv> (\<lambda>a m. sF (sG a (gF m)) m)\<close>
  using setter_chain[OF assms(1,2), abs_def]
  by (simp add: assms(3-5))

lemma same_outside_cregister_sym:
  \<open>cregister F \<Longrightarrow> same_outside_cregister F n m \<longleftrightarrow> same_outside_cregister F m n\<close>
  apply (simp add: same_outside_cregister_def)
  by (metis setter_getter_same setter_setter_same)

(* TODO unused? *)
lemma cregister_lens_soc_conv_chain_aux:
  assumes [simp]: \<open>cregister F\<close>
  assumes [simp]: \<open>cregister G\<close>
  assumes socF: \<open>same_outside_cregister F \<equiv> socF\<close>
  assumes socG: \<open>same_outside_cregister G \<equiv> socG\<close>
  assumes gF: \<open>getter F \<equiv> gF\<close>
  shows \<open>same_outside_cregister (cregister_chain F G) \<equiv> 
            (\<lambda>m n. socF m n \<and> socG (gF m) (gF n))\<close>
proof (intro eq_reflection ext iffI)
  fix m n
  define gG sF sG where \<open>gG = getter G\<close> and \<open>sF = setter F\<close> and \<open>sG = setter G\<close>
  have sF_twice: \<open>sF a (sF b m) = sF a m\<close> for a b m
    by (simp add: sF_def)
  have sG_twice: \<open>sG a (sG b m) = sG a m\<close> for a b m
    by (simp add: sG_def)
  have sF_gF: \<open>sF (gF m) m = m\<close> for m
    by (simp add: sF_def flip: gF)
  have sG_gG: \<open>sG (gG m) m = m\<close> for m
    by (simp add: sG_def gG_def)
  have gF_sF: \<open>gF (sF a m) = a\<close> for a m
    by (simp add: sF_def flip: gF)

  show \<open>socF m n \<and> socG (gF m) (gF n)\<close> if \<open>same_outside_cregister (cregister_chain F G) m n\<close>
  proof (rule conjI)
    from that have m_def: \<open>m = sF (sG (gG (gF m)) (gF n)) n\<close>
      by (simp add: same_outside_cregister_def setter_chain getter_chain gF
          flip: sF_def sG_def gG_def)
    have \<open>socF n m\<close>
    proof (simp flip: socF sF_def add: gF same_outside_cregister_def)
      have \<open>sF (gF n) m = sF (gF n) (sF (sG (gG (gF m)) (gF n)) n)\<close>
        apply (subst m_def) by simp
      also have \<open>\<dots> = n\<close>
        by (simp add: sF_twice sF_gF)
      finally show \<open>n = sF (gF n) m\<close>
        by simp
    qed
    then show \<open>socF m n\<close>
      by (metis assms(1) assms(3) same_outside_cregister_sym)
    have \<open>socG (gF n) (gF m)\<close>
    proof (simp flip: socG sG_def gG_def add: gF same_outside_cregister_def)
      have \<open>sG (gG (gF n)) (gF m) = sG (gG (gF n)) (gF (sF (sG (gG (gF m)) (gF n)) n))\<close>
        apply (subst m_def) by simp
      also have \<open>\<dots> = gF n\<close>
        by (simp add: gF_sF sG_twice sG_gG)
      finally show \<open>gF n = sG (gG (gF n)) (gF m)\<close>
        by simp
    qed
    then show \<open>socG (gF m) (gF n)\<close>
      by (metis assms(2) assms(4) same_outside_cregister_sym)
  qed

  show \<open>same_outside_cregister (cregister_chain F G) m n\<close> if \<open>socF m n \<and> socG (gF m) (gF n)\<close> 
  proof -
    from that have \<open>socF m n\<close> and \<open>socG (gF m) (gF n)\<close>
      by auto
    from \<open>socG (gF m) (gF n)\<close>
    have 1: \<open>sG (gG (gF m)) (gF n) = gF m\<close>
      by (simp add: same_outside_cregister_def flip: socG sG_def gG_def)
    from \<open>socF m n\<close>
    have 2: \<open>sF (gF m) n = m\<close>
      by (simp add: same_outside_cregister_def gF flip: socF sF_def)

    have \<open>Prog_Variables.setter (cregister_chain F G)
     (Prog_Variables.getter (cregister_chain F G) m) n = sF (sG (gG (gF m)) (gF n)) n\<close>
      by (simp add: getter_chain setter_chain gF flip: gG_def sG_def sF_def)
    also have \<open>\<dots> = sF (gF m) n\<close>
      by (simp add: 1)
    also from 2 have \<open>\<dots> = m\<close>
      by -
    finally show \<open>same_outside_cregister (cregister_chain F G) m n\<close>
      by (simp add: same_outside_cregister_def)
  qed
qed

lemma getter_empty: \<open>getter empty_cregister a = undefined\<close>
  by (rule everything_the_same)

ML \<open>
fun cregister_lens_getter_conv_tac ctxt st =
  ((DETERM (resolve_tac ctxt @{thms cregister_lens_getter_conv_pair_aux cregister_lens_getter_conv_chain_aux} 1)
    THEN Prog_Variables.distinct_vars_tac ctxt 1 THEN cregister_lens_getter_conv_tac ctxt THEN cregister_lens_getter_conv_tac ctxt)
  ORELSE (DETERM (resolve_tac ctxt 
    @{thms getter_cFst[THEN eq_reflection] getter_cSnd[THEN eq_reflection] getter_id[abs_def] getter_empty[abs_def]} 1))) st\<close>

ML \<open>
val cregister_lens_getter_conv = Misc.conv_from_tac
  (fn _ => fn t => case t of \<^Const_>\<open>getter _ _\<close> $ F => is_index_cregister F orelse raise TERM ("not an index register", [t])
                           | _ => raise TERM ("not of the form `getter \<dots>`", [t]))
  cregister_lens_getter_conv_tac\<close>

lemma setter_cregister: \<open>setter empty_cregister a m = m\<close>
  by (metis getter_empty setter_getter_same setter_setter_same)

ML \<open>
fun cregister_lens_setter_conv_tac ctxt st =
  ((DETERM (resolve_tac ctxt @{thms cregister_lens_setter_conv_pair_aux} 1)
    THEN Prog_Variables.distinct_vars_tac ctxt 1 THEN cregister_lens_setter_conv_tac ctxt THEN cregister_lens_setter_conv_tac ctxt)
  ORELSE (DETERM (resolve_tac ctxt @{thms cregister_lens_setter_conv_chain_aux} 1)
    THEN Prog_Variables.distinct_vars_tac ctxt 1 THEN Prog_Variables.distinct_vars_tac ctxt 1
    THEN cregister_lens_setter_conv_tac ctxt THEN cregister_lens_setter_conv_tac ctxt
    THEN cregister_lens_getter_conv_tac ctxt)
  ORELSE (DETERM (resolve_tac ctxt 
    @{thms setter_cFst[abs_def] setter_cSnd[abs_def] setter_id[abs_def] setter_cregister[abs_def]} 1))) st\<close>

thm setter_cFst[abs_def] setter_cSnd[abs_def] setter_id[abs_def] setter_cregister[abs_def]

ML \<open>
val cregister_lens_setter_conv = Misc.conv_from_tac
  (fn _ => fn t => case t of \<^Const_>\<open>setter _ _\<close> $ F => is_index_cregister F orelse raise TERM ("not an index register", [t])
                           | _ => raise TERM ("not of the form `setter \<dots>`", [t]))
  cregister_lens_setter_conv_tac\<close>

ML \<open>
fun tmp_conv ct = let
  val goal = Logic.mk_equals (Thm.term_of ct, Free ("HELLO", Thm.typ_of_cterm ct --> Thm.typ_of_cterm ct) $ Thm.term_of ct)
  val thm = Skip_Proof.make_thm (Thm.theory_of_cterm ct) goal
in thm end 
\<close>

ML \<open>
fun abs_conv' conv = Conv.abs_conv (fn (_,ctxt) => conv ctxt)
\<close>


ML \<open>
open Conv
(* Converts same_outside_qregister F into (\<lambda>m n. \<dots>) for an index-register F *)
fun cregister_lens_soc_conv ctxt = 
Conv.rewr_conv @{lemma \<open>same_outside_cregister F \<equiv> (\<lambda>x y. x = Prog_Variables.setter F (Prog_Variables.getter F x) y)\<close> by (simp add: same_outside_cregister_def[abs_def])}
then_conv
(
 Misc.mk_ctxt_conv2 combination_conv 
      cregister_lens_setter_conv
      (Misc.mk_ctxt_conv fun_conv cregister_lens_getter_conv)
 |> Misc.mk_ctxt_conv fun_conv
 |> Misc.mk_ctxt_conv arg_conv
 |> abs_conv'
 |> abs_conv'
) ctxt
\<close>

ML \<open>
fun cregister_lens_conv ctxt = 
  cregister_lens_getter_conv ctxt
  else_conv cregister_lens_setter_conv ctxt
  else_conv cregister_lens_soc_conv ctxt
\<close>

abbreviation \<open>upfst x \<equiv> apfst (\<lambda>_. x)\<close>
abbreviation \<open>upsnd x \<equiv> apsnd (\<lambda>_. x)\<close>

lemma permute_and_tensor1_cblinfun_conv_tac_aux:
  fixes f :: \<open>'a::eenum \<Rightarrow> 'b::eenum\<close> and g h :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'c::eenum\<close>
  assumes \<open>\<And>a. enum_index (f a) \<equiv> f' (enum_index a)\<close>
  assumes \<open>\<And>a b. enum_index (g a b) \<equiv> g' (enum_index a) (enum_index b)\<close>
  assumes \<open>\<And>a b. enum_index (h a b) \<equiv> h' (enum_index a) (enum_index b)\<close>
  (* assumes \<open>\<And>a b. R a b = R' (enum_index a) (enum_index b)\<close> *)
  shows \<open>permute_and_tensor1_cblinfun f (\<lambda>a b. g a b = h a b) \<equiv> 
      (\<lambda>a. permute_and_tensor1_mat' CARD('a) f' (\<lambda>a b. g' a b = h' b b) (mat_of_cblinfun a))\<close>
  sorry

lemma enum_index_apfst:
  fixes f :: \<open>'a::eenum \<Rightarrow> 'c::eenum\<close> and x :: \<open>'a \<times> 'b::eenum\<close>
  assumes \<open>\<And>a. enum_index (f a) = f' (enum_index a)\<close>
  shows \<open>enum_index (apfst f x) = f' (enum_index x div CARD('b)) * CARD('b) + enum_index x mod CARD('b)\<close>
  by (simp add: apfst_def map_prod_def case_prod_beta enum_index_prod_def assms)

lemma enum_index_apsnd:
  fixes f :: \<open>'b::eenum \<Rightarrow> 'c::eenum\<close> and x :: \<open>'a::eenum \<times> 'b\<close>
  assumes \<open>\<And>a. enum_index (f a) = f' (enum_index a)\<close>
  shows \<open>enum_index (apsnd f x) = enum_index x div CARD('b) * CARD('c) + f' (enum_index (snd x))\<close>
  by (simp add: apsnd_def map_prod_def case_prod_beta enum_index_prod_def assms)

lemma enum_index_upfst:
  fixes a :: \<open>'c::eenum\<close> and x :: \<open>'a::eenum \<times> 'b::eenum\<close>
  shows \<open>enum_index (upfst a x) = enum_index a * CARD('b) + enum_index x mod CARD('b)\<close>
  by (simp add: enum_index_apfst)

lemma enum_index_upsnd:
  fixes a :: \<open>'c::eenum\<close> and x :: \<open>'a::eenum \<times> 'b::eenum\<close>
  shows \<open>enum_index (upsnd a x) = enum_index x div CARD('b) * CARD('c) + enum_index a\<close>
  by (simp add: enum_index_apsnd)

lemma enum_index_convol:
  fixes f :: \<open>'a \<Rightarrow> 'b::eenum\<close> and g :: \<open>'a \<Rightarrow> 'c::eenum\<close>
  shows \<open>enum_index (BNF_Def.convol f g a) = enum_index (f a) * CARD('c) + enum_index (g a)\<close>
  by (simp add: enum_index_prod_def convol_def)

lemma upsnd_twice: \<open>upsnd a (upsnd b x) = upsnd a x\<close>
  by (simp add: prod.expand)

lemma upfst_twice: \<open>upfst a (upfst b x) = upfst a x\<close>
  by (simp add: prod.expand)

lemma upfst_upsnd: \<open>upfst a (upsnd b x) = (a,b)\<close>
  by simp

lemma upsnd_upfst: \<open>upsnd b (upfst a x) = (a,b)\<close>
  by simp

lemma snd_upsnd: \<open>snd (upsnd a x) = a\<close>
  by simp

lemma fst_upfst: \<open>fst (upfst a x) = a\<close>
  by simp

lemma enum_index_pair: \<open>enum_index (a,b) = enum_index a * CARD('b) + enum_index b\<close> for a :: \<open>'a::eenum\<close> and b :: \<open>'b::eenum\<close>
  by (simp add: enum_index_prod_def)

lemma enum_index_CARD_1: \<open>enum_index a = 0\<close> for a :: \<open>'a::{eenum,CARD_1}\<close>
  apply (subst everything_the_same[of a \<open>enum_nth 0\<close>])
  apply (subst enum_index_nth)
  by simp

instantiation unit :: eenum begin
definition \<open>enum_nth_unit (_::nat) = ()\<close>
definition \<open>enum_index_unit (_::unit) = (0::nat)\<close>
instance
  apply intro_classes
  by (simp_all add: enum_index_unit_def)
end

ML \<open>
local
  val round1_simps = @{thms case_prod_beta snd_convol' fst_convol' o_def
      upsnd_twice upfst_twice prod.collapse fst_conv snd_conv
      upfst_upsnd upsnd_upfst snd_upsnd fst_upfst}
  val round2_simps = @{thms enum_index_convol enum_index_upsnd enum_index_upfst
      enum_index_fst enum_index_snd enum_index_pair div_leq_simp mod_mod_cancel
      enum_index_CARD_1}
in
fun enum_index_conv ctxt = let
  val round1_ctxt = (clear_simpset ctxt) addsimps round1_simps
  val round2_ctxt = ctxt addsimps round2_simps
in Simplifier.rewrite round1_ctxt then_conv Simplifier.rewrite round2_ctxt end
end
\<close>

ML \<open>
fun permute_and_tensor1_cblinfun_conv_tac ctxt =
  resolve_tac ctxt @{thms permute_and_tensor1_cblinfun_conv_tac_aux} 1
  THEN
  CONVERSION ((enum_index_conv |> Misc.mk_ctxt_conv arg1_conv |> params_conv ~1) ctxt) 1
  THEN
  resolve_tac ctxt @{thms reflexive} 1
  THEN
  CONVERSION ((enum_index_conv |> Misc.mk_ctxt_conv arg1_conv |> params_conv ~1) ctxt) 1
  THEN
  resolve_tac ctxt @{thms reflexive} 1
  THEN
  CONVERSION ((enum_index_conv |> Misc.mk_ctxt_conv arg1_conv |> params_conv ~1) ctxt) 1
  THEN
  resolve_tac ctxt @{thms reflexive} 1
\<close>

ML \<open>
val permute_and_tensor1_cblinfun_conv = Misc.conv_from_tac
  (fn ctxt => fn t => case t of \<^Const_>\<open>permute_and_tensor1_cblinfun _ _\<close> $ _ $ _  => (* \<^print> ("Found one") *) ()
                           | _ => raise TERM ("permute_and_tensor1_cblinfun_conv", [t]))
  permute_and_tensor1_cblinfun_conv_tac
\<close>



ML \<open>
fun wrap_dbg conv ctxt ct = let val res : thm
 = conv ctxt ct (* handle e => (\<^print> ("exn"); raise e) *) 
val orig = Thm.term_of ct
val new = Thm.term_of (Thm.lhs_of res)
val _ = new = orig orelse error
   (\<^make_string> ("BLA", 
orig = new, orig aconv new, Envir.beta_eta_contract orig = Envir.beta_eta_contract new,
Envir.beta_norm orig = Envir.beta_norm new,
Envir.aeconv (orig, new),
orig, new))
val _ = \<^print> ("Success") in res end
\<close>

ML \<open>
cregister_lens_getter_conv \<^context> \<^cterm>\<open>Prog_Variables.getter empty_cregister\<close>
\<close>

schematic_goal \<open>permute_and_tensor1_cblinfun (\<lambda>a::'a::eenum. undefined :: unit) (\<lambda>x y. x = y) \<equiv> ?X\<close>
  apply (tactic \<open>CONVERSION (top_everywhere_conv (wrap_dbg  permute_and_tensor1_cblinfun_conv) \<^context>) 1\<close>)
  oops
schematic_goal \<open>(Proj (apply_qregister qregister_id pauliZ *\<^sub>S apply_qregister_space (empty_qregister :: (unit,_) qregister) \<top>))
=xxx\<close>
  for XXX :: \<open>bit ell2 \<Rightarrow>\<^sub>C\<^sub>L bit ell2 \<Rightarrow> (bit \<times> bit \<times> bit) ell2 \<Rightarrow>\<^sub>C\<^sub>L (bit \<times> bit \<times> bit) ell2\<close>
    apply (tactic \<open>CONVERSION (top_everywhere_conv qregister_to_cregister_conv \<^context>) 1\<close>)
  apply (tactic \<open>CONVERSION (top_everywhere_conv apply_qregister_to_cregister_conv \<^context>) 1\<close>)
  apply (tactic \<open>CONVERSION (top_everywhere_conv cregister_lens_conv \<^context>) 1\<close>)

  apply (tactic \<open>CONVERSION (top_everywhere_conv (wrap_dbg  permute_and_tensor1_cblinfun_conv) \<^context>) 1\<close>)
  oops

ML \<open>
fun foc l = CSUBGOAL (fn (ct,i) => let
  val t = Thm.term_of ct
  val thy = Thm.theory_of_cterm ct
  fun subterm (t $ u) (0::ls) = subterm t ls
    | subterm (t $ u) (_::ls) = subterm u ls
    | subterm (Abs (n,T,t)) (_::ls) = subterm (subst_bound (Free(":"^n,T), t)) ls
    | subterm t _ = t
  val t' = subterm t l
  val new_goal = Logic.mk_equals (t', Var(("XXX",0),fastype_of t'))
  fun conv ct = Logic.mk_equals (Thm.term_of ct, new_goal) |> Skip_Proof.make_thm thy
in CONVERSION conv i end) 1
\<close>

ML \<open>
normalize_register_conv \<^context> \<^cterm>\<open>\<lbrakk>\<lbrakk>#1\<rbrakk>\<^sub>q, \<lbrakk>#2\<rbrakk>\<^sub>q, \<lbrakk>#3\<rbrakk>\<^sub>q, \<lbrakk>#4.\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q\<close>
\<close>

ML \<open>
(* TODO *)
fun complement_of_index_register ctxt ct = let
  val thm1 = normalize_register_conv2 ctxt ct  (* ct \<equiv> ct' *)
  val ct' = Thm.rhs_of thm1 |> \<^print>
in () end
;;

complement_of_index_register \<^context> \<^cterm>\<open>\<lbrakk>\<lbrakk>#3\<rbrakk>\<^sub>q, \<lbrakk>#2\<rbrakk>\<^sub>q, \<lbrakk>#1\<rbrakk>\<^sub>q, \<lbrakk>#5.\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q\<close>
\<close>

lift_definition equivalent_qregisters :: \<open>('a,'c) qregister \<Rightarrow> ('b,'c) qregister \<Rightarrow> bool\<close> is
  equivalent_registers.

definition \<open>equivalent_qregisters' F G \<longleftrightarrow> equivalent_qregisters F G \<or> (F = non_qregister \<and> G = non_qregister)\<close>

lemma QREGISTER_of_non_qregister: \<open>QREGISTER_of non_qregister = QREGISTER_unit\<close>
  apply (rule Rep_QREGISTER_inject[THEN iffD1])
  by (simp add: QREGISTER_of.rep_eq QREGISTER_unit.rep_eq)

definition QREGISTER_of' where \<open>QREGISTER_of' F = (if qregister F then Some (QREGISTER_of F) else None)\<close>

lemma x1:
  assumes \<open>qregister F\<close>
  assumes \<open>equivalent_qregisters' F H\<close>
  assumes \<open>qcomplements H G\<close>
  shows \<open>qcomplements F G\<close>
  sorry



(* 
lemma x2:
  assumes \<open>QREGISTER_of' F \<equiv> QREGISTER_of' F'\<close>
  assumes \<open>QREGISTER_of' G \<equiv> QREGISTER_of' G'\<close>
  assumes \<open>QREGISTER_of' \<lbrakk>F',G'\<rbrakk> \<equiv> QREGISTER_of' H\<close>
  shows \<open>QREGISTER_of' \<lbrakk>F,G\<rbrakk> \<equiv> QREGISTER_of' H\<close>
  sorry

lemma x3:
  assumes \<open>QREGISTER_of' F \<equiv> QREGISTER_of' F'\<close>
  shows \<open>QREGISTER_of' (qregister_chain qFst F) \<equiv> QREGISTER_of' (qregister_chain qFst F')\<close>
  sorry

lemma x4:
  assumes \<open>QREGISTER_of' F \<equiv> QREGISTER_of' F'\<close>
  shows \<open>QREGISTER_of' (qregister_chain qSnd F) \<equiv> QREGISTER_of' (qregister_chain qSnd F')\<close>
  sorry

lemma x5:
  shows \<open>QREGISTER_of' \<lbrakk>qFst, qSnd\<rbrakk> \<equiv> QREGISTER_of' qregister_id\<close>
  sorry

lemma x6:
  shows \<open>QREGISTER_of' \<lbrakk>qFst, qregister_chain qSnd F\<rbrakk> \<equiv> QREGISTER_of' \<lbrakk>qFst, qregister_chain qSnd F\<rbrakk>\<close>
  by simp
  sorry

ML \<open>
open Misc
\<close>

ML \<open>
(* Given \<open>QREGISTER_of' F \<equiv> QREGISTER_of' ?Q\<close>, instantiates ?Q with a "sorted" F.
   Assumes F is index-register.
   "Sorted" means: \<open>Q = Fst o \<dots>\<close> or \<open>Q = Snd o \<dots>\<close> or \<open>Q = id\<close> or \<open>Q = empty\<close>
    or \<open>Q = \<lbrakk>Fst o \<dots>, Snd o \<dots>\<rbrakk> where \<dots> is also sorted and not empty/id\<close>
 *)
fun QREGISTER_of'_index_reg_norm_tac ctxt = SUBGOAL (fn (t,i) => 
  (\<^print> (Thm.cterm_of ctxt t);
  case t of
    \<^Const_>\<open>Pure.eq _\<close> $ (\<^Const_>\<open>QREGISTER_of' _ _\<close> $ (\<^Const_>\<open>qregister_pair _ _ _\<close> $ _ $ _)) $ _ =>
      resolve_tac ctxt @{thms x2} i
      THEN
      QREGISTER_of'_index_reg_norm_tac ctxt i
      THEN
      QREGISTER_of'_index_reg_norm_tac ctxt i
      THEN
      print_here_tac ctxt \<^here>
      THEN
      resolve_tac ctxt @{thms x5 x6} i
  | \<^Const_>\<open>Pure.eq _\<close> $ (\<^Const_>\<open>QREGISTER_of' _ _\<close> $ 
         (\<^Const_>\<open>qregister_chain _ _ _\<close> $ \<^Const_>\<open>qFst _ _\<close> $ _)) $ _ =>
      resolve_tac ctxt @{thms x3} i
      THEN
      QREGISTER_of'_index_reg_norm_tac ctxt i
  | \<^Const_>\<open>Pure.eq _\<close> $ (\<^Const_>\<open>QREGISTER_of' _ _\<close> $ 
         (\<^Const_>\<open>qregister_chain _ _ _\<close> $ \<^Const_>\<open>qSnd _ _\<close> $ _)) $ _ =>
      resolve_tac ctxt @{thms x4} i
      THEN
      QREGISTER_of'_index_reg_norm_tac ctxt i
  | \<^Const_>\<open>Pure.eq _\<close> $ (\<^Const_>\<open>QREGISTER_of' _ _\<close> $ \<^Const_>\<open>qFst _ _\<close>) $ _ =>
      resolve_tac ctxt @{thms reflexive} i
  | \<^Const_>\<open>Pure.eq _\<close> $ (\<^Const_>\<open>QREGISTER_of' _ _\<close> $ \<^Const_>\<open>qSnd _ _\<close>) $ _ =>
      resolve_tac ctxt @{thms reflexive} i
  | \<^Const_>\<open>Pure.eq _\<close> $ (\<^Const_>\<open>QREGISTER_of' _ _\<close> $ _) $ _ =>
      print_here_tac ctxt \<^here>
      THEN
      resolve_tac ctxt @{thms} 1
    ))
\<close>
 *)

definition \<open>QREGISTER_pair' F G = (case (F,G) of (Some F', Some G') \<Rightarrow> Some (QREGISTER_pair F' G')
  | _ \<Rightarrow> None)\<close>

lemma x7: \<open>QREGISTER_pair (QREGISTER_chain qSnd F) (QREGISTER_chain qFst G)
= QREGISTER_pair (QREGISTER_chain qFst G) (QREGISTER_chain qSnd F)\<close>
  sorry
lemma x6: \<open>QREGISTER_pair (QREGISTER_chain qSnd F) QREGISTER_fst
= QREGISTER_pair QREGISTER_fst (QREGISTER_chain qSd F)\<close>
  sorry
lemma x8: \<open>QREGISTER_pair QREGISTER_snd (QREGISTER_chain qFst G)
= QREGISTER_pair (QREGISTER_chain qFst G) QREGISTER_snd\<close>
  sorry


ML "open Misc"

lemma QREGISTER_of_empty_qregister: \<open>QREGISTER_of empty_qregister = QREGISTER_unit\<close>
  sorry


ML \<open>
fun qcomplement_of_index_qregister ctxt ct = let
  val _ = Prog_Variables.is_index_qregister (Thm.term_of ct)
          orelse raise CTERM ("qcomplement_of_index_qregister: not an index qregister", [ct])
  val index = Thm.maxidx_of_cterm ct + 1
  val (inT,outT) = dest_qregisterT (Thm.typ_of_cterm ct)
  val x_inT = TVar(("'x", index), [])
  val qcomplement_const = Thm.cterm_of ctxt \<^Const>\<open>qcomplements inT outT x_inT\<close>
  val x = Thm.cterm_of ctxt (Var (("x", index), \<^Type>\<open>qregister x_inT outT\<close>))
  val goal =  (* qcomplements ct ? *)
      Thm.apply (Thm.apply qcomplement_const ct) x |> Thm.apply \<^cterm>\<open>Trueprop\<close>
  val thm = Goal.prove_internal \<^context> [] goal (K (qcomplements_tac ctxt 1))
  val complement = thm |> Thm.cprop_of |> Thm.dest_arg |> Thm.dest_arg
  val _ = Prog_Variables.is_index_qregister (Thm.term_of complement)
          orelse raise CTERM ("qcomplement_of_index_qregister: failed to compute index-register", [ct, complement])
in (complement, thm) end
;;
qcomplement_of_index_qregister \<^context> \<^cterm>\<open>\<lbrakk>\<lbrakk>#2\<rbrakk>\<^sub>q, \<lbrakk>#3\<rbrakk>\<^sub>q, \<lbrakk>#1\<rbrakk>\<^sub>q, \<lbrakk>#5.\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q\<close>
\<close>


(* TODO: Implement TTIR-tactics for this. *)
(* For index-register F *)
definition \<open>TTIR_COMPLEMENT F G \<longleftrightarrow> qcomplements F G\<close>
(* For index-iso-register F *)
definition \<open>TTIR_INVERSE F G \<longleftrightarrow> 
  qregister_chain F G = qregister_id \<and> qregister_chain G F = qregister_id\<close>

lemma translate_to_index_registers_space_div_unlift:
  fixes A' :: \<open>'a ell2 ccsubspace\<close> and G :: \<open>('b,'a) qregister\<close>
    and F :: \<open>('c,'a) qregister\<close> and FG :: \<open>('d,'a) qregister\<close>
  assumes \<open>TTIR_APPLY_QREGISTER_SPACE A' F A\<close>
  assumes \<open>TTIR_LUB F G FG F' G'\<close>
  assumes \<open>TTIR_COMPLEMENT G' L\<close>
  assumes \<open>TTIR_INVERSE \<lbrakk>L, G'\<rbrakk>\<^sub>q H\<close>
  shows \<open>TTIR_APPLY_QREGISTER_SPACE (space_div A' \<psi> G)
          (qregister_chain FG L) (space_div_unlifted (apply_qregister_space (qregister_chain H F') A) \<psi>)\<close>
proof -
  from \<open>TTIR_COMPLEMENT G' L\<close>
  have [simp]: \<open>qregister \<lbrakk>G', L\<rbrakk>\<^sub>q\<close>
    by (simp add: TTIR_COMPLEMENT_def qcomplements_def')
  have F'_decomp: \<open>F' = qregister_chain (qregister_chain \<lbrakk>L, G'\<rbrakk> H) F'\<close>
    using TTIR_INVERSE_def assms(4) by force

  have \<open>space_div A' \<psi> G = space_div (A \<guillemotright> F') \<psi> G' \<guillemotright> FG\<close>
    using assms by (simp add: space_div_lift TTIR_APPLY_QREGISTER_SPACE_def TTIR_LUB_def)
  also have \<open>\<dots> = space_div (A \<guillemotright> F' \<guillemotright> H \<guillemotright> \<lbrakk>L,G'\<rbrakk>) \<psi> G' \<guillemotright> FG\<close>
    apply (subst F'_decomp) by simp
  also have \<open>\<dots> = space_div_unlifted (A \<guillemotright> F' \<guillemotright> H) \<psi> \<guillemotright> L \<guillemotright> FG\<close>
    by (simp add: space_div_space_div_unlifted)
  also have \<open>\<dots> = (space_div_unlifted (A \<guillemotright> qregister_chain H F') \<psi>) \<guillemotright> (qregister_chain FG L)\<close>
    by simp
  finally show ?thesis
    by (simp add: TTIR_APPLY_QREGISTER_SPACE_def)
qed

(* Use in this form? *)
lemma space_div_space_div_unlifted_inv:
  assumes \<open>qcomplements Q R\<close>
  shows \<open>space_div A \<psi> Q = 
            space_div_unlifted (apply_qregister_space (qregister_inv \<lbrakk>R,Q\<rbrakk>) A) \<psi> \<guillemotright> R\<close>
proof -
  from assms have \<open>qcomplements R Q\<close>
    by (meson complements_sym qcomplements.rep_eq)
  define A' where \<open>A' = apply_qregister_space (qregister_inv \<lbrakk>R,Q\<rbrakk>) A\<close>
  have \<open>qregister_chain \<lbrakk>R,Q\<rbrakk> (qregister_inv \<lbrakk>R,Q\<rbrakk>) = qregister_id\<close>
    apply (rule iso_qregister_chain_inv)
    using \<open>qcomplements R Q\<close> by (simp add: qcomplements_def')
  then have \<open>space_div A \<psi> Q = space_div (apply_qregister_space \<lbrakk>R,Q\<rbrakk> A') \<psi> Q\<close>
    by (metis (no_types, opaque_lifting) A'_def apply_qregister_space_id qregister_chain_apply_space)
  also have \<open>\<dots> = apply_qregister_space R (space_div_unlifted A' \<psi>)\<close>
    using space_div_space_div_unlifted assms qcomplements_def' by blast
  finally show ?thesis
    by (simp add: A'_def)
qed

lemma \<open>qregister_chain (\<lbrakk>\<lbrakk>#1\<rbrakk>\<^sub>q, \<lbrakk>#2\<rbrakk>\<^sub>q, \<lbrakk>#4.\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q) empty_qregister = xxx\<close>
  apply (tactic \<open>CONVERSION (top_sweep_conv normalize_register_conv \<^context>) 1\<close>)
  oops

lemma lemma_724698:
  fixes C :: "(bit, qu) qregister" and A :: "(bit, qu) qregister" and B :: "(bit, qu) qregister"
  assumes [register]: \<open>declared_qvars \<lbrakk>C, A, B\<rbrakk>\<close>
  shows "qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q (C::(bit, qu) qregister) \<equiv>\<qq> qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q A \<le> \<CC>\<ll>\<aa>[\<parallel>EPR\<parallel> = 1] \<sqinter> (\<CC>\<ll>\<aa>[isometry CNOT] \<sqinter> (apply_qregister \<lbrakk>qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q C, qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q A\<rbrakk>\<^sub>q CNOT* *\<^sub>S (\<CC>\<ll>\<aa>[isometry hadamard] \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q C) hadamard* *\<^sub>S ((let M = computational_basis in \<CC>\<ll>\<aa>[mtotal M] \<sqinter> (\<Sqinter>z. let P = apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q A) (mproj M z) *\<^sub>S \<top> in (let M = computational_basis in \<CC>\<ll>\<aa>[mtotal M] \<sqinter> (\<Sqinter>za. let P = apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q C) (mproj M za) *\<^sub>S \<top> in (\<CC>\<ll>\<aa>[z \<noteq> 1] + \<CC>\<ll>\<aa>[isometry pauliX] \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B) pauliX* *\<^sub>S ((\<CC>\<ll>\<aa>[za \<noteq> 1] + \<CC>\<ll>\<aa>[isometry pauliZ] \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B) pauliZ* *\<^sub>S (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B \<equiv>\<qq> qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q A \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B) pauliZ *\<^sub>S \<top>)))) \<sqinter> (\<CC>\<ll>\<aa>[za = 1] + qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B \<equiv>\<qq> qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q A) \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B) pauliX *\<^sub>S \<top>)))) \<sqinter> (\<CC>\<ll>\<aa>[z = 1] + (\<CC>\<ll>\<aa>[za \<noteq> 1] + \<CC>\<ll>\<aa>[isometry pauliZ] \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B) pauliZ* *\<^sub>S (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B \<equiv>\<qq> qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q A \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B) pauliZ *\<^sub>S \<top>)))) \<sqinter> (\<CC>\<ll>\<aa>[za = 1] + qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B \<equiv>\<qq> qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q A)) \<sqinter> P + - P)) \<sqinter> P + - P)) \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q C) hadamard *\<^sub>S \<top>))) \<sqinter> (apply_qregister \<lbrakk>qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q C, qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q A\<rbrakk>\<^sub>q CNOT *\<^sub>S \<top>)))) \<div> EPR\<guillemotright>\<lbrakk>qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q A, qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B\<rbrakk>\<^sub>q"
  apply translate_to_index_registers
  apply (simp add: quantum_equality_full_def_let space_div_space_div_unlifted)
  apply (tactic \<open>CONVERSION (top_everywhere_conv normalize_register_conv \<^context>) 1\<close>)
  apply (simp only: apply_qregister_id apply_qregister_space_id)
  apply (tactic \<open>CONVERSION (top_everywhere_conv qregister_to_cregister_conv \<^context>) 1\<close>)
  apply (tactic \<open>CONVERSION (top_everywhere_conv apply_qregister_to_cregister_conv \<^context>) 1\<close>)
  apply (tactic \<open>CONVERSION (top_everywhere_conv cregister_lens_conv \<^context>) 1\<close>)
  using [[ML_print_depth=30]]
  using [[show_types]]
  apply (tactic \<open>CONVERSION (top_everywhere_conv ((* wrap_dbg *) permute_and_tensor1_cblinfun_conv) \<^context>) 1\<close>)
  (* apply (tactic \<open>foc [1,1,0,1,1,1,1,0,1,1,1,0,0,1,0,1,1,1,1,0,1,1,1,1,0,1,1,1,0,1,0,1,1,1,1,0,1,1,1,1]\<close>) *)
  (* apply (tactic \<open>foc [0,1,0,1,1,1,0,1,0,1,1,1,1,1,1,0,1,1,1,1,0,1,1,1,1,0,1,0,1,1,1,0,1,0,1,1,1,1,1,1]\<close>) *)
  (* apply (tactic \<open>foc [0,1,0,1,1,1,1,0,1,1,1,1,1,0,1,0]\<close>) *)
  (* apply (tactic \<open>CONVERSION Thm.eta_conversion 1\<close>) *)
  (* apply (tactic \<open>CONVERSION (Thm.beta_conversion true) 1\<close>) *)
  (* apply (tactic \<open>CONVERSION (top_everywhere_conv (wrap_dbg permute_and_tensor1_cblinfun_conv) \<^context>) 1\<close>) *)
(* TODO: Still contains: (Proj (apply_qregister qregister_id pauliZ *\<^sub>S apply_qregister_space empty_qregister \<top>))) *)
  apply simp x

  apply (simp add: join_registers   ZZZ
cong del: if_weak_cong 
cong: permute_and_tensor1_mat'_cong
add:
    permute_and_tensor1_cblinfun_code_prep 
    

   case_prod_beta if_distrib[of fst] if_distrib[of snd] prod_eq_iff 

  div_leq_simp mod_mod_cancel 

   enum_index_prod_def fst_enum_nth snd_enum_nth enum_index_nth if_distrib[of enum_index] 
   enum_nth_injective 

  (* quantum_equality_full_def_let space_div_space_div_unlifted INF_lift Cla_inf_lift Cla_plus_lift Cla_sup_lift *)
  (* top_leq_lift top_geq_lift bot_leq_lift bot_geq_lift top_eq_lift bot_eq_lift top_eq_lift2 bot_eq_lift2 *)


 flip:
 (* prepare_for_code_flip *)

)
  
  (* apply prepare_for_code *)
   apply eval 
  by -

ML\<open>open QRHL_Operations\<close>


no_notation m_inv ("inv\<index> _" [81] 80)
unbundle no_vec_syntax
unbundle jnf_notation
hide_const (open) Finite_Cartesian_Product.mat
hide_const (open) Finite_Cartesian_Product.vec

derive (eq) ceq bit
derive (compare) ccompare bit
derive (dlist) set_impl bit


lemma
  fixes a b c
  assumes t[variable]: \<open>qregister (\<lbrakk>a,b,c\<rbrakk> :: (bit*bit*bit) qvariable)\<close>
  shows True
proof -
  define CNOT' where \<open>CNOT' = apply_qregister \<lbrakk>a,c \<mapsto> a,b,c\<rbrakk> CNOT\<close>

  have \<open>apply_qregister \<lbrakk>a,b\<rbrakk> CNOT o\<^sub>C\<^sub>L apply_qregister \<lbrakk>a,c\<rbrakk> CNOT = 
        apply_qregister \<lbrakk>a,c\<rbrakk> CNOT o\<^sub>C\<^sub>L apply_qregister \<lbrakk>a,b\<rbrakk> CNOT\<close>
    apply prepare_for_code
    by normalization

  have \<open>CNOT' *\<^sub>V ket (1,1,1) = (ket (1,1,0) :: (bit*bit*bit) ell2)\<close>
    unfolding CNOT'_def
    apply prepare_for_code
    by normalization


  oops



ML \<open>open Prog_Variables\<close>

(* TEST *)
lemma
  fixes a b c
  assumes t[variable]: \<open>qregister (\<lbrakk>a,b,c\<rbrakk> :: (bit*bit*bit) qvariable)\<close>
  shows True
proof -
  define CNOT' where \<open>CNOT' = apply_qregister \<lbrakk>a,c \<mapsto> a,b,c\<rbrakk> CNOT\<close>
  have \<open>apply_qregister \<lbrakk>a,b\<rbrakk> CNOT o\<^sub>C\<^sub>L apply_qregister \<lbrakk>a,c\<rbrakk> CNOT = 
        apply_qregister \<lbrakk>a,c\<rbrakk> CNOT o\<^sub>C\<^sub>L apply_qregister \<lbrakk>a,b\<rbrakk> CNOT\<close>
    apply (simp add: join_registers)
    oops


(* (* TODO keep? *)
lemma qregister_chain_unit_right[simp]: \<open>qregister F \<Longrightarrow> qregister_chain F qvariable_unit = qvariable_unit\<close>
  by (simp add: qvariable_unit_def)
lemma qregister_chain_unit_left[simp]: \<open>qregister F \<Longrightarrow> qregister_chain qvariable_unit F = qvariable_unit\<close>
  by (simp add: qvariable_unit_def) *)


(* TODO keep? *)
lemma qregister_conversion_chain:
  assumes \<open>qregister_le F G\<close> \<open>qregister_le G H\<close>
  shows \<open>qregister_chain (qregister_conversion G H) (qregister_conversion F G) = qregister_conversion F H\<close>
  using assms unfolding qregister_le_def apply (transfer fixing: F G H) apply transfer
  by (auto intro!: ext qregister_conversion_raw_register simp: f_inv_into_f range_subsetD)


(* TODO keep? *)
lemma permute_and_tensor1_cblinfun_butterfly: 
  fixes f :: \<open>_::finite \<Rightarrow> _::finite\<close>
  assumes [simp]: \<open>bij f\<close> \<open>\<And>x y. R x y\<close>
  shows \<open>permute_and_tensor1_cblinfun f R (butterket a b) = butterket (inv f a) (inv f b)\<close>
proof (rule equal_ket, rule Rep_ell2_inject[THEN iffD1], rule ext)
  fix i j
  have \<open>Rep_ell2 (permute_and_tensor1_cblinfun f R (butterket a b) \<cdot> ket i) j = 
          Rep_ell2 ((ket b \<bullet>\<^sub>C ket (f i)) *\<^sub>C ket a) (f j)\<close>
    by auto
  also have \<open>\<dots> = (if b=f i then 1 else 0) * (if a=f j then 1 else 0)\<close>
    by (auto simp add: scaleC_ell2.rep_eq ket.rep_eq)
  also have \<open>\<dots> = (if inv f b=i then 1 else 0) * (if inv f a=j then 1 else 0)\<close>
    by (smt (verit, del_insts) assms(1) assms(2) bij_inv_eq_iff)
  also have \<open>\<dots> = Rep_ell2 ((ket (inv f b) \<bullet>\<^sub>C ket i) *\<^sub>C ket (inv f a)) j\<close>
    by (simp add: scaleC_ell2.rep_eq ket.rep_eq)
  also have \<open>\<dots> = Rep_ell2 (butterket (inv f a) (inv f b) \<cdot> ket i) j\<close>
    by auto
  finally show \<open>Rep_ell2 (permute_and_tensor1_cblinfun f R (butterket a b) \<cdot> ket i) j
                   = Rep_ell2 (butterket (inv f a) (inv f b) \<cdot> ket i) j\<close>
    by -
qed

(* TODO: to bounded operators *)
declare enum_idx_correct[simp]


