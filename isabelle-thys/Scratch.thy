theory Scratch
  imports QRHL
 (* "HOL-ex.Sketch_and_Explore" *) 
(* "HOL-Eisbach.Eisbach" *)
(* QRHL_Operations  *)
begin

no_notation eq_closure_of ("closure'_of\<index>")

ML "open Prog_Variables"

(* MOVE 1 *)


lemma commutant_memberI:
  assumes \<open>\<And>y. y \<in> X \<Longrightarrow> x o\<^sub>C\<^sub>L y = y o\<^sub>C\<^sub>L x\<close>
  shows \<open>x \<in> commutant X\<close>
  using assms by (simp add: commutant_def)


lemma Proj_compose_cancelI:
  assumes \<open>A *\<^sub>S \<top> \<le> S\<close>
  shows \<open>Proj S o\<^sub>C\<^sub>L A = A\<close>
  apply (rule cblinfun_eqI)
proof -
  fix x
  have \<open>(Proj S o\<^sub>C\<^sub>L A) *\<^sub>V x = Proj S *\<^sub>V (A *\<^sub>V x)\<close>
  by simp
  also have \<open>\<dots> = A *\<^sub>V x\<close>
    apply (rule Proj_fixes_image)
    using assms cblinfun_apply_in_image less_eq_ccsubspace.rep_eq by blast
  finally show \<open>(Proj S o\<^sub>C\<^sub>L A) *\<^sub>V x = A *\<^sub>V x\<close>
    by -
qed

lemma continuous_cstrong_operator_topology_plus[continuous_intros]:
  assumes \<open>continuous_map T cstrong_operator_topology f\<close>
  assumes \<open>continuous_map T cstrong_operator_topology g\<close>
  shows \<open>continuous_map T cstrong_operator_topology (\<lambda>x. f x + g x)\<close>
  using assms
  by (auto intro!: continuous_map_add
      simp: continuous_on_cstrong_operator_topo_iff_coordinatewise cblinfun.add_left)

lemma continuous_cstrong_operator_topology_uminus[continuous_intros]:
  assumes \<open>continuous_map T cstrong_operator_topology f\<close>
  shows \<open>continuous_map T cstrong_operator_topology (\<lambda>x. - f x)\<close>
  using assms
  by (auto simp add: continuous_on_cstrong_operator_topo_iff_coordinatewise cblinfun.minus_left)

lemma continuous_cstrong_operator_topology_minus[continuous_intros]:
  assumes \<open>continuous_map T cstrong_operator_topology f\<close>
  assumes \<open>continuous_map T cstrong_operator_topology g\<close>
  shows \<open>continuous_map T cstrong_operator_topology (\<lambda>x. f x - g x)\<close>
  apply (subst diff_conv_add_uminus)
  by (intro continuous_intros assms)


lemma cblinfun_image_ccspan_leqI:
  assumes \<open>\<And>v. v \<in> M \<Longrightarrow> A *\<^sub>V v \<in> space_as_set T\<close>
  shows \<open>A *\<^sub>S ccspan M \<le> T\<close>
  by (simp add: assms cblinfun_image_ccspan ccspan_leqI image_subsetI)

lemma space_as_setI_via_Proj:
  assumes \<open>Proj M *\<^sub>V x = x\<close>
  shows \<open>x \<in> space_as_set M\<close>
  using assms norm_Proj_apply by fastforce

lemma commutant_sot_closed: \<open>closedin cstrong_operator_topology (commutant A)\<close>
  \<comment> \<open>@{cite conway13functional}, Exercise IX.6.2\<close>
proof (cases \<open>A = {}\<close>)
  case True
  then show ?thesis
    apply simp
    by (metis closedin_topspace cstrong_operator_topology_topspace)
next
  case False
  have closed_a: \<open>closedin cstrong_operator_topology (commutant {a})\<close> for a :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  proof -
    have comm_a: \<open>commutant {a} = (\<lambda>b. a o\<^sub>C\<^sub>L b - b o\<^sub>C\<^sub>L a) -` {0}\<close>
      by (auto simp: commutant_def)
    have closed_0: \<open>closedin cstrong_operator_topology {0}\<close>
      apply (rule closedin_singleton)
      by simp_all
    have cont: \<open>continuous_map cstrong_operator_topology cstrong_operator_topology (\<lambda>b. a o\<^sub>C\<^sub>L b - b o\<^sub>C\<^sub>L a)\<close>
      by (intro continuous_intros continuous_map_left_comp_sot continuous_map_right_comp_sot)
      (* TODO: Put continuous_map_left_comp_sot continuous_map_right_comp_sot into [continuous_intros]
              (suitably rewritten) *)
    show ?thesis
      using closedin_vimage[OF closed_0 cont]
      by (simp add: comm_a)
  qed
  have *: \<open>commutant A = (\<Inter>a\<in>A. commutant {a})\<close>
    by (auto simp add: commutant_def)
  show ?thesis
    by (auto intro!: closedin_Inter simp: * False closed_a)
qed



fun inflation_op' :: \<open>nat \<Rightarrow> ('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2) list \<Rightarrow> ('a\<times>nat) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('b\<times>nat) ell2\<close> where
  \<open>inflation_op' n Nil = 0\<close>
| \<open>inflation_op' n (a#as) = (a \<otimes>\<^sub>o selfbutterket n) + inflation_op' (n+1) as\<close>

abbreviation \<open>inflation_op \<equiv> inflation_op' 0\<close>

fun inflation_state' :: \<open>nat \<Rightarrow> 'a ell2 list \<Rightarrow> ('a\<times>nat) ell2\<close> where
  \<open>inflation_state' n Nil = 0\<close>
| \<open>inflation_state' n (a#as) = (a \<otimes>\<^sub>s ket n) + inflation_state' (n+1) as\<close>

abbreviation \<open>inflation_state \<equiv> inflation_state' 0\<close>

fun inflation_space' :: \<open>nat \<Rightarrow> 'a ell2 ccsubspace list \<Rightarrow> ('a\<times>nat) ell2 ccsubspace\<close> where
  \<open>inflation_space' n Nil = 0\<close>
| \<open>inflation_space' n (S#Ss) = (S \<otimes>\<^sub>S ccspan {ket n}) + inflation_space' (n+1) Ss\<close>

abbreviation \<open>inflation_space \<equiv> inflation_space' 0\<close>

definition inflation_carrier :: \<open>nat \<Rightarrow> ('a\<times>nat) ell2 ccsubspace\<close> where
  \<open>inflation_carrier n = inflation_space (replicate n \<top>)\<close>

definition inflation_op_carrier :: \<open>nat \<Rightarrow> (('a\<times>nat) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('b\<times>nat) ell2) set\<close> where
  \<open>inflation_op_carrier n = { Proj (inflation_carrier n) o\<^sub>C\<^sub>L a o\<^sub>C\<^sub>L Proj (inflation_carrier n) | a. True }\<close>

lemma is_Proj_id[simp]: \<open>is_Proj id_cblinfun\<close>
  apply transfer
  by (auto intro!: exI[of _ UNIV] simp: is_projection_on_def is_arg_min_def)

lemma inflation_op_compose_outside: \<open>inflation_op' m ops o\<^sub>C\<^sub>L (a \<otimes>\<^sub>o selfbutterket n) = 0\<close> if \<open>n < m\<close>
  using that apply (induction ops arbitrary: m)
  by (auto simp: cblinfun_compose_add_left comp_tensor_op cinner_ket)

lemma inflation_op_compose_outside_rev: \<open>(a \<otimes>\<^sub>o selfbutterket n) o\<^sub>C\<^sub>L inflation_op' m ops = 0\<close> if \<open>n < m\<close>
  using that apply (induction ops arbitrary: m)
  by (auto simp: cblinfun_compose_add_right comp_tensor_op cinner_ket)


lemma Proj_inflation_carrier: \<open>Proj (inflation_carrier n) = inflation_op (replicate n id_cblinfun)\<close>
proof -
  have \<open>Proj (inflation_space' m (replicate n \<top>)) = inflation_op' m (replicate n id_cblinfun)\<close> for m
  proof (induction n arbitrary: m)
    case 0
    then show ?case
      by simp
  next
    case (Suc n)
    have *: \<open>orthogonal_spaces ((\<top> :: 'b ell2 ccsubspace) \<otimes>\<^sub>S ccspan {|m\<rangle>}) (inflation_space' (Suc m) (replicate n \<top>))\<close>
      by (auto simp add: orthogonal_projectors_orthogonal_spaces Suc tensor_ccsubspace_via_Proj 
          Proj_on_own_range is_Proj_tensor_op inflation_op_compose_outside_rev butterfly_is_Proj
          simp flip: butterfly_eq_proj)
    show ?case 
      apply (simp add: Suc * Proj_sup)
      by (metis (no_types, opaque_lifting) Proj_is_Proj Proj_on_own_range Proj_top 
          butterfly_eq_proj is_Proj_tensor_op norm_ket tensor_ccsubspace_via_Proj)
  qed
  then show ?thesis
    by (force simp add: inflation_carrier_def)
qed

lemma inflation_op_carrierI:
  assumes \<open>Proj (inflation_carrier n) o\<^sub>C\<^sub>L a o\<^sub>C\<^sub>L Proj (inflation_carrier n) = a\<close>
  shows \<open>a \<in> inflation_op_carrier n\<close>
  using assms by (auto intro!: exI[of _ a] simp add: inflation_op_carrier_def)

lemma inflation_op_compose: \<open>inflation_op' n ops1 o\<^sub>C\<^sub>L inflation_op' n ops2 = inflation_op' n (map2 cblinfun_compose ops1 ops2)\<close>
proof (induction ops2 arbitrary: ops1 n)
  case Nil
  then show ?case by simp
next
  case (Cons op ops2)
  note IH = this
  fix ops1 :: \<open>('c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2) list\<close>
  show \<open>inflation_op' n ops1 o\<^sub>C\<^sub>L inflation_op' n (op # ops2) =
        inflation_op' n (map2 (o\<^sub>C\<^sub>L) ops1 (op # ops2))\<close>
  proof (cases ops1)
    case Nil
    then show ?thesis 
      by simp
  next
    case (Cons a list)
    then show ?thesis
      by (simp add: cblinfun_compose_add_right cblinfun_compose_add_left tensor_op_ell2
          inflation_op_compose_outside comp_tensor_op inflation_op_compose_outside_rev
          flip: IH)
  qed
qed

lemma inflation_op_in_carrier: \<open>inflation_op ops \<in> inflation_op_carrier n\<close> if \<open>length ops \<le> n\<close>
  apply (rule inflation_op_carrierI)
  using that
  by (simp add: Proj_inflation_carrier inflation_op_carrier_def inflation_op_compose
      zip_replicate1 zip_replicate2 o_def)

lemma inflation_op'_apply_tensor_outside: \<open>n < m \<Longrightarrow> inflation_op' m as *\<^sub>V (v \<otimes>\<^sub>s |n\<rangle>) = 0\<close>
  apply (induction as arbitrary: m)
  by (auto simp: cblinfun.add_left tensor_op_ell2 cinner_ket)

lemma inflation_op'_compose_tensor_outside: \<open>n < m \<Longrightarrow> inflation_op' m as o\<^sub>C\<^sub>L tensor_ell2_right (ket n) = 0\<close>
  apply (rule cblinfun_eqI)
  by (simp add: inflation_op'_apply_tensor_outside)

lemma inflation_state'_apply_tensor_outside: \<open>n < m \<Longrightarrow> (a \<otimes>\<^sub>o butterfly \<psi> (ket n)) *\<^sub>V inflation_state' m vs = 0\<close>
  apply (induction vs arbitrary: m)
  by (auto simp: cblinfun.add_right tensor_op_ell2 cinner_ket)

lemma inflation_op_apply_inflation_state: \<open>inflation_op' n ops *\<^sub>V inflation_state' n vecs = inflation_state' n (map2 cblinfun_apply ops vecs)\<close>
proof (induction vecs arbitrary: ops n)
  case Nil
  then show ?case by simp
next
  case (Cons v vecs)
  note IH = this
  fix ops :: \<open>('b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2) list\<close>
  show \<open>inflation_op' n ops *\<^sub>V inflation_state' n (v # vecs) =
        inflation_state' n (map2 (*\<^sub>V) ops (v # vecs))\<close>
  proof (cases ops)
    case Nil
    then show ?thesis 
      by simp
  next
    case (Cons a list)
    then show ?thesis
      by (simp add: cblinfun.add_right cblinfun.add_left tensor_op_ell2
          inflation_op'_apply_tensor_outside inflation_state'_apply_tensor_outside
          flip: IH)
  qed
qed

lemma inflation_state_in_carrier: \<open>inflation_state vecs \<in> space_as_set (inflation_carrier n)\<close> if \<open>length vecs + m \<le> n\<close>
  apply (rule space_as_setI_via_Proj)
  using that
  by (simp add: Proj_inflation_carrier inflation_op_apply_inflation_state zip_replicate1 o_def)

lemma inflation_op'_apply_tensor_outside': \<open>n \<ge> length as + m \<Longrightarrow> inflation_op' m as *\<^sub>V (v \<otimes>\<^sub>s |n\<rangle>) = 0\<close>
  apply (induction as arbitrary: m)
  by (auto simp: cblinfun.add_left tensor_op_ell2 cinner_ket)

lemma Proj_inflation_carrier_outside: \<open>Proj (inflation_carrier n) *\<^sub>V (\<psi> \<otimes>\<^sub>s |i\<rangle>) = 0\<close> if \<open>i \<ge> n\<close>
  by (simp add: Proj_inflation_carrier inflation_op'_apply_tensor_outside' that)

lemma inflation_state'_is_orthogonal_outside: \<open>n < m \<Longrightarrow> is_orthogonal (a \<otimes>\<^sub>s ket n) (inflation_state' m vs)\<close>
  apply (induction vs arbitrary: m)
  by (auto simp: cinner_add_right)

lemma inflation_op_adj: \<open>(inflation_op' n ops)* = inflation_op' n (map adj ops)\<close>
  apply (induction ops arbitrary: n)
  by (simp_all add: adj_plus tensor_op_adjoint)


(* TODO replace  *) thm limitin_closure_of (* with this *)
lemma limitin_closure_of:
  assumes limit: \<open>limitin T f c F\<close>
  assumes in_S: \<open>\<forall>\<^sub>F x in F. f x \<in> S\<close>
  assumes nontrivial: \<open>\<not> trivial_limit F\<close>
  shows \<open>c \<in> T closure_of S\<close>
proof (intro in_closure_of[THEN iffD2] conjI impI allI)
  from limit show \<open>c \<in> topspace T\<close>
    by (simp add: limitin_topspace)
  fix U
  assume \<open>c \<in> U \<and> openin T U\<close>
  with limit have \<open>\<forall>\<^sub>F x in F. f x \<in> U\<close>
    by (simp add: limitin_def)
  with in_S have \<open>\<forall>\<^sub>F x in F. f x \<in> U \<and> f x \<in> S\<close>
    by (simp add: eventually_frequently_simps)
  with nontrivial
  show \<open>\<exists>y. y \<in> S \<and> y \<in> U\<close>
    using eventually_happens' by blast
qed


(* TODO: can be generalized for more pullback topologies, I think *)
lemma cstrong_operator_topology_in_closureI:
  assumes \<open>\<And>M \<epsilon>. \<epsilon> > 0 \<Longrightarrow> finite M \<Longrightarrow> \<exists>a\<in>A. \<forall>v\<in>M. norm ((b-a) *\<^sub>V v) \<le> \<epsilon>\<close>
  shows \<open>b \<in> cstrong_operator_topology closure_of A\<close>
proof -
  define F :: \<open>('a set \<times> real) filter\<close> where \<open>F = finite_subsets_at_top UNIV \<times>\<^sub>F at_right 0\<close>
  obtain f where fA: \<open>f M \<epsilon> \<in> A\<close> and f: \<open>v \<in> M \<Longrightarrow> norm ((f M \<epsilon> - b) *\<^sub>V v) \<le> \<epsilon>\<close> if \<open>finite M\<close> and \<open>\<epsilon> > 0\<close> for M \<epsilon> v
    apply atomize_elim
    apply (intro allI choice2)
    using assms
    by (metis cblinfun.diff_left norm_minus_commute)
  have F_props: \<open>\<forall>\<^sub>F (M,\<epsilon>) in F. finite M \<and> \<epsilon> > 0\<close>
    apply (auto intro!: eventually_prodI simp: F_def case_prod_unfold)
    by (simp add: eventually_at_right_less)
  then have inA: \<open>\<forall>\<^sub>F (M,\<epsilon>) in F. f M \<epsilon> \<in> A\<close>
    apply (rule eventually_rev_mp)
    using fA by (auto intro!: always_eventually)
  have \<open>limitin cstrong_operator_topology (case_prod f) b F\<close>
  proof -
    have \<open>\<forall>\<^sub>F (M,\<epsilon>) in F. \<parallel>f M \<epsilon> *\<^sub>V v - b *\<^sub>V v\<parallel> < e\<close> if \<open>e > 0\<close> for e v
    proof -
      have 1: \<open>\<forall>\<^sub>F (M,\<epsilon>) in F. (finite M \<and> v \<in> M) \<and> (\<epsilon> > 0 \<and> \<epsilon> < e)\<close>
        apply (unfold F_def case_prod_unfold, rule eventually_prodI)
        using eventually_at_right that
        by (auto simp add: eventually_finite_subsets_at_top)
      have 2: \<open>\<parallel>f M \<epsilon> *\<^sub>V v - b *\<^sub>V v\<parallel> < e\<close> if \<open>(finite M \<and> v \<in> M) \<and> (\<epsilon> > 0 \<and> \<epsilon> < e)\<close> for M \<epsilon>
        by (smt (verit) cblinfun.diff_left f that)
      show ?thesis
        using 1 apply (rule eventually_mono)
        using 2 by auto
    qed
    then have \<open>((\<lambda>(M,\<epsilon>). f M \<epsilon> *\<^sub>V v) \<longlongrightarrow> b *\<^sub>V v) F\<close> for v
      by (simp add: tendsto_iff dist_norm case_prod_unfold)
    then show ?thesis
      by (simp add: case_prod_unfold limitin_cstrong_operator_topology)
  qed
  then show ?thesis
    apply (rule limitin_closure_of)
    using inA by (auto simp: F_def fA case_prod_unfold prod_filter_eq_bot)
qed

lemma inflation_state0:
  assumes \<open>\<And>v. v \<in> set f \<Longrightarrow> v = 0\<close>
  shows \<open>inflation_state' n f = 0\<close>
  using assms apply (induction f arbitrary: n)
   apply simp
  using tensor_ell2_0_left by force

lemma inflation_state_plus:
  assumes \<open>length f = length g\<close>
  shows \<open>inflation_state' n f + inflation_state' n g = inflation_state' n (map2 plus f g)\<close>
  using assms apply (induction f g arbitrary: n rule: list_induct2)
  by (auto simp: algebra_simps tensor_ell2_add1)

lemma inflation_state_minus:
  assumes \<open>length f = length g\<close>
  shows \<open>inflation_state' n f - inflation_state' n g = inflation_state' n (map2 minus f g)\<close>
  using assms apply (induction f g arbitrary: n rule: list_induct2)
  by (auto simp: algebra_simps tensor_ell2_diff1)

lemma inflation_state_scaleC:
  shows \<open>c *\<^sub>C inflation_state' n f = inflation_state' n (map (scaleC c) f)\<close>
  apply (induction f arbitrary: n)
  by (auto simp: algebra_simps tensor_ell2_scaleC1)

lemma inflation_op_compose_tensor_ell2_right:
  assumes \<open>i \<ge> n\<close> and \<open>i < n + length f\<close>
  shows \<open>inflation_op' n f o\<^sub>C\<^sub>L tensor_ell2_right (ket i) = tensor_ell2_right (ket i) o\<^sub>C\<^sub>L (f!(i-n))\<close>
proof (insert assms, induction f arbitrary: n)
  case Nil
  then show ?case
    by simp
next
  case (Cons a f)
  show ?case
  proof (cases \<open>i = n\<close>)
    case True
    have \<open>a \<otimes>\<^sub>o selfbutterket n o\<^sub>C\<^sub>L tensor_ell2_right |n\<rangle> = tensor_ell2_right |n\<rangle> o\<^sub>C\<^sub>L a\<close>
      apply (rule cblinfun_eqI)
      by (simp add: tensor_op_ell2 cinner_ket)
    with True show ?thesis
      by (simp add: cblinfun_compose_add_left inflation_op'_compose_tensor_outside)
  next
    case False
    with Cons.prems have 1: \<open>Suc n \<le> i\<close>
      by presburger
    have 2: \<open>a \<otimes>\<^sub>o selfbutterket n o\<^sub>C\<^sub>L tensor_ell2_right |i\<rangle> = 0\<close>
      apply (rule cblinfun_eqI)
      using False by (simp add: tensor_op_ell2 cinner_ket)
    show ?thesis
      using Cons.prems 1
      by (simp add: cblinfun_compose_add_left Cons.IH[where n=\<open>Suc n\<close>] 2)
  qed
qed

lemma inflation_op_apply:
  assumes \<open>i \<ge> n\<close> and \<open>i < n + length f\<close>
  shows \<open>inflation_op' n f *\<^sub>V (\<psi> \<otimes>\<^sub>s ket i) = (f!(i-n) *\<^sub>V \<psi>) \<otimes>\<^sub>s ket i\<close>
  by (simp add: inflation_op_compose_tensor_ell2_right assms
      flip: tensor_ell2_right_apply cblinfun_apply_cblinfun_compose)

lemma norm_inflation_state:
  \<open>norm (inflation_state' n f) = sqrt (\<Sum>v\<leftarrow>f. \<parallel>v\<parallel>\<^sup>2)\<close>
proof -
  have \<open>(norm (inflation_state' n f))\<^sup>2 = (\<Sum>v\<leftarrow>f. \<parallel>v\<parallel>\<^sup>2)\<close>
  proof (induction f arbitrary: n)
    case Nil
    then show ?case by simp
  next
    case (Cons v f)
    have \<open>\<parallel>inflation_state' n (v # f)\<parallel>\<^sup>2 = \<parallel>v \<otimes>\<^sub>s |n\<rangle> + inflation_state' (Suc n) f\<parallel>\<^sup>2\<close>
      by simp
    also have \<open>\<dots> = \<parallel>v \<otimes>\<^sub>s |n\<rangle>\<parallel>\<^sup>2 + \<parallel>inflation_state' (Suc n) f\<parallel>\<^sup>2\<close>
      apply (rule pythagorean_theorem)
      apply (rule inflation_state'_is_orthogonal_outside)
      by simp
    also have \<open>\<dots> = \<parallel>v \<otimes>\<^sub>s |n\<rangle>\<parallel>\<^sup>2 + (\<Sum>v\<leftarrow>f. \<parallel>v\<parallel>\<^sup>2)\<close>
      by (simp add: Cons.IH)
    also have \<open>\<dots> = \<parallel>v\<parallel>\<^sup>2 + (\<Sum>v\<leftarrow>f. \<parallel>v\<parallel>\<^sup>2)\<close>
      by (simp add: norm_tensor_ell2)
    also have \<open>\<dots> = (\<Sum>v\<leftarrow>v#f. \<parallel>v\<parallel>\<^sup>2)\<close>
      by simp
    finally show ?case
      by -
  qed
  then show ?thesis
    by (simp add: real_sqrt_unique)
qed

lemma cstrong_operator_topology_in_closure_algebraicI:
  \<comment> \<open>@{cite conway13functional}, Proposition IX.5.3\<close>
  assumes space: \<open>csubspace A\<close>
  assumes mult: \<open>\<And>a a'. a \<in> A \<Longrightarrow> a' \<in> A \<Longrightarrow> a o\<^sub>C\<^sub>L a' \<in> A\<close>
  assumes one: \<open>id_cblinfun \<in> A\<close>
  assumes main: \<open>\<And>n S. S \<le> inflation_carrier n \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> inflation_op (replicate n a) *\<^sub>S S \<le> S) \<Longrightarrow>
                 inflation_op (replicate n b) *\<^sub>S S \<le> S\<close>
  shows \<open>b \<in> cstrong_operator_topology closure_of A\<close>
proof (rule cstrong_operator_topology_in_closureI)
  fix F :: \<open>'a ell2 set\<close> and \<epsilon> :: real
  assume \<open>finite F\<close> and \<open>\<epsilon> > 0\<close>
  obtain f where \<open>set f = F\<close> and \<open>distinct f\<close>
    using \<open>finite F\<close> finite_distinct_list by blast
  define n M' M where \<open>n = length f\<close>
    and \<open>M' = ((\<lambda>a. inflation_state (map (cblinfun_apply a) f)) ` A)\<close>
    and \<open>M = ccspan M'\<close>
  have M_carrier: \<open>M \<le> inflation_carrier n\<close>
  proof -
    have \<open>M' \<subseteq> space_as_set (inflation_carrier n)\<close>
      by (auto intro!: inflation_state_in_carrier simp add: M'_def n_def)
    then show ?thesis
      by (simp add: M_def ccspan_leqI)
  qed

  have \<open>inflation_op (replicate n a) *\<^sub>S M \<le> M\<close> if \<open>a \<in> A\<close> for a
  proof (unfold M_def, rule cblinfun_image_ccspan_leqI)
    fix v assume \<open>v \<in> M'\<close>
    then obtain a' where \<open>a' \<in> A\<close> and v_def: \<open>v = inflation_state (map (cblinfun_apply a') f)\<close>
      using M'_def by blast
    then have \<open>inflation_op (replicate n a) *\<^sub>V v = inflation_state (map ((*\<^sub>V) (a o\<^sub>C\<^sub>L a')) f)\<close>
      by (simp add: v_def n_def inflation_op_apply_inflation_state map2_map_map 
          flip: cblinfun_apply_cblinfun_compose map_replicate_const)
    also have \<open>\<dots> \<in> M'\<close>
      using M'_def \<open>a' \<in> A\<close> \<open>a \<in> A\<close> mult
      by simp
    also have \<open>\<dots> \<subseteq> space_as_set (ccspan M')\<close>
      by (simp add: ccspan_superset)
    finally show \<open>inflation_op (replicate n a) *\<^sub>V v \<in> space_as_set (ccspan M')\<close>
      by -
  qed
  then have b_invariant: \<open>inflation_op (replicate n b) *\<^sub>S M \<le> M\<close>
    using M_carrier by (simp add: main)
  have f_M: \<open>inflation_state f \<in> space_as_set M\<close>
  proof -
    have \<open>inflation_state f = inflation_state (map (cblinfun_apply id_cblinfun) f)\<close>
      by simp
    also have \<open>\<dots> \<in> M'\<close>
      using M'_def one by blast
    also have \<open>\<dots> \<subseteq> space_as_set M\<close>
      by (simp add: M_def ccspan_superset)
    finally show ?thesis
      by -
  qed
  have \<open>csubspace M'\<close>
  proof (rule complex_vector.subspaceI)
    fix c x y
    show \<open>0 \<in> M'\<close>
      apply (auto intro!: image_eqI[where x=0] simp add: M'_def)
       apply (subst inflation_state0)
      by (auto simp add: space complex_vector.subspace_0)
    show \<open>x \<in> M' \<Longrightarrow> y \<in> M' \<Longrightarrow> x + y \<in> M'\<close>
      by (auto intro!: image_eqI[where x=\<open>_ + _\<close>] 
          simp add: M'_def inflation_state_plus map2_map_map
          cblinfun.add_left[abs_def] space complex_vector.subspace_add)
    show \<open>c *\<^sub>C x \<in> M' \<close> if \<open>x \<in> M'\<close>
    proof -
      from that
      obtain a where \<open>a \<in> A\<close> and \<open>x = inflation_state (map ((*\<^sub>V) a) f)\<close>
        by (auto simp add: M'_def)
      then have \<open>c *\<^sub>C x = inflation_state (map ((*\<^sub>V) (c *\<^sub>C a)) f)\<close>
        by (simp add: inflation_state_scaleC o_def scaleC_cblinfun.rep_eq)
      moreover have \<open>c *\<^sub>C a \<in> A\<close>
         by (simp add: \<open>a \<in> A\<close> space complex_vector.subspace_scale)
      ultimately show ?thesis
        unfolding M'_def
        by (rule image_eqI)
    qed
  qed
  then have M_closure_M': \<open>space_as_set M = closure M'\<close>
    by (metis M_def ccspan.rep_eq complex_vector.span_eq_iff)
  have \<open>inflation_state (map (cblinfun_apply b) f) \<in> space_as_set M\<close>
  proof -
    have \<open>map2 (*\<^sub>V) (replicate n b) f = map ((*\<^sub>V) b) f\<close>
      using map2_map_map[where h=cblinfun_apply and g=id and f=\<open>\<lambda>_. b\<close> and xs=f]
      by (simp add: n_def flip: map_replicate_const)
    then have \<open>inflation_state (map (cblinfun_apply b) f) = inflation_op (replicate n b) *\<^sub>V inflation_state f\<close>
      by (simp add: inflation_op_apply_inflation_state)
    also have \<open>\<dots> \<in> space_as_set (inflation_op (replicate n b) *\<^sub>S M)\<close>
      by (simp add: f_M cblinfun_apply_in_image')
    also have \<open>\<dots> \<subseteq> space_as_set M\<close>
      using b_invariant less_eq_ccsubspace.rep_eq by blast
    finally show ?thesis
      by -
  qed
    (* apply (auto intro!: ccspan_superset' simp add: M_def M'_def) *)
  then obtain m where \<open>m \<in> M'\<close> and m_close: \<open>norm (m - inflation_state (map (cblinfun_apply b) f)) \<le> \<epsilon>\<close>
    apply atomize_elim
    apply (simp add: M_closure_M' closure_approachable dist_norm)
    using \<open>\<epsilon> > 0\<close> by fastforce
  from \<open>m \<in> M'\<close>
  obtain a where \<open>a \<in> A\<close> and m_def: \<open>m = inflation_state (map (cblinfun_apply a) f)\<close>
    by (auto simp add: M'_def)
  have \<open>(\<Sum>v\<leftarrow>f. \<parallel>(a - b) *\<^sub>V v\<parallel>\<^sup>2) \<le> \<epsilon>\<^sup>2\<close>
  proof -
    have \<open>(\<Sum>v\<leftarrow>f. \<parallel>(a - b) *\<^sub>V v\<parallel>\<^sup>2) = \<parallel>inflation_state (map (cblinfun_apply (a - b)) f)\<parallel>\<^sup>2\<close>
      apply (simp add: norm_inflation_state o_def)
      apply (subst real_sqrt_pow2)
       apply (rule sum_list_nonneg)
      by (auto simp: sum_list_nonneg)
    also have \<open>\<dots> = \<parallel>m - inflation_state (map (cblinfun_apply b) f)\<parallel>\<^sup>2\<close>
      by (simp add: m_def inflation_state_minus map2_map_map cblinfun.diff_left[abs_def])
    also have \<open>\<dots> \<le> \<epsilon>\<^sup>2\<close>
      by (simp add: m_close power_mono)
    finally show ?thesis
      by -
  qed
  then have \<open>\<parallel>(a - b) *\<^sub>V v\<parallel>\<^sup>2 \<le> \<epsilon>\<^sup>2\<close> if \<open>v \<in> F\<close> for v
    using that apply (simp flip: sum.distinct_set_conv_list add: \<open>distinct f\<close>)
    by (smt (verit) \<open>finite F\<close> \<open>set f = F\<close> sum_nonneg_leq_bound zero_le_power2)
  then show \<open>\<exists>a\<in>A. \<forall>f\<in>F. \<parallel>(b - a) *\<^sub>V f\<parallel> \<le> \<epsilon>\<close>
    using \<open>0 < \<epsilon>\<close> \<open>a \<in> A\<close>
    by (metis cblinfun.real.diff_left norm_minus_commute power2_le_imp_le power_eq_0_iff power_zero_numeral realpow_pos_nth_unique zero_compare_simps(12))
qed

lemma commutant_inflation:
  \<comment> \<open>One direction of @{cite conway13functional}, Proposition IX.6.2.\<close>
  fixes n
  defines \<open>\<And>X. commutant' X \<equiv> commutant X \<inter> inflation_op_carrier n\<close>
  shows \<open>(\<lambda>a. inflation_op (replicate n a)) ` commutant (commutant A) 
         \<subseteq> commutant' (commutant' ((\<lambda>a. inflation_op (replicate n a)) ` A))\<close>
proof (unfold commutant'_def, rule subsetI, rule IntI)
  fix b
  assume \<open>b \<in> (\<lambda>a. inflation_op (replicate n a)) ` commutant (commutant A)\<close>
  then obtain b0 where b_def: \<open>b = inflation_op (replicate n b0)\<close> and b0_A'': \<open>b0 \<in> commutant (commutant A)\<close>
    by auto
  show \<open>b \<in> inflation_op_carrier n\<close>
    by (simp add: b_def inflation_op_in_carrier)
  show \<open>b \<in> commutant (commutant ((\<lambda>a. inflation_op (replicate n a)) ` A) \<inter> inflation_op_carrier n)\<close>
  proof (rule commutant_memberI)
    fix c
    assume \<open>c \<in> commutant ((\<lambda>a. inflation_op (replicate n a)) ` A) \<inter> inflation_op_carrier n\<close>
    then have c_comm: \<open>c \<in> commutant ((\<lambda>a. inflation_op (replicate n a)) ` A)\<close>
      and c_carr: \<open>c \<in> inflation_op_carrier n\<close>
      by auto
    define c' where \<open>c' i j = (tensor_ell2_right (ket i))* o\<^sub>C\<^sub>L c o\<^sub>C\<^sub>L tensor_ell2_right (ket j)\<close> for i j
    have \<open>c' i j o\<^sub>C\<^sub>L a = a o\<^sub>C\<^sub>L c' i j\<close> if \<open>a \<in> A\<close> and \<open>i < n\<close> and \<open>j < n\<close> for a i j
    proof -
      from c_comm have \<open>c o\<^sub>C\<^sub>L inflation_op (replicate n a) = inflation_op (replicate n a) o\<^sub>C\<^sub>L c\<close>
        using that by (auto simp: commutant_def)
      then have \<open>(tensor_ell2_right (ket i))* o\<^sub>C\<^sub>L c o\<^sub>C\<^sub>L (inflation_op (replicate n a) o\<^sub>C\<^sub>L tensor_ell2_right (ket j))
               = (inflation_op (replicate n (a*)) o\<^sub>C\<^sub>L (tensor_ell2_right (ket i)))* o\<^sub>C\<^sub>L c o\<^sub>C\<^sub>L tensor_ell2_right (ket j)\<close>
        apply (simp add: inflation_op_adj)
        by (metis (no_types, lifting) Misc.lift_cblinfun_comp(2))
      then show ?thesis
        apply (subst (asm) inflation_op_compose_tensor_ell2_right)
          apply (simp, simp add: that)
        apply (subst (asm) inflation_op_compose_tensor_ell2_right)
          apply (simp, simp add: that)
        by (simp add: that c'_def cblinfun_compose_assoc)
    qed
    then have \<open>c' i j \<in> commutant A\<close> if \<open>i < n\<close> and \<open>j < n\<close> for i j
      using that by (simp add: commutant_memberI)
    with b0_A'' have b0_c': \<open>b0 o\<^sub>C\<^sub>L c' i j = c' i j o\<^sub>C\<^sub>L b0\<close> if \<open>i < n\<close> and \<open>j < n\<close> for i j
      using that by (simp add: commutant_def)

    from c_carr obtain c'' where c'': \<open>c = Proj (inflation_carrier n) o\<^sub>C\<^sub>L c'' o\<^sub>C\<^sub>L Proj (inflation_carrier n)\<close>
      by (auto simp add: inflation_op_carrier_def)
    
    have c0: \<open>c *\<^sub>V (\<psi> \<otimes> ket i) = 0\<close> if \<open>i \<ge> n\<close> for i \<psi>
      using that by (simp add: c'' Proj_inflation_carrier_outside)
    have cadj0: \<open>c* *\<^sub>V (\<psi> \<otimes> ket j) = 0\<close> if \<open>j \<ge> n\<close> for j \<psi>
      using that by (simp add: c'' adj_Proj Proj_inflation_carrier_outside)

    have \<open>inflation_op (replicate n b0) o\<^sub>C\<^sub>L c = c o\<^sub>C\<^sub>L inflation_op (replicate n b0)\<close>
    proof (rule equal_ket, rule cinner_ket_eqI)
      fix ii jj
      obtain i' j' :: 'a and i j :: nat where ii_def: \<open>ii = (i',i)\<close> and jj_def: \<open>jj = (j',j)\<close>
        by force
      show \<open>|ii\<rangle> \<bullet>\<^sub>C ((inflation_op (replicate n b0) o\<^sub>C\<^sub>L c) *\<^sub>V |jj\<rangle>) =
                 |ii\<rangle> \<bullet>\<^sub>C ((c o\<^sub>C\<^sub>L inflation_op (replicate n b0)) *\<^sub>V |jj\<rangle>)\<close>
      proof (cases \<open>i < n \<and> j < n\<close>)
        case True
        have \<open>|ii\<rangle> \<bullet>\<^sub>C ((inflation_op (replicate n b0) o\<^sub>C\<^sub>L c) *\<^sub>V |jj\<rangle>) = ((b0* *\<^sub>V |i'\<rangle>) \<otimes>\<^sub>s |i\<rangle>) \<bullet>\<^sub>C (c *\<^sub>V |j'\<rangle> \<otimes>\<^sub>s |j\<rangle>)\<close>
          using True by (simp add: ii_def jj_def inflation_op_adj inflation_op_apply flip: tensor_ell2_inner_prod
              flip: tensor_ell2_ket cinner_adj_left[where G=\<open>inflation_op _\<close>])
        also have \<open>\<dots> = ( |i'\<rangle> \<otimes>\<^sub>s |i\<rangle>) \<bullet>\<^sub>C (c *\<^sub>V (b0 *\<^sub>V |j'\<rangle>) \<otimes>\<^sub>s |j\<rangle>)\<close>
          using b0_c' apply (simp add: c'_def flip: tensor_ell2_right_apply cinner_adj_right)
          by (metis (no_types, lifting) True simp_a_oCL_b')
        also have \<open>\<dots> = |ii\<rangle> \<bullet>\<^sub>C ((c o\<^sub>C\<^sub>L inflation_op (replicate n b0)) *\<^sub>V |jj\<rangle>)\<close>
          by (simp add: True ii_def jj_def inflation_op_adj inflation_op_apply flip: tensor_ell2_inner_prod
              flip: tensor_ell2_ket cinner_adj_left[where G=\<open>inflation_op _\<close>])
        finally show ?thesis
          by -
      next
        case False
        then show ?thesis
          apply (auto simp add: ii_def jj_def inflation_op_adj c0 inflation_op'_apply_tensor_outside'
              simp flip: tensor_ell2_ket  cinner_adj_left[where G=\<open>inflation_op _\<close>])
          by (simp add: cadj0 flip: cinner_adj_left[where G=c])
      qed
    qed
    then show \<open>b o\<^sub>C\<^sub>L c = c o\<^sub>C\<^sub>L b\<close>
      by (simp add: b_def)
  qed
qed

lemma double_commutant_theorem: (* TODO: generalize to non-ell2 spaces *)
  \<comment> \<open>@{cite conway13functional}, Proposition IX.6.4\<close>
  fixes A :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2) set\<close>
  assumes \<open>csubspace A\<close>
  assumes \<open>\<And>a a'. a \<in> A \<Longrightarrow> a' \<in> A \<Longrightarrow> a o\<^sub>C\<^sub>L a' \<in> A\<close>
  assumes \<open>id_cblinfun \<in> A\<close>
  assumes \<open>\<And>a. a \<in> A \<Longrightarrow> a* \<in> A\<close>
  shows \<open>commutant (commutant A) = cstrong_operator_topology closure_of A\<close>
proof (intro Set.set_eqI iffI)
  show \<open>x \<in> commutant (commutant A)\<close> if \<open>x \<in> cstrong_operator_topology closure_of A\<close> for x
    using closure_of_minimal commutant_sot_closed double_commutant_grows that by blast
next
  show \<open>b \<in> cstrong_operator_topology closure_of A\<close> if b_A'': \<open>b \<in> commutant (commutant A)\<close> for b
  proof (rule cstrong_operator_topology_in_closure_algebraicI)
    show \<open>csubspace A\<close> and \<open>a \<in> A \<Longrightarrow> a' \<in> A \<Longrightarrow> a o\<^sub>C\<^sub>L a' \<in> A\<close> and \<open>id_cblinfun \<in> A\<close> for a a'
      using assms by auto
    fix n M
    assume asm: \<open>a \<in> A \<Longrightarrow> inflation_op (replicate n a) *\<^sub>S M \<le> M\<close> for a
    assume M_carrier: \<open>M \<le> inflation_carrier n\<close>
    define commutant' where \<open>commutant' X = commutant X \<inter> inflation_op_carrier n\<close> for X :: \<open>(('a \<times> nat) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> nat) ell2) set\<close>
    define An where \<open>An = (\<lambda>a. inflation_op (replicate n a)) ` A\<close>
    have *: \<open>Proj M o\<^sub>C\<^sub>L (inflation_op (replicate n a) o\<^sub>C\<^sub>L Proj M) = inflation_op (replicate n a) o\<^sub>C\<^sub>L Proj M\<close> if \<open>a \<in> A\<close> for a
      apply (rule Proj_compose_cancelI)
      using asm that by (simp add: cblinfun_compose_image)
    have \<open>Proj M o\<^sub>C\<^sub>L inflation_op (replicate n a) = inflation_op (replicate n a) o\<^sub>C\<^sub>L Proj M\<close> if \<open>a \<in> A\<close> for a
    proof -
      have \<open>Proj M o\<^sub>C\<^sub>L inflation_op (replicate n a) = (inflation_op (replicate n (a*)) o\<^sub>C\<^sub>L Proj M)*\<close>
        by (simp add: inflation_op_adj adj_Proj)
      also have \<open>\<dots> = (Proj M o\<^sub>C\<^sub>L inflation_op (replicate n (a*)) o\<^sub>C\<^sub>L Proj M)*\<close>
        apply (subst *[symmetric])
        by (simp_all add: that assms flip: cblinfun_compose_assoc)
      also have \<open>\<dots> = Proj M o\<^sub>C\<^sub>L inflation_op (replicate n a) o\<^sub>C\<^sub>L Proj M\<close>
        by (simp add: inflation_op_adj adj_Proj cblinfun_compose_assoc)
      also have \<open>\<dots> = inflation_op (replicate n a) o\<^sub>C\<^sub>L Proj M\<close>
        apply (subst *[symmetric])
        by (simp_all add: that flip: cblinfun_compose_assoc)
      finally show ?thesis
        by -
    qed
    then have \<open>Proj M \<in> commutant' An\<close>
      using  M_carrier 
      apply (auto intro!: inflation_op_carrierI simp add: An_def commutant_def commutant'_def)
      by (metis Proj_compose_cancelI Proj_range adj_Proj adj_cblinfun_compose)
    from b_A'' have \<open>inflation_op (replicate n b) \<in> commutant' (commutant' An)\<close>
      using commutant_inflation[of n A, folded commutant'_def]
      by (auto simp add: An_def commutant'_def)
    with \<open>Proj M \<in> commutant' An\<close>
    have *: \<open>inflation_op (replicate n b) o\<^sub>C\<^sub>L Proj M = Proj M o\<^sub>C\<^sub>L inflation_op (replicate n b)\<close>
      by (simp add: commutant_def commutant'_def)
    show \<open>inflation_op (replicate n b) *\<^sub>S M \<le> M\<close>
    proof -
      have \<open>inflation_op (replicate n b) *\<^sub>S M = (inflation_op (replicate n b) o\<^sub>C\<^sub>L Proj M) *\<^sub>S \<top>\<close>
        by (metis Misc.lift_cblinfun_comp(3) Proj_range)
      also have \<open>\<dots> = (Proj M o\<^sub>C\<^sub>L inflation_op (replicate n b)) *\<^sub>S \<top>\<close>
        by (simp add: * )
      also have \<open>\<dots> \<le> M\<close>
        by (metis Misc.lift_cblinfun_comp(3) Proj_image_leq)
      finally show ?thesis
        by -
    qed
  qed
qed


(* MOVE *)

lemma QREGISTER_of_qregister_id: \<open>QREGISTER_of qregister_id = QREGISTER_all\<close>
  apply (rule Rep_QREGISTER_inject[THEN iffD1])
  by (simp add: QREGISTER_of.rep_eq QREGISTER_all.rep_eq)



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


