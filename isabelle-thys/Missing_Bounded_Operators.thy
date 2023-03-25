theory Missing_Bounded_Operators
  imports Complex_Bounded_Operators.Complex_L2 Complex_Bounded_Operators.Cblinfun_Code Complex_Bounded_Operators.BO_Unsorted
    Tensor_Product.Hilbert_Space_Tensor_Product
    With_Type.With_Type Registers.Axioms_Quantum Misc_Missing
begin

unbundle cblinfun_notation
no_notation m_inv ("inv\<index> _" [81] 80)
unbundle jnf_notation
hide_const (open) Finite_Cartesian_Product.vec
hide_const (open) Finite_Cartesian_Product.mat
hide_const (open) Order.top
hide_const (open) Coset.kernel

lemma enum_idx_enum_index[simp]: \<open>enum_idx = enum_index\<close>
proof (rule ext)
  fix x :: 'a
  have \<open>(Enum.enum ! enum_idx x :: 'a) = Enum.enum ! enum_index x\<close>
    unfolding enum_idx_correct
    by simp
  then show \<open>enum_idx x = enum_index x\<close>
    using enum_distinct apply (rule nth_eq_iff_index_eq[THEN iffD1, rotated -1])
    by (simp_all flip: card_UNIV_length_enum)
qed

lemma mat_of_cblinfun_explicit_cblinfun[code,simp]:
  fixes m :: \<open>'a::eenum \<Rightarrow> 'b::eenum \<Rightarrow> complex\<close>
  defines \<open>m' \<equiv> (\<lambda>(i,j). m (enum_nth i) (enum_nth j))\<close>
  shows \<open>mat_of_cblinfun (explicit_cblinfun m) = mat CARD('a) CARD('b) m'\<close> 
proof (rule eq_matI)
  fix i j
  assume \<open>i < dim_row (mat CARD('a) CARD('b) m')\<close> \<open>j < dim_col (mat CARD('a) CARD('b) m')\<close>
  then have ij[simp]: \<open>i < CARD('a)\<close> \<open>j < CARD('b)\<close>
    by auto
  have \<open>m (enum_class.enum ! i) (enum_class.enum ! j) = m' (i, j)\<close>
    by (auto simp: m'_def)
  then show \<open>mat_of_cblinfun (explicit_cblinfun m) $$ (i, j) = Matrix.mat CARD('a) CARD('b) m' $$ (i, j)\<close>
    by (simp add: mat_of_cblinfun_ell2_component)
next
  show \<open>dim_row (mat_of_cblinfun (explicit_cblinfun m)) = dim_row (Matrix.mat CARD('a) CARD('b) m')\<close> by simp
  show \<open>dim_col (mat_of_cblinfun (explicit_cblinfun m)) = dim_col (Matrix.mat CARD('a) CARD('b) m')\<close> by simp
qed

definition permute_and_tensor1_cblinfun where [code del]: \<open>permute_and_tensor1_cblinfun f R a =
  explicit_cblinfun (\<lambda>i j. of_bool (R i j) * Rep_ell2 (a *\<^sub>V ket (f j)) (f i))\<close>

definition permute_and_tensor1_cblinfun_exists where \<open>permute_and_tensor1_cblinfun_exists f R a \<longleftrightarrow>
  explicit_cblinfun_exists (\<lambda>i j. of_bool (R i j) * Rep_ell2 (a *\<^sub>V ket (f j)) (f i))\<close>

definition permute_and_tensor1_mat where \<open>permute_and_tensor1_mat d f R m =
  mat d d (\<lambda>(i,j). if R i j then m $$ (f i, f j) else 0)\<close>

definition permute_and_tensor1_mat' :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> ('a::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a::enum ell2)\<close> where 
 [code del]: \<open>permute_and_tensor1_mat' d f R m = cblinfun_of_mat (permute_and_tensor1_mat d f R m)\<close>

lemma permute_and_tensor1_cblinfun_code_prep[code]:
  fixes f :: \<open>'b::eenum \<Rightarrow> 'a::eenum\<close>
  shows \<open>permute_and_tensor1_cblinfun f R a = 
      permute_and_tensor1_mat' CARD('b) (\<lambda>i. enum_index (f (enum_nth i)))
      (\<lambda>i j. R (enum_nth i) (enum_nth j)) (mat_of_cblinfun a)\<close>
  apply (rule cblinfun_eq_mat_of_cblinfunI)
  apply (simp add: mat_of_cblinfun_explicit_cblinfun permute_and_tensor1_cblinfun_def
      permute_and_tensor1_mat_def permute_and_tensor1_mat'_def cblinfun_of_mat_inverse)
  apply (rule cong_mat, simp, simp)
  by (simp add: mat_of_cblinfun_ell2_component enum_idx_correct)

lemma mat_of_cblinfun_permute_and_tensor1_mat'[code]:
  \<open>mat_of_cblinfun (permute_and_tensor1_mat' d f R m :: 'a::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2) 
    = (if d=CARD('a) then mat d d (\<lambda>(i,j). if R i j then m $$ (f i, f j) else 0) else zero_mat CARD('a) CARD('a))\<close>
  apply (cases \<open>d = CARD('a)\<close>)
   apply (auto simp add: permute_and_tensor1_mat'_def cblinfun_of_mat_inverse permute_and_tensor1_mat_def)
  apply (subst cblinfun_of_mat_invalid)
  by (auto simp: mat_of_cblinfun_zero)

lemma mat_of_cblinfun_permute_and_tensor1_cblinfun[code]:
  fixes f :: \<open>'b::eenum \<Rightarrow> 'a::eenum\<close>
  shows \<open>mat_of_cblinfun (permute_and_tensor1_cblinfun f R a) = 
      permute_and_tensor1_mat CARD('b) (\<lambda>i. enum_index (f (enum_nth i)))
      (\<lambda>i j. R (enum_nth i) (enum_nth j)) (mat_of_cblinfun a)\<close>
  apply (simp add: mat_of_cblinfun_explicit_cblinfun permute_and_tensor1_cblinfun_def
      permute_and_tensor1_mat_def cblinfun_of_mat_inverse)
  apply (rule cong_mat, simp, simp)
  by (simp add: mat_of_cblinfun_ell2_component enum_idx_correct)

lemma permute_and_tensor1_cblinfun_exists_finite[simp]: \<open>permute_and_tensor1_cblinfun_exists f R A\<close>
  for f :: \<open>'a::finite \<Rightarrow> 'b\<close>
  by (simp add: permute_and_tensor1_cblinfun_exists_def)

(* lemma trunc_ell2_singleton[simp]: \<open>trunc_ell2 {x} \<phi> = Rep_ell2 \<phi> x *\<^sub>C ket x\<close>
  apply (transfer fixing: x)
  by auto *)

definition \<open>permute_and_tensor1_cblinfun_basis R = UNIV // {(x,y). R x y}\<close>
definition permute_and_tensor1_cblinfun_U :: \<open>('c \<Rightarrow> 'a set) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close> where
 \<open>permute_and_tensor1_cblinfun_U Rep f R = classical_operator (Some o (\<lambda>(a,c). inv_into (Rep c) f a))\<close>

lemma permute_and_tensor1_cblinfun_U_bij:
  fixes Rep :: \<open>'c \<Rightarrow> 'a set\<close> and f :: \<open>'a \<Rightarrow> 'b\<close> and R :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assumes Rep: \<open>range Rep = permute_and_tensor1_cblinfun_basis R\<close>
  assumes equiv: \<open>equivp R\<close>
  assumes \<open>inj Rep\<close>
  assumes bij_f: \<open>\<And>a. bij_betw f (Collect (R a)) UNIV\<close>
  shows \<open>bij (\<lambda>(a, c). inv_into (Rep c) f a)\<close>
proof -
  from equiv have equiv': \<open>equiv UNIV {(x, y). R x y}\<close>
    by (simp add: equivp_equiv)
  from equiv have [simp]: \<open>R a a\<close> for a
    by (simp add: equivp_reflp)
  from Rep equiv' have Collect_R: \<open>Collect (R a) \<in> range Rep\<close> for a
    by (auto simp: permute_and_tensor1_cblinfun_basis_def quotient_def)
  have inj': \<open>inj_on f (Collect (R a))\<close> for a
    using bij_f by (rule bij_betw_imp_inj_on)
  have b_f_Rep: \<open>b \<in> f ` Rep c\<close> for b c
  proof -
    from Rep
    have \<open>Rep c \<in> UNIV // {(x, y). R x y}\<close>
      by (auto simp add: permute_and_tensor1_cblinfun_basis_def)
    then obtain a where \<open>Rep c = Collect (R a)\<close>
      apply atomize_elim
      by (simp add: quotient_def)
    moreover from bij_f have \<open>b \<in> f ` Collect (R a)\<close>
      by (simp add: bij_betw_def)
    ultimately
    show ?thesis
      by simp
  qed

  have \<open>b = b'\<close> and \<open>c = c'\<close>
    if \<open>inv_into (Rep c) f b = inv_into (Rep c') f b'\<close> for b c b' c'
  proof -
    from Rep have \<open>Rep c \<in> UNIV // {(x, y). R x y}\<close>
      by (auto simp: permute_and_tensor1_cblinfun_basis_def)
    have \<open>inv_into (Rep c) f b \<in> Rep c\<close> for b c
      apply (rule inv_into_into)
      by (simp add: b_f_Rep)
    with that have \<open>Rep c \<inter> Rep c' \<noteq> {}\<close>
      by (metis disjoint_iff)
    with Rep have \<open>Rep c = Rep c'\<close>
      apply (simp add: permute_and_tensor1_cblinfun_basis_def)
      by (metis equiv' quotient_disj rangeI)
    then show \<open>c = c'\<close>
      using \<open>inj Rep\<close>
      by (simp add: inj_eq)
    with that have \<open>inv_into (Rep c) f b = inv_into (Rep c) f b'\<close>
      by simp
    then show \<open>b = b'\<close>
      apply (rule inv_into_injective)
      by (simp_all add: b_f_Rep)
  qed
  then have inj: \<open>inj (\<lambda>(a, c). inv_into (Rep c) f a)\<close>
    by (auto intro!: injI)

  have surj: \<open>surj (\<lambda>(a, c). inv_into (Rep c) f a)\<close>
    apply (rule surjI[where f=\<open>\<lambda>b. (f b, inv Rep (Collect (R b)))\<close>])
    by (simp_all add: f_inv_into_f[where f=Rep] Collect_R inv_into_f_f inj')
  from inj surj show ?thesis
    using bij_betw_def by blast
qed


lemma permute_and_tensor1_cblinfun_U_exists:
  fixes Rep :: \<open>'c \<Rightarrow> 'a set\<close> and f :: \<open>'a \<Rightarrow> 'b\<close> and R :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assumes \<open>range Rep = permute_and_tensor1_cblinfun_basis R\<close>
  assumes \<open>equivp R\<close>
  assumes \<open>inj Rep\<close>
  assumes \<open>\<And>a. bij_betw f (Collect (R a)) UNIV\<close>
  shows \<open>classical_operator_exists (Some o (\<lambda>(a,c). inv_into (Rep c) f a))\<close>
  apply (rule classical_operator_exists_inj)
  apply (subst inj_map_total)
  apply (rule bij_is_inj)
  using assms by (rule permute_and_tensor1_cblinfun_U_bij)

lemma permute_and_tensor1_cblinfun_U_apply:
  fixes Rep :: \<open>'c \<Rightarrow> 'a set\<close> and f :: \<open>'a \<Rightarrow> 'b\<close> and R :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assumes \<open>range Rep = permute_and_tensor1_cblinfun_basis R\<close>
  assumes \<open>equivp R\<close>
  assumes \<open>inj Rep\<close>
  assumes \<open>\<And>a. bij_betw f (Collect (R a)) UNIV\<close>
  shows \<open>permute_and_tensor1_cblinfun_U Rep f R *\<^sub>V ket (b,c) = ket (inv_into (Rep c) f b)\<close>
  using assms
  by (auto simp: permute_and_tensor1_cblinfun_U_def classical_operator_ket permute_and_tensor1_cblinfun_U_exists)

lemma permute_and_tensor1_cblinfun_U_unitary: 
  fixes Rep :: \<open>'c \<Rightarrow> 'a set\<close> and f :: \<open>'a \<Rightarrow> 'b\<close> and R :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assumes \<open>range Rep = permute_and_tensor1_cblinfun_basis R\<close>
  assumes \<open>equivp R\<close>
  assumes \<open>inj Rep\<close>
  assumes \<open>\<And>a. bij_betw f (Collect (R a)) UNIV\<close>
  shows \<open>unitary (permute_and_tensor1_cblinfun_U Rep f R)\<close>
  using assms by (auto intro!: unitary_classical_operator permute_and_tensor1_cblinfun_U_bij 
      simp: permute_and_tensor1_cblinfun_U_def)

lemma permute_and_tensor1_cblinfun_U_adj_apply:
  fixes Rep :: \<open>'c \<Rightarrow> 'a set\<close> and f :: \<open>'a \<Rightarrow> 'b\<close> and R :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> and a :: 'a
  assumes Rep: \<open>range Rep = permute_and_tensor1_cblinfun_basis R\<close>
  assumes equiv: \<open>equivp R\<close>
  assumes \<open>inj Rep\<close>
  assumes bij_f: \<open>\<And>a. bij_betw f (Collect (R a)) UNIV\<close>
  shows \<open>(permute_and_tensor1_cblinfun_U Rep f R)* *\<^sub>V ket a = ket (f a, inv Rep (Collect (case_prod R) `` {a}))\<close>
proof -
   have \<open>Collect (R a) \<in> UNIV // {(x, y). R x y}\<close> for a
    by (auto intro!: exI[of _ a] simp: quotient_def equiv equivp_reflp)
  then have 1: \<open>Collect (R a) \<in> range Rep\<close> for a
    by (simp_all add: Rep permute_and_tensor1_cblinfun_basis_def)
  have 2: \<open>inj_on f (Collect (R a))\<close>
    using bij_f bij_betw_def by auto
  have 3: \<open>R a a\<close>
    by (simp add: equiv equivp_reflp)
  have *: \<open>permute_and_tensor1_cblinfun_U Rep f R *\<^sub>V ket (f a, inv Rep (Collect (case_prod R) `` {a})) = ket a\<close>
    apply (subst permute_and_tensor1_cblinfun_U_apply)
    using assms apply auto[4]
    by (simp add: f_inv_into_f[where f=Rep] 1 inv_into_f_f[where f=f] 2 3)
  have uni: \<open>unitary (permute_and_tensor1_cblinfun_U Rep f R)\<close>
    using assms by (rule permute_and_tensor1_cblinfun_U_unitary)
  have \<open>(permute_and_tensor1_cblinfun_U Rep f R)* *\<^sub>V ket a = 
        (permute_and_tensor1_cblinfun_U Rep f R)* *\<^sub>V 
          permute_and_tensor1_cblinfun_U Rep f R *\<^sub>V ket (f a, inv Rep (Collect (case_prod R) `` {a}))\<close>
    by (simp flip: * )
  also from uni have \<open>\<dots> = ket (f a, inv Rep (Collect (case_prod R) `` {a}))\<close>
    by (simp flip: cblinfun_apply_cblinfun_compose)
  finally show ?thesis
    by -
qed


lemma permute_and_tensor1_cblinfun_exists[simp]:
  \<open>permute_and_tensor1_cblinfun_exists f R A\<close>
  if \<open>part_equivp R\<close> and inj_f: \<open>\<forall>x. inj_on f (Collect (R x))\<close>
proof -
  define RR where \<open>RR = {(x,y). R x y}\<close>
  define Rdom where \<open>Rdom = {x. R x x}\<close>
  have \<open>equiv Rdom RR\<close>
    using \<open>part_equivp R\<close>
    apply (auto intro!: equivI simp add: RR_def Rdom_def)
      apply (smt (verit) case_prodI case_prodI2 internal_case_prod_conv internal_case_prod_def mem_Collect_eq part_equivp_def refl_on_def')
    apply (metis (mono_tags, lifting) case_prodD case_prodI mem_Collect_eq part_equivp_symp symI)
    using part_equivpE transp_trans by auto

  define B where \<open>B = (norm A)\<^sup>2\<close>
  have [simp]: \<open>B \<ge> 0\<close>
    by (simp add: B_def)
  define A' where \<open>A' x y = Rep_ell2 (A *\<^sub>V ket x) y\<close> for x y
  define K where \<open>K a b = (of_bool (R b a) * A' (f a) (f b))\<close> for a b
  have \<open>(\<Sum>b\<in>S. (cmod (\<Sum>a\<in>T. \<psi> a *\<^sub>C K a b))\<^sup>2)
       \<le> B * (\<Sum>a\<in>T. (cmod (\<psi> a))\<^sup>2)\<close> (is \<open>?lhs \<le> ?rhs\<close>)
    if [simp]: \<open>finite S\<close> \<open>finite T\<close> and \<psi>T: \<open>\<And>a. a\<notin>T \<Longrightarrow> \<psi> a = 0\<close> for S T \<psi>
  proof -
    define \<psi>' where \<open>\<psi>' = Abs_ell2 \<psi>\<close>
    have \<open>has_ell2_norm \<psi>\<close>
      unfolding has_ell2_norm_def
      apply (subst summable_on_cong_neutral[where g=\<open>\<lambda>x. cmod ((\<psi> x)\<^sup>2)\<close> and T=T])
      using \<psi>T by auto
    then have Rep_\<psi>': \<open>Rep_ell2 \<psi>' = \<psi>\<close>
      by (auto intro!: Abs_ell2_inverse simp: \<psi>'_def)
    define \<phi> where \<open>\<phi> C = Abs_ell2 (\<lambda>a. of_bool (a \<in> f`(T\<inter>C)) * \<psi> (inv_into (T\<inter>C) f a))\<close> for C
    have Rep_\<phi>: \<open>Rep_ell2 (\<phi> C) a = of_bool (a \<in> f`(T\<inter>C)) * \<psi> (inv_into (T\<inter>C) f a)\<close> for C a
      unfolding \<phi>_def apply (subst Abs_ell2_inverse)
       apply (auto simp: has_ell2_norm_def)
      apply (subst summable_on_cong_neutral[OF _ _ refl, where T=\<open>f ` (T \<inter> C)\<close>])
      by auto
    define S' where \<open>S' = Set.filter (\<lambda>C. C \<inter> S \<noteq> {}) (Rdom // RR)\<close>
    have \<open>disjoint S'\<close>
      apply (auto simp add: S'_def disjoint_def)
      using \<open>equiv Rdom RR\<close> quotient_disj by fastforce+
    have [simp]: \<open>finite S'\<close>
    proof -
      obtain g where g: \<open>g C \<in> C \<inter> S\<close> if \<open>C \<inter> S \<noteq> {}\<close> for C
        by (metis IntI disjoint_iff)
      have \<open>inj_on g S'\<close>
        apply (rule inj_onI)
        apply (auto simp: S'_def)
        by (metis Int_iff \<open>equiv Rdom RR\<close> empty_iff g quotient_disj)+
      moreover have \<open>g ` S' \<subseteq> S\<close>
        using g by (auto simp: S'_def)
      moreover note \<open>finite S\<close>
      ultimately show \<open>finite S'\<close>
        by (simp add: Finite_Set.inj_on_finite)
    qed
    have aux1: \<open>\<And>C x y. C \<in> S' \<Longrightarrow> x \<in> C \<Longrightarrow> K y x \<noteq> 0 \<Longrightarrow> y \<in> C\<close>
      apply (auto simp: S'_def K_def)
      by (metis RR_def \<open>equiv Rdom RR\<close> case_prodI in_quotient_imp_closed mem_Collect_eq)
    have aux2: \<open>R x y\<close> if \<open>C \<in> S'\<close> \<open>x \<in> C\<close> \<open>y \<in> C\<close> for C x y
      using that apply (auto simp: S'_def RR_def quotient_def)
      by (metis \<open>part_equivp R\<close> part_equivp_symp part_equivp_transp)
    have inj_f''[simp]: \<open>inj_on f C\<close> if \<open>C \<in> S'\<close> for C
      apply (rule inj_onI)
      using that inj_f apply (auto simp: S'_def)
      by (metis aux2 inj_onD mem_Collect_eq that)
    then have inj_f'[simp]: \<open>inj_on f (X \<inter> C)\<close> if \<open>C \<in> S'\<close> for C X
      using that 
      by (simp add: inj_on_Int)
    then have inj_f''[simp]: \<open>inj_on f (C \<inter> X)\<close> if \<open>C \<in> S'\<close> for C X
      using that
      by (simp add: inj_on_Int)

    have \<open>?lhs = (\<Sum>b\<in>S\<inter>Rdom. (cmod (\<Sum>a\<in>T. \<psi> a *\<^sub>C K a b))\<^sup>2)\<close>
    proof (rule sum.mono_neutral_cong_right)
      show \<open>finite S\<close> by simp
      show \<open>S \<inter> Rdom \<subseteq> S\<close> by simp
      have \<open>(\<psi> a *\<^sub>C K a i) = 0\<close> if \<open>i \<in> S - S \<inter> Rdom\<close> for i a
        using that apply (auto simp: K_def)
        by (metis Rdom_def \<open>part_equivp R\<close> mem_Collect_eq part_equivp_def)
      then show \<open>\<forall>i\<in>S - S \<inter> Rdom. (cmod (\<Sum>a\<in>T. \<psi> a *\<^sub>C K a i))\<^sup>2 = 0\<close>
        by auto
      show \<open>(cmod (\<Sum>a\<in>T. \<psi> a *\<^sub>C K a x))\<^sup>2 = (cmod (\<Sum>a\<in>T. \<psi> a *\<^sub>C K a x))\<^sup>2\<close> for x
        by simp 
    qed
    also have \<open>\<dots> = (\<Sum>C\<in>S'. \<Sum>b\<in>C\<inter>S. (cmod (\<Sum>a\<in>T. \<psi> a *\<^sub>C K a b))\<^sup>2)\<close>
    proof -
      have \<open>x \<in> snd ` (SIGMA C:S'. C \<inter> S)\<close> if \<open>x \<in> S\<close> and \<open>x \<in> Rdom\<close> for x
      proof -
        have \<open>(RR``{x}, x) \<in> (SIGMA C:S'. C \<inter> S)\<close>
          using that
          apply (auto intro!: quotientI simp add: S'_def)
          using \<open>equiv Rdom RR\<close> equiv_class_self apply fastforce
          using RR_def Rdom_def by blast
        then show ?thesis
          apply (rule image_eqI[rotated])
          by simp
      qed        
      moreover have \<open>b \<in> Rdom\<close> if \<open>b \<in> C\<close> and \<open>C \<in> S'\<close> for b C
        using that apply (auto simp: S'_def)
        using Rdom_def aux2 that(2) by blast
      ultimately have 1: \<open>S \<inter> Rdom = snd ` (SIGMA C:S'. C \<inter> S)\<close>
        by auto 
      have 2: \<open>inj_on snd (SIGMA C:S'. C \<inter> S)\<close>
        apply (rule inj_onI)
        apply auto
         apply (metis Int_iff S'_def Set.member_filter \<open>equiv Rdom RR\<close> empty_iff quotient_disj)
        by (metis Int_iff S'_def Set.member_filter \<open>equiv Rdom RR\<close> empty_iff quotient_disj)
      show ?thesis
        by (auto simp: sum.Sigma sum.reindex 1 2 case_prod_beta)
    qed
    also have \<open>\<dots> = (\<Sum>C\<in>S'. \<Sum>b\<in>C\<inter>S. (cmod (\<Sum>a\<in>T\<inter>C. \<psi> a *\<^sub>C K a b))\<^sup>2)\<close>
      apply (rule sum.cong, simp)
      apply (rule sum.cong, simp)
      apply (rule arg_cong[where f=\<open>\<lambda>x. (cmod x)\<^sup>2\<close>])
      apply (rule sum.mono_neutral_cong_right)
      using aux1 by auto
    also have \<open>\<dots> = (\<Sum>C\<in>S'. \<Sum>b\<in>C\<inter>S. (cmod (\<Sum>a\<in>T\<inter>C. \<psi> a *\<^sub>C A' (f a) (f b)))\<^sup>2)\<close>
      apply (rule sum.cong, simp)
      apply (rule sum.cong, simp)
      apply (rule arg_cong[where f=\<open>\<lambda>x. (cmod x)\<^sup>2\<close>])
      apply (rule sum.cong, simp)
      by (simp add: K_def aux2)
    also have \<open>\<dots> = (\<Sum>C\<in>S'. \<Sum>b\<in>C\<inter>S. (cmod (\<Sum>a\<in>f`(T\<inter>C). Rep_ell2 (\<phi> C) a *\<^sub>C A' a (f b)))\<^sup>2)\<close>
      apply (rule sum.cong, simp)
      apply (rule sum.cong, simp)
      apply (rule arg_cong[where f=\<open>\<lambda>x. (cmod x)\<^sup>2\<close>])
      by (simp add: sum.reindex Rep_\<phi>)
    also have \<open>\<dots> = (\<Sum>C\<in>S'. \<Sum>b\<in>f`(C\<inter>S). (cmod (\<Sum>a\<in>f`(T\<inter>C). Rep_ell2 (\<phi> C) a *\<^sub>C A' a b))\<^sup>2)\<close>
      apply (rule sum.cong, simp)
      apply (subst (3) sum.reindex)
      by (simp_all add: o_def)
    also have \<open>\<dots> = (\<Sum>C\<in>S'. \<Sum>b\<in>f`(C\<inter>S). (cmod (\<Sum>\<^sub>\<infinity>a. Rep_ell2 (\<phi> C) a *\<^sub>C A' a b))\<^sup>2)\<close>
      apply (rule sum.cong, simp)
      apply (rule sum.cong, simp)
      apply (rule arg_cong[where f=\<open>\<lambda>x. (cmod x)\<^sup>2\<close>])
      apply (subst infsum_finite[symmetric], simp)
      apply (rule infsum_cong_neutral)
      by (simp_all add: Rep_\<phi>)
    also have \<open>\<dots> = (\<Sum>C\<in>S'. \<Sum>b\<in>f`(C\<inter>S). (cmod (Rep_ell2 (A *\<^sub>V \<phi> C) b))\<^sup>2)\<close>
      apply (rule sum.cong, simp)
      apply (rule sum.cong, simp)
      apply (rule arg_cong[where f=\<open>\<lambda>x. (cmod x)\<^sup>2\<close>])
      by (simp add: A'_def flip: Rep_ell2_cblinfun_apply_sum)
    also have \<open>\<dots> = (\<Sum>C\<in>S'. \<Sum>\<^sub>\<infinity>b. (cmod (Rep_ell2 (trunc_ell2 (f`(C\<inter>S)) (A *\<^sub>V \<phi> C)) b))\<^sup>2)\<close>
      apply (rule sum.cong, simp)
      apply (subst infsum_finite[symmetric], simp)
      apply (rule infsum_cong_neutral)
      by (simp_all add: trunc_ell2.rep_eq)
    also have \<open>\<dots> = (\<Sum>C\<in>S'. (norm (trunc_ell2 (f`(C\<inter>S)) (A *\<^sub>V \<phi> C)))\<^sup>2)\<close>
      by (simp add: norm_ell2.rep_eq ell2_norm_square)
    also have \<open>\<dots> \<le> (\<Sum>C\<in>S'. (norm (A *\<^sub>V \<phi> C))\<^sup>2)\<close>
      apply (rule sum_mono)
      apply (rule power_mono[rotated], simp)
      by (rule trunc_ell2_reduces_norm)
    also have \<open>\<dots> \<le> (\<Sum>C\<in>S'. (norm A * norm (\<phi> C))\<^sup>2)\<close>
      apply (rule sum_mono)
      apply (rule power_mono[rotated], simp)
      by (simp add: norm_cblinfun)
    also have \<open>\<dots> = B * (\<Sum>C\<in>S'. (norm (\<phi> C))\<^sup>2)\<close>
      by (simp add: B_def mult_hom.hom_sum power_mult_distrib)
    also have \<open>\<dots> = B * (\<Sum>C\<in>S'. (\<Sum>\<^sub>\<infinity>i\<in>f`(T\<inter>C). (cmod (Rep_ell2 (\<phi> C) i))\<^sup>2))\<close>
      apply (rule class_cring.factors_equal, simp)
      apply (rule sum.cong, simp)
      unfolding norm_ell2.rep_eq ell2_norm_square
      apply (rule infsum_cong_neutral)
      by (simp_all add: Rep_\<phi>)
    also have \<open>\<dots> = B * (\<Sum>C\<in>S'. (\<Sum>\<^sub>\<infinity>i\<in>f`(T\<inter>C). (cmod (\<psi> (inv_into (T\<inter>C) f i)))\<^sup>2))\<close>
      apply (rule class_cring.factors_equal, simp)
      apply (rule sum.cong, simp)
      apply (rule infsum_cong)
      by (simp add: Rep_\<phi>)
    also have \<open>\<dots> = B * (\<Sum>C\<in>S'. (\<Sum>\<^sub>\<infinity>i\<in>T\<inter>C. (cmod (\<psi> i))\<^sup>2))\<close>
      apply (rule class_cring.factors_equal, simp)
      apply (rule sum.cong, simp)
      apply (subst infsum_reindex)
       apply simp_all
      by -
    also have \<open>\<dots> = B * (\<Sum>C\<in>S'. (norm (trunc_ell2 (T\<inter>C) \<psi>'))\<^sup>2)\<close>
      apply (rule class_cring.factors_equal, simp)
      apply (rule sum.cong, simp)
      apply (subst norm_trunc_ell2_finite, simp)
      by (simp add: Rep_\<psi>' real_sqrt_pow2 sum_nonneg)
    also have \<open>\<dots> = B * (norm (\<Sum>C\<in>S'. (trunc_ell2 (T\<inter>C) \<psi>')))\<^sup>2\<close>
      apply (rule class_cring.factors_equal, simp)
      apply (rule pythagorean_theorem_sum[symmetric])
       apply (rule is_orthogonal_trunc_ell2)
      using \<open>disjoint S'\<close> disjointD by auto
    also have \<open>\<dots> = B * (norm (trunc_ell2 (\<Union>C\<in>S'. T\<inter>C) \<psi>'))\<^sup>2\<close>
      apply (rule arg_cong[where f=\<open>\<lambda>x. B * (norm x)\<^sup>2\<close>])
      using \<open>finite S'\<close> \<open>disjoint S'\<close> 
    proof (induction S')
      case empty
      show ?case
        by simp
    next
      case (insert C S')
      from insert.prems have \<open>disjoint S'\<close>
        by (simp add: pairwise_insert)
      note IH = insert.IH[OF \<open>disjoint S'\<close>]
      have *: \<open>disjnt C C'\<close> if \<open>C' \<in> S'\<close> for C'
        by (metis insert.hyps(2) insert.prems pairwise_insert that)
      show ?case
        apply (simp add: insert.hyps IH )
        apply (subst trunc_ell2_union_disjoint)
        using * by (auto simp: disjnt_def)
    qed
    also have \<open>\<dots> \<le> B * (norm (trunc_ell2 T \<psi>'))\<^sup>2\<close>
      apply (rule mult_left_mono[rotated], simp)
      apply (rule power_mono[rotated], simp)
      apply (rule trunc_ell2_norm_mono)
      by auto
    also have \<open>\<dots> = B * (\<Sum>i\<in>T. (cmod (\<psi> i))\<^sup>2)\<close>
      by (simp add: norm_trunc_ell2_finite Rep_\<psi>' real_sqrt_pow2 sum_nonneg)
    finally show \<open>?lhs \<le> ?rhs\<close>
      by -
  qed
  then show ?thesis
    unfolding permute_and_tensor1_cblinfun_exists_def K_def A'_def
    by (rule explicit_cblinfun_exists_bounded)
qed

lemma permute_and_tensor1_cblinfun_ket[simp]: \<open>Rep_ell2 (permute_and_tensor1_cblinfun f R A *\<^sub>V ket a) b =
  of_bool (R b a) * Rep_ell2 (A *\<^sub>V ket (f a)) (f b)\<close> 
  if \<open>permute_and_tensor1_cblinfun_exists f R A\<close>
  using that
  by (simp add: permute_and_tensor1_cblinfun_def permute_and_tensor1_cblinfun_exists_def)

lemma permute_and_tensor1_cblinfun_as_register:
  fixes R :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assumes equiv_R: \<open>equivp R\<close>
  assumes bij_f: \<open>\<And>a. bij_betw f (Collect (R a)) UNIV\<close>
  shows \<open>\<forall>\<^sub>\<tau> 'c::type = permute_and_tensor1_cblinfun_basis R. 
            (\<forall>A. sandwich (permute_and_tensor1_cblinfun_U rep_c f R) (A \<otimes>\<^sub>o id_cblinfun) =
            permute_and_tensor1_cblinfun f R A)
            \<and> unitary (permute_and_tensor1_cblinfun_U rep_c f R)\<close>
proof (rule with_typeI)
  define S where \<open>S = permute_and_tensor1_cblinfun_basis R\<close>
  show \<open>fst (S, ()) \<noteq> {}\<close>
    by (simp add: permute_and_tensor1_cblinfun_basis_def S_def equiv_R equivp_reflp)
  show \<open>fst with_type_type_class (fst (S, ())) (snd (S, ()))\<close>
    by (auto simp: with_type_type_class_def)
  show \<open>with_type_compat_rel (fst with_type_type_class) (fst (S, ())) (snd with_type_type_class)\<close>
    by (auto simp: with_type_type_class_def with_type_compat_rel_def)
  fix Rep :: \<open>'c \<Rightarrow> 'a set\<close> and Abs abs_ops

  assume \<open>type_definition Rep Abs (fst (S, ()))\<close>
  then interpret type_definition Rep Abs S
    by simp

  assume \<open>snd with_type_type_class (\<lambda>x y. x = Rep y) (snd (S, ())) abs_ops\<close>
  define U where \<open>U = permute_and_tensor1_cblinfun_U Rep f R\<close>

  have \<open>Collect (R a) \<in> UNIV // {(x, y). R x y}\<close> for a
    by (auto intro!: exI[of _ a] simp: quotient_def equiv_R equivp_reflp)
  then have Collect_R: \<open>Collect (R a) \<in> range Rep\<close> for a
    by (simp_all add: Rep_range S_def permute_and_tensor1_cblinfun_basis_def)

  have inv_Rep_Collect_eq: \<open>(inv Rep (Collect (R b)) = inv Rep (Collect (R a))) \<longleftrightarrow> R b a\<close> for a b
  proof (rule iffI)
    assume \<open>inv Rep (Collect (R b)) = inv Rep (Collect (R a))\<close>
    then have \<open>Collect (R b) = Collect (R a)\<close>
      by (simp add: inv_into_injective Collect_R)
    then have \<open>R b = R a\<close>
      by (rule Collect_inj)
    then show \<open>R b a\<close>
      using equiv_R
      by (simp add: equivp_reflp)
  next
    assume \<open>R b a\<close>
    then have \<open>Collect (R b) = Collect (R a)\<close>
      by (metis equiv_R equivp_def)
    then show \<open>inv Rep (Collect (R b)) = inv Rep (Collect (R a))\<close>
      by simp
  qed

  have \<open>inj Rep\<close>
    by (meson Rep_inject injI)

  have \<open>Rep_ell2 ((sandwich U *\<^sub>V A \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket a) b =
           of_bool (R b a) * Rep_ell2 (A *\<^sub>V ket (f a)) (f b)\<close> for a b A
  proof -
    have \<open>Rep_ell2 ((sandwich U *\<^sub>V A \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket a) b =
            (U* *\<^sub>V ket b) \<bullet>\<^sub>C ((A \<otimes>\<^sub>o id_cblinfun) *\<^sub>V U* *\<^sub>V ket a)\<close>
      by (simp add: sandwich_apply cinner_adj_left flip: cinner_ket_left)
    also have \<open>\<dots> = ket (f b) \<bullet>\<^sub>C (A *\<^sub>V ket (f a)) *
                        (ket (inv Rep (Collect (R b))) \<bullet>\<^sub>C ket (inv Rep (Collect (R a))))\<close>
      unfolding U_def
      apply (subst permute_and_tensor1_cblinfun_U_adj_apply)
          apply (simp_all add: Rep_range S_def assms \<open>inj Rep\<close> bij_f)[4]
      apply (subst permute_and_tensor1_cblinfun_U_adj_apply)
          apply (simp_all add: Rep_range S_def assms \<open>inj Rep\<close> bij_f)[4]
      by (simp add: tensor_op_ell2 flip: tensor_ell2_ket)
    also have \<open>\<dots> = ket (f b) \<bullet>\<^sub>C (A *\<^sub>V ket (f a)) * of_bool (R b a)\<close>
      by (simp add: cinner_ket inv_Rep_Collect_eq)
    also have \<open>\<dots> = of_bool (R b a) * Rep_ell2 (A *\<^sub>V ket (f a)) (f b)\<close>
      by (simp add: cinner_ket_left)
    finally show ?thesis
      by -
  qed
  moreover have \<open>permute_and_tensor1_cblinfun_exists f R A\<close> for A
    apply (rule permute_and_tensor1_cblinfun_exists)
    using assms bij_betw_imp_inj_on equivp_implies_part_equivp by auto
  moreover have \<open>unitary (permute_and_tensor1_cblinfun_U Rep f R)\<close>
    apply (rule permute_and_tensor1_cblinfun_U_unitary)
    using assms bij_betw_imp_inj_on equivp_implies_part_equivp Rep S_def Rep_range \<open>inj Rep\<close> by auto
  ultimately show \<open>(\<forall>A. sandwich U *\<^sub>V A \<otimes>\<^sub>o id_cblinfun =
       permute_and_tensor1_cblinfun f R A) \<and> unitary (permute_and_tensor1_cblinfun_U Rep f R)\<close>
    by (auto intro!: equal_ket Rep_ell2_inject[THEN iffD1])
qed

lemma clinear_permute_and_tensor1_cblinfun[simp]: \<open>clinear (permute_and_tensor1_cblinfun f R)\<close>
  if [simp]: \<open>\<And>A. permute_and_tensor1_cblinfun_exists f R A\<close>
proof (rule clinearI)
  show \<open>permute_and_tensor1_cblinfun f R (A + B) = permute_and_tensor1_cblinfun f R A + permute_and_tensor1_cblinfun f R B\<close> for A B
    apply (rule equal_ket)
    by (auto simp: plus_ell2.rep_eq cblinfun.add_left simp flip: Rep_ell2_inject)
  show \<open>permute_and_tensor1_cblinfun f R (s *\<^sub>C A) = s *\<^sub>C permute_and_tensor1_cblinfun f R A\<close> for s A
    apply (rule equal_ket)
    by (auto simp: scaleC_ell2.rep_eq simp flip: Rep_ell2_inject)
qed

lemma [code]: \<open>vec_of_ell2 (Abs_ell2 f) = vec CARD('a) (\<lambda>n. f (enum_nth n))\<close> for f :: \<open>'a::eenum \<Rightarrow> complex\<close>
  by (auto simp: vec_of_ell2_def vec_eq_iff vec_of_basis_enum_ell2_component)
lemma [code]: \<open>Rep_ell2 \<psi> i = vec_of_ell2 \<psi> $ (enum_index i)\<close> for i :: \<open>'a::eenum\<close>
  by (auto simp: vec_of_ell2_def vec_eq_iff vec_of_basis_enum_ell2_component)

lemma permute_and_tensor1_mat_cong[cong]: 
  assumes \<open>d = d'\<close>
  assumes \<open>\<And>i. i < d' \<Longrightarrow> f i = f' i\<close>
  assumes \<open>\<And>i j. i < d' \<Longrightarrow> j < d' \<Longrightarrow> R i j = R' i j\<close>
  assumes \<open>m = m'\<close>
  shows \<open>(permute_and_tensor1_mat' d f R m :: 'a::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2) = permute_and_tensor1_mat' d' f' R' m'\<close>
  unfolding permute_and_tensor1_mat_def permute_and_tensor1_mat'_def 
  apply (rule arg_cong[of _ _ cblinfun_of_mat])
  apply (rule cong_mat)
  using assms by auto


lemma csubspace_commutant[simp]: \<open>csubspace (commutant X)\<close>
  by (auto simp add: complex_vector.subspace_def commutant_def cblinfun_compose_add_right cblinfun_compose_add_left)

lemma closed_commutant[simp]: \<open>closed (commutant X)\<close>
proof (subst closed_sequential_limits, intro allI impI, erule conjE)
  fix s :: \<open>nat \<Rightarrow> _\<close> and l 
  assume s_comm: \<open>\<forall>n. s n \<in> commutant X\<close>
  assume \<open>s \<longlonglongrightarrow> l\<close>
  have \<open>l o\<^sub>C\<^sub>L x - x o\<^sub>C\<^sub>L l = 0\<close> if \<open>x \<in> X\<close> for x
  proof -
    from \<open>s \<longlonglongrightarrow> l\<close>
    have \<open>(\<lambda>n. s n o\<^sub>C\<^sub>L x - x o\<^sub>C\<^sub>L s n) \<longlonglongrightarrow> l o\<^sub>C\<^sub>L x - x o\<^sub>C\<^sub>L l\<close>
      apply (rule isCont_tendsto_compose[rotated])
      by (intro continuous_intros)
    then have \<open>(\<lambda>_. 0) \<longlonglongrightarrow> l o\<^sub>C\<^sub>L x - x o\<^sub>C\<^sub>L l\<close>
      using s_comm that by (auto simp add: commutant_def)
    then show ?thesis
      by (simp add: LIMSEQ_const_iff that)
  qed
  then show \<open>l \<in> commutant X\<close>
    by (simp add: commutant_def)
qed

lemma closed_csubspace_commutant[simp]: \<open>closed_csubspace (commutant X)\<close>
  apply (rule closed_csubspace.intro) by simp_all

lemma commutant_mult: \<open>a o\<^sub>C\<^sub>L b \<in> commutant X\<close> if \<open>a \<in> commutant X\<close> and \<open>b \<in> commutant X\<close>
  using that 
  apply (auto simp: commutant_def cblinfun_compose_assoc)
  by (simp flip: cblinfun_compose_assoc)

lemma double_commutant_grows[simp]: \<open>X \<subseteq> commutant (commutant X)\<close>
  by (auto simp add: commutant_def)

lemma commutant_antimono: \<open>X \<subseteq> Y \<Longrightarrow> commutant X \<supseteq> commutant Y\<close>
  by (auto simp add: commutant_def)




lemma triple_commutant[simp]: \<open>commutant (commutant (commutant X)) = commutant X\<close>
  by (auto simp: commutant_def)

lemma commutant_adj: \<open>adj ` commutant X = commutant (adj ` X)\<close>
  apply (auto intro!: image_eqI double_adj[symmetric] simp: commutant_def simp flip: adj_cblinfun_compose)
  by (metis adj_cblinfun_compose double_adj)

lemma commutant_empty[simp]: \<open>commutant {} = UNIV\<close>
  by (simp add: commutant_def)

lemma commutant_weak_star_closed[simp]: \<open>closedin weak_star_topology (commutant X)\<close>
proof -
  have comm_inter: \<open>commutant X = (\<Inter>x\<in>X. commutant {x})\<close>
    by (auto simp: commutant_def)
  have comm_x: \<open>commutant {x} = (\<lambda>y. x o\<^sub>C\<^sub>L y - y o\<^sub>C\<^sub>L x) -` {0}\<close> for x :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
    by (auto simp add: commutant_def vimage_def)
  have cont: \<open>continuous_map weak_star_topology weak_star_topology (\<lambda>y. x o\<^sub>C\<^sub>L y - y o\<^sub>C\<^sub>L x)\<close> for x :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
    apply (rule continuous_intros)
    by (simp_all add: continuous_map_left_comp_weak_star continuous_map_right_comp_weak_star)
  have \<open>closedin weak_star_topology ((\<lambda>y. x o\<^sub>C\<^sub>L y - y o\<^sub>C\<^sub>L x) -` {0})\<close> for x :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
    using closedin_vimage[where U=\<open>weak_star_topology\<close> and S=\<open>{0}\<close> and T=weak_star_topology]
    using cont by (auto simp add: closedin_singleton)
  then show ?thesis
    apply (cases \<open>X = {}\<close>)
    using closedin_topspace[of weak_star_topology]
    by (auto simp add: comm_inter comm_x)
qed

lemma cspan_in_double_commutant: \<open>cspan X \<subseteq> commutant (commutant X)\<close>
  by (simp add: complex_vector.span_minimal)

lemma weak_star_closure_in_double_commutant: \<open>weak_star_topology closure_of X \<subseteq> commutant (commutant X)\<close>
  by (simp add: closure_of_minimal)

lemma weak_star_closure_cspan_in_double_commutant: \<open>weak_star_topology closure_of cspan X \<subseteq> commutant (commutant X)\<close>
  by (simp add: closure_of_minimal cspan_in_double_commutant)





lemma map_vec_conjugate: \<open>map_vec conjugate v = conjugate v\<close>
  by fastforce

lemma map_map_vec_cols: \<open>map (map_vec f) (cols m) = cols (map_mat f m)\<close>
  by (simp add: cols_def)

lemma vec_of_ell2_carrier_vec[simp]: \<open>vec_of_ell2 v \<in> carrier_vec CARD('a)\<close> for v :: \<open>'a::enum ell2\<close>
  apply (simp only: dim_vec_of_basis_enum' carrier_vec_def vec_of_ell2_def)
  by simp

definition butterfly_code :: \<open>'a ell2 \<Rightarrow> 'b ell2 \<Rightarrow> 'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close> 
  where [code del,code_abbrev]: \<open>butterfly_code = butterfly\<close> 
lemma butterfly_code[code]: \<open>mat_of_cblinfun (butterfly_code s t)
   = mat_of_cols (CARD('a)) [vec_of_ell2 s] * mat_of_rows (CARD('b)) [map_vec cnj (vec_of_ell2 t)]\<close>
  for s :: \<open>'a::enum ell2\<close> and t :: \<open>'b::enum ell2\<close>
  by (simp add: butterfly_code_def butterfly_def vector_to_cblinfun_code mat_of_cblinfun_compose
      mat_of_cblinfun_adj mat_adjoint_def map_map_vec_cols
      flip: vector_to_cblinfun_code_def map_vec_conjugate[abs_def])


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
    have *: \<open>orthogonal_spaces ((\<top> :: 'b ell2 ccsubspace) \<otimes>\<^sub>S ccspan {ket m}) (inflation_space' (Suc m) (replicate n \<top>))\<close>
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

lemma inflation_op'_apply_tensor_outside: \<open>n < m \<Longrightarrow> inflation_op' m as *\<^sub>V (v \<otimes>\<^sub>s ket n) = 0\<close>
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

lemma inflation_op'_apply_tensor_outside': \<open>n \<ge> length as + m \<Longrightarrow> inflation_op' m as *\<^sub>V (v \<otimes>\<^sub>s ket n) = 0\<close>
  apply (induction as arbitrary: m)
  by (auto simp: cblinfun.add_left tensor_op_ell2 cinner_ket)

lemma Proj_inflation_carrier_outside: \<open>Proj (inflation_carrier n) *\<^sub>V (\<psi> \<otimes>\<^sub>s ket i) = 0\<close> if \<open>i \<ge> n\<close>
  by (simp add: Proj_inflation_carrier inflation_op'_apply_tensor_outside' that)

lemma inflation_state'_is_orthogonal_outside: \<open>n < m \<Longrightarrow> is_orthogonal (a \<otimes>\<^sub>s ket n) (inflation_state' m vs)\<close>
  apply (induction vs arbitrary: m)
  by (auto simp: cinner_add_right)

lemma inflation_op_adj: \<open>(inflation_op' n ops)* = inflation_op' n (map adj ops)\<close>
  apply (induction ops arbitrary: n)
  by (simp_all add: adj_plus tensor_op_adjoint)


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
    have \<open>\<forall>\<^sub>F (M,\<epsilon>) in F. norm (f M \<epsilon> *\<^sub>V v - b *\<^sub>V v) < e\<close> if \<open>e > 0\<close> for e v
    proof -
      have 1: \<open>\<forall>\<^sub>F (M,\<epsilon>) in F. (finite M \<and> v \<in> M) \<and> (\<epsilon> > 0 \<and> \<epsilon> < e)\<close>
        apply (unfold F_def case_prod_unfold, rule eventually_prodI)
        using eventually_at_right that
        by (auto simp add: eventually_finite_subsets_at_top)
      have 2: \<open>norm (f M \<epsilon> *\<^sub>V v - b *\<^sub>V v) < e\<close> if \<open>(finite M \<and> v \<in> M) \<and> (\<epsilon> > 0 \<and> \<epsilon> < e)\<close> for M \<epsilon>
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
    have \<open>a \<otimes>\<^sub>o selfbutterket n o\<^sub>C\<^sub>L tensor_ell2_right (ket n) = tensor_ell2_right (ket n) o\<^sub>C\<^sub>L a\<close>
      apply (rule cblinfun_eqI)
      by (simp add: tensor_op_ell2 cinner_ket)
    with True show ?thesis
      by (simp add: cblinfun_compose_add_left inflation_op'_compose_tensor_outside)
  next
    case False
    with Cons.prems have 1: \<open>Suc n \<le> i\<close>
      by presburger
    have 2: \<open>a \<otimes>\<^sub>o selfbutterket n o\<^sub>C\<^sub>L tensor_ell2_right (ket i) = 0\<close>
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
  \<open>norm (inflation_state' n f) = sqrt (\<Sum>v\<leftarrow>f. (norm v)\<^sup>2)\<close>
proof -
  have \<open>(norm (inflation_state' n f))\<^sup>2 = (\<Sum>v\<leftarrow>f. (norm v)\<^sup>2)\<close>
  proof (induction f arbitrary: n)
    case Nil
    then show ?case by simp
  next
    case (Cons v f)
    have \<open>(norm (inflation_state' n (v # f)))\<^sup>2 = (norm (v \<otimes>\<^sub>s ket n + inflation_state' (Suc n) f))\<^sup>2\<close>
      by simp
    also have \<open>\<dots> = (norm (v \<otimes>\<^sub>s ket n))\<^sup>2 + (norm (inflation_state' (Suc n) f))\<^sup>2\<close>
      apply (rule pythagorean_theorem)
      apply (rule inflation_state'_is_orthogonal_outside)
      by simp
    also have \<open>\<dots> = (norm (v \<otimes>\<^sub>s ket n))\<^sup>2 + (\<Sum>v\<leftarrow>f. (norm v)\<^sup>2)\<close>
      by (simp add: Cons.IH)
    also have \<open>\<dots> = (norm v)\<^sup>2 + (\<Sum>v\<leftarrow>f. (norm v)\<^sup>2)\<close>
      by (simp add: norm_tensor_ell2)
    also have \<open>\<dots> = (\<Sum>v\<leftarrow>v#f. (norm v)\<^sup>2)\<close>
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
  have \<open>(\<Sum>v\<leftarrow>f. (norm ((a - b) *\<^sub>V v))\<^sup>2) \<le> \<epsilon>\<^sup>2\<close>
  proof -
    have \<open>(\<Sum>v\<leftarrow>f. (norm ((a - b) *\<^sub>V v))\<^sup>2) = (norm (inflation_state (map (cblinfun_apply (a - b)) f)))\<^sup>2\<close>
      apply (simp add: norm_inflation_state o_def)
      apply (subst real_sqrt_pow2)
       apply (rule sum_list_nonneg)
      by (auto simp: sum_list_nonneg)
    also have \<open>\<dots> = (norm (m - inflation_state (map (cblinfun_apply b) f)))\<^sup>2\<close>
      by (simp add: m_def inflation_state_minus map2_map_map cblinfun.diff_left[abs_def])
    also have \<open>\<dots> \<le> \<epsilon>\<^sup>2\<close>
      by (simp add: m_close power_mono)
    finally show ?thesis
      by -
  qed
  then have \<open>(norm ((a - b) *\<^sub>V v))\<^sup>2 \<le> \<epsilon>\<^sup>2\<close> if \<open>v \<in> F\<close> for v
    using that apply (simp flip: sum.distinct_set_conv_list add: \<open>distinct f\<close>)
    by (smt (verit) \<open>finite F\<close> \<open>set f = F\<close> sum_nonneg_leq_bound zero_le_power2)
  then show \<open>\<exists>a\<in>A. \<forall>f\<in>F. norm ((b - a) *\<^sub>V f) \<le> \<epsilon>\<close>
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
    
    have c0: \<open>c *\<^sub>V (\<psi> \<otimes>\<^sub>s ket i) = 0\<close> if \<open>i \<ge> n\<close> for i \<psi>
      using that by (simp add: c'' Proj_inflation_carrier_outside)
    have cadj0: \<open>c* *\<^sub>V (\<psi> \<otimes>\<^sub>s ket j) = 0\<close> if \<open>j \<ge> n\<close> for j \<psi>
      using that by (simp add: c'' adj_Proj Proj_inflation_carrier_outside)

    have \<open>inflation_op (replicate n b0) o\<^sub>C\<^sub>L c = c o\<^sub>C\<^sub>L inflation_op (replicate n b0)\<close>
    proof (rule equal_ket, rule cinner_ket_eqI)
      fix ii jj
      obtain i' j' :: 'a and i j :: nat where ii_def: \<open>ii = (i',i)\<close> and jj_def: \<open>jj = (j',j)\<close>
        by force
      show \<open>ket ii \<bullet>\<^sub>C ((inflation_op (replicate n b0) o\<^sub>C\<^sub>L c) *\<^sub>V ket jj) =
                 ket ii \<bullet>\<^sub>C ((c o\<^sub>C\<^sub>L inflation_op (replicate n b0)) *\<^sub>V ket jj)\<close>
      proof (cases \<open>i < n \<and> j < n\<close>)
        case True
        have \<open>ket ii \<bullet>\<^sub>C ((inflation_op (replicate n b0) o\<^sub>C\<^sub>L c) *\<^sub>V ket jj) = ((b0* *\<^sub>V ket i') \<otimes>\<^sub>s ket i) \<bullet>\<^sub>C (c *\<^sub>V ket j' \<otimes>\<^sub>s ket j)\<close>
          using True by (simp add: ii_def jj_def inflation_op_adj inflation_op_apply flip: tensor_ell2_inner_prod
              flip: tensor_ell2_ket cinner_adj_left[where G=\<open>inflation_op _\<close>])
        also have \<open>\<dots> = (ket i' \<otimes>\<^sub>s ket i) \<bullet>\<^sub>C (c *\<^sub>V (b0 *\<^sub>V ket j') \<otimes>\<^sub>s ket j)\<close>
          using b0_c' apply (simp add: c'_def flip: tensor_ell2_right_apply cinner_adj_right)
          by (metis (no_types, lifting) True simp_a_oCL_b')
        also have \<open>\<dots> = ket ii \<bullet>\<^sub>C ((c o\<^sub>C\<^sub>L inflation_op (replicate n b0)) *\<^sub>V ket jj)\<close>
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

lemma double_commutant_theorem_aux:
  \<comment> \<open>Basically the double commutant theorem, except that we restricted to spaces of the form \<^typ>\<open>'a ell2\<close>\<close>
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

(* TODO move next to *) thm continuous_map_right_comp_sot
lemma continuous_map_right_comp_sot'[continuous_intros]: 
  fixes a :: \<open>'d \<Rightarrow> _ \<Rightarrow>\<^sub>C\<^sub>L 'c::complex_normed_vector\<close> and
    b :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  assumes \<open>continuous_map T cstrong_operator_topology a\<close> 
  shows \<open>continuous_map T cstrong_operator_topology (\<lambda>x. a x o\<^sub>C\<^sub>L b)\<close> 
  using continuous_map_compose[OF assms continuous_map_right_comp_sot, of b]
  by (simp add: o_def)

(* TODO move next to *) thm continuous_map_left_comp_sot
lemma continuous_map_left_comp_sot'[continuous_intros]: 
  fixes a :: \<open>_ \<Rightarrow>\<^sub>C\<^sub>L 'c::complex_normed_vector\<close> and
    b :: \<open>'d \<Rightarrow> 'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  assumes \<open>continuous_map T cstrong_operator_topology b\<close>
  shows \<open>continuous_map T cstrong_operator_topology (\<lambda>x. a o\<^sub>C\<^sub>L b x)\<close> 
  using continuous_map_compose[OF assms continuous_map_left_comp_sot, of a]
  by (simp add: o_def)


lemma sandwich_sot_cont[continuous_intros]:
  assumes \<open>continuous_map T cstrong_operator_topology f\<close>
  shows \<open>continuous_map T cstrong_operator_topology (\<lambda>x. sandwich A (f x))\<close>
  apply (simp add: sandwich_apply)
  by (intro continuous_intros assms)

lemma sandwich_arg_compose:
  assumes \<open>isometry U\<close>
  shows \<open>sandwich U x o\<^sub>C\<^sub>L sandwich U y = sandwich U (x o\<^sub>C\<^sub>L y)\<close>
  apply (simp add: sandwich_apply)
  by (metis (no_types, lifting) Misc.lift_cblinfun_comp(2) assms cblinfun_compose_id_right isometryD)

lemma double_commutant_theorem_aux2: (* TODO: generalize to non-not_singleton *)
  \<comment> \<open>Basically the double commutant theorem, except that we restricted to spaces of typeclass \<^class>\<open>not_singleton\<close>\<close>
  \<comment> \<open>@{cite conway13functional}, Proposition IX.6.4\<close>
  fixes A :: \<open>('a::{chilbert_space,not_singleton} \<Rightarrow>\<^sub>C\<^sub>L 'a) set\<close>
  assumes subspace: \<open>csubspace A\<close>
  assumes mult: \<open>\<And>a a'. a \<in> A \<Longrightarrow> a' \<in> A \<Longrightarrow> a o\<^sub>C\<^sub>L a' \<in> A\<close>
  assumes id: \<open>id_cblinfun \<in> A\<close>
  assumes adj: \<open>\<And>a. a \<in> A \<Longrightarrow> a* \<in> A\<close>
  shows \<open>commutant (commutant A) = cstrong_operator_topology closure_of A\<close>
proof -
  define A' :: \<open>('a chilbert2ell2 ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a chilbert2ell2 ell2) set\<close>
    where \<open>A' = sandwich (ell2_to_hilbert*) ` A\<close>
  have subspace: \<open>csubspace A'\<close>
    using subspace by (auto intro!: complex_vector.linear_subspace_image simp: A'_def)
  have mult: \<open>\<And>a a'. a \<in> A' \<Longrightarrow> a' \<in> A' \<Longrightarrow> a o\<^sub>C\<^sub>L a' \<in> A'\<close>
    using mult by (auto simp add: A'_def sandwich_arg_compose unitary_ell2_to_hilbert)
  have id: \<open>id_cblinfun \<in> A'\<close>
    using id by (auto intro!: image_eqI simp add: A'_def sandwich_isometry_id unitary_ell2_to_hilbert)
  have adj: \<open>\<And>a. a \<in> A' \<Longrightarrow> a* \<in> A'\<close>
    using adj by (auto intro!: image_eqI simp: A'_def simp flip: sandwich_apply_adj)
  have homeo: \<open>homeomorphic_map cstrong_operator_topology cstrong_operator_topology
     ((*\<^sub>V) (sandwich ell2_to_hilbert))\<close>
    by (auto intro!: continuous_intros homeomorphic_maps_imp_map[where g=\<open>sandwich (ell2_to_hilbert*)\<close>]
        simp: homeomorphic_maps_def sandwich_compose unitary_ell2_to_hilbert
        simp flip: cblinfun_apply_cblinfun_compose)
  have \<open>commutant (commutant A') = cstrong_operator_topology closure_of A'\<close>
    using subspace mult id adj by (rule double_commutant_theorem_aux)
  then have \<open>sandwich ell2_to_hilbert ` commutant (commutant A') = sandwich ell2_to_hilbert ` (cstrong_operator_topology closure_of A')\<close>
    by simp
  then show ?thesis
    by (simp add: A'_def unitary_ell2_to_hilbert sandwich_unitary_complement image_image
        sandwich_compose homeo
        flip: cblinfun_apply_cblinfun_compose
        homeomorphic_map_closure_of[where Y=cstrong_operator_topology])
qed

lemma double_commutant_theorem:
  \<comment> \<open>@{cite conway13functional}, Proposition IX.6.4\<close>
  fixes A :: \<open>('a::{chilbert_space} \<Rightarrow>\<^sub>C\<^sub>L 'a) set\<close>
  assumes subspace: \<open>csubspace A\<close>
  assumes mult: \<open>\<And>a a'. a \<in> A \<Longrightarrow> a' \<in> A \<Longrightarrow> a o\<^sub>C\<^sub>L a' \<in> A\<close>
  assumes id: \<open>id_cblinfun \<in> A\<close>
  assumes adj: \<open>\<And>a. a \<in> A \<Longrightarrow> a* \<in> A\<close>
  shows \<open>commutant (commutant A) = cstrong_operator_topology closure_of A\<close>
proof (cases \<open>UNIV = {0::'a}\<close>)
  case True
  then have \<open>(x :: 'a) = 0\<close> for x
    by auto
  then have UNIV_0: \<open>UNIV = {0 :: 'a\<Rightarrow>\<^sub>C\<^sub>L'a}\<close>
    by (auto intro!: cblinfun_eqI)
  have \<open>0 \<in> commutant (commutant A)\<close>
    using complex_vector.subspace_0 csubspace_commutant by blast
  then have 1: \<open>commutant (commutant A) = UNIV\<close>
    using UNIV_0
    by force
  have \<open>0 \<in> A\<close>
    by (simp add: assms(1) complex_vector.subspace_0)
  then have \<open>0 \<in> cstrong_operator_topology closure_of A\<close>
    by (simp add: assms(1) complex_vector.subspace_0)
  then have 2: \<open>cstrong_operator_topology closure_of A = UNIV\<close>
    using UNIV_0
    by force
  from 1 2 show ?thesis 
    by simp
next
  case False
  note aux2 = double_commutant_theorem_aux2[where 'a=\<open>'z::{chilbert_space,not_singleton}\<close>, rule_format, internalize_sort \<open>'z::{chilbert_space,not_singleton}\<close>]
  have hilbert: \<open>class.chilbert_space (*\<^sub>R) (*\<^sub>C) (+) (0::'a) (-) uminus dist norm sgn uniformity open (\<bullet>\<^sub>C)\<close>
    by (rule chilbert_space_class.chilbert_space_axioms)
  from False
  have not_singleton: \<open>class.not_singleton TYPE('a)\<close>
    by (rule class_not_singletonI_monoid_add)
  show ?thesis 
    apply (rule aux2)
    using assms hilbert not_singleton by auto
qed

hide_fact double_commutant_theorem_aux double_commutant_theorem_aux2

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


definition one_algebra :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'a::chilbert_space) set\<close> where
  \<open>one_algebra = range (\<lambda>c. c *\<^sub>C id_cblinfun)\<close>

lemma commutant_tensor1': \<open>commutant (range (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a)) = range (\<lambda>b. b \<otimes>\<^sub>o id_cblinfun)\<close>
proof -
  have \<open>commutant (range (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a)) = commutant (sandwich swap_ell2 ` range (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun))\<close>
    by (metis (no_types, lifting) image_cong range_composition swap_tensor_op_sandwich)
  also have \<open>\<dots> = sandwich swap_ell2 ` commutant (range (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun))\<close>
    by (simp add: sandwich_unitary_complement)
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
      have \<open>((\<lambda>x. f x *\<^sub>V (\<psi> \<otimes>\<^sub>s ket b)) \<longlongrightarrow> l *\<^sub>V (\<psi> \<otimes>\<^sub>s ket b)) F\<close>
        using limitin_cstrong_operator_topology that(2) by auto
      then have \<open>((\<lambda>x. (f' x *\<^sub>V \<psi>) \<otimes>\<^sub>s ket b) \<longlongrightarrow> (l' *\<^sub>V \<psi>) \<otimes>\<^sub>s ket b) F\<close>
        by (simp add: f_def l_def tensor_op_ell2)
      then have \<open>((\<lambda>x. (tensor_ell2_right (ket b))* *\<^sub>V ((f' x *\<^sub>V \<psi>) \<otimes>\<^sub>s ket b)) 
                  \<longlongrightarrow> (tensor_ell2_right (ket b))* *\<^sub>V ((l' *\<^sub>V \<psi>) \<otimes>\<^sub>s ket b)) F\<close>
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

definition von_neumann_algebra where \<open>von_neumann_algebra A \<longleftrightarrow> (\<forall>a\<in>A. a* \<in> A) \<and> commutant (commutant A) = A\<close>
definition von_neumann_factor where \<open>von_neumann_factor A \<longleftrightarrow> von_neumann_algebra A \<and> A \<inter> commutant A = one_algebra\<close>

lemma von_neumann_algebraI: \<open>(\<And>a. a\<in>A \<Longrightarrow> a* \<in> A) \<Longrightarrow> commutant (commutant A) \<subseteq> A \<Longrightarrow> von_neumann_algebra A\<close> for \<FF>
  apply (auto simp: von_neumann_algebra_def)
  using double_commutant_grows by blast

lemma von_neumann_factorI:
  assumes \<open>von_neumann_algebra A\<close>
  assumes \<open>A \<inter> commutant A \<subseteq> one_algebra\<close>
  shows \<open>von_neumann_factor A\<close>
proof -
  have 1: \<open>A \<supseteq> one_algebra\<close>
    apply (subst asm_rl[of \<open>A = commutant (commutant A)\<close>])
    using assms(1) von_neumann_algebra_def apply blast
    by (auto simp: commutant_def one_algebra_def)
  have 2: \<open>commutant A \<supseteq> one_algebra\<close>
    by (auto simp: commutant_def one_algebra_def)
  from 1 2 assms show ?thesis
    by (auto simp add: von_neumann_factor_def)
qed

lemma commutant_UNIV: \<open>commutant (UNIV :: ('a \<Rightarrow>\<^sub>C\<^sub>L 'a::chilbert_space) set) = one_algebra\<close>
  (* Not sure if the assumption chilbert_space is needed *)
proof -
  have 1: \<open>c *\<^sub>C id_cblinfun \<in> commutant UNIV\<close> for c
    by (simp add: commutant_def)
  moreover have 2: \<open>x \<in> range (\<lambda>c. c *\<^sub>C id_cblinfun)\<close> if x_comm: \<open>x \<in> commutant UNIV\<close> for x :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  proof -
    obtain B :: \<open>'a set\<close> where \<open>is_onb B\<close>
      using is_onb_some_chilbert_basis by blast
    have \<open>\<exists>c. x *\<^sub>V \<psi> = c *\<^sub>C \<psi>\<close> for \<psi>
    proof -
      have \<open>norm (x *\<^sub>V \<psi>) = norm ((x o\<^sub>C\<^sub>L selfbutter (sgn \<psi>)) *\<^sub>V \<psi>)\<close>
        by (simp add: cnorm_eq_1)
      also have \<open>\<dots> = norm ((selfbutter (sgn \<psi>) o\<^sub>C\<^sub>L x) *\<^sub>V \<psi>)\<close>
        using x_comm by (simp add: commutant_def del: butterfly_apply)
      also have \<open>\<dots> = norm (proj \<psi> *\<^sub>V (x *\<^sub>V \<psi>))\<close>
        by (simp add: butterfly_sgn_eq_proj)
      finally have \<open>x *\<^sub>V \<psi> \<in> space_as_set (ccspan {\<psi>})\<close>
        by (metis norm_Proj_apply)
      then show ?thesis
        by (auto simp add: ccspan_finite complex_vector.span_singleton)
    qed
    then obtain f where f: \<open>x *\<^sub>V \<psi> = f \<psi> *\<^sub>C \<psi>\<close> for \<psi>
      apply atomize_elim apply (rule choice) by auto

    have \<open>f \<psi> = f \<phi>\<close> if \<open>\<psi> \<in> B\<close> and \<open>\<phi> \<in> B\<close> for \<psi> \<phi>
    proof (cases \<open>\<psi> = \<phi>\<close>)
      case True
      then show ?thesis by simp
    next
      case False
      with that \<open>is_onb B\<close>
      have [simp]: \<open>\<psi> \<bullet>\<^sub>C \<phi> = 0\<close>
        by (auto simp: is_onb_def is_ortho_set_def)
      then have [simp]: \<open>\<phi> \<bullet>\<^sub>C \<psi> = 0\<close>
        using is_orthogonal_sym by blast
      from that \<open>is_onb B\<close> have [simp]: \<open>\<psi> \<noteq> 0\<close>
        by (auto simp: is_onb_def)
      from that \<open>is_onb B\<close> have [simp]: \<open>\<phi> \<noteq> 0\<close>
        by (auto simp: is_onb_def)

      have \<open>f (\<psi>+\<phi>) *\<^sub>C \<psi> + f (\<psi>+\<phi>) *\<^sub>C \<phi> = f (\<psi>+\<phi>) *\<^sub>C (\<psi> + \<phi>)\<close>
        by (simp add: complex_vector.vector_space_assms(1))
      also have \<open>\<dots> = x *\<^sub>V (\<psi> + \<phi>)\<close>
        by (simp add: f)
      also have \<open>\<dots> = x *\<^sub>V \<psi> + x *\<^sub>V \<phi>\<close>
        by (simp add: cblinfun.add_right)
      also have \<open>\<dots> = f \<psi> *\<^sub>C \<psi> + f \<phi> *\<^sub>C \<phi>\<close>
        by (simp add: f)
      finally have *: \<open>f (\<psi> + \<phi>) *\<^sub>C \<psi> + f (\<psi> + \<phi>) *\<^sub>C \<phi> = f \<psi> *\<^sub>C \<psi> + f \<phi> *\<^sub>C \<phi>\<close>
        by -
      have \<open>f (\<psi> + \<phi>) = f \<psi>\<close>
        using *[THEN arg_cong[where f=\<open>cinner \<psi>\<close>]]
        by (simp add: cinner_add_right)
      moreover have \<open>f (\<psi> + \<phi>) = f \<phi>\<close>
        using *[THEN arg_cong[where f=\<open>cinner \<phi>\<close>]]
        by (simp add: cinner_add_right)
      ultimately show \<open>f \<psi> = f \<phi>\<close>
        by simp
    qed
    then obtain c where \<open>f \<psi> = c\<close> if \<open>\<psi> \<in> B\<close> for \<psi>
      by meson
    then have \<open>x *\<^sub>V \<psi> = (c *\<^sub>C id_cblinfun) *\<^sub>V \<psi>\<close> if \<open>\<psi> \<in> B\<close> for \<psi>
      by (simp add: f that)
    then have \<open>x = c *\<^sub>C id_cblinfun\<close>
      apply (rule cblinfun_eq_gen_eqI[where G=B])
      using \<open>is_onb B\<close> by (auto simp: is_onb_def)
    then show \<open>x \<in> range (\<lambda>c. c *\<^sub>C id_cblinfun)\<close>
      by (auto)
  qed

  from 1 2 show ?thesis
    by (auto simp: one_algebra_def)
qed


lemma von_neumann_algebra_UNIV: \<open>von_neumann_algebra UNIV\<close>
  by (auto simp: von_neumann_algebra_def commutant_def)

lemma von_neumann_factor_UNIV: \<open>von_neumann_factor UNIV\<close>
  by (simp add: von_neumann_factor_def commutant_UNIV von_neumann_algebra_UNIV)

lemma von_neumann_algebra_UNION:
  assumes \<open>\<And>x. x \<in> X \<Longrightarrow> von_neumann_algebra (A x)\<close>
  shows \<open>von_neumann_algebra (commutant (commutant (\<Union>x\<in>X. A x)))\<close>
proof (rule von_neumann_algebraI)
  show \<open>commutant (commutant (commutant (commutant (\<Union>x\<in>X. A x))))
    \<subseteq> commutant (commutant (\<Union>x\<in>X. A x))\<close>
    by (meson commutant_antimono double_commutant_grows)
next
  fix a
  assume \<open>a \<in> commutant (commutant (\<Union>x\<in>X. A x))\<close>
  then have \<open>a* \<in> adj ` commutant (commutant (\<Union>x\<in>X. A x))\<close>
    by simp
  also have \<open>\<dots> = commutant (commutant (\<Union>x\<in>X. adj ` A x))\<close>
    by (simp add: commutant_adj image_UN)
  also have \<open>\<dots> \<subseteq> commutant (commutant (\<Union>x\<in>X. A x))\<close>
    using assms by (auto simp: von_neumann_algebra_def intro!: commutant_antimono)
  finally show \<open>a* \<in> commutant (commutant (\<Union>x\<in>X. A x))\<close>
    by -
qed

lemma von_neumann_algebra_union:
  assumes \<open>von_neumann_algebra A\<close>
  assumes \<open>von_neumann_algebra B\<close>
  shows \<open>von_neumann_algebra (commutant (commutant (A \<union> B)))\<close>
  using von_neumann_algebra_UNION[where X=\<open>{True,False}\<close> and A=\<open>\<lambda>x. if x then A else B\<close>]
  by (auto simp: assms Un_ac(3))

(* lemma von_neumann_factor_union:
  assumes \<open>von_neumann_factor A\<close>
  assumes \<open>von_neumann_factor B\<close>
  shows \<open>von_neumann_factor (commutant (commutant (A \<union> B)))\<close>
proof (rule von_neumann_factorI)
  show \<open>von_neumann_algebra (commutant (commutant (A \<union> B)))\<close>
    apply (rule von_neumann_algebra_union)
    using assms by (simp_all add: von_neumann_factor_def)
  show \<open>commutant (commutant (A \<union> B)) \<inter> commutant (commutant (commutant (A \<union> B)))
    \<subseteq> range (\<lambda>c. c *\<^sub>C id_cblinfun)\<close>
  proof (rule subsetI)
    fix a
    assume asm: \<open>a \<in> commutant (commutant (A \<union> B)) \<inter>
             commutant (commutant (commutant (A \<union> B)))\<close>
    then have a_cc: \<open>a \<in> commutant (commutant (A \<union> B))\<close>
      and a_c: \<open>a \<in> commutant (A \<union> B)\<close>
      by auto
    from a_cc have \<open>a \<in> cstrong_operator_topology closure_of (A + B)\<close>
  try0
  by -
  then have \<open>a \<in> cstrong_operator_topology closure_of A \<or> a \<in> cstrong_operator_topology closure_of B\<close>
    by (simp add: closure_of_Un)

  show \<open>a \<in> range (\<lambda>c. c *\<^sub>C id_cblinfun)\<close>

  by -
qed *)

lemma von_neumann_algebra_commutant: \<open>von_neumann_algebra (commutant A)\<close> if \<open>von_neumann_algebra A\<close>
proof (rule von_neumann_algebraI)
  show \<open>a* \<in> commutant A\<close> if \<open>a \<in> commutant A\<close> for a
    by (smt (verit) Set.basic_monos(7) \<open>von_neumann_algebra A\<close> commutant_adj commutant_antimono double_adj image_iff image_subsetI that von_neumann_algebra_def)
  show \<open>commutant (commutant (commutant A)) \<subseteq> commutant A \<close>
    by simp
qed


lemma id_in_commutant[iff]: \<open>id_cblinfun \<in> commutant A\<close>
  by (simp add: commutant_memberI)

lemma von_neumann_algebra_def_sot:
  \<open>von_neumann_algebra \<FF> \<longleftrightarrow> 
      (\<forall>a\<in>\<FF>. a* \<in> \<FF>) \<and> csubspace \<FF> \<and> (\<forall>a\<in>\<FF>. \<forall>b\<in>\<FF>. a o\<^sub>C\<^sub>L b \<in> \<FF>) \<and> id_cblinfun \<in> \<FF> \<and>
      closedin cstrong_operator_topology \<FF>\<close>
proof (unfold von_neumann_algebra_def, intro iffI conjI; elim conjE; assumption?)
  assume comm: \<open>commutant (commutant \<FF>) = \<FF>\<close>
  from comm show \<open>closedin cstrong_operator_topology \<FF>\<close>
    by (metis commutant_sot_closed)
  from comm show \<open>csubspace \<FF>\<close>
    by (metis csubspace_commutant)
  from comm show \<open>\<forall>a\<in>\<FF>. \<forall>b\<in>\<FF>. a o\<^sub>C\<^sub>L b \<in> \<FF>\<close>
    using commutant_mult by blast
  from comm show \<open>id_cblinfun \<in> \<FF>\<close>
    by blast
next
  assume adj: \<open>\<forall>a\<in>\<FF>. a* \<in> \<FF>\<close>
  assume subspace: \<open>csubspace \<FF>\<close>
  assume closed: \<open>closedin cstrong_operator_topology \<FF>\<close>
  assume mult: \<open>\<forall>a\<in>\<FF>. \<forall>b\<in>\<FF>. a o\<^sub>C\<^sub>L b \<in> \<FF>\<close>
  assume id: \<open>id_cblinfun \<in> \<FF>\<close>
  have \<open>commutant (commutant \<FF>) = cstrong_operator_topology closure_of \<FF>\<close>
    apply (rule double_commutant_theorem)
    thm double_commutant_theorem[of \<FF>]
    using subspace subspace mult id adj 
    by simp_all
  also from closed have \<open>\<dots> = \<FF>\<close>
    by (simp add: closure_of_eq)
  finally show \<open>commutant (commutant \<FF>) = \<FF>\<close>
    by -
qed


lemma isometry_inj:
  assumes \<open>isometry U\<close>
  shows \<open>inj_on U X\<close>
  apply (rule inj_on_inverseI[where g=\<open>U*\<close>])
  using assms by (simp flip: cblinfun_apply_cblinfun_compose)

lemma unitary_inj:
  assumes \<open>unitary U\<close>
  shows \<open>inj_on U X\<close>
  apply (rule isometry_inj)
  using assms by simp

lemma unitary_adj_inv: \<open>unitary U \<Longrightarrow> cblinfun_apply (U*) = inv (cblinfun_apply U)\<close>
  apply (rule inj_imp_inv_eq[symmetric])
   apply (simp add: unitary_inj)
  unfolding unitary_def
  by (simp flip: cblinfun_apply_cblinfun_compose)

lemma isometry_cinner_both_sides:
  assumes \<open>isometry U\<close>
  shows \<open>cinner (U x) (U y) = cinner x y\<close>
  using assms by (simp add: flip: cinner_adj_right cblinfun_apply_cblinfun_compose)

lemma isometry_image_is_ortho_set:
  assumes \<open>is_ortho_set A\<close>
  assumes \<open>isometry U\<close>
  shows \<open>is_ortho_set (U ` A)\<close>
  using assms apply (auto simp add: is_ortho_set_def isometry_cinner_both_sides)
  by (metis cinner_eq_zero_iff isometry_cinner_both_sides)

lemma unitary_image_onb:
  assumes \<open>is_onb A\<close>
  assumes \<open>unitary U\<close>
  shows \<open>is_onb (U ` A)\<close>
  using assms
  by (auto simp add: is_onb_def isometry_image_is_ortho_set isometry_preserves_norm
      simp flip: cblinfun_image_ccspan)

lemma double_commutant_hull: \<open>commutant (commutant X) = (\<lambda>X. commutant (commutant X) = X) hull X\<close>
  by (smt (verit) commutant_antimono double_commutant_grows hull_unique triple_commutant)

lemma commutant_adj_closed: \<open>(\<And>x. x \<in> X \<Longrightarrow> x* \<in> X) \<Longrightarrow> x \<in> commutant X \<Longrightarrow> x* \<in> commutant X\<close>
  by (metis (no_types, opaque_lifting) commutant_adj commutant_antimono double_adj imageI subset_iff)

lemma double_commutant_hull':
  assumes \<open>\<And>x. x \<in> X \<Longrightarrow> x* \<in> X\<close>
  shows \<open>commutant (commutant X) = von_neumann_algebra hull X\<close>
proof (rule antisym)
  show \<open>commutant (commutant X) \<subseteq> von_neumann_algebra hull X\<close>
    apply (subst double_commutant_hull)
    apply (rule hull_antimono)
    by (simp add: von_neumann_algebra_def)
  show \<open>von_neumann_algebra hull X \<subseteq> commutant (commutant X)\<close>
    apply (rule hull_minimal)
    by (simp_all add: von_neumann_algebra_def assms commutant_adj_closed)
qed

lemma hull_cong_restricted: \<open>X = Y \<Longrightarrow> P hull X = P hull Y\<close>
  by simp

lemma double_commutant_Un_left: \<open>commutant (commutant (commutant (commutant X) \<union> Y)) = commutant (commutant (X \<union> Y))\<close>
  apply (simp add: double_commutant_hull cong: hull_cong_restricted)
  using hull_Un_left by fastforce

lemma double_commutant_Un_right: \<open>commutant (commutant (X \<union> commutant (commutant Y))) = commutant (commutant (X \<union> Y))\<close>
  by (metis Un_ac(3) double_commutant_Un_left)

lemma tensor_ell2_right_butterfly: \<open>tensor_ell2_right \<psi> o\<^sub>C\<^sub>L tensor_ell2_right \<phi>* = id_cblinfun \<otimes>\<^sub>o butterfly \<psi> \<phi>\<close>
  by (auto intro!: equal_ket cinner_ket_eqI simp: tensor_op_ell2 simp flip: tensor_ell2_ket)
lemma tensor_ell2_left_butterfly: \<open>tensor_ell2_left \<psi> o\<^sub>C\<^sub>L tensor_ell2_left \<phi>* = butterfly \<psi> \<phi> \<otimes>\<^sub>o id_cblinfun\<close>
  by (auto intro!: equal_ket cinner_ket_eqI simp: tensor_op_ell2 simp flip: tensor_ell2_ket)

lemma amplification_double_commutant_commute:
  \<open>commutant (commutant ((\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) ` X))
    = (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) `  commutant (commutant X)\<close>
\<comment> \<open>@{cite takesaki}, Corollary IV.1.5\<close>
proof -
  define \<pi> :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2) \<Rightarrow> (('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2)\<close> where 
    \<open>\<pi> a = a \<otimes>\<^sub>o id_cblinfun\<close> for a
  define U :: \<open>'b \<Rightarrow> 'a ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2\<close> where \<open>U i = tensor_ell2_right (ket i)\<close> for i :: 'b
  write commutant (\<open>_''\<close> [120] 120)
      \<comment> \<open>Notation \<^term>\<open>X '\<close> for \<^term>\<open>commutant X\<close>\<close>
  write id_cblinfun (\<open>\<one>\<close>)
  have *: \<open>(\<pi> ` X)'' \<subseteq> range \<pi>\<close> for X
  proof (rule subsetI)
    fix x assume asm: \<open>x \<in> (\<pi> ` X)''\<close>
    fix t
    define y where \<open>y = U t* o\<^sub>C\<^sub>L x o\<^sub>C\<^sub>L U t\<close>
    have \<open>ket (k,l) \<bullet>\<^sub>C (x *\<^sub>V ket (m,n)) = ket (k,l) \<bullet>\<^sub>C (\<pi> y *\<^sub>V ket (m,n))\<close> for k l m n
    proof -
      have comm: \<open>x o\<^sub>C\<^sub>L (U i o\<^sub>C\<^sub>L U j*) = (U i o\<^sub>C\<^sub>L U j*) o\<^sub>C\<^sub>L x\<close> for i j
      proof -
        have \<open>U i o\<^sub>C\<^sub>L U j* = id_cblinfun \<otimes>\<^sub>o butterket i j\<close>
          by (simp add: U_def tensor_ell2_right_butterfly)
        also have \<open>\<dots> \<in> (\<pi> ` X)'\<close>
          by (simp add: \<pi>_def commutant_def comp_tensor_op)
        finally show ?thesis
          using asm
          by (simp add: commutant_def)
      qed
      have \<open>ket (k,l) \<bullet>\<^sub>C (x *\<^sub>V ket (m,n)) = ket k \<bullet>\<^sub>C (U l* *\<^sub>V x *\<^sub>V U n *\<^sub>V ket m)\<close>
        by (simp add: cinner_adj_right U_def tensor_ell2_ket)
      also have \<open>\<dots> = ket k \<bullet>\<^sub>C (U l* *\<^sub>V x *\<^sub>V U n *\<^sub>V U t* *\<^sub>V U t *\<^sub>V ket m)\<close>
        using U_def by fastforce
      also have \<open>\<dots> = ket k \<bullet>\<^sub>C (U l* *\<^sub>V U n *\<^sub>V U t* *\<^sub>V x *\<^sub>V U t *\<^sub>V ket m)\<close>
        using simp_a_oCL_b'[OF comm]
        by simp
      also have \<open>\<dots> = of_bool (l=n) * (ket k \<bullet>\<^sub>C (U t* *\<^sub>V x *\<^sub>V U t *\<^sub>V ket m))\<close>
        using U_def by fastforce
      also have \<open>\<dots> = of_bool (l=n) * (ket k \<bullet>\<^sub>C (y *\<^sub>V ket m))\<close>
        using y_def by force
      also have \<open>\<dots> = ket (k,l) \<bullet>\<^sub>C (\<pi> y *\<^sub>V ket (m,n))\<close>
        by (simp add: \<pi>_def tensor_op_ell2 flip: tensor_ell2_ket)
      finally show ?thesis
        by -
    qed
    then have \<open>x = \<pi> y\<close>
      by (metis cinner_ket_eqI equal_ket surj_pair)
    then show \<open>x \<in> range \<pi>\<close>
      by simp
  qed
  have **: \<open>\<pi> ` (Y ') = (\<pi> ` Y)' \<inter> range \<pi>\<close> for Y
    using inj_tensor_left[of id_cblinfun]
    apply (auto simp add: commutant_def \<pi>_def comp_tensor_op
        intro!: image_eqI)
    using injD by fastforce
  have 1: \<open>(\<pi> ` X)'' \<subseteq> \<pi> ` (X '')\<close> for X
  proof -
    have \<open>(\<pi> ` X)'' \<subseteq> (\<pi> ` X)'' \<inter> range \<pi>\<close>
      by (simp add: "*")
    also have \<open>\<dots> \<subseteq> ((\<pi> ` X)' \<inter> range \<pi>)' \<inter> range \<pi>\<close>
      by (simp add: commutant_antimono inf.coboundedI1)
    also have \<open>\<dots> = \<pi> ` (X '')\<close>
      by (simp add: ** )
    finally show ?thesis
      by -
  qed

  have \<open>x o\<^sub>C\<^sub>L y = y o\<^sub>C\<^sub>L x\<close> if \<open>x \<in> \<pi> ` (X '')\<close> and \<open>y \<in> (\<pi> ` X)'\<close> for x y
  proof (intro equal_ket cinner_ket_eqI)
    fix i j :: \<open>'a \<times> 'b\<close>
    from that obtain w where \<open>w \<in> X ''\<close> and x_def: \<open>x = w \<otimes>\<^sub>o \<one>\<close>
      by (auto simp: \<pi>_def)
    obtain i1 i2 where i_def: \<open>i = (i1, i2)\<close> by force
    obtain j1 j2 where j_def: \<open>j = (j1, j2)\<close> by force
    define y\<^sub>0 where \<open>y\<^sub>0 = U i2* o\<^sub>C\<^sub>L y o\<^sub>C\<^sub>L U j2\<close>

    have \<open>y\<^sub>0 \<in> X '\<close>
    proof (rule commutant_memberI)
      fix z assume \<open>z \<in> X\<close>
      then have \<open>z \<otimes>\<^sub>o \<one> \<in> \<pi> ` X\<close>
        by (auto simp: \<pi>_def)
      have \<open>y\<^sub>0 o\<^sub>C\<^sub>L z = U i2* o\<^sub>C\<^sub>L y o\<^sub>C\<^sub>L (z \<otimes>\<^sub>o \<one>) o\<^sub>C\<^sub>L U j2\<close>
        by (auto intro!: equal_ket simp add: y\<^sub>0_def U_def tensor_op_ell2)
      also have \<open>\<dots> = U i2* o\<^sub>C\<^sub>L (z \<otimes>\<^sub>o \<one>) o\<^sub>C\<^sub>L y o\<^sub>C\<^sub>L U j2\<close>
        using \<open>z \<otimes>\<^sub>o \<one> \<in> \<pi> ` X\<close> and \<open>y \<in> (\<pi> ` X)'\<close>
        apply (auto simp add: commutant_def)
        by (simp add: cblinfun_compose_assoc)
      also have \<open>\<dots> = z o\<^sub>C\<^sub>L y\<^sub>0\<close>
        by (auto intro!: equal_ket cinner_ket_eqI
            simp add: y\<^sub>0_def U_def tensor_op_ell2 tensor_op_adjoint simp flip: cinner_adj_left)
      finally show \<open>y\<^sub>0 o\<^sub>C\<^sub>L z = z o\<^sub>C\<^sub>L y\<^sub>0\<close>
        by -
    qed
    have \<open>ket i \<bullet>\<^sub>C ((x o\<^sub>C\<^sub>L y) *\<^sub>V ket j) = ket i1 \<bullet>\<^sub>C (U i2* *\<^sub>V (w \<otimes>\<^sub>o \<one>) *\<^sub>V y *\<^sub>V U j2 *\<^sub>V ket j1)\<close>
      by (simp add: U_def i_def j_def tensor_ell2_ket cinner_adj_right x_def)
    also have \<open>\<dots> = ket i1 \<bullet>\<^sub>C (U i2* *\<^sub>V (w \<otimes>\<^sub>o \<one>) *\<^sub>V (U i2 o\<^sub>C\<^sub>L U i2*) *\<^sub>V y *\<^sub>V U j2 *\<^sub>V ket j1)\<close>
      by (simp add: U_def tensor_ell2_right_butterfly tensor_op_adjoint tensor_op_ell2
          flip: cinner_adj_left)
    also have \<open>\<dots> = ket i1 \<bullet>\<^sub>C (w *\<^sub>V y\<^sub>0 *\<^sub>V ket j1)\<close>
      by (simp add: y\<^sub>0_def tensor_op_adjoint tensor_op_ell2 U_def flip: cinner_adj_left)
    also have \<open>\<dots> = ket i1 \<bullet>\<^sub>C (y\<^sub>0 *\<^sub>V w *\<^sub>V ket j1)\<close>
      using \<open>y\<^sub>0 \<in> X '\<close> \<open>w \<in> X ''\<close>
      apply (subst (asm) (2) commutant_def)
      using lift_cblinfun_comp(4) by force
    also have \<open>\<dots> = ket i1 \<bullet>\<^sub>C (U i2* *\<^sub>V y *\<^sub>V (U j2 o\<^sub>C\<^sub>L U j2*) *\<^sub>V (w \<otimes>\<^sub>o \<one>) *\<^sub>V U j2 *\<^sub>V ket j1)\<close>
      by (simp add: y\<^sub>0_def tensor_op_adjoint tensor_op_ell2 U_def flip: cinner_adj_left)
    also have \<open>\<dots> = ket i1 \<bullet>\<^sub>C (U i2* *\<^sub>V y *\<^sub>V (w \<otimes>\<^sub>o \<one>) *\<^sub>V U j2 *\<^sub>V ket j1)\<close>
      by (simp add: U_def tensor_ell2_right_butterfly tensor_op_adjoint tensor_op_ell2
          flip: cinner_adj_left)
    also have \<open>\<dots> = ket i \<bullet>\<^sub>C ((y o\<^sub>C\<^sub>L x) *\<^sub>V ket j)\<close>
      by (simp add: U_def i_def j_def tensor_ell2_ket cinner_adj_right x_def)
    finally show \<open>ket i \<bullet>\<^sub>C ((x o\<^sub>C\<^sub>L y) *\<^sub>V ket j) = ket i \<bullet>\<^sub>C ((y o\<^sub>C\<^sub>L x) *\<^sub>V ket j)\<close>
      by -
  qed
  then have 2: \<open>(\<pi> ` X)'' \<supseteq> \<pi> ` (X '')\<close>
    by (auto intro!: commutant_memberI)
  from 1 2 show ?thesis
    by (auto simp flip: \<pi>_def)
qed

lemma amplification_double_commutant_commute':
  \<open>commutant (commutant ((\<lambda>a. id_cblinfun \<otimes>\<^sub>o a) ` X))
    = (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a) `  commutant (commutant X)\<close>
proof -
  have \<open>commutant (commutant ((\<lambda>a. id_cblinfun \<otimes>\<^sub>o a) ` X))
    = commutant (commutant (sandwich swap_ell2 ` (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) ` X))\<close>
    by (simp add: swap_tensor_op_sandwich image_image)
  also have \<open>\<dots> = sandwich swap_ell2 ` commutant (commutant ((\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) ` X))\<close>
    by (simp add: sandwich_unitary_complement)
  also have \<open>\<dots> = sandwich swap_ell2 ` (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) ` commutant (commutant X)\<close>
    by (simp add: amplification_double_commutant_commute)
  also have \<open>\<dots> = (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a) `  commutant (commutant X)\<close>
    by (simp add: swap_tensor_op_sandwich image_image)
  finally show ?thesis
    by -
qed

lemma commutant_one_algebra: \<open>commutant one_algebra = UNIV\<close>
  by (metis commutant_UNIV commutant_empty triple_commutant)

end
