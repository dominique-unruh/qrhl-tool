theory Missing_Bounded_Operators
  imports Complex_Bounded_Operators.Complex_L2
    Complex_Bounded_Operators.Cblinfun_Code
    Tensor_Product.Hilbert_Space_Tensor_Product
    With_Type.With_Type Misc_Missing
    Tensor_Product.Unsorted_HSTP
    Tensor_Product.Partial_Trace
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
  show \<open>dim_row (mat_of_cblinfun (explicit_cblinfun m)) = dim_row (Matrix.mat CARD('a) CARD('b) m')\<close>
    by (simp add: canonical_basis_length)
  show \<open>dim_col (mat_of_cblinfun (explicit_cblinfun m)) = dim_col (Matrix.mat CARD('a) CARD('b) m')\<close>
    by (simp add: canonical_basis_length)
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
  by (auto simp: mat_of_cblinfun_zero canonical_basis_length)

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

lemma Abs_ell2_code[code]: \<open>vec_of_ell2 (Abs_ell2 f) = vec CARD('a) (\<lambda>n. f (enum_nth n))\<close> for f :: \<open>'a::eenum \<Rightarrow> complex\<close>
  by (auto simp: vec_of_ell2_def vec_eq_iff vec_of_basis_enum_ell2_component)
lemma Rep_ell2_code[code]: \<open>Rep_ell2 \<psi> i = vec_of_ell2 \<psi> $ (enum_index i)\<close> for i :: \<open>'a::eenum\<close>
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





(* (* TODO: replace  *) thm continuous_map_left_comp_sot (* with this *)
lemma continuous_map_left_comp_sot[continuous_intros]: 
  assumes \<open>continuous_map T cstrong_operator_topology f\<close> 
  shows \<open>continuous_map T cstrong_operator_topology (\<lambda>x. b o\<^sub>C\<^sub>L f x)\<close> 
  by (fact continuous_map_compose[OF assms continuous_map_left_comp_sot, unfolded o_def])

(* TODO: replace  *) thm continuous_map_right_comp_sot (* with this *)
lemma continuous_map_right_comp_sot[continuous_intros]: 
  assumes \<open>continuous_map T cstrong_operator_topology f\<close> 
  shows \<open>continuous_map T cstrong_operator_topology (\<lambda>x. f x o\<^sub>C\<^sub>L a)\<close> 
  by (fact continuous_map_compose[OF assms continuous_map_right_comp_sot, unfolded o_def]) *)

lemmas sandwich_sot_continuous = sandwich_sot_cont
(* lemma sandwich_sot_continuous[continuous_intros]:
  assumes \<open>continuous_map T cstrong_operator_topology f\<close>
  shows \<open>continuous_map T cstrong_operator_topology (\<lambda>x. sandwich A (f x))\<close>
  unfolding sandwich_apply
  by (intro continuous_intros assms) *)


(*
NOT TRUE: https://mathoverflow.net/questions/445927/intersection-of-von-neumann-algebra-factors

 lemma von_neumann_factor_union:
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

lemma infsum_of_bool_scaleC: \<open>(\<Sum>\<^sub>\<infinity>x\<in>X. of_bool (x=y) *\<^sub>C f x) = of_bool (y\<in>X) *\<^sub>C f y\<close> for f :: \<open>_ \<Rightarrow> _::complex_vector\<close>
  apply (cases \<open>y\<in>X\<close>)
   apply (subst infsum_cong_neutral[where T=\<open>{y}\<close> and g=f])
      apply auto[4]
  apply (subst infsum_cong_neutral[where T=\<open>{}\<close> and g=f])
  by auto

lemma inj_selfbutter_ket:
  assumes "selfbutter (ket x) = selfbutter (ket y)"
  shows "x = y"
proof -
  have \<open>1 = norm (selfbutter (ket x) *\<^sub>V ket x)\<close>
    by auto
  also have \<open>\<dots> = norm (selfbutter (ket y) *\<^sub>V ket x)\<close>
    using assms by simp
  also have \<open>\<dots> = of_bool (x=y)\<close>
    by (simp add: cinner_ket)
  finally show ?thesis
    by simp
qed

instantiation cblinfun :: (chilbert_space, chilbert_space) Sup_order begin
definition \<open>Sup_cblinfun (X::('a\<Rightarrow>\<^sub>C\<^sub>L'b) set) = (SOME s. is_Sup X s)\<close>
definition \<open>sup_cblinfun (x::'a\<Rightarrow>\<^sub>C\<^sub>L'b) y = Sup {x,y}\<close>
instance
proof
  fix X :: \<open>('a\<Rightarrow>\<^sub>C\<^sub>L'b) set\<close> and x y :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
  show \<open>has_Sup X \<Longrightarrow> is_Sup X (\<Squnion> X)\<close>
    by (simp add: Sup_cblinfun_def has_Sup_def someI_ex)
  show \<open>has_Sup {x, y} \<Longrightarrow> is_Sup {x, y} (x \<squnion> y)\<close>
    by (simp add: Sup_cblinfun_def has_Sup_def someI_ex sup_cblinfun_def)
qed
end


(* TODO: Conway, operator, 43.1(i,ii), but translated to filters *)
(* TODO move *)
lemma monotone_convergence_wot:
  fixes f :: \<open>'b \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'a::chilbert_space)\<close>
  assumes bounded: \<open>\<forall>\<^sub>F x in F. f x \<le> B\<close>
  assumes pos: \<open>\<forall>\<^sub>F x in F. f x \<ge> 0\<close> (* TODO can be removed wlog *)
  assumes increasing: \<open>increasing_filter (filtermap f F)\<close>
  shows \<open>\<exists>L. limitin cweak_operator_topology f L F\<close>
proof (cases \<open>F = \<bottom>\<close>)
  case True
  then show ?thesis
    by (auto intro!: exI limitin_trivial)
next
  case False
  define surround where \<open>surround \<psi> a = \<psi> \<bullet>\<^sub>C (a *\<^sub>V \<psi>)\<close> for \<psi> :: 'a and a
  have mono_surround: \<open>mono (surround \<psi>)\<close> for \<psi>
    by (auto intro!: monoI simp: surround_def less_eq_cblinfun_def)
  obtain l' where  tendsto_l': \<open>((\<lambda>x. surround \<psi> (f x)) \<longlongrightarrow> l' \<psi>) F\<close>
    (* and l'_bound: \<open>norm (l' \<psi>) \<le> norm B * (norm \<psi>)\<^sup>2\<close> *) for \<psi>
  proof (atomize_elim, intro choice allI)
    fix \<psi> :: 'a
    from bounded
    have surround_bound: \<open>\<forall>\<^sub>F x in F. surround \<psi> (f x) \<le> surround \<psi> B\<close>
      unfolding surround_def
      apply (rule eventually_mono)
      by (simp add: less_eq_cblinfun_def)
    moreover have \<open>increasing_filter (filtermap (\<lambda>x. surround \<psi> (f x)) F)\<close>
      using increasing_filtermap[OF increasing mono_surround]
      by (simp add: filtermap_filtermap)
    ultimately obtain l' where \<open>((\<lambda>x. surround \<psi> (f x)) \<longlongrightarrow> l') F\<close>
      apply atomize_elim
      by (auto intro!: monotone_convergence_complex increasing mono_surround
          simp: eventually_filtermap)
(*     then have \<open>l' \<le> surround \<psi> B\<close>
      using surround_bound False by (rule tendsto_upperbound_complex)
    then have \<open>norm l' \<le> norm (surround \<psi> B)\<close>
      by -
    also have \<open>\<dots> \<le> norm B * (norm \<psi>)\<^sup>2\<close>
      using Cauchy_Schwarz_ineq2
      apply (auto intro!: simp: surround_def )
      by -
    finally have \<open>norm l' \<le> norm B * (norm \<psi>)\<^sup>2\<close>
      by simp
    with tendsto *)
    then show \<open>\<exists>l'. ((\<lambda>x. surround \<psi> (f x)) \<longlongrightarrow> l') F\<close>
      by auto
  qed
  define l where \<open>l \<phi> \<psi> = (l' (\<phi>+\<psi>) - l' (\<phi>-\<psi>) - \<i> * l' (\<phi> + \<i> *\<^sub>C \<psi>) + \<i> * l' (\<phi> - \<i> *\<^sub>C \<psi>)) / 4\<close> for \<phi> \<psi> :: 'a
(*   have \<open>norm (l \<phi> \<psi>) \<le> xxxx\<close> for \<phi> \<psi>
  proof -
    from l'_bound[of \<open>\<phi> + \<psi>\<close>]
    have \<open>norm (l' (\<phi> + \<psi>)) \<le> norm B * (norm \<phi> + norm \<psi>)\<^sup>2\<close>
      by (smt (verit, ccfv_SIG) mult_left_mono norm_ge_zero norm_triangle_ineq norm_zero power2_diff real_inner_class.parallelogram_law sum_squares_bound)
    moreover from l'_bound[of \<open>\<phi> - \<psi>\<close>]
    have \<open>norm (l' (\<phi> - \<psi>)) \<le> norm B * (norm \<phi> + norm \<psi>)\<^sup>2\<close>
      by (smt (verit, ccfv_SIG) mult_left_mono norm_ge_zero norm_triangle_ineq4 norm_zero power2_diff real_inner_class.parallelogram_law sum_squares_bound)
    moreover from l'_bound[of \<open>\<phi> + \<i> *\<^sub>C \<psi>\<close>]
    have \<open>norm (l' (\<phi> + \<i> *\<^sub>C \<psi>)) \<le> norm B * (norm \<phi> + norm \<psi>)\<^sup>2\<close>
      by -
    moreover from l'_bound[of \<open>\<phi> - \<i> *\<^sub>C \<psi>\<close>]
    have \<open>norm (l' (\<phi> - \<i> *\<^sub>C \<psi>)) \<le> norm B * (norm \<phi> + norm \<psi>)\<^sup>2\<close>
      by -
    ultimately have \<open>norm (l \<phi> \<psi>) \<le> norm B * (norm \<phi> + norm \<psi>)\<^sup>2\<close>
      apply (auto intro!: simp: l_def)
      by -
    also have \<open>\<dots> \<le> norm B * norm \<phi> * norm \<psi>\<close>
      (* ? ? ? *)
      apply (auto intro!: simp: l_def)
      by x
    show ?thesis
      by x
  qed *)
  have polar: \<open>\<phi> \<bullet>\<^sub>C a \<psi> = (surround (\<phi>+\<psi>) a - surround (\<phi>-\<psi>) a - \<i> * surround (\<phi> + \<i> *\<^sub>C \<psi>) a + \<i> * surround (\<phi> - \<i> *\<^sub>C \<psi>) a) / 4\<close> for a :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> and \<phi> \<psi>
    by (simp add: surround_def cblinfun.add_right cinner_add cblinfun.diff_right 
        cinner_diff cblinfun.scaleC_right ring_distribs)
  have tendsto_l: \<open>((\<lambda>x. \<phi> \<bullet>\<^sub>C f x \<psi>) \<longlongrightarrow> l \<phi> \<psi>) F\<close> for \<phi> \<psi>
    by (auto intro!: tendsto_divide tendsto_add tendsto_diff tendsto_l' simp: l_def polar)
  have l_bound: \<open>norm (l \<phi> \<psi>) \<le> norm B * norm \<phi> * norm \<psi>\<close> for \<phi> \<psi>
  proof -
    from bounded pos
    have \<open>\<forall>\<^sub>F x in F. norm (\<phi> \<bullet>\<^sub>C f x \<psi>) \<le> norm B * norm \<phi> * norm \<psi>\<close> for \<phi> \<psi>
    proof (rule eventually_elim2)
      fix x
      assume \<open>f x \<le> B\<close> and \<open>0 \<le> f x\<close>
      have \<open>cmod (\<phi> \<bullet>\<^sub>C (f x *\<^sub>V \<psi>)) \<le> norm \<phi> * norm (f x *\<^sub>V \<psi>)\<close>
        using complex_inner_class.Cauchy_Schwarz_ineq2 by blast
      also have \<open>\<dots> \<le> norm \<phi> * (norm (f x) * norm \<psi>)\<close>
        by (simp add: mult_left_mono norm_cblinfun)
      also from \<open>f x \<le> B\<close> \<open>0 \<le> f x\<close>
      have \<open>\<dots> \<le> norm \<phi> * (norm B * norm \<psi>)\<close>
        by (auto intro!: mult_left_mono mult_right_mono norm_cblinfun_mono simp: )
      also have \<open>\<dots> = norm B * norm \<phi> * norm \<psi>\<close>
        by simp
      finally show \<open>norm (\<phi> \<bullet>\<^sub>C f x \<psi>) \<le> norm B * norm \<phi> * norm \<psi>\<close>
        by -
    qed
    moreover from tendsto_l
    have \<open>((\<lambda>x. norm (\<phi> \<bullet>\<^sub>C f x \<psi>)) \<longlongrightarrow> norm (l \<phi> \<psi>)) F\<close> for \<phi> \<psi>
      using tendsto_norm by blast
    ultimately show ?thesis
      using False tendsto_upperbound by blast
  qed
  have \<open>bounded_sesquilinear l\<close>
  proof (rule bounded_sesquilinear.intro)
    fix \<phi> \<phi>' \<psi> \<psi>' and r :: complex
    from tendsto_l have \<open>((\<lambda>x. \<phi> \<bullet>\<^sub>C f x \<psi> + \<phi> \<bullet>\<^sub>C f x \<psi>') \<longlongrightarrow> l \<phi> \<psi> + l \<phi> \<psi>') F\<close>
      by (simp add: tendsto_add)
    moreover from tendsto_l have \<open>((\<lambda>x. \<phi> \<bullet>\<^sub>C f x \<psi> + \<phi> \<bullet>\<^sub>C f x \<psi>') \<longlongrightarrow> l \<phi> (\<psi> + \<psi>')) F\<close>
      by (simp flip: cinner_add_right cblinfun.add_right)
    ultimately show \<open>l \<phi> (\<psi> + \<psi>') = l \<phi> \<psi> + l \<phi> \<psi>'\<close>
      by (rule tendsto_unique[OF False, rotated])
    from tendsto_l have \<open>((\<lambda>x. \<phi> \<bullet>\<^sub>C f x \<psi> + \<phi>' \<bullet>\<^sub>C f x \<psi>) \<longlongrightarrow> l \<phi> \<psi> + l \<phi>' \<psi>) F\<close>
      by (simp add: tendsto_add)
    moreover from tendsto_l have \<open>((\<lambda>x. \<phi> \<bullet>\<^sub>C f x \<psi> + \<phi>' \<bullet>\<^sub>C f x \<psi>) \<longlongrightarrow> l (\<phi> + \<phi>') \<psi>) F\<close>
      by (simp flip: cinner_add_left cblinfun.add_left)
    ultimately show \<open>l (\<phi> + \<phi>') \<psi> = l \<phi> \<psi> + l \<phi>' \<psi>\<close>
      by (rule tendsto_unique[OF False, rotated])
    from tendsto_l have \<open>((\<lambda>x. r *\<^sub>C (\<phi> \<bullet>\<^sub>C f x \<psi>)) \<longlongrightarrow> r *\<^sub>C l \<phi> \<psi>) F\<close>
      using tendsto_scaleC by blast
    moreover from tendsto_l have \<open>((\<lambda>x. r *\<^sub>C (\<phi> \<bullet>\<^sub>C f x \<psi>)) \<longlongrightarrow> l \<phi> (r *\<^sub>C \<psi>)) F\<close>
      by (simp flip: cinner_scaleC_right cblinfun.scaleC_right)
    ultimately show \<open>l \<phi> (r *\<^sub>C \<psi>) = r *\<^sub>C l \<phi> \<psi>\<close>
      by (rule tendsto_unique[OF False, rotated])
    from tendsto_l have \<open>((\<lambda>x. cnj r *\<^sub>C (\<phi> \<bullet>\<^sub>C f x \<psi>)) \<longlongrightarrow> cnj r *\<^sub>C l \<phi> \<psi>) F\<close>
      using tendsto_scaleC by blast
    moreover from tendsto_l have \<open>((\<lambda>x. cnj r *\<^sub>C (\<phi> \<bullet>\<^sub>C f x \<psi>)) \<longlongrightarrow> l (r *\<^sub>C \<phi>) \<psi>) F\<close>
      by (simp flip: cinner_scaleC_left cblinfun.scaleC_left)
    ultimately show \<open>l (r *\<^sub>C \<phi>) \<psi> = cnj r *\<^sub>C l \<phi> \<psi>\<close>
      by (rule tendsto_unique[OF False, rotated])
    show \<open>\<exists>K. \<forall>a b. cmod (l a b) \<le> norm a * norm b * K\<close>
      using l_bound by (auto intro!: exI[of _ \<open>norm B\<close>] simp: mult_ac)
  qed
  define L where \<open>L = (the_riesz_rep_sesqui l)*\<close>
  then have \<open>\<phi> \<bullet>\<^sub>C L \<psi> = l \<phi> \<psi>\<close> for \<phi> \<psi>
    by (auto intro!: \<open>bounded_sesquilinear l\<close> the_riesz_rep_sesqui_apply simp: cinner_adj_right)
  with tendsto_l have \<open>((\<lambda>x. \<phi> \<bullet>\<^sub>C f x \<psi>) \<longlongrightarrow> \<phi> \<bullet>\<^sub>C L \<psi>) F\<close> for \<phi> \<psi>
    by simp
  then have \<open>limitin cweak_operator_topology f L F\<close>
    by (simp add: limitin_cweak_operator_topology)
  then show ?thesis
    by auto
qed

lemma summable_wot_boundedI:
  fixes f :: \<open>'b \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'a::chilbert_space)\<close>
  assumes bounded: \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> X \<Longrightarrow> sum f F \<le> B\<close>
  assumes pos: \<open>\<And>x. x \<in> X \<Longrightarrow> f x \<ge> 0\<close>
  shows \<open>summable_on_in cweak_operator_topology f X\<close>
proof -
  have pos': \<open>(\<Sum>x\<in>F. f x) \<ge> 0\<close> if \<open>finite F\<close> and \<open>F \<subseteq> X\<close> for F
    using that pos
    by (simp add: basic_trans_rules(31) sum_nonneg)
  from pos have incr: \<open>increasing_filter (filtermap (sum f) (finite_subsets_at_top X))\<close>
    by (auto intro!: increasing_filtermap[where X=\<open>{F. finite F \<and> F \<subseteq> X}\<close>] mono_onI sum_mono2)
  show ?thesis
    apply (simp add: summable_on_in_def has_sum_in_def) 
    by (safe intro!: bounded pos' incr monotone_convergence_wot[where B=B] eventually_finite_subsets_at_top_weakI)
qed

instantiation cblinfun_wot :: (chilbert_space, chilbert_space) order begin
lift_definition less_eq_cblinfun_wot :: \<open>('a, 'b) cblinfun_wot \<Rightarrow> ('a, 'b) cblinfun_wot \<Rightarrow> bool\<close> is less_eq.
lift_definition less_cblinfun_wot :: \<open>('a, 'b) cblinfun_wot \<Rightarrow> ('a, 'b) cblinfun_wot \<Rightarrow> bool\<close> is less.
instance
  apply (intro_classes; transfer')
  by auto
end

lemma is_Sup_wot_transfer[transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_set cr_cblinfun_wot ===> cr_cblinfun_wot ===> (\<longleftrightarrow>)) is_Sup is_Sup\<close>
  apply (simp add: is_Sup_def[abs_def])
  by transfer_prover

lemma has_Sup_wot_transfer[transfer_rule]:
  includes lifting_syntax
  shows \<open>(rel_set cr_cblinfun_wot ===> (\<longleftrightarrow>)) has_Sup has_Sup\<close>
  apply (simp add: has_Sup_def[abs_def])
  by transfer_prover

instantiation cblinfun_wot :: (chilbert_space, chilbert_space) Sup_order begin
lift_definition sup_cblinfun_wot :: \<open>('a, 'b) cblinfun_wot \<Rightarrow> ('a, 'b) cblinfun_wot \<Rightarrow> ('a, 'b) cblinfun_wot\<close> is sup.
lift_definition Sup_cblinfun_wot :: \<open>('a, 'b) cblinfun_wot set \<Rightarrow> ('a, 'b) cblinfun_wot\<close> is Sup.
instance
  apply (intro_classes; transfer')
  by (auto intro!: is_Sup_Sup is_Sup_sup simp: )
end

instance cblinfun_wot :: (complex_normed_vector, complex_inner) topological_ab_group_add
  by intro_classes

lemma infsum_wot_is_Sup:
  fixes f :: \<open>'b \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'a::chilbert_space)\<close>
  (* assumes bounded: \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> X \<Longrightarrow> sum f F \<le> B\<close> *)
  assumes summable: \<open>summable_on_in cweak_operator_topology f X\<close>
    \<comment> \<open>See also @{thm [source] summable_wot_boundedI} for proving this.\<close>
  assumes pos: \<open>\<And>x. x \<in> X \<Longrightarrow> f x \<ge> 0\<close>
  defines \<open>S \<equiv> infsum_in cweak_operator_topology f X\<close>
  shows \<open>is_Sup ((\<lambda>F. \<Sum>x\<in>F. f x) ` {F. finite F \<and> F \<subseteq> X}) S\<close>
proof (rule is_SupI)
  have has_sum: \<open>has_sum_in cweak_operator_topology f X S\<close>
    unfolding S_def
    apply (rule has_sum_in_infsum_in)
    using assms by auto
  show \<open>s \<le> S\<close> if \<open>s \<in> ((\<lambda>F. \<Sum>x\<in>F. f x) ` {F. finite F \<and> F \<subseteq> X})\<close> for s
  proof -
    from that obtain F where [simp]: \<open>finite F\<close> and \<open>F \<subseteq> X\<close> and s_def: \<open>s = (\<Sum>x\<in>F. f x)\<close>
      by auto
    show ?thesis
    proof (rule has_sum_mono_neutral_wot)
      show \<open>has_sum_in cweak_operator_topology f F s\<close>
        by (auto intro!: has_sum_in_finite simp: s_def)
      show \<open>has_sum_in cweak_operator_topology f X S\<close>
        by (fact has_sum)
      show \<open>f x \<le> f x\<close> for x
        by simp
      show \<open>f x \<le> 0\<close> if \<open>x \<in> F - X\<close> for x
        using \<open>F \<subseteq> X\<close> that by auto
      show \<open>f x \<ge> 0\<close> if \<open>x \<in> X - F\<close> for x
        using that pos by auto
    qed
  qed
  show \<open>S \<le> y\<close>
    if y_bound: \<open>\<And>x. x \<in> ((\<lambda>F. \<Sum>x\<in>F. f x) ` {F. finite F \<and> F \<subseteq> X}) \<Longrightarrow> x \<le> y\<close> for y
  proof (rule cblinfun_leI, rename_tac \<psi>)
    fix \<psi> :: 'a
    define g where \<open>g x = \<psi> \<bullet>\<^sub>C Rep_cblinfun_wot x \<psi>\<close> for x
    from has_sum have lim: \<open>((\<lambda>i. \<psi> \<bullet>\<^sub>C ((\<Sum>x\<in>i. f x) *\<^sub>V \<psi>)) \<longlongrightarrow> \<psi> \<bullet>\<^sub>C (S *\<^sub>V \<psi>)) (finite_subsets_at_top X)\<close>
      by (simp add: has_sum_in_def limitin_cweak_operator_topology)
    have bound: \<open>\<psi> \<bullet>\<^sub>C (\<Sum>x\<in>F. f x) \<psi> \<le> \<psi> \<bullet>\<^sub>C y \<psi>\<close> if \<open>finite F\<close> \<open>F \<subseteq> X\<close> for F
      using y_bound less_eq_cblinfun_def that(1) that(2) by fastforce
    show \<open>\<psi> \<bullet>\<^sub>C (S *\<^sub>V \<psi>) \<le> \<psi> \<bullet>\<^sub>C y \<psi>\<close>
      using finite_subsets_at_top_neq_bot tendsto_const lim apply (rule tendsto_le_complex)
      using bound by (auto intro!: eventually_finite_subsets_at_top_weakI)
  qed
qed

lemma summable_wot_bdd_above:
  fixes f :: \<open>'b \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'a::chilbert_space)\<close>
  assumes summable: \<open>summable_on_in cweak_operator_topology f X\<close>
    \<comment> \<open>See also @{thm [source] summable_wot_boundedI} for proving this.\<close>
  assumes pos: \<open>\<And>x. x \<in> X \<Longrightarrow> f x \<ge> 0\<close>
  shows \<open>bdd_above (sum f ` {F. finite F \<and> F \<subseteq> X})\<close>
  using infsum_wot_is_Sup[OF assms]
  by (auto intro!: simp: is_Sup_def bdd_above_def)

(* TODO move *)
lemma trace_comp_pos:
  fixes a b :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>trace_class b\<close>
  assumes \<open>a \<ge> 0\<close> and \<open>b \<ge> 0\<close>
  shows \<open>trace (a o\<^sub>C\<^sub>L b) \<ge> 0\<close>
proof -
  obtain c :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> where \<open>a = c* o\<^sub>C\<^sub>L c\<close>
  by (metis assms(2) positive_hermitianI sqrt_op_pos sqrt_op_square)
  then have \<open>trace (a o\<^sub>C\<^sub>L b) = trace (sandwich c b)\<close>
    by (simp add: sandwich_apply assms(1) cblinfun_assoc_left(1) circularity_of_trace trace_class_comp_right)
  also have \<open>\<dots> \<ge> 0\<close>
    by (auto intro!: trace_pos sandwich_pos assms)
  finally show ?thesis
    by -
qed

lemma has_sum_in_cweak_operator_topology_pointwise:
  \<open>has_sum_in cweak_operator_topology f X s \<longleftrightarrow> (\<forall>\<psi> \<phi>. ((\<lambda>x. \<psi> \<bullet>\<^sub>C f x \<phi>) has_sum \<psi> \<bullet>\<^sub>C s \<phi>) X)\<close>
  by (simp add: has_sum_in_def has_sum_def limitin_cweak_operator_topology
      cblinfun.sum_left cinner_sum_right)


lemma has_sum_on_wot_transfer[transfer_rule]:
  includes lifting_syntax
  shows \<open>(((=) ===> cr_cblinfun_wot) ===> (=) ===> cr_cblinfun_wot ===> (\<longleftrightarrow>)) (has_sum_in cweak_operator_topology) HAS_SUM\<close>
  unfolding has_sum_euclidean_iff[abs_def, symmetric] has_sum_in_def[abs_def]
  by transfer_prover

lemma summable_on_wot_transfer[transfer_rule]:
  includes lifting_syntax
  shows \<open>(((=) ===> cr_cblinfun_wot) ===> (=) ===> (\<longleftrightarrow>)) (summable_on_in cweak_operator_topology) (summable_on)\<close>
  apply (auto intro!: simp: summable_on_def[abs_def] summable_on_in_def[abs_def])
  by transfer_prover

lemma Abs_cblinfun_wot_transfer[transfer_rule]:
  includes lifting_syntax
  shows \<open>((=) ===> cr_cblinfun_wot) id Abs_cblinfun_wot\<close>
  by (auto intro!: rel_funI simp: cr_cblinfun_wot_def Abs_cblinfun_wot_inverse)

(* TODO move *)
lemma trace_norm_tensor: \<open>trace_norm (a \<otimes>\<^sub>o b) = trace_norm a * trace_norm b\<close>
  apply (rule of_real_hom.injectivity[where 'a=complex])
  by (simp add: abs_op_tensor trace_tensor flip: trace_abs_op)


(* TODO move *)
lemma bounded_cbilinear_tc_tensor: \<open>bounded_cbilinear tc_tensor\<close>
  unfolding bounded_cbilinear_def
  apply transfer
  by (auto intro!: exI[of _ 1]
      simp: trace_norm_tensor tensor_op_left_add tensor_op_right_add tensor_op_scaleC_left tensor_op_scaleC_right)
lemmas bounded_clinear_tc_tensor_left[bounded_clinear] = bounded_cbilinear.bounded_clinear_left[OF bounded_cbilinear_tc_tensor]
lemmas bounded_clinear_tc_tensor_right[bounded_clinear] = bounded_cbilinear.bounded_clinear_right[OF bounded_cbilinear_tc_tensor]


(* TODO move *)
lemma bounded_cbilinear_tc_compose: \<open>bounded_cbilinear tc_compose\<close>
  unfolding bounded_cbilinear_def
  apply transfer
  apply (auto intro!: exI[of _ 1] simp: cblinfun_compose_add_left cblinfun_compose_add_right)
  by (meson Unsorted_HSTP.norm_leq_trace_norm dual_order.trans mult_right_mono trace_norm_comp_right trace_norm_nneg)
lemmas bounded_clinear_tc_compose_left[bounded_clinear] = bounded_cbilinear.bounded_clinear_left[OF bounded_cbilinear_tc_compose]
lemmas bounded_clinear_tc_compose_right[bounded_clinear] = bounded_cbilinear.bounded_clinear_right[OF bounded_cbilinear_tc_compose]

lemma abs_op_one_dim: \<open>abs_op x = one_dim_iso (abs (one_dim_iso x :: complex))\<close>
  by (metis (mono_tags, lifting) abs_opI abs_op_scaleC of_complex_def one_cblinfun_adj one_comp_one_cblinfun one_dim_iso_is_of_complex one_dim_iso_of_one one_dim_iso_of_zero one_dim_loewner_order one_dim_scaleC_1 zero_less_one_class.zero_le_one)

lemma trace_norm_one_dim: \<open>trace_norm x = cmod (one_dim_iso x)\<close>
  apply (rule of_real_hom.injectivity[where 'a=complex])
  apply (simp add: abs_op_one_dim flip: trace_abs_op)
  by (simp add: abs_complex_def)

instantiation trace_class :: (one_dim, one_dim) complex_inner begin
lift_definition cinner_trace_class :: \<open>('a, 'b) trace_class \<Rightarrow> ('a, 'b) trace_class \<Rightarrow> complex\<close> is \<open>(\<bullet>\<^sub>C)\<close>.
instance
proof intro_classes
  fix x y z :: \<open>('a, 'b) trace_class\<close>
  show \<open>x \<bullet>\<^sub>C y = cnj (y \<bullet>\<^sub>C x)\<close>
    apply transfer'
    by simp
  show \<open>(x + y) \<bullet>\<^sub>C z = x \<bullet>\<^sub>C z + y \<bullet>\<^sub>C z\<close>
    apply transfer'
    by (simp add: cinner_simps)
  show \<open>r *\<^sub>C x \<bullet>\<^sub>C y = cnj r * (x \<bullet>\<^sub>C y)\<close> for r
    apply (transfer' fixing: r)
    using cinner_simps by blast
  show \<open>0 \<le> x \<bullet>\<^sub>C x\<close>
    apply transfer'
    by simp
  show \<open>(x \<bullet>\<^sub>C x = 0) = (x = 0)\<close>
    apply transfer'
    by auto
  show \<open>norm x = sqrt (cmod (x \<bullet>\<^sub>C x))\<close>
  proof transfer'
    fix x :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
    define c :: complex where \<open>c = one_dim_iso x\<close>
    then have xc: \<open>x = c *\<^sub>C 1\<close>
      by simp
    have \<open>trace_norm x = norm c\<close>
      by (simp add: trace_norm_one_dim xc)
    also have \<open>norm c = sqrt (cmod (x \<bullet>\<^sub>C x))\<close>
      by (metis inner_real_def norm_eq_sqrt_cinner norm_one norm_scaleC real_inner_1_right xc)
    finally show \<open>trace_norm x = sqrt (cmod (x \<bullet>\<^sub>C x)) \<close>
      by (simp add: cinner_cblinfun_def)
  qed
qed
end


(* TODO move *)
instantiation trace_class :: (one_dim, one_dim) one_dim begin
lift_definition one_trace_class :: \<open>('a, 'b) trace_class\<close> is 1
  by auto
lift_definition times_trace_class :: \<open>('a, 'b) trace_class \<Rightarrow> ('a, 'b) trace_class \<Rightarrow> ('a, 'b) trace_class\<close> is \<open>(*)\<close>
  by auto
lift_definition divide_trace_class :: \<open>('a, 'b) trace_class \<Rightarrow> ('a, 'b) trace_class \<Rightarrow> ('a, 'b) trace_class\<close> is \<open>(/)\<close>
  by auto
lift_definition inverse_trace_class :: \<open>('a, 'b) trace_class \<Rightarrow> ('a, 'b) trace_class\<close> is \<open>Fields.inverse\<close>
  by auto
definition canonical_basis_trace_class :: \<open>('a, 'b) trace_class list\<close> where \<open>canonical_basis_trace_class = [1]\<close>
definition canonical_basis_length_trace_class :: \<open>('a, 'b) trace_class itself \<Rightarrow> nat\<close> where \<open>canonical_basis_length_trace_class = 1\<close>
instance
proof intro_classes
  fix x y z :: \<open>('a, 'b) trace_class\<close>
  have [simp]: \<open>1 \<noteq> (0 :: ('a, 'b) trace_class)\<close>
    using one_trace_class.rep_eq by force
  then have [simp]: \<open>0 \<noteq> (1 :: ('a, 'b) trace_class)\<close>
    by force
  show \<open>distinct (canonical_basis :: (_,_) trace_class list)\<close>
    by (simp add: canonical_basis_trace_class_def)
  show \<open>cindependent (set canonical_basis :: (_,_) trace_class set)\<close>
    by (simp add: canonical_basis_trace_class_def)
  show \<open>canonical_basis_length TYPE(('a, 'b) trace_class) = length (canonical_basis :: (_,_) trace_class list)\<close>
    by (simp add: canonical_basis_length_trace_class_def canonical_basis_trace_class_def)
  show \<open>x \<in> set canonical_basis \<Longrightarrow> norm x = 1\<close>
    apply (simp add: canonical_basis_trace_class_def)
    by (smt (verit, ccfv_threshold) one_trace_class_def cinner_trace_class.abs_eq cnorm_eq_1 one_cinner_one one_trace_class.rsp)
  show \<open>canonical_basis = [1 :: ('a,'b) trace_class]\<close>
    by (simp add: canonical_basis_trace_class_def)
  show \<open>a *\<^sub>C 1 * b *\<^sub>C 1 = (a * b) *\<^sub>C (1 :: ('a,'b) trace_class)\<close> for a b :: complex
    apply (transfer' fixing: a b)
    by simp
  show \<open>x div y = x * inverse y\<close>
    apply transfer'
    by (simp add: divide_cblinfun_def)
  show \<open>inverse (a *\<^sub>C 1 :: ('a,'b) trace_class) = 1 /\<^sub>C a\<close> for a :: complex
    apply transfer'
    by simp
  show \<open>is_ortho_set (set canonical_basis :: ('a,'b) trace_class set)\<close>
    by (simp add: is_ortho_set_def canonical_basis_trace_class_def)
  show \<open>cspan (set canonical_basis :: ('a,'b) trace_class set) = UNIV\<close>
  proof (intro Set.set_eqI iffI UNIV_I)
    fix x :: \<open>('a,'b) trace_class\<close>
    have \<open>\<exists>c. y = c *\<^sub>C 1\<close> for y :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
      apply (rule exI[where x=\<open>one_dim_iso y\<close>])
      by simp
    then obtain c where \<open>x = c *\<^sub>C 1\<close>
      apply transfer'
      by auto
    then show \<open>x \<in> cspan (set canonical_basis)\<close>
      by (auto intro!: complex_vector.span_base complex_vector.span_clauses
          simp: canonical_basis_trace_class_def)
  qed
qed
end

lemma from_trace_class_one_dim_iso[simp]: \<open>from_trace_class = one_dim_iso\<close>
proof (rule ext)
  fix x:: \<open>('a, 'b) trace_class\<close>
  have \<open>from_trace_class x = from_trace_class (one_dim_iso x *\<^sub>C 1)\<close>
    by simp
  also have \<open>\<dots> = one_dim_iso x *\<^sub>C from_trace_class 1\<close>
    using scaleC_trace_class.rep_eq by blast
  also have \<open>\<dots> = one_dim_iso x *\<^sub>C 1\<close>
    by (simp add: one_trace_class.rep_eq)
  also have \<open>\<dots> = one_dim_iso x\<close>
    by simp
  finally show \<open>from_trace_class x = one_dim_iso x\<close>
    by -
qed


lemma trace_tc_one_dim_iso[simp]: \<open>trace_tc = one_dim_iso\<close>
  by (simp add: trace_tc.rep_eq[abs_def])

lemma compose_tcr_id_left[simp]: \<open>compose_tcr id_cblinfun t = t\<close>
  by (auto intro!: from_trace_class_inject[THEN iffD1] simp: compose_tcr.rep_eq)

lemma compose_tcl_id_right[simp]: \<open>compose_tcl t id_cblinfun = t\<close>
  by (auto intro!: from_trace_class_inject[THEN iffD1] simp: compose_tcl.rep_eq)

lemma sandwich_tc_id_cblinfun[simp]: \<open>sandwich_tc id_cblinfun t = t\<close>
  by (simp add: from_trace_class_inverse sandwich_tc_def)

(* TODO move *)
(* TODO: generalize original is_ortho_set_ket to this *) thm is_ortho_set_ket 
lemma is_ortho_set_ket[simp]: \<open>is_ortho_set (ket ` A)\<close>
  using is_ortho_set_def by fastforce

lemma is_Proj_butterfly_ket: \<open>is_Proj (\<Sum>x\<in>M. selfbutter (ket x))\<close>
  apply (subst sum.reindex[symmetric, unfolded o_def, of ket])
  by (auto intro!: inj_onI sum_butterfly_is_Proj simp: )

(* TODO move *)
lemma infsum_cblinfun_compose_left:
  assumes \<open>b summable_on X\<close>
  shows \<open>(\<Sum>\<^sub>\<infinity>x\<in>X. a o\<^sub>C\<^sub>L b x) = a o\<^sub>C\<^sub>L (\<Sum>\<^sub>\<infinity>x\<in>X. b x)\<close>
  apply (subst infsum_bounded_linear[symmetric, where g=b and S=X and f=\<open>\<lambda>b. a o\<^sub>C\<^sub>L b\<close>])
  by (auto intro!: bounded_clinear.bounded_linear bounded_clinear_cblinfun_compose_right simp add: assms o_def)
lemma infsum_cblinfun_compose_right:
  assumes \<open>a summable_on X\<close>
  shows \<open>(\<Sum>\<^sub>\<infinity>x\<in>X. a x o\<^sub>C\<^sub>L b) = (\<Sum>\<^sub>\<infinity>x\<in>X. a x) o\<^sub>C\<^sub>L b\<close>
  apply (subst infsum_bounded_linear[symmetric, where g=a and S=X and f=\<open>\<lambda>a. a o\<^sub>C\<^sub>L b\<close>])
  by (auto intro!: bounded_clinear.bounded_linear bounded_clinear_cblinfun_compose_left simp add: assms o_def)

(* TODO move *)
lemma summable_cblinfun_compose_left:
  assumes \<open>b summable_on X\<close>
  shows \<open>(\<lambda>x. a o\<^sub>C\<^sub>L b x) summable_on X\<close>
  apply (rule Infinite_Sum.summable_on_bounded_linear[where h=\<open>\<lambda>b. a o\<^sub>C\<^sub>L b\<close>])
  by (auto intro!: bounded_clinear.bounded_linear bounded_clinear_cblinfun_compose_right simp add: assms o_def)
lemma summable_cblinfun_compose_right:
  assumes \<open>a summable_on X\<close>
  shows \<open>(\<lambda>x. a x o\<^sub>C\<^sub>L b) summable_on X\<close>
  apply (rule Infinite_Sum.summable_on_bounded_linear[where h=\<open>\<lambda>a. a o\<^sub>C\<^sub>L b\<close>])
  by (auto intro!: bounded_clinear.bounded_linear bounded_clinear_cblinfun_compose_left simp add: assms o_def)


(* TODO move *)
lemma from_trace_class_abs_summable: \<open>f abs_summable_on X \<Longrightarrow> (\<lambda>x. from_trace_class (f x)) abs_summable_on X\<close>
    apply (rule abs_summable_on_comparison_test[where g=\<open>f\<close>])
    by (simp_all add: Unsorted_HSTP.norm_leq_trace_norm norm_trace_class.rep_eq)

(* TODO move *)
lemma from_trace_class_summable: \<open>f summable_on X \<Longrightarrow> (\<lambda>x. from_trace_class (f x)) summable_on X\<close>
  apply (rule Infinite_Sum.summable_on_bounded_linear[where h=from_trace_class])
  by (simp_all add: bounded_clinear.bounded_linear bounded_clinear_from_trace_class)

(* TODO move *)
lemma from_trace_class_infsum: 
  assumes \<open>f summable_on UNIV\<close>
  shows \<open>from_trace_class (\<Sum>\<^sub>\<infinity>x. f x) = (\<Sum>\<^sub>\<infinity>x. from_trace_class (f x))\<close>
  apply (rule infsum_bounded_linear_strong[symmetric])
  using assms
  by (auto intro!: bounded_clinear.bounded_linear bounded_clinear_from_trace_class from_trace_class_summable)


(* TODO move *)
lemma is_Proj_leq_id: \<open>is_Proj P \<Longrightarrow> P \<le> id_cblinfun\<close>
  by (metis diff_ge_0_iff_ge is_Proj_algebraic is_Proj_complement positive_cblinfun_squareI)

lemma sum_butterfly_leq_id: 
  assumes \<open>is_ortho_set E\<close>
  assumes \<open>\<And>e. e\<in>E \<Longrightarrow> norm e = 1\<close>
  shows \<open>(\<Sum>i\<in>E. butterfly i i) \<le> id_cblinfun\<close>
proof -
  have \<open>is_Proj (\<Sum>\<psi>\<in>E. butterfly \<psi> \<psi>)\<close>
    using assms by (rule sum_butterfly_is_Proj)
  then show ?thesis
    by (auto intro!: is_Proj_leq_id)
qed

lemma tc_tensor_0_left[simp]: \<open>tc_tensor 0 x = 0\<close>
  apply transfer' by simp
lemma tc_tensor_0_right[simp]: \<open>tc_tensor x 0 = 0\<close>
  apply transfer' by simp

lemma compact_op_comp_right: \<open>compact_op (a o\<^sub>C\<^sub>L b)\<close> if \<open>compact_op b\<close>
  for a b :: \<open>_::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L _::chilbert_space\<close>
proof -
  from that have \<open>b \<in> closure (Collect finite_rank)\<close>
  using compact_op_finite_rank by blast
  then have \<open>a o\<^sub>C\<^sub>L b \<in> cblinfun_compose a ` closure (Collect finite_rank)\<close>
    by blast
  also have \<open>\<dots> \<subseteq> closure (cblinfun_compose a ` Collect finite_rank)\<close>
    by (auto intro!: closure_bounded_linear_image_subset bounded_clinear.bounded_linear bounded_clinear_cblinfun_compose_right)
  also have \<open>\<dots> \<subseteq> closure (Collect finite_rank)\<close>
    by (auto intro!: closure_mono finite_rank_comp_right)
  finally show \<open>compact_op (a o\<^sub>C\<^sub>L b)\<close>
    using compact_op_finite_rank by blast
qed

lemma norm_cblinfun_bound_unit: "norm f \<le> b"
  if \<open>0 \<le> b\<close> and \<open>\<And>x. norm x = 1 \<Longrightarrow> norm (f *\<^sub>V x) \<le> b\<close>
proof (rule norm_cblinfun_bound)
  show \<open>0 \<le> b\<close> by (fact that)
  show \<open>norm (f *\<^sub>V x) \<le> b * norm x\<close> for x
  proof (cases \<open>x = 0\<close>)
    case True
    then show ?thesis by simp
  next
    case False
    then have \<open>norm (f *\<^sub>V x) = norm (f *\<^sub>V sgn x) * norm x\<close>
      by (simp add: sgn_div_norm cblinfun.scaleR_right)
    also have \<open>\<dots> \<le> b * norm x\<close>
      by (auto intro!: mult_right_mono that simp: False norm_sgn)
    finally show ?thesis
      by -
  qed
qed

lemma cspan_trace_class:
  \<open>cspan (Collect trace_class :: ('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space) set) = Collect trace_class\<close>
proof (intro Set.set_eqI iffI)
  fix x :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
  show \<open>x \<in> Collect trace_class \<Longrightarrow> x \<in> cspan (Collect trace_class)\<close>
    by (simp add: complex_vector.span_clauses)
  assume \<open>x \<in> cspan (Collect trace_class)\<close>
  then obtain F f where x_def: \<open>x = (\<Sum>a\<in>F. f a *\<^sub>C a)\<close> and \<open>F \<subseteq> Collect trace_class\<close>
    by (auto intro!: simp: complex_vector.span_explicit)
  then have \<open>trace_class x\<close>
    by (auto intro!: trace_class_sum trace_class_scaleC simp: x_def)
  then show \<open>x \<in> Collect trace_class \<close>
    by simp
qed

definition diagonal_operator where \<open>diagonal_operator f = 
  (if bdd_above (range (\<lambda>x. cmod (f x))) then explicit_cblinfun (\<lambda>x y. of_bool (x=y) * f x) else 0)\<close>

lemma diagonal_operator_exists:
  assumes \<open>bdd_above (range (\<lambda>x. cmod (f x)))\<close>
  shows \<open>explicit_cblinfun_exists (\<lambda>x y. of_bool (x = y) * f x)\<close>
proof -
  from assms obtain B where B: \<open>cmod (f x) \<le> B\<close> for x
    by (auto simp: bdd_above_def)
  show ?thesis
  proof (rule explicit_cblinfun_exists_bounded)
    fix S T :: \<open>'a set\<close> and \<psi> :: \<open>'a \<Rightarrow> complex\<close>
    assume [simp]: \<open>finite S\<close> \<open>finite T\<close>
    assume \<open>\<psi> a = 0\<close> if \<open>a \<notin> T\<close> for a
    have \<open>(\<Sum>b\<in>S. (cmod (\<Sum>a\<in>T. \<psi> a *\<^sub>C (of_bool (b = a) * f b)))\<^sup>2)
        = (\<Sum>b\<in>S. (cmod (of_bool (b \<in> T) * \<psi> b * f b))\<^sup>2)\<close>
      apply (rule sum.cong[OF refl])
      subgoal for b
        apply (subst sum_single[where i=b])
        by auto
      by -
    also have \<open>\<dots> = (\<Sum>b\<in>S\<inter>T. (cmod (\<psi> b * f b))\<^sup>2)\<close>
      apply (rule sum.mono_neutral_cong_right)
      by auto
    also have \<open>\<dots> \<le> (\<Sum>b\<in>T. (cmod (\<psi> b * f b))\<^sup>2)\<close>
      by (simp add: sum_mono2)
    also have \<open>\<dots> \<le> (\<Sum>b\<in>T. B\<^sup>2 * (cmod (\<psi> b))\<^sup>2)\<close>
      apply (rule sum_mono)
      apply (auto intro!: simp: norm_mult power_mult_distrib)
      apply (subst mult.commute)
      by (simp add: B mult_right_mono power_mono)
    also have \<open>\<dots> = B\<^sup>2 * (\<Sum>b\<in>T. (cmod (\<psi> b))\<^sup>2)\<close>
      by (simp add: vector_space_over_itself.scale_sum_right)
    finally
    show \<open>(\<Sum>b\<in>S. (cmod (\<Sum>a\<in>T. \<psi> a *\<^sub>C (of_bool (b = a) * f b)))\<^sup>2)
       \<le> B\<^sup>2 * (\<Sum>a\<in>T. (cmod (\<psi> a))\<^sup>2)\<close>
      by -
  qed
qed

lemma diagonal_operator_ket:
  assumes \<open>bdd_above (range (\<lambda>x. cmod (f x)))\<close>
  shows \<open>diagonal_operator f (ket x) = f x *\<^sub>C ket x\<close>
proof -
  have [simp]: \<open>has_ell2_norm (\<lambda>b. of_bool (b = x) * f b)\<close>
    by (auto intro!: finite_nonzero_values_imp_summable_on simp: has_ell2_norm_def)
  have \<open>Abs_ell2 (\<lambda>b. of_bool (b = x) * f b) = f x *\<^sub>C ket x\<close>
    apply (rule Rep_ell2_inject[THEN iffD1])
    by (auto simp: Abs_ell2_inverse scaleC_ell2.rep_eq ket.rep_eq)
  then show ?thesis
    by (auto intro!: simp: diagonal_operator_def assms explicit_cblinfun_ket diagonal_operator_exists)
qed

lemma diagonal_operator_invalid:
  assumes \<open>\<not> bdd_above (range (\<lambda>x. cmod (f x)))\<close>
  shows \<open>diagonal_operator f = 0\<close>
  by (simp add: assms diagonal_operator_def)

lemma diagonal_operator_comp:
  assumes \<open>bdd_above (range (\<lambda>x. cmod (f x)))\<close>
  assumes \<open>bdd_above (range (\<lambda>x. cmod (g x)))\<close>
  shows \<open>diagonal_operator f o\<^sub>C\<^sub>L diagonal_operator g = diagonal_operator (\<lambda>x. (f x * g x))\<close>
proof -
  have \<open>bdd_above (range (\<lambda>x. cmod (f x * g x)))\<close>
  proof -
    from assms(1) obtain F where \<open>cmod (f x) \<le> F\<close> for x
      by (auto simp: bdd_above_def)
    moreover from assms(2) obtain G where \<open>cmod (g x) \<le> G\<close> for x
      by (auto simp: bdd_above_def)
    ultimately have \<open>cmod (f x * g x) \<le> F * G\<close> for x
      by (smt (verit, del_insts) mult_right_mono norm_ge_zero norm_mult ordered_comm_semiring_class.comm_mult_left_mono)
    then show ?thesis
      by fast
  qed
  then show ?thesis
    by (auto intro!: equal_ket simp: diagonal_operator_ket assms cblinfun.scaleC_right)
qed

lemma diagonal_operator_adj: \<open>diagonal_operator f* = diagonal_operator (\<lambda>x. cnj (f x))\<close>
  apply (cases \<open>bdd_above (range (\<lambda>x. cmod (f x)))\<close>)
  by (auto intro!: equal_ket cinner_ket_eqI 
      simp: diagonal_operator_ket cinner_adj_right diagonal_operator_invalid)


lemma diagonal_operator_pos:
  assumes \<open>\<And>x. f x \<ge> 0\<close>
  shows \<open>diagonal_operator f \<ge> 0\<close>
proof (cases \<open>bdd_above (range (\<lambda>x. cmod (f x)))\<close>)
  case True
  have [simp]: \<open>csqrt (f x) = sqrt (cmod (f x))\<close> for x
    by (simp add: Extra_Ordered_Fields.complex_of_real_cmod assms of_real_sqrt)
  have bdd: \<open>bdd_above (range (\<lambda>x. sqrt (cmod (f x))))\<close>
  proof -
    from True obtain B where \<open>cmod (f x) \<le> B\<close> for x
      by (auto simp: bdd_above_def)
    then show ?thesis
      by (auto intro!: bdd_aboveI[where M=\<open>sqrt B\<close>] simp: )
  qed
  show ?thesis
    apply (rule positive_cblinfun_squareI[where B=\<open>diagonal_operator (\<lambda>x. csqrt (f x))\<close>])
    by (simp add: assms diagonal_operator_adj diagonal_operator_comp bdd complex_of_real_cmod abs_pos
        flip: of_real_mult)
next
  case False
  then show ?thesis
    by (simp add: diagonal_operator_invalid)
qed



lemma abs_op_diagonal_operator: 
  \<open>abs_op (diagonal_operator f) = diagonal_operator (\<lambda>x. abs (f x))\<close>
proof (cases \<open>bdd_above (range (\<lambda>x. cmod (f x)))\<close>)
  case True
  show ?thesis
    apply (rule abs_opI[symmetric])
    by (auto intro!: diagonal_operator_pos abs_nn simp: True diagonal_operator_adj diagonal_operator_comp cnj_x_x)
next
  case False
  then show ?thesis
    by (simp add: diagonal_operator_invalid)
qed

lift_definition diagonal_operator_tc :: \<open>('a \<Rightarrow> complex) \<Rightarrow> ('a ell2, 'a ell2) trace_class\<close> is
  \<open>\<lambda>f. if f abs_summable_on UNIV then diagonal_operator f else 0\<close>
proof (rule CollectI)
  fix f :: \<open>'a \<Rightarrow> complex\<close>
  show \<open>trace_class (if f abs_summable_on UNIV then diagonal_operator f else 0)\<close>
  proof (cases \<open>f abs_summable_on UNIV\<close>)
    case True
    have bdd: \<open>bdd_above (range (\<lambda>x. cmod (f x)))\<close>
    proof (rule bdd_aboveI2)
      fix x
      have \<open>cmod (f x) = (\<Sum>\<^sub>\<infinity>x\<in>{x}. cmod (f x))\<close>
        by simp
      also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>x. cmod (f x))\<close>
        apply (rule infsum_mono_neutral)
        by (auto intro!: True)
      finally show \<open>cmod (f x) \<le> (\<Sum>\<^sub>\<infinity>x. cmod (f x))\<close>
        by -
    qed
    have \<open>trace_class (diagonal_operator f)\<close>
      by (auto intro!: trace_classI[OF is_onb_ket] summable_on_reindex[THEN iffD2] True
          simp: abs_op_diagonal_operator o_def diagonal_operator_ket bdd)
    with True show ?thesis
      by simp
  next
    case False
    then show ?thesis
      by simp
  qed
qed

lemma diagonal_operator_tc_invalid: \<open>\<not> f abs_summable_on UNIV \<Longrightarrow> diagonal_operator_tc f = 0\<close>
  apply (transfer fixing: f) by simp

lemma from_trace_class_diagonal_operator_tc:
  assumes \<open>f abs_summable_on UNIV\<close>
  shows \<open>from_trace_class (diagonal_operator_tc f) = diagonal_operator f\<close>
  apply (transfer fixing: f)
  using assms by simp

lemma vector_sandwich_partial_trace_has_sum:
  \<open>((\<lambda>z. ((x \<otimes>\<^sub>s ket z) \<bullet>\<^sub>C (from_trace_class \<rho> *\<^sub>V (y \<otimes>\<^sub>s ket z))))
      has_sum x \<bullet>\<^sub>C (from_trace_class (partial_trace \<rho>) *\<^sub>V y)) UNIV\<close>
proof -
  define x\<rho>y where \<open>x\<rho>y = x \<bullet>\<^sub>C (from_trace_class (partial_trace \<rho>) *\<^sub>V y)\<close>
  have \<open>((\<lambda>j. compose_tcl (compose_tcr ((tensor_ell2_right (ket j))*) \<rho>) (tensor_ell2_right (ket j))) 
        has_sum partial_trace \<rho>) UNIV\<close>
    using partial_trace_has_sum by force
  then have \<open>((\<lambda>j. x \<bullet>\<^sub>C (from_trace_class (compose_tcl (compose_tcr ((tensor_ell2_right (ket j))*) \<rho>) (tensor_ell2_right (ket j))) *\<^sub>V y))
        has_sum x\<rho>y) UNIV\<close>
    unfolding x\<rho>y_def
    apply (rule Infinite_Sum.has_sum_bounded_linear[rotated])
    by (intro bounded_clinear.bounded_linear bounded_linear_intros)
  then have \<open>((\<lambda>j. x \<bullet>\<^sub>C (tensor_ell2_right (ket j)* *\<^sub>V from_trace_class \<rho> *\<^sub>V y \<otimes>\<^sub>s ket j)) has_sum
     x\<rho>y) UNIV\<close>
    by (simp add: compose_tcl.rep_eq compose_tcr.rep_eq)
  then show ?thesis
    by (metis (no_types, lifting) cinner_adj_right has_sum_cong tensor_ell2_right_apply x\<rho>y_def)
qed

lemma vector_sandwich_partial_trace:
  \<open>x \<bullet>\<^sub>C (from_trace_class (partial_trace \<rho>) *\<^sub>V y) =
      (\<Sum>\<^sub>\<infinity>z. ((x \<otimes>\<^sub>s ket z) \<bullet>\<^sub>C (from_trace_class \<rho> *\<^sub>V (y \<otimes>\<^sub>s ket z))))\<close>
  by (metis (mono_tags, lifting) infsumI vector_sandwich_partial_trace_has_sum)

lemma pos_imp_selfadjoint: \<open>a \<ge> 0 \<Longrightarrow> selfadjoint a\<close>
  by (simp add: comparable_hermitean selfadjoint_def)

lemma sandwich_tc_scaleC_right: \<open>sandwich_tc e (c *\<^sub>C t) = c *\<^sub>C sandwich_tc e t\<close>
  apply (transfer fixing: e c)
  by (simp add: cblinfun.scaleC_right)


lemma sandwich_tc_plus: \<open>sandwich_tc e (t + u) = sandwich_tc e t + sandwich_tc e u\<close>
  by (simp add: sandwich_tc_def compose_tcr.add_right compose_tcl.add_left)

lemma sandwich_tc_minus: \<open>sandwich_tc e (t - u) = sandwich_tc e t - sandwich_tc e u\<close>
  by (simp add: sandwich_tc_def compose_tcr.diff_right compose_tcl.diff_left)

lemma bounded_clinear_sandwich_tc[bounded_clinear]: \<open>bounded_clinear (sandwich_tc e)\<close>
  using norm_sandwich_tc[of e]
  by (auto intro!: bounded_clinearI[where K=\<open>(norm e)\<^sup>2\<close>]
      simp: sandwich_tc_plus sandwich_tc_scaleC_right cross3_simps)

lemma sandwich_tc_uminus_right: \<open>sandwich_tc e (- t) = - sandwich_tc e t\<close>
  by (metis (no_types, lifting) add.right_inverse arith_simps(50) diff_0 group_cancel.sub1 sandwich_tc_minus)

lemma clinear_of_complex[iff]: \<open>clinear of_complex\<close>
  by (simp add: clinearI)

definition some_onb_of :: \<open>'a ccsubspace \<Rightarrow> 'a::chilbert_space set\<close> where
  \<open>some_onb_of S = (SOME B::'a set. is_ortho_set B \<and> (\<forall>b\<in>B. norm b = 1) \<and> ccspan B = S)\<close>

lemma is_ortho_set_some_onb_of[iff]: \<open>is_ortho_set (some_onb_of S)\<close> (is \<open>?thesis1\<close>)
  and some_onb_of_normed: \<open>b \<in> some_onb_of S \<Longrightarrow> norm b = 1\<close> (is \<open>PROP ?thesis2\<close>)
  and ccspan_some_onb_of[simp]: \<open>ccspan (some_onb_of S) = S\<close> (is \<open>?thesis3\<close>)
proof -
  define P where \<open>P B \<longleftrightarrow> is_ortho_set B \<and> (\<forall>b\<in>B. norm b = 1) \<and> ccspan B = S\<close> for B
  from orthonormal_subspace_basis_exists[where S=\<open>{}\<close>]
  have \<open>\<exists>B. P B\<close>
    by (auto simp: P_def)
  then have \<open>P (SOME B. P B)\<close>
    by (simp add: someI_ex)
  then have \<open>P (some_onb_of S)\<close>
    by (simp add: P_def some_onb_of_def)
  then show ?thesis1 \<open>PROP ?thesis2\<close> ?thesis3
    by (simp_all add: P_def)
qed

lemma some_onb_of_0[simp]: \<open>some_onb_of 0 = {}\<close>
proof -
  have no0: \<open>0 \<notin> some_onb_of 0\<close>
    using is_ortho_set_def by blast
  have \<open>ccspan (some_onb_of 0) = (0 :: 'a ccsubspace)\<close>
    by simp
  then have \<open>some_onb_of 0 \<subseteq> space_as_set (0 :: 'a ccsubspace)\<close>
    by (metis ccspan_superset)
  also have \<open>\<dots> = {0}\<close>
    by simp
  finally show ?thesis
    using no0
    by blast
qed

definition spectral_dec_vecs :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow> 'a::chilbert_space set\<close> where
  \<open>spectral_dec_vecs a = (\<Union>n. scaleC (csqrt (spectral_dec_val a n)) ` some_onb_of (spectral_dec_space a n))\<close>

lift_definition spectral_dec_vecs_tc :: \<open>('a,'a) trace_class \<Rightarrow> 'a::chilbert_space set\<close> is
  spectral_dec_vecs.

lemma spectral_dec_vecs_ortho:
  assumes \<open>selfadjoint a\<close> and \<open>compact_op a\<close>
  shows \<open>is_ortho_set (spectral_dec_vecs a)\<close>
proof (unfold is_ortho_set_def, intro conjI ballI impI)
  show \<open>0 \<notin> spectral_dec_vecs a\<close>
  proof (rule notI)
    assume \<open>0 \<in> spectral_dec_vecs a\<close>
    then obtain n v where v0: \<open>0 = csqrt (spectral_dec_val a n) *\<^sub>C v\<close> and v_in: \<open>v \<in> some_onb_of (spectral_dec_space a n)\<close>
      by (auto simp: spectral_dec_vecs_def)
    from v_in have \<open>v \<noteq> 0\<close>
      using is_ortho_set_def is_ortho_set_some_onb_of by blast
    from v_in have \<open>spectral_dec_space a n \<noteq> 0\<close>
      using some_onb_of_0 by force
    then have \<open>spectral_dec_val a n \<noteq> 0\<close>
      by (meson spectral_dec_space.elims)
    with v0 \<open>v \<noteq> 0\<close> show False
      by force
  qed
  fix g h assume g: \<open>g \<in> spectral_dec_vecs a\<close> and h: \<open>h \<in> spectral_dec_vecs a\<close> and \<open>g \<noteq> h\<close>
  from g obtain ng g' where gg': \<open>g = csqrt (spectral_dec_val a ng) *\<^sub>C g'\<close> and g'_in: \<open>g' \<in> some_onb_of (spectral_dec_space a ng)\<close>
    by (auto simp: spectral_dec_vecs_def)
  from h obtain nh h' where hh': \<open>h = csqrt (spectral_dec_val a nh) *\<^sub>C h'\<close> and h'_in: \<open>h' \<in> some_onb_of (spectral_dec_space a nh)\<close>
    by (auto simp: spectral_dec_vecs_def)
  have \<open>is_orthogonal g' h'\<close>
  proof (cases \<open>ng = nh\<close>)
    case True
    with h'_in have \<open>h' \<in> some_onb_of (spectral_dec_space a nh)\<close>
      by simp
    with g'_in True \<open>g \<noteq> h\<close> gg' hh'
    show ?thesis
      using  is_ortho_set_def by fastforce
  next
    case False
    then have \<open>orthogonal_spaces (spectral_dec_space a ng) (spectral_dec_space a nh)\<close>
      by (auto intro!: spectral_dec_space_orthogonal assms simp: )
    with h'_in g'_in show \<open>is_orthogonal g' h'\<close>
      using orthogonal_spaces_ccspan by force
  qed
  then show \<open>is_orthogonal g h\<close>
    by (simp add: gg' hh')
qed

lemma inj_scaleC:
  fixes A :: \<open>'a::complex_vector set\<close>
  assumes \<open>c \<noteq> 0\<close>
  shows \<open>inj_on (scaleC c) A\<close>
  by (meson assms inj_onI scaleC_left_imp_eq)


lemma finite_dim_ccsubspace_zero[iff]: \<open>finite_dim_ccsubspace 0\<close>
proof -
  have *: \<open>cfinite_dim (cspan {0})\<close>
    by blast
  show ?thesis
    apply transfer
    using * by simp
qed

lemma finite_dim_ccsubspace_bot[iff]: \<open>finite_dim_ccsubspace \<bottom>\<close>
  using finite_dim_ccsubspace_zero by auto


lemma spectral_dec_space_0:
  assumes \<open>spectral_dec_val a n = 0\<close>
  shows \<open>spectral_dec_space a n = 0\<close>
  by (simp add: assms spectral_dec_space_def)

lemma spectral_dec_space_finite_dim[intro]:
  assumes \<open>compact_op a\<close>
  shows \<open>finite_dim_ccsubspace (spectral_dec_space a n)\<close>
  by (auto intro!: compact_op_eigenspace_finite_dim spectral_dec_op_compact assms simp: spectral_dec_space_def )


lemma some_onb_of_finite_dim:
  assumes \<open>finite_dim_ccsubspace S\<close>
  shows \<open>finite (some_onb_of S)\<close>
proof -
  from assms obtain C where CS: \<open>cspan C = space_as_set S\<close> and \<open>finite C\<close>
    by (meson cfinite_dim_subspace_has_basis csubspace_space_as_set finite_dim_ccsubspace.rep_eq)
  then show \<open>finite (some_onb_of S)\<close>
    using ccspan_superset complex_vector.independent_span_bound is_ortho_set_cindependent by fastforce
qed

lemma cdim_infinite_0:
  assumes \<open>\<not> cfinite_dim S\<close>
  shows \<open>cdim S = 0\<close>
proof -
  from assms have not_fin_cspan: \<open>\<not> cfinite_dim (cspan S)\<close>
    using cfinite_dim_def cfinite_dim_subspace_has_basis complex_vector.span_superset by fastforce
  obtain B where \<open>cindependent B\<close> and \<open>cspan S = cspan B\<close>
    using csubspace_has_basis by blast
  with not_fin_cspan have \<open>infinite B\<close>
    by auto
  then have \<open>card B = 0\<close>
    by force
  have \<open>cdim (cspan S) = 0\<close> 
    apply (rule complex_vector.dim_unique[of B])
       apply (auto intro!: simp add: \<open>cspan S = cspan B\<close> complex_vector.span_superset)
    using \<open>cindependent B\<close> \<open>card B = 0\<close> by auto
  then show ?thesis
    by simp
qed



lemma some_onb_of_card:
  shows \<open>card (some_onb_of S) = cdim (space_as_set S)\<close>
proof (cases \<open>finite_dim_ccsubspace S\<close>)
  case True
  show ?thesis
    apply (rule complex_vector.dim_eq_card[symmetric])
     apply (auto simp: is_ortho_set_cindependent)
     apply (metis True ccspan_finite ccspan_some_onb_of complex_vector.span_clauses(1) some_onb_of_finite_dim)
    by (metis True ccspan_finite ccspan_some_onb_of complex_vector.span_eq_iff csubspace_space_as_set some_onb_of_finite_dim)
next
  case False
  then have \<open>cdim (space_as_set S) = 0\<close>
    by (simp add: cdim_infinite_0 finite_dim_ccsubspace.rep_eq)
  moreover from False have \<open>infinite (some_onb_of S)\<close>
    using ccspan_finite_dim by fastforce
  ultimately show ?thesis 
    by simp
qed

lemma compact_from_trace_class[iff]: \<open>compact_op (from_trace_class t)\<close>
  by (auto intro!: simp: trace_class_compact)

(* TODO move *)
lemma some_onb_of_in_space[iff]:
  \<open>some_onb_of S \<subseteq> space_as_set S\<close>
  using ccspan_superset by fastforce


lemma sum_some_onb_of_butterfly:
  assumes \<open>finite_dim_ccsubspace S\<close>
  shows \<open>(\<Sum>x\<in>some_onb_of S. butterfly x x) = Proj S\<close>
proof -
  obtain B where onb_S_in_B: \<open>some_onb_of S \<subseteq> B\<close> and \<open>is_onb B\<close>
    apply atomize_elim
    apply (rule orthonormal_basis_exists)
    by (simp_all add: some_onb_of_normed)
  have S_ccspan: \<open>S = ccspan (some_onb_of S)\<close>
    by simp

  show ?thesis
  proof (rule cblinfun_eq_gen_eqI[where G=B])
    show \<open>ccspan B = \<top>\<close>
      using \<open>is_onb B\<close> is_onb_def by blast
    fix b assume \<open>b \<in> B\<close>
    show \<open>(\<Sum>x\<in>some_onb_of S. selfbutter x) *\<^sub>V b = Proj S *\<^sub>V b\<close>
    proof (cases \<open>b \<in> some_onb_of S\<close>)
      case True
      have \<open>(\<Sum>x\<in>some_onb_of S. selfbutter x) *\<^sub>V b = (\<Sum>x\<in>some_onb_of S. selfbutter x *\<^sub>V b)\<close>
        using cblinfun.sum_left by blast
      also have \<open>\<dots> = b\<close>
        apply (subst sum_single[where i=b])
        using True apply (auto intro!: simp add: assms some_onb_of_finite_dim) 
        using is_ortho_set_def apply fastforce
        using cnorm_eq_1 some_onb_of_normed by force
      also have \<open>\<dots> = Proj S *\<^sub>V b\<close>
        apply (rule Proj_fixes_image[symmetric])
        using True some_onb_of_in_space by blast
      finally show ?thesis
        by -
    next
      case False
      have *: \<open>is_orthogonal x b\<close> if \<open>x \<in> some_onb_of S\<close> and \<open>x \<noteq> 0\<close> for x
      proof -
        have \<open>x \<in> B\<close>
          using onb_S_in_B that(1) by fastforce
        moreover note \<open>b \<in> B\<close>
        moreover have \<open>x \<noteq> b\<close>
          using False that(1) by blast
        moreover note \<open>is_onb B\<close>
        ultimately show \<open>is_orthogonal x b\<close>
          by (simp add: is_onb_def is_ortho_set_def)
      qed
      have \<open>(\<Sum>x\<in>some_onb_of S. selfbutter x) *\<^sub>V b = (\<Sum>x\<in>some_onb_of S. selfbutter x *\<^sub>V b)\<close>
        using cblinfun.sum_left by blast
      also have \<open>\<dots> = 0\<close>
        by (auto intro!: sum.neutral simp: * )
      also have \<open>\<dots> = Proj S *\<^sub>V b\<close>
        apply (rule Proj_0_compl[symmetric])
        apply (subst S_ccspan)
        apply (rule mem_ortho_ccspanI)
        using "*" cinner_zero_right is_orthogonal_sym by blast
      finally show ?thesis 
        by -
    qed
  qed
qed




lemma sum_some_onb_of_tc_butterfly:
  assumes \<open>finite_dim_ccsubspace S\<close>
  shows \<open>(\<Sum>x\<in>some_onb_of S. tc_butterfly x x) = Abs_trace_class (Proj S)\<close>
  by (metis (mono_tags, lifting) assms from_trace_class_inverse from_trace_class_sum sum.cong sum_some_onb_of_butterfly tc_butterfly.rep_eq)


lemma eigenvalues_nonneg:
  assumes \<open>a \<ge> 0\<close> and \<open>v \<in> eigenvalues a\<close>
  shows \<open>v \<ge> 0\<close>
proof -
  from assms obtain h where \<open>norm h = 1\<close> and ahvh: \<open>a *\<^sub>V h = v *\<^sub>C h\<close>
    using unit_eigenvector_ex by blast
  have \<open>0 \<le> h \<bullet>\<^sub>C a h\<close>
    by (simp add: assms(1) cinner_pos_if_pos)
  also have \<open>\<dots> = v * (h \<bullet>\<^sub>C h)\<close>
    by (simp add: ahvh)
  also have \<open>\<dots> = v\<close>
    using \<open>norm h = 1\<close> cnorm_eq_1 by auto
  finally show \<open>v \<ge> 0\<close>
    by blast
qed

(* TODO move *)
lemma spectral_dec_val_nonneg:
  assumes \<open>a \<ge> 0\<close>
  assumes \<open>compact_op a\<close>
  shows \<open>spectral_dec_val a n \<ge> 0\<close>
proof -
  define v where \<open>v = spectral_dec_val a n\<close>
  wlog non0: \<open>spectral_dec_val a n \<noteq> 0\<close> generalizing v keeping v_def
    using negation by force
  have [simp]: \<open>selfadjoint a\<close>
    using adj_0 assms(1) comparable_hermitean selfadjoint_def by blast
  have \<open>v \<in> eigenvalues a\<close>
    by (auto intro!: non0 spectral_dec_val_eigenvalue assms simp: v_def)
  then show \<open>spectral_dec_val a n \<ge> 0\<close>
    using assms(1) eigenvalues_nonneg v_def by blast
qed

lemma Proj_pos[iff]: \<open>Proj S \<ge> 0\<close>
  apply (rule positive_cblinfun_squareI[where B=\<open>Proj S\<close>])
  by (simp add: adj_Proj)

lemma abs_op_Proj[simp]: \<open>abs_op (Proj S) = Proj S\<close>
  by (simp add: abs_op_id_on_pos)

lemma trace_class_Proj: \<open>trace_class (Proj S) \<longleftrightarrow> finite_dim_ccsubspace S\<close>
proof -
  define C where \<open>C = some_onb_of S\<close>
  then obtain B where \<open>is_onb B\<close> and \<open>C \<subseteq> B\<close>
    using orthonormal_basis_exists some_onb_of_normed by blast
  have card_C: \<open>card C = cdim (space_as_set S)\<close>
    by (simp add: C_def some_onb_of_card)
  have S_C: \<open>S = ccspan C\<close>
    by (simp add: C_def)

  from \<open>is_onb B\<close>
  have \<open>trace_class (Proj S) \<longleftrightarrow> ((\<lambda>x. cmod (x \<bullet>\<^sub>C (abs_op (Proj S) *\<^sub>V x))) abs_summable_on B)\<close>
    by (rule trace_class_iff_summable)
  also have \<open>\<dots> \<longleftrightarrow> ((\<lambda>x. cmod (x \<bullet>\<^sub>C (Proj S *\<^sub>V x))) abs_summable_on B)\<close>
    by simp
  also have \<open>\<dots> \<longleftrightarrow> ((\<lambda>x. 1::real) abs_summable_on C)\<close>
  proof (rule summable_on_cong_neutral)
    fix x :: 'a
    show \<open>norm 1 = 0\<close> if \<open>x \<in> C - B\<close>
      using that \<open>C \<subseteq> B\<close> by auto
    show \<open>norm (cmod (x \<bullet>\<^sub>C (Proj S *\<^sub>V x))) = norm (1::real)\<close> if \<open>x \<in> B \<inter> C\<close>
      apply (subst Proj_fixes_image)
      using C_def Int_absorb1 that \<open>is_onb B\<close>
      by (auto simp: is_onb_def cnorm_eq_1)
    show \<open>norm (cmod (x \<bullet>\<^sub>C (Proj S *\<^sub>V x))) = 0\<close> if \<open>x \<in> B - C\<close>
      apply (subst Proj_0_compl)
       apply (subst S_C)
       apply (rule mem_ortho_ccspanI)
      using that \<open>is_onb B\<close> \<open>C \<subseteq> B\<close>
      by (force simp: is_onb_def is_ortho_set_def)+
  qed
  also have \<open>\<dots> \<longleftrightarrow> finite C\<close>
    using infsum_diverge_constant[where A=C and c=\<open>1::real\<close>]
    by auto
  also have \<open>\<dots> \<longleftrightarrow> finite_dim_ccsubspace S\<close>
    by (metis C_def S_C ccspan_finite_dim some_onb_of_finite_dim)
  finally show ?thesis
    by -
qed

lemma not_trace_class_trace0: \<open>trace a = 0\<close> if \<open>\<not> trace_class a\<close>
  using that by (simp add: trace_def)


lemma trace_Proj: \<open>trace (Proj S) = cdim (space_as_set S)\<close>
proof (cases \<open>finite_dim_ccsubspace S\<close>)
  case True
  define C where \<open>C = some_onb_of S\<close>
  then obtain B where \<open>is_onb B\<close> and \<open>C \<subseteq> B\<close>
    using orthonormal_basis_exists some_onb_of_normed by blast
  have [simp]: \<open>finite C\<close>
    using C_def True some_onb_of_finite_dim by blast
  have card_C: \<open>card C = cdim (space_as_set S)\<close>
    by (simp add: C_def some_onb_of_card)
  have S_C: \<open>S = ccspan C\<close>
    by (simp add: C_def)

  from True have \<open>trace_class (Proj S)\<close>
    by (simp add: trace_class_Proj)
  with \<open>is_onb B\<close> have \<open>((\<lambda>e. e \<bullet>\<^sub>C (Proj S *\<^sub>V e)) has_sum trace (Proj S)) B\<close>
    by (rule trace_has_sum)
  then have \<open>((\<lambda>e. 1) has_sum trace (Proj S)) C\<close>
  proof (rule has_sum_cong_neutral[THEN iffD1, rotated -1])
    fix x :: 'a
    show \<open>1 = 0\<close> if \<open>x \<in> C - B\<close>
      using that \<open>C \<subseteq> B\<close> by auto
    show \<open>x \<bullet>\<^sub>C (Proj S *\<^sub>V x) = 1\<close> if \<open>x \<in> B \<inter> C\<close>
      apply (subst Proj_fixes_image)
      using C_def Int_absorb1 that \<open>is_onb B\<close>
      by (auto simp: is_onb_def cnorm_eq_1)
    show \<open>is_orthogonal x (Proj S *\<^sub>V x)\<close> if \<open>x \<in> B - C\<close>
      apply (subst Proj_0_compl)
       apply (subst S_C)
       apply (rule mem_ortho_ccspanI)
      using that \<open>is_onb B\<close> \<open>C \<subseteq> B\<close>
      by (force simp: is_onb_def is_ortho_set_def)+
  qed
  then have \<open>trace (Proj S) = card C\<close>
    using has_sum_constant[OF \<open>finite C\<close>, of 1]
    apply simp
    using has_sum_unique by blast
  also have \<open>\<dots> = cdim (space_as_set S)\<close>
    using card_C by presburger
  finally show ?thesis
    by -
next
  case False
  then have \<open>\<not> trace_class (Proj S)\<close>
    using trace_class_Proj by blast
  then have \<open>trace (Proj S) = 0\<close>
    by (rule not_trace_class_trace0)
  moreover from False have \<open>cdim (space_as_set S) = 0\<close>
    apply transfer
    by (simp add: cdim_infinite_0)
  ultimately show ?thesis
    by simp
qed

lemma butterfly_spectral_dec_vec_tc_has_sum:
  (* assumes \<open>selfadjoint_tc t\<close> *)
  assumes \<open>t \<ge> 0\<close>
(* TODO: wrong - only positive t *)
  shows \<open>((\<lambda>v. tc_butterfly v v) has_sum t) (spectral_dec_vecs_tc t)\<close>
proof -
  define t' where \<open>t' = from_trace_class t\<close>
  note power2_csqrt[unfolded power2_eq_square, simp]
  note Reals_cnj_iff[simp]
  have [simp]: \<open>compact_op t'\<close>
    by (simp add: t'_def)
  from assms have \<open>selfadjoint_tc t\<close>
    apply transfer
    by (simp add: comparable_hermitean selfadjoint_def)
  have spectral_real[simp]: \<open>spectral_dec_val t' n \<in> \<real>\<close> for n
    apply (rule spectral_dec_val_real)
    using \<open>selfadjoint_tc t\<close> by (auto intro!: trace_class_compact simp: selfadjoint_tc.rep_eq t'_def)

  have *: \<open>((\<lambda>(n,v). tc_butterfly v v) has_sum t) (SIGMA n:UNIV. (*\<^sub>C) (csqrt (spectral_dec_val t' n)) ` some_onb_of (spectral_dec_space t' n))\<close>
  proof (rule has_sum_SigmaI[where g=\<open>\<lambda>n. spectral_dec_val t' n *\<^sub>C spectral_dec_proj_tc t n\<close>])
    have \<open>spectral_dec_val t' n \<ge> 0\<close> for n
      by (simp add: assms from_trace_class_pos spectral_dec_val_nonneg t'_def)
    then have [simp]: \<open>cnj (csqrt (spectral_dec_val t' n)) * csqrt (spectral_dec_val t' n) = spectral_dec_val t' n\<close> for n
      apply (auto simp add: csqrt_of_real_nonneg less_eq_complex_def)
      by (metis of_real_Re of_real_mult spectral_real sqrt_sqrt)
    have sum: \<open>(\<Sum>y\<in>(\<lambda>x. csqrt (spectral_dec_val t' n) *\<^sub>C x) ` some_onb_of (spectral_dec_space t' n). tc_butterfly y y) = spectral_dec_val t' n *\<^sub>C spectral_dec_proj_tc t n\<close> for n
    proof (cases \<open>spectral_dec_val t' n = 0\<close>)
      case True
      then show ?thesis
        by (metis (mono_tags, lifting) csqrt_0 imageE scaleC_eq_0_iff sum.neutral tc_butterfly_scaleC_left)
    next
      case False
      then have \<open>inj_on (\<lambda>x. csqrt (spectral_dec_val t' n) *\<^sub>C x) X\<close> for X :: \<open>'a set\<close>
        by (meson csqrt_eq_0 inj_scaleC)
      then show ?thesis 
        by (simp add: sum.reindex False spectral_dec_space_finite_dim sum_some_onb_of_tc_butterfly
            spectral_dec_proj_def spectral_dec_proj_tc_def flip: scaleC_sum_right t'_def)
    qed
    then show \<open>((\<lambda>y. case (n, y) of (n, v) \<Rightarrow> tc_butterfly v v) has_sum spectral_dec_val t' n *\<^sub>C spectral_dec_proj_tc t n)
          ((*\<^sub>C) (csqrt (spectral_dec_val t' n)) ` some_onb_of (spectral_dec_space t' n))\<close> for n
      by (auto intro!: has_sum_finiteI finite_imageI some_onb_of_finite_dim spectral_dec_space_finite_dim simp: t'_def)
    show \<open>((\<lambda>n. spectral_dec_val t' n *\<^sub>C spectral_dec_proj_tc t n) has_sum t) UNIV\<close>
      by (auto intro!: spectral_dec_has_sum_tc \<open>selfadjoint_tc t\<close> simp: t'_def simp flip: spectral_dec_val_tc.rep_eq)
    show \<open>(\<lambda>(n, v). tc_butterfly v v) summable_on (SIGMA n:UNIV. (*\<^sub>C) (csqrt (spectral_dec_val t' n)) ` some_onb_of (spectral_dec_space t' n))\<close>
    proof -
      have inj: \<open>inj_on ((*\<^sub>C) (csqrt (spectral_dec_val t' n))) (some_onb_of (spectral_dec_space t' n))\<close> for n
      proof (cases \<open>spectral_dec_val t' n = 0\<close>)
        case True
        then have \<open>spectral_dec_space t' n = 0\<close>
          using spectral_dec_space_0 by blast
        then have \<open>some_onb_of (spectral_dec_space t' n) = {}\<close>
          using some_onb_of_0 by auto
        then show ?thesis
          by simp
      next
        case False
        then show ?thesis
          by (auto intro!: inj_scaleC)
      qed
      have 1: \<open>(\<lambda>x. tc_butterfly x x) abs_summable_on (\<lambda>xa. csqrt (spectral_dec_val t' n) *\<^sub>C xa) ` some_onb_of (spectral_dec_space t' n)\<close> for n
        by (auto intro!: summable_on_finite some_onb_of_finite_dim spectral_dec_space_finite_dim simp: t'_def)
      (* have \<open>(\<Sum>\<^sub>\<infinity>x\<in>some_onb_of (spectral_dec_space t' h). norm (tc_butterfly x x)) = spectral_dec_proj t' h\<close> for h *)
      have \<open>(\<lambda>n. cmod (spectral_dec_val t' n) * (\<Sum>\<^sub>\<infinity>h\<in>some_onb_of (spectral_dec_space t' n). norm (tc_butterfly h h))) abs_summable_on UNIV\<close>
      proof -
        have *: \<open>(\<Sum>\<^sub>\<infinity>h\<in>some_onb_of (spectral_dec_space t' n). norm (tc_butterfly h h)) = norm (spectral_dec_proj_tc t n)\<close> for n
        proof -
          have \<open>(\<Sum>\<^sub>\<infinity>h\<in>some_onb_of (spectral_dec_space t' n). norm (tc_butterfly h h))
              = (\<Sum>\<^sub>\<infinity>h\<in>some_onb_of (spectral_dec_space t' n). 1)\<close>
            by (simp add: infsum_cong norm_tc_butterfly some_onb_of_normed)
          also have \<open>\<dots> = card (some_onb_of (spectral_dec_space t' n))\<close>
            by simp
          also have \<open>\<dots> = cdim (space_as_set (spectral_dec_space t' n))\<close>
            by (simp add: some_onb_of_card)
          also have \<open>\<dots> = norm (spectral_dec_proj_tc t n)\<close>
            unfolding t'_def 
            apply transfer
            by (metis of_real_eq_iff of_real_of_nat_eq spectral_dec_proj_def spectral_dec_proj_pos
                trace_Proj trace_norm_pos)
          finally show ?thesis
            by -
        qed
        show ?thesis
          apply (simp add: * )
          by (metis (no_types, lifting) \<open>selfadjoint_tc t\<close> norm_scaleC spectral_dec_summable_tc
              spectral_dec_val_tc.rep_eq summable_on_cong t'_def)
      qed
      then have 2: \<open>(\<lambda>n. \<Sum>\<^sub>\<infinity>v\<in>(*\<^sub>C) (csqrt (spectral_dec_val t' n)) ` some_onb_of (spectral_dec_space t' n).
            norm (tc_butterfly v v)) abs_summable_on UNIV\<close>
        apply (subst infsum_reindex)
        by (auto intro!: inj simp: o_def infsum_cmult_right' norm_mult (* inj_on_def *) simp del: real_norm_def)
      show ?thesis
        apply (rule abs_summable_summable)
        apply (rule abs_summable_on_Sigma_iff[THEN iffD2])
        using 1 2 by auto
    qed
  qed
  have \<open>((\<lambda>v. tc_butterfly v v) has_sum t) (\<Union>n. (*\<^sub>C) (csqrt (spectral_dec_val t' n)) ` some_onb_of (spectral_dec_space t' n))\<close>
  proof -
    have **: \<open>(\<Union>n. (*\<^sub>C) (csqrt (spectral_dec_val t' n)) ` some_onb_of (spectral_dec_space t' n)) =
              snd ` (SIGMA n:UNIV. (*\<^sub>C) (csqrt (spectral_dec_val t' n)) ` some_onb_of (spectral_dec_space t' n))\<close>
      by force
    have inj: \<open>inj_on snd (SIGMA n:UNIV. (\<lambda>x. csqrt (spectral_dec_val t' n) *\<^sub>C x) ` some_onb_of (spectral_dec_space t' n))\<close>
    proof (rule inj_onI)
      fix nh assume nh: \<open>nh \<in> (SIGMA n:UNIV. (\<lambda>x. csqrt (spectral_dec_val t' n) *\<^sub>C x) ` some_onb_of (spectral_dec_space t' n))\<close>
      fix mg assume mg: \<open>mg \<in> (SIGMA m:UNIV. (\<lambda>x. csqrt (spectral_dec_val t' m) *\<^sub>C x) ` some_onb_of (spectral_dec_space t' m))\<close>
      assume \<open>snd nh = snd mg\<close>
      from nh obtain n h where nh': \<open>nh = (n, csqrt (spectral_dec_val t' n) *\<^sub>C h)\<close> and h: \<open>h \<in> some_onb_of (spectral_dec_space t' n)\<close>
        by blast
      from mg obtain m g where mg': \<open>mg = (m, csqrt (spectral_dec_val t' m) *\<^sub>C g)\<close> and g: \<open>g \<in> some_onb_of (spectral_dec_space t' m)\<close>
        by blast
      have \<open>n = m\<close>
      proof (rule ccontr)
        assume [simp]: \<open>n \<noteq> m\<close>
        from h have val_not_0: \<open>spectral_dec_val t' n \<noteq> 0\<close>
          using some_onb_of_0 spectral_dec_space_0 by fastforce
        from \<open>snd nh = snd mg\<close> nh' mg' have eq: \<open>csqrt (spectral_dec_val t' n) *\<^sub>C h = csqrt (spectral_dec_val t' m) *\<^sub>C g\<close>
          by simp
        from \<open>n \<noteq> m\<close> have \<open>orthogonal_spaces (spectral_dec_space t' n) (spectral_dec_space t' m)\<close>
          apply (rule spectral_dec_space_orthogonal[rotated -1])
          using \<open>selfadjoint_tc t\<close> by (auto intro!: trace_class_compact simp: t'_def selfadjoint_tc.rep_eq)
        with h g have \<open>is_orthogonal h g\<close>
          using orthogonal_spaces_ccspan by fastforce
        then have \<open>is_orthogonal (csqrt (spectral_dec_val t' n) *\<^sub>C h) (csqrt (spectral_dec_val t' m) *\<^sub>C g)\<close>
          by force
        with eq have val_h_0: \<open>csqrt (spectral_dec_val t' n) *\<^sub>C h = 0\<close>
          by simp
        with val_not_0 have \<open>h = 0\<close>
          by fastforce
        with h show False
          using is_ortho_set_some_onb_of
          by (auto simp: is_ortho_set_def)
      qed
      with \<open>snd nh = snd mg\<close> nh' mg' show \<open>nh = mg\<close>
        by simp
    qed
    from * show ?thesis
      apply (subst ** )
      apply (rule has_sum_reindex[THEN iffD2, rotated])
      by (auto intro!: inj simp: o_def case_prod_unfold)
  qed
  then show ?thesis
    by (simp add: spectral_dec_vecs_tc.rep_eq spectral_dec_vecs_def flip: t'_def)
qed

lemma spectral_dec_vec_tc_norm_summable:
  assumes \<open>t \<ge> 0\<close>
  shows \<open>(\<lambda>v. (norm v)\<^sup>2) summable_on (spectral_dec_vecs_tc t)\<close>
proof -
  from butterfly_spectral_dec_vec_tc_has_sum[OF assms]
  have \<open>(\<lambda>v. tc_butterfly v v) summable_on (spectral_dec_vecs_tc t)\<close>
    using has_sum_imp_summable by blast
  then have \<open>(\<lambda>v. trace_tc (tc_butterfly v v)) summable_on (spectral_dec_vecs_tc t)\<close>
    apply (rule summable_on_bounded_linear[rotated])
    by (simp add: bounded_clinear.bounded_linear)
  moreover have *: \<open>trace_tc (tc_butterfly v v) = of_real ((norm v)\<^sup>2)\<close> for v :: 'a
    by (metis norm_tc_butterfly norm_tc_pos power2_eq_square tc_butterfly_pos)
  ultimately have \<open>(\<lambda>v. complex_of_real ((norm v)\<^sup>2)) summable_on (spectral_dec_vecs_tc t)\<close>
    by simp
  then show ?thesis
    by (smt (verit, ccfv_SIG) *
        complex_Re_le_cmod norm_tc_butterfly of_real_hom.hom_power power2_eq_square power2_norm_eq_cinner 
        power2_norm_eq_cinner' summable_on_cong summable_on_iff_abs_summable_on_complex trace_tc_norm)
qed


(* lemma spectral_dec_vec_tc_norm_summable:
  \<open>(\<lambda>n. (norm (spectral_dec_vec_tc t n))\<^sup>2) summable_on UNIV\<close>
  by xxx *)


(* TODO move next to *) thm one_dim_loewner_order
lemma one_dim_loewner_order_strict: \<open>A > B \<longleftrightarrow> one_dim_iso A > (one_dim_iso B :: complex)\<close> for A B :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a::{chilbert_space, one_dim}\<close>
  by (auto simp: less_cblinfun_def one_dim_loewner_order)

(* TODO move to One_Dim *)
lemma one_dim_cblinfun_zero_le_one: \<open>0 < (1 :: 'a::one_dim \<Rightarrow>\<^sub>C\<^sub>L 'a)\<close>
  by (simp add: one_dim_loewner_order_strict)
lemma one_dim_cblinfun_one_pos: \<open>0 \<le> (1 :: 'a::one_dim \<Rightarrow>\<^sub>C\<^sub>L 'a)\<close>
  by (simp add: one_dim_loewner_order)

lemma pos_selfadjoint: \<open>selfadjoint a\<close> if \<open>a \<ge> 0\<close>
  using adj_0 comparable_hermitean selfadjoint_def that by blast

(* TODO move *)
lemma tc_butterfly_scaleC_summable:
  fixes f :: \<open>'a \<Rightarrow> complex\<close>
  assumes \<open>f abs_summable_on A\<close>
  shows \<open>(\<lambda>x. f x *\<^sub>C tc_butterfly (ket x) (ket x)) summable_on A\<close>
proof -
  define M where \<open>M = (\<Sum>\<^sub>\<infinity>x\<in>A. norm (f x))\<close>
  have \<open>(\<Sum>x\<in>F. cmod (f x) * norm (tc_butterfly (ket x) (ket x))) \<le> M\<close> if \<open>finite F\<close> and \<open>F \<subseteq> A\<close> for F
  proof -
    have \<open>(\<Sum>x\<in>F. norm (f x) * norm (tc_butterfly (ket x) (ket x))) = (\<Sum>x\<in>F. norm (f x))\<close>
      by (simp add: norm_tc_butterfly)
    also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>x\<in>A. norm (f x))\<close>
      using assms finite_sum_le_infsum norm_ge_zero that(1) that(2) by blast
    also have \<open>\<dots> = M\<close>
      by (simp add: M_def)
    finally show ?thesis
      by -
  qed
  then have \<open>(\<lambda>x. norm (f x *\<^sub>C tc_butterfly (ket x) (ket x))) abs_summable_on A\<close>
    apply (intro nonneg_bdd_above_summable_on bdd_aboveI)
    by auto
  then show ?thesis
    by (auto intro: abs_summable_summable)
qed

lift_definition tc_apply :: \<open>('a::chilbert_space,'b::chilbert_space) trace_class \<Rightarrow> 'a \<Rightarrow> 'b\<close> is cblinfun_apply.

lemma bounded_cbilinear_tc_apply: \<open>bounded_cbilinear tc_apply\<close>
  apply (rule bounded_cbilinear.intro; transfer)
      apply (auto intro!: simp: )
  apply (auto intro!: exI[of _ 1] cblinfun.add_left cblinfun.add_right cblinfun.scaleC_right)
  by (smt (verit, del_insts) Unsorted_HSTP.norm_leq_trace_norm mult_hom.hom_zero mult_less_cancel_right norm_cblinfun norm_not_less_zero not_square_less_zero ordered_field_class.sign_simps(5) ordered_field_class.sign_simps(50) rel_simps(70) vector_space_over_itself.scale_eq_0_iff vector_space_over_itself.scale_left_commute vector_space_over_itself.vector_space_assms(3))


(* TODO move *)
lemma tc_butterfly_scaleC_has_sum:
  fixes f :: \<open>'a \<Rightarrow> complex\<close>
  assumes \<open>f abs_summable_on UNIV\<close>
  shows \<open>((\<lambda>x. f x *\<^sub>C tc_butterfly (ket x) (ket x)) has_sum diagonal_operator_tc f) UNIV\<close>
proof -
  define D where \<open>D = (\<Sum>\<^sub>\<infinity>x. f x *\<^sub>C tc_butterfly (ket x) (ket x))\<close>
  have bdd_f: \<open>bdd_above (range (\<lambda>x. cmod (f x)))\<close>
    by (metis assms summable_on_bdd_above_real)

  have \<open>ket y \<bullet>\<^sub>C from_trace_class D (ket z) = ket y \<bullet>\<^sub>C from_trace_class (diagonal_operator_tc f) (ket z)\<close> for y z
  proof -
    have blin_tc_apply: \<open>bounded_linear (\<lambda>a. tc_apply a (ket z))\<close>
      by (intro bounded_clinear.bounded_linear bounded_cbilinear.bounded_clinear_left bounded_cbilinear_tc_apply)
    have summ: \<open>(\<lambda>x. f x *\<^sub>C tc_butterfly (ket x) (ket x)) summable_on UNIV\<close>
      by (intro tc_butterfly_scaleC_summable assms)

    have \<open>((\<lambda>x. f x *\<^sub>C tc_butterfly (ket x) (ket x)) has_sum D) UNIV\<close>
      by (simp add: D_def summ)
    with blin_tc_apply have \<open>((\<lambda>x. tc_apply (f x *\<^sub>C tc_butterfly (ket x) (ket x)) (ket z)) has_sum tc_apply D (ket z)) UNIV\<close>
      by (rule Infinite_Sum.has_sum_bounded_linear)
    then have \<open>((\<lambda>x. ket y \<bullet>\<^sub>C tc_apply (f x *\<^sub>C tc_butterfly (ket x) (ket x)) (ket z)) has_sum ket y \<bullet>\<^sub>C tc_apply D (ket z)) UNIV\<close>
      by (smt (verit, best) has_sum_cong has_sum_imp_summable has_sum_infsum infsumI infsum_cinner_left summable_on_cinner_left)
    then have \<open>((\<lambda>x. of_bool (x=y) * of_bool (y=z) * f y) has_sum ket y \<bullet>\<^sub>C tc_apply D (ket z)) UNIV\<close>
      apply (rule has_sum_cong[THEN iffD2, rotated])
      by (auto intro!: simp: tc_apply.rep_eq scaleC_trace_class.rep_eq tc_butterfly.rep_eq)
    then have \<open>((\<lambda>x. of_bool (y=z) * f y) has_sum ket y \<bullet>\<^sub>C tc_apply D (ket z)) {y}\<close>
      apply (rule has_sum_cong_neutral[THEN iffD2, rotated -1])
      by auto
    then have \<open>ket y \<bullet>\<^sub>C tc_apply D (ket z) = of_bool (y=z) * f y\<close>
      by simp
    also have \<open>\<dots> = ket y \<bullet>\<^sub>C from_trace_class (diagonal_operator_tc f) (ket z)\<close>
      by (simp add: diagonal_operator_tc.rep_eq assms diagonal_operator_ket bdd_f)
    finally show ?thesis
      by (simp add: tc_apply.rep_eq)
  qed
  then have \<open>from_trace_class D = from_trace_class (diagonal_operator_tc f)\<close>
    by (auto intro!: equal_ket cinner_ket_eqI)
  then have \<open>D = diagonal_operator_tc f\<close>
    by (simp add: from_trace_class_inject)
  with tc_butterfly_scaleC_summable[OF assms]
  show ?thesis
    using D_def by force
qed

(* TODO move *)
lemma tc_butterfly_scaleC_infsum:
  fixes f :: \<open>'a \<Rightarrow> complex\<close>
  shows \<open>(\<Sum>\<^sub>\<infinity>x. f x *\<^sub>C tc_butterfly (ket x) (ket x)) = diagonal_operator_tc f\<close>
proof (cases \<open>f abs_summable_on UNIV\<close>)
  case True
  then show ?thesis
    using infsumI tc_butterfly_scaleC_has_sum by fastforce
next
  case False
  then have [simp]: \<open>diagonal_operator_tc f = 0\<close>
    apply (transfer fixing: f) by simp
  have \<open>\<not> (\<lambda>x. f x *\<^sub>C tc_butterfly (ket x) (ket x)) summable_on UNIV\<close>
  proof (rule notI)
    assume \<open>(\<lambda>x. f x *\<^sub>C tc_butterfly (ket x) (ket x)) summable_on UNIV\<close>
    then have \<open>(\<lambda>x. trace_tc (f x *\<^sub>C tc_butterfly (ket x) (ket x))) summable_on UNIV\<close>
      apply (rule summable_on_bounded_linear[rotated])
      by (simp add: bounded_clinear.bounded_linear)
    then have \<open>f summable_on UNIV\<close>
      apply (rule summable_on_cong[THEN iffD1, rotated])
      apply (transfer' fixing: f)
      by (simp add: trace_scaleC trace_butterfly)
    with False
    show False
      by (metis summable_on_iff_abs_summable_on_complex)
  qed
  then have [simp]: \<open>(\<Sum>\<^sub>\<infinity>x. f x *\<^sub>C tc_butterfly (ket x) (ket x)) = 0\<close>
    using infsum_not_exists by blast
  show ?thesis 
    by simp
qed


lemma has_sum_in_0: 
  assumes \<open>t1_space T\<close> and \<open>0 \<in> topspace T\<close>
  assumes \<open>\<And>x. x\<in>M \<Longrightarrow> f x = 0\<close>
  shows \<open>has_sum_in T f M 0\<close>
proof -
  have \<open>limitin T (\<lambda>_. 0) 0 (finite_subsets_at_top M)\<close>
    apply (rule limitin_const_iff[THEN iffD2])
    by (auto intro!: assms)
  then have \<open>limitin T (sum f) 0 (finite_subsets_at_top M)\<close>
    apply (rule limitin_cong[THEN iffD2, rotated])
    by (auto intro!: eventually_finite_subsets_at_top_weakI sum.neutral assms simp: )
  then show ?thesis
    by (simp add: has_sum_in_def)
qed

(* TODO: remove "hausdorff" *)
lemma Hausdorff_space_hausdorff: \<open>Hausdorff_space T \<longleftrightarrow> hausdorff T\<close>
  by (auto simp: hausdorff_def Hausdorff_space_def disjnt_def)


lemma infsum_in_0:
  assumes \<open>hausdorff T\<close> and \<open>0 \<in> topspace T\<close>
  assumes \<open>\<And>x. x\<in>M \<Longrightarrow> f x = 0\<close>
  shows \<open>infsum_in T f M = 0\<close>
proof -
  have \<open>has_sum_in T f M 0\<close>
    using assms
    by (auto intro!: has_sum_in_0 Hausdorff_imp_t1_space simp: Hausdorff_space_hausdorff)
  then show ?thesis
    by (meson assms(1) has_sum_in_infsum_in has_sum_in_unique not_summable_infsum_in_0)
qed

lemma norm_sgn_1: 
  fixes x :: \<open>'a :: {sgn_div_norm, real_normed_vector}\<close>
  assumes \<open>x \<noteq> 0\<close>
  shows \<open>norm (sgn x) = 1\<close>
  by (simp add: assms norm_sgn)



(* TODO replace original cblinfun_cinner_eqI *)
lemma cblinfun_cinner_eqI:
  fixes A B :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>\<And>\<psi>. norm \<psi> = 1 \<Longrightarrow> cinner \<psi> (A *\<^sub>V \<psi>) = cinner \<psi> (B *\<^sub>V \<psi>)\<close>
  shows \<open>A = B\<close>
proof -
  have \<open>cinner \<psi> (A *\<^sub>V \<psi>) = cinner \<psi> (B *\<^sub>V \<psi>)\<close> for \<psi>
    apply (cases \<open>\<psi> = 0\<close>)
    using assms[of \<open>sgn \<psi>\<close>]
    by (simp_all add: norm_sgn_1 sgn_div_norm cblinfun.scaleR_right)
  then show ?thesis
    by (rule cblinfun_cinner_eqI)
qed

lemma summable_Sigma_positive:
  fixes f :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c::{topological_comm_monoid_add, linorder_topology,
             ordered_comm_monoid_add, conditionally_complete_linorder}\<close>
  assumes \<open>\<And>x. x\<in>X \<Longrightarrow> f x summable_on Y x\<close>
  assumes \<open>(\<lambda>x. \<Sum>\<^sub>\<infinity>y\<in>Y x. f x y) summable_on X\<close>
  assumes \<open>\<And>x y. x \<in> X \<Longrightarrow> y \<in> Y x \<Longrightarrow> f x y \<ge> 0\<close>
  shows \<open>(\<lambda>(x, y). f x y) summable_on (SIGMA x:X. Y x)\<close>
proof -
  have \<open>(\<Sum>(x,y)\<in>F. f x y) \<le> (\<Sum>\<^sub>\<infinity>x\<in>X. \<Sum>\<^sub>\<infinity>y\<in>Y x. f x y)\<close> if \<open>F \<subseteq> Sigma X Y\<close> and \<open>finite F\<close> for F
  proof -
    define g where \<open>g x y = (if (x,y) \<in> Sigma X Y then f x y else 0)\<close> for x y
    have g_pos[iff]: \<open>g x y \<ge> 0\<close> for x y
       using assms by (auto intro!: simp: g_def)
    have \<open>(\<Sum>(x,y)\<in>F. f x y) = (\<Sum>(x,y)\<in>F. g x y)\<close>
      by (smt (verit, ccfv_SIG) g_def split_cong subsetD sum.cong that(1))
    also have \<open>(\<Sum>(x,y)\<in>F. g x y) \<le> (\<Sum>(x,y)\<in>fst ` F \<times> snd ` F. g x y)\<close>
      using that assms apply (auto intro!: sum_mono2 assms simp: image_iff)
      by force+
    also have \<open>\<dots> = (\<Sum>x\<in>fst ` F. \<Sum>y\<in>snd ` F. g x y)\<close>
      by (metis (no_types, lifting) finite_imageI sum.Sigma sum.cong that(2))
    also have \<open>\<dots> = (\<Sum>x\<in>fst ` F. \<Sum>\<^sub>\<infinity>y\<in>snd ` F. g x y)\<close>
      by (metis finite_imageI infsum_finite that(2))
    also have \<open>\<dots> \<le> (\<Sum>x\<in>fst ` F. \<Sum>\<^sub>\<infinity>y\<in>Y x. g x y)\<close>
      apply (intro sum_mono infsum_mono_neutral)
      using assms that
          apply (auto intro!: simp: )
       apply (smt (verit, best) Orderings.order_eq_iff SigmaD1 g_def subsetD summable_on_comparison_test)
      by (simp add: g_def)
    also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x\<in>fst ` F. \<Sum>\<^sub>\<infinity>y\<in>Y x. g x y)\<close>
      using that by (auto intro!: infsum_finite[symmetric] simp: )
    also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>x\<in>X. \<Sum>\<^sub>\<infinity>y\<in>Y x. g x y)\<close>
      apply (rule infsum_mono_neutral)
      using that assms apply (auto intro!: infsum_nonneg simp: )
      by (metis (mono_tags, lifting) g_def infsum_cong mem_Sigma_iff summable_on_cong)
    also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x\<in>X. \<Sum>\<^sub>\<infinity>y\<in>Y x. f x y)\<close>
      by (smt (verit, ccfv_threshold) g_def infsum_cong mem_Sigma_iff)
    finally show ?thesis
      by -
  qed
  then show ?thesis
    apply (rule_tac nonneg_bdd_above_summable_on)
    by (auto intro!: assms bdd_aboveI2)
qed

lemma monotone_convergence_tc:
  fixes f :: \<open>'b \<Rightarrow> ('a, 'a::chilbert_space) trace_class\<close>
  assumes bounded: \<open>\<forall>\<^sub>F x in F. trace_tc (f x) \<le> B\<close>
  assumes pos: \<open>\<forall>\<^sub>F x in F. f x \<ge> 0\<close>
  assumes increasing: \<open>increasing_filter (filtermap f F)\<close>
  shows \<open>\<exists>L. (f \<longlongrightarrow> L) F\<close>
proof -
  wlog \<open>F \<noteq> \<bottom>\<close>
    using negation by simp
  then have \<open>filtermap f F \<noteq> \<bottom>\<close>
    by (simp add: filtermap_bot_iff)
  have \<open>mono_on {t::('a,'a) trace_class. t \<ge> 0} trace_tc\<close>
    by (simp add: ord.mono_onI trace_tc_mono)
  with increasing
  have \<open>increasing_filter (filtermap (trace_tc o f) F)\<close>
    unfolding filtermap_compose
    apply (rule increasing_filtermap)
    by (auto intro!: pos simp: eventually_filtermap)
  then obtain l where l: \<open>((\<lambda>x. trace_tc (f x)) \<longlongrightarrow> l) F\<close>
    apply atomize_elim
    apply (rule monotone_convergence_complex)
    using bounded by (simp_all add: o_def)
  have \<open>cauchy_filter (filtermap f F)\<close>
  proof (rule cauchy_filter_metricI)
    fix e :: real assume \<open>e > 0\<close>
    define d where \<open>d = e/4\<close>
    have \<open>\<forall>\<^sub>F x in filtermap f F. dist (trace_tc x) l < d\<close>
      unfolding eventually_filtermap
      using l apply (rule tendstoD)
      using \<open>e > 0\<close> by (simp add: d_def)
    then obtain P1 where ev_P1: \<open>eventually P1 (filtermap f F)\<close> and P1: \<open>P1 x \<Longrightarrow> dist (trace_tc x) l < d\<close> for x
      by blast
    from increasing obtain P2 where ev_P2: \<open>eventually P2 (filtermap f F)\<close> and
      P2: \<open>P2 x \<Longrightarrow> (\<forall>\<^sub>F z in filtermap f F. z \<ge> x)\<close> for x
      using increasing_filter_def by blast
    define P where \<open>P x \<longleftrightarrow> P1 x \<and> P2 x\<close> for x
    with ev_P1 ev_P2 have ev_P: \<open>eventually P (filtermap f F)\<close>
      by (auto intro!: eventually_conj simp: P_def[abs_def])
    have \<open>dist x y < e\<close> if \<open>P x\<close> and \<open>P y\<close> for x y
    proof -
      from \<open>P x\<close> have \<open>\<forall>\<^sub>F z in filtermap f F. z \<ge> x\<close>
        by (simp add: P_def P2)
      moreover from \<open>P y\<close> have \<open>\<forall>\<^sub>F z in filtermap f F. z \<ge> y\<close>
        by (simp add: P_def P2)
      ultimately have \<open>\<forall>\<^sub>F z in filtermap f F. z \<ge> x \<and> z \<ge> y \<and> P1 z\<close>
        using ev_P1 by (auto intro!: eventually_conj)
      from eventually_happens'[OF \<open>filtermap f F \<noteq> \<bottom>\<close> this]
      obtain z where \<open>z \<ge> x\<close> and \<open>z \<ge> y\<close> and \<open>P1 z\<close>
        by auto
      have \<open>dist x y \<le> norm (z - x) + norm (z - y)\<close>
        by (metis (no_types, lifting) diff_add_cancel diff_add_eq_diff_diff_swap dist_trace_class_def norm_minus_commute norm_triangle_sub)
      also from \<open>x \<le> z\<close> \<open>y \<le> z\<close> have \<open>\<dots> = (trace_tc z - trace_tc x) + (trace_tc z - trace_tc y)\<close>
        by (metis (no_types, lifting) cross3_simps(16) diff_left_mono diff_self norm_tc_pos of_real_hom.hom_add trace_tc_plus)
      also from \<open>x \<le> z\<close> \<open>y \<le> z\<close> have \<open>\<dots> = norm (trace_tc z - trace_tc x) + norm (trace_tc z - trace_tc y)\<close>                  
        by (simp add: Extra_Ordered_Fields.complex_of_real_cmod trace_tc_mono)
      also have \<open>\<dots> = dist (trace_tc z) (trace_tc x) + dist (trace_tc z) (trace_tc y)\<close>
        using dist_complex_def by presburger
      also have \<open>\<dots> \<le> (dist (trace_tc z) l + dist (trace_tc x) l) + (dist (trace_tc z) l + dist (trace_tc y) l)\<close> 
        apply (intro complex_of_real_mono add_mono)
        by (simp_all add: dist_triangle2)
      also from P1 \<open>P1 z\<close> that have \<open>\<dots> < 4 * d\<close>
        by (smt (verit, best) P_def complex_of_real_strict_mono_iff)
      also have \<open>\<dots> = e\<close>
        by (simp add: d_def)
      finally show ?thesis
        by simp
    qed
    with ev_P show \<open>\<exists>P. eventually P (filtermap f F) \<and> (\<forall>x y. P x \<and> P y \<longrightarrow> dist x y < e)\<close>
      by blast
  qed
  then have \<open>convergent_filter (filtermap f F)\<close>
  using cauchy_filter_convergent by fastforce
  then show \<open>\<exists>L. (f \<longlongrightarrow> L) F\<close>
    by (simp add: convergent_filter_iff filterlim_def)
qed


lemma nonneg_bdd_above_summable_on_tc:
  fixes f :: \<open>'a \<Rightarrow> ('c::chilbert_space, 'c) trace_class\<close>
  assumes pos: \<open>\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0\<close>
  assumes bdd: \<open>bdd_above (trace_tc ` sum f ` {F. F\<subseteq>A \<and> finite F})\<close>
  shows \<open>f summable_on A\<close>
proof -
  have pos': \<open>(\<Sum>x\<in>F. f x) \<ge> 0\<close> if \<open>finite F\<close> and \<open>F \<subseteq> A\<close> for F
    using that pos
    by (simp add: basic_trans_rules(31) sum_nonneg)
  from pos have incr: \<open>increasing_filter (filtermap (sum f) (finite_subsets_at_top A))\<close>
    by (auto intro!: increasing_filtermap[where X=\<open>{F. finite F \<and> F \<subseteq> A}\<close>] mono_onI sum_mono2)
  from bdd obtain B where B: \<open>trace_tc (sum f X) \<le> B\<close> if \<open>finite X\<close> and \<open>X \<subseteq> A\<close> for X
    apply atomize_elim
    by (auto simp: bdd_above_def)
  show ?thesis
    apply (simp add: summable_on_def has_sum_def)
    by (safe intro!: pos' incr monotone_convergence_tc[where B=B] B
        eventually_finite_subsets_at_top_weakI)
qed


lemma summable_Sigma_positive_tc:
  fixes f :: \<open>'a \<Rightarrow> 'b \<Rightarrow> ('c, 'c::chilbert_space) trace_class\<close>
  assumes \<open>\<And>x. x\<in>X \<Longrightarrow> f x summable_on Y x\<close>
  assumes \<open>(\<lambda>x. \<Sum>\<^sub>\<infinity>y\<in>Y x. f x y) summable_on X\<close>
  assumes \<open>\<And>x y. x \<in> X \<Longrightarrow> y \<in> Y x \<Longrightarrow> f x y \<ge> 0\<close>
  shows \<open>(\<lambda>(x, y). f x y) summable_on (SIGMA x:X. Y x)\<close>
proof -
  have \<open>trace_tc (\<Sum>(x,y)\<in>F. f x y) \<le> trace_tc (\<Sum>\<^sub>\<infinity>x\<in>X. \<Sum>\<^sub>\<infinity>y\<in>Y x. f x y)\<close> if \<open>F \<subseteq> Sigma X Y\<close> and \<open>finite F\<close> for F
  proof -
    define g where \<open>g x y = (if (x,y) \<in> Sigma X Y then f x y else 0)\<close> for x y
    have g_pos[iff]: \<open>g x y \<ge> 0\<close> for x y
      using assms by (auto intro!: simp: g_def)
    have g_summable: \<open>g x summable_on Y x\<close> for x
      by (metis assms(1) g_def mem_Sigma_iff summable_on_0 summable_on_cong)
    have sum_g_summable: \<open>(\<lambda>x. \<Sum>\<^sub>\<infinity>y\<in>Y x. g x y) summable_on X\<close>
      by (metis (mono_tags, lifting) SigmaI g_def assms(2) infsum_cong summable_on_cong)
    have \<open>(\<Sum>(x,y)\<in>F. f x y) = (\<Sum>(x,y)\<in>F. g x y)\<close>
      by (smt (verit, ccfv_SIG) g_def split_cong subsetD sum.cong that(1))
    also have \<open>(\<Sum>(x,y)\<in>F. g x y) \<le> (\<Sum>(x,y)\<in>fst ` F \<times> snd ` F. g x y)\<close>
      using that assms apply (auto intro!: sum_mono2 assms simp: image_iff)
      by force+
    also have \<open>\<dots> = (\<Sum>x\<in>fst ` F. \<Sum>y\<in>snd ` F. g x y)\<close>
      by (metis (no_types, lifting) finite_imageI sum.Sigma sum.cong that(2))
    also have \<open>\<dots> = (\<Sum>x\<in>fst ` F. \<Sum>\<^sub>\<infinity>y\<in>snd ` F. g x y)\<close>
      by (metis finite_imageI infsum_finite that(2))
    also have \<open>\<dots> \<le> (\<Sum>x\<in>fst ` F. \<Sum>\<^sub>\<infinity>y\<in>Y x. g x y)\<close>
      apply (intro sum_mono infsum_mono_neutral_traceclass)
      using assms that
          apply (auto intro!: g_summable)
      by (simp add: g_def)
    also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x\<in>fst ` F. \<Sum>\<^sub>\<infinity>y\<in>Y x. g x y)\<close>
      using that by (auto intro!: infsum_finite[symmetric] simp: )
    also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>x\<in>X. \<Sum>\<^sub>\<infinity>y\<in>Y x. g x y)\<close>
      apply (rule infsum_mono_neutral_traceclass)
      using that assms by (auto intro!: infsum_nonneg_traceclass sum_g_summable)
    also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x\<in>X. \<Sum>\<^sub>\<infinity>y\<in>Y x. f x y)\<close>
      by (smt (verit, ccfv_threshold) g_def infsum_cong mem_Sigma_iff)
    finally show ?thesis
      using trace_tc_mono by blast
  qed
  then show ?thesis
    apply (rule_tac nonneg_bdd_above_summable_on_tc)
    by (auto intro!: assms bdd_aboveI2)
qed


lemma infsum_Sigma_positive:
  fixes f :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c::{topological_comm_monoid_add, linorder_topology,
             ordered_comm_monoid_add, conditionally_complete_linorder, banach}\<close>
  assumes \<open>\<And>x. x\<in>X \<Longrightarrow> f x summable_on Y x\<close>
  assumes \<open>\<And>x y. x \<in> X \<Longrightarrow> y \<in> Y x \<Longrightarrow> f x y \<ge> 0\<close>
  shows \<open>(\<Sum>\<^sub>\<infinity>x\<in>X. \<Sum>\<^sub>\<infinity>y\<in>Y x. f x y) = (\<Sum>\<^sub>\<infinity>(x,y)\<in>Sigma X Y. f x y)\<close>
proof (cases \<open>(\<lambda>x. \<Sum>\<^sub>\<infinity>y\<in>Y x. f x y) summable_on X\<close>)
  case True
  show ?thesis
    apply (rule infsum_Sigma'_banach)
    apply (rule summable_Sigma_positive)
    using assms True by auto
next
  case False
  then have 1: \<open>(\<Sum>\<^sub>\<infinity>x\<in>X. \<Sum>\<^sub>\<infinity>y\<in>Y x. f x y) = 0\<close>
    using infsum_not_exists by blast
  from False have \<open>\<not> (\<lambda>(x,y). f x y) summable_on Sigma X Y\<close>
    using summable_on_Sigma_banach by blast
  then have 2: \<open>(\<Sum>\<^sub>\<infinity>(x, y)\<in>Sigma X Y. f x y) = 0\<close>
    using infsum_not_exists by blast
  from 1 2 show ?thesis
    by simp
qed


lemma infsum_Sigma_positive_tc:
  fixes f :: \<open>'a \<Rightarrow> 'b \<Rightarrow> ('c::chilbert_space, 'c) trace_class\<close>
  assumes \<open>\<And>x. x\<in>X \<Longrightarrow> f x summable_on Y x\<close>
  assumes \<open>\<And>x y. x \<in> X \<Longrightarrow> y \<in> Y x \<Longrightarrow> f x y \<ge> 0\<close>
  shows \<open>(\<Sum>\<^sub>\<infinity>x\<in>X. \<Sum>\<^sub>\<infinity>y\<in>Y x. f x y) = (\<Sum>\<^sub>\<infinity>(x,y)\<in>Sigma X Y. f x y)\<close>
proof (cases \<open>(\<lambda>x. \<Sum>\<^sub>\<infinity>y\<in>Y x. f x y) summable_on X\<close>)
  case True
  show ?thesis
    apply (rule infsum_Sigma'_banach)
    apply (rule summable_Sigma_positive_tc)
    using assms True by auto
next
  case False
  then have 1: \<open>(\<Sum>\<^sub>\<infinity>x\<in>X. \<Sum>\<^sub>\<infinity>y\<in>Y x. f x y) = 0\<close>
    using infsum_not_exists by blast
  from False have \<open>\<not> (\<lambda>(x,y). f x y) summable_on Sigma X Y\<close>
    using summable_on_Sigma_banach by blast
  then have 2: \<open>(\<Sum>\<^sub>\<infinity>(x, y)\<in>Sigma X Y. f x y) = 0\<close>
    using infsum_not_exists by blast
  from 1 2 show ?thesis
    by simp
qed

lemma infsum_swap_positive_tc:
  fixes f :: \<open>'a \<Rightarrow> 'b \<Rightarrow> ('c::chilbert_space, 'c) trace_class\<close>
  assumes \<open>\<And>x. x\<in>X \<Longrightarrow> f x summable_on Y\<close>
  assumes \<open>\<And>y. y\<in>Y \<Longrightarrow> (\<lambda>x. f x y) summable_on X\<close>
  assumes \<open>\<And>x y. x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> f x y \<ge> 0\<close>
  shows \<open>(\<Sum>\<^sub>\<infinity>x\<in>X. \<Sum>\<^sub>\<infinity>y\<in>Y. f x y) = (\<Sum>\<^sub>\<infinity>y\<in>Y. \<Sum>\<^sub>\<infinity>x\<in>X. f x y)\<close>
proof -
  have \<open>(\<Sum>\<^sub>\<infinity>x\<in>X. \<Sum>\<^sub>\<infinity>y\<in>Y. f x y) = (\<Sum>\<^sub>\<infinity>(x,y)\<in>X\<times>Y. f x y)\<close>
    apply (rule infsum_Sigma_positive_tc)
    using assms by auto
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>(y,x)\<in>Y\<times>X. f x y)\<close>
    apply (subst product_swap[symmetric])
    by (simp add: infsum_reindex o_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>y\<in>Y. \<Sum>\<^sub>\<infinity>x\<in>X. f x y)\<close>
    apply (rule infsum_Sigma_positive_tc[symmetric])
    using assms by auto
  finally show ?thesis
    by -
qed


(* TODO move *)
lemma trace_tc_pos: \<open>t \<ge> 0 \<Longrightarrow> trace_tc t \<ge> 0\<close>
  using trace_tc_mono by fastforce

(* TODO replace original *)
lemma infsum_nonneg_complex:
  fixes f :: "'a \<Rightarrow> complex"
  assumes "\<And>x. x \<in> M \<Longrightarrow> 0 \<le> f x"
  shows "infsum f M \<ge> 0" (is "?lhs \<ge> _")
  apply (cases \<open>f summable_on M\<close>)
   apply (metis assms infsum_0_simp summable_on_0_simp infsum_mono_complex)
  by (simp add: infsum_not_exists)

lemma has_sumI:
  assumes \<open>f summable_on X\<close>
  assumes \<open>infsum f X = s\<close>
  shows \<open>(f has_sum s) X\<close>
  using assms has_sum_infsum by blast

lemma separating_set_clinear_cspan:
  assumes \<open>cspan S = UNIV\<close>
  shows \<open>separating_set clinear S\<close>
  using assms
  by (auto intro: complex_vector.linear_eq_on simp: separating_set_def)

lemma separating_density_ops:
  assumes \<open>B > 0\<close>
  shows \<open>separating_set clinear {t :: ('a::chilbert_space, 'a) trace_class. 0 \<le> t \<and> norm t \<le> B}\<close>
proof -
  define S where \<open>S = {t :: ('a, 'a) trace_class. 0 \<le> t \<and> norm t \<le> B}\<close>
  have \<open>cspan S = UNIV\<close>
  proof (intro Set.set_eqI iffI UNIV_I)
    fix t :: \<open>('a, 'a) trace_class\<close>
    from trace_class_decomp_4pos'
    obtain t1 t2 t3 t4 where t_decomp: \<open>t = t1 - t2 + \<i> *\<^sub>C t3 - \<i> *\<^sub>C t4\<close>
      and pos: \<open>t1 \<ge> 0\<close> \<open>t2 \<ge> 0\<close> \<open>t3 \<ge> 0\<close> \<open>t4 \<ge> 0\<close>
      by fast
    have \<open>t' \<in> cspan S\<close> if \<open>t' \<ge> 0\<close> for t'
    proof -
      define t'' where \<open>t'' = (B / norm t') *\<^sub>R t'\<close>
      have \<open>t'' \<in> S\<close>
        using \<open>B > 0\<close>
        by (simp add: S_def that zero_le_scaleR_iff t''_def)
      have t'_t'': \<open>t' = (norm t' / B) *\<^sub>R t''\<close>
        using \<open>B > 0\<close> t''_def by auto
      show \<open>t' \<in> cspan S\<close>
        apply (subst t'_t'')
        using \<open>t'' \<in> S\<close>
        by (simp add: scaleR_scaleC complex_vector.span_clauses)
    qed
    with pos have \<open>t1 \<in> cspan S\<close> and \<open>t2 \<in> cspan S\<close> and \<open>t3 \<in> cspan S\<close> and \<open>t4 \<in> cspan S\<close>
      by auto
    then show \<open>t \<in> cspan S\<close>
      by (auto intro!: complex_vector.span_diff complex_vector.span_add complex_vector.span_scale
          intro: complex_vector.span_base simp: t_decomp)
  qed
  then show \<open>separating_set clinear S\<close>
    by (rule separating_set_clinear_cspan)
qed

lemma summable_abs_summable_tc:
  fixes f :: \<open>'a \<Rightarrow> ('b::chilbert_space,'b) trace_class\<close>
  assumes \<open>f summable_on X\<close>
  assumes \<open>\<And>x. x\<in>X \<Longrightarrow> f x \<ge> 0\<close>
  shows \<open>f abs_summable_on X\<close>
proof -
  from assms(1) have \<open>(\<lambda>x. trace_tc (f x)) summable_on X\<close>
    apply (rule summable_on_bounded_linear[rotated])
    by (simp add: bounded_clinear.bounded_linear)
  then have \<open>(\<lambda>x. Re (trace_tc (f x))) summable_on X\<close>
    using summable_on_Re by blast
  then show \<open>(\<lambda>x. norm (f x)) summable_on X\<close>
    by (metis (mono_tags, lifting) assms(2) norm_tc_pos_Re summable_on_cong)
qed

lemma map_commutant_empty[simp]: \<open>map_commutant {Map.empty} = UNIV\<close>
  by (auto simp: map_commutant_def)

lemma redundant_option_case: \<open>(case a of None \<Rightarrow> None | Some x \<Rightarrow> Some x) = a\<close>
  apply (cases a)
  by auto




end
