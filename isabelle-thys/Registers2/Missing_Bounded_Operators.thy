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

lemma trace_minus: 
  assumes \<open>trace_class a\<close> \<open>trace_class b\<close>
  shows \<open>trace (a - b) = trace a - trace b\<close>
  by (metis (no_types, lifting) add_uminus_conv_diff assms(1) assms(2) trace_class_uminus trace_plus trace_uminus)
                                    
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


lemma sandwich_tc_id_cblinfun[simp]: \<open>sandwich_tc id_cblinfun t = t\<close>
  by (simp add: from_trace_class_inverse sandwich_tc_apply)


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

interpretation tensor_op_cbilinear: bounded_cbilinear tensor_op
  by simp

lemma finite_rank_cspan_butterflies:
  \<open>finite_rank a \<longleftrightarrow> a \<in> cspan (range (case_prod butterfly))\<close>
  for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
proof -
  have \<open>(Collect finite_rank :: ('a \<Rightarrow>\<^sub>C\<^sub>L 'b) set) = cspan (Collect rank1)\<close>
    using finite_rank_def by fastforce
  also have \<open>\<dots> = cspan (insert 0 (Collect rank1))\<close>
    by force
  also have \<open>\<dots> = cspan (range (case_prod butterfly))\<close>
    apply (rule arg_cong[where f=cspan])
    apply (auto intro!: simp: rank1_iff_butterfly case_prod_beta image_def)
    apply auto
    by (metis butterfly_0_left)
  finally show ?thesis
    by auto
qed

lemma finite_rank_comp_right: \<open>finite_rank (a o\<^sub>C\<^sub>L b)\<close> if \<open>finite_rank b\<close>
  for a b :: \<open>_::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L _::chilbert_space\<close>
proof -
  from that
  have \<open>b \<in> cspan (range (case_prod butterfly))\<close>
    by (simp add: finite_rank_cspan_butterflies)
  then have \<open>a o\<^sub>C\<^sub>L b \<in> ((o\<^sub>C\<^sub>L) a) ` cspan (range (case_prod butterfly))\<close>
    by fast
  also have \<open>\<dots> = cspan (((o\<^sub>C\<^sub>L) a) ` range (case_prod butterfly))\<close>
    by (simp add: clinear_cblinfun_compose_right complex_vector.linear_span_image)
  also have \<open>\<dots> \<subseteq> cspan (range (case_prod butterfly))\<close>
    apply (auto intro!: complex_vector.span_mono
        simp add: image_image case_prod_unfold cblinfun_comp_butterfly image_def)
    by fast
  finally show ?thesis
    using finite_rank_cspan_butterflies by blast
qed

lemma finite_rank_comp_left: \<open>finite_rank (a o\<^sub>C\<^sub>L b)\<close> if \<open>finite_rank a\<close>
  for a b :: \<open>_::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L _::chilbert_space\<close>
proof -
  from that
  have \<open>a \<in> cspan (range (case_prod butterfly))\<close>
    by (simp add: finite_rank_cspan_butterflies)
  then have \<open>a o\<^sub>C\<^sub>L b \<in> (\<lambda>a. a o\<^sub>C\<^sub>L b) ` cspan (range (case_prod butterfly))\<close>
    by fast
  also have \<open>\<dots> = cspan ((\<lambda>a. a o\<^sub>C\<^sub>L b) ` range (case_prod butterfly))\<close>
    by (simp add: clinear_cblinfun_compose_left complex_vector.linear_span_image)
  also have \<open>\<dots> \<subseteq> cspan (range (case_prod butterfly))\<close>
    apply (auto intro!: complex_vector.span_mono
        simp add: image_image case_prod_unfold butterfly_comp_cblinfun image_def)
    by fast
  finally show ?thesis
    using finite_rank_cspan_butterflies by blast
qed


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

lemma compact_op_comp_left: \<open>compact_op (a o\<^sub>C\<^sub>L b)\<close> if \<open>compact_op a\<close>
  for a b :: \<open>_::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L _::chilbert_space\<close>
proof -
  from that have \<open>a \<in> closure (Collect finite_rank)\<close>
  using compact_op_finite_rank by blast
  then have \<open>a o\<^sub>C\<^sub>L b \<in> (\<lambda>a. a o\<^sub>C\<^sub>L b) ` closure (Collect finite_rank)\<close>
    by blast
  also have \<open>\<dots> \<subseteq> closure ((\<lambda>a. a o\<^sub>C\<^sub>L b) ` Collect finite_rank)\<close>
    by (auto intro!: closure_bounded_linear_image_subset bounded_clinear.bounded_linear bounded_clinear_cblinfun_compose_left)
  also have \<open>\<dots> \<subseteq> closure (Collect finite_rank)\<close>
    by (auto intro!: closure_mono finite_rank_comp_left)
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

lemma hilbert_schmidt_norm_geq_norm:
(* TODO cite conway operators, Prop 18.6(c) *)
  assumes \<open>hilbert_schmidt a\<close>
  shows \<open>norm a \<le> hilbert_schmidt_norm a\<close>
proof -
  have \<open>norm (a x) \<le> hilbert_schmidt_norm a\<close> if \<open>norm x = 1\<close> for x
  proof -
    obtain B where \<open>x \<in> B\<close> and \<open>is_onb B\<close>
      using orthonormal_basis_exists[of \<open>{x}\<close>] \<open>norm x = 1\<close>
      by force
    have \<open>(norm (a x))\<^sup>2 = (\<Sum>\<^sub>\<infinity>x\<in>{x}. (norm (a x))\<^sup>2)\<close>
      by simp
    also have \<open>\<dots> \<le> (\<Sum>\<^sub>\<infinity>x\<in>B. (norm (a x))\<^sup>2)\<close>
      apply (rule infsum_mono_neutral)
      by (auto intro!: summable_hilbert_schmidt_norm_square \<open>is_onb B\<close> assms \<open>x \<in> B\<close>)
    also have \<open>\<dots> = (hilbert_schmidt_norm a)\<^sup>2\<close>
      using infsum_hilbert_schmidt_norm_square[OF \<open>is_onb B\<close> assms]
      by -
    finally show ?thesis
      by force
  qed
  then show ?thesis
    by (auto intro!: norm_cblinfun_bound_unit)
qed

lemma finite_rank_trace_class: \<open>trace_class a\<close> if \<open>finite_rank a\<close>
  for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
proof -
  from \<open>finite_rank a\<close> obtain F f where \<open>finite F\<close> and \<open>F \<subseteq> Collect rank1\<close>
    and a_def: \<open>a = (\<Sum>x\<in>F. f x *\<^sub>C x)\<close>
    by (smt (verit, ccfv_threshold) complex_vector.span_explicit finite_rank_def mem_Collect_eq)
  then show \<open>trace_class a\<close>
    unfolding a_def
    apply induction
    by (auto intro!: trace_class_plus trace_class_scaleC intro: rank1_trace_class)
qed

lemma trace_class_hilbert_schmidt: \<open>hilbert_schmidt a\<close> if \<open>trace_class a\<close>
  for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  by (auto intro!: trace_class_comp_right that simp: hilbert_schmidt_def)

lemma finite_rank_hilbert_schmidt: \<open>hilbert_schmidt a\<close> if \<open>finite_rank a\<close>
  for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  using finite_rank_comp_right finite_rank_trace_class hilbert_schmidtI that by blast

lemma hilbert_schmidt_compact: \<open>compact_op a\<close> if \<open>hilbert_schmidt a\<close>
  for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  \<comment> \<open>(* TODO cite: conway operators *), Corollary 18.7.
      (Only the second part. The first part is stated inside the proof though.)\<close>
proof -
  have \<open>\<exists>b. finite_rank b \<and> hilbert_schmidt_norm (b - a) < \<epsilon>\<close> if \<open>\<epsilon> > 0\<close> for \<epsilon>
  proof -
    have \<open>\<epsilon>\<^sup>2 > 0\<close>
      using that by force
    obtain B :: \<open>'a set\<close> where \<open>is_onb B\<close>
      using is_onb_some_chilbert_basis by blast
    with \<open>hilbert_schmidt a\<close> have a_sum_B: \<open>(\<lambda>x. (norm (a *\<^sub>V x))\<^sup>2) summable_on B\<close>
      by (auto intro!: summable_hilbert_schmidt_norm_square)
    then have \<open>((\<lambda>x. (norm (a *\<^sub>V x))\<^sup>2) has_sum (\<Sum>\<^sub>\<infinity>x\<in>B. (norm (a *\<^sub>V x))\<^sup>2)) B\<close>
      using has_sum_infsum by blast
    from tendsto_iff[THEN iffD1, rule_format, OF this[unfolded has_sum_def] \<open>\<epsilon>\<^sup>2 > 0\<close>]
    obtain F where [simp]: \<open>finite F\<close> and \<open>F \<subseteq> B\<close>
      and Fbound: \<open>dist (\<Sum>x\<in>F. (norm (a *\<^sub>V x))\<^sup>2) (\<Sum>\<^sub>\<infinity>x\<in>B. (norm (a *\<^sub>V x))\<^sup>2) < \<epsilon>\<^sup>2\<close>
      apply atomize_elim
      by (auto intro!: simp: eventually_finite_subsets_at_top)
    define p b where \<open>p = (\<Sum>x\<in>F. selfbutter x)\<close> and \<open>b = a o\<^sub>C\<^sub>L p\<close>
    have [simp]: \<open>p x = x\<close> if \<open>x \<in> F\<close> for x
      apply (simp add: p_def cblinfun.sum_left)
      apply (subst sum_single[where i=x])
      using \<open>F \<subseteq> B\<close> that \<open>is_onb B\<close>
      by (auto intro!: simp:  cnorm_eq_1 is_onb_def is_ortho_set_def)
    have [simp]: \<open>p x = 0\<close> if \<open>x \<in> B - F\<close> for x
      using \<open>F \<subseteq> B\<close> that \<open>is_onb B\<close>
      apply (auto intro!: sum.neutral simp add: p_def cblinfun.sum_left is_onb_def is_ortho_set_def)
      by auto
    have \<open>finite_rank p\<close>
      by (simp add: finite_rank_sum p_def)
    then have \<open>finite_rank b\<close>
      by (simp add: b_def finite_rank_comp_right)
    with \<open>hilbert_schmidt a\<close> have \<open>hilbert_schmidt (b - a)\<close>
      by (auto intro!: hilbert_schmidt_minus intro: finite_rank_hilbert_schmidt)
    then have \<open>(hilbert_schmidt_norm (b - a))\<^sup>2 = (\<Sum>\<^sub>\<infinity>x\<in>B. (norm ((b - a) *\<^sub>V x))\<^sup>2)\<close>
      by (simp add: infsum_hilbert_schmidt_norm_square \<open>is_onb B\<close>)
    also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x\<in>B-F. (norm (a *\<^sub>V x))\<^sup>2)\<close>
      by (auto intro!: infsum_cong_neutral
          simp: b_def cblinfun.diff_left)
    also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x\<in>B. (norm (a *\<^sub>V x))\<^sup>2) - (\<Sum>x\<in>F. (norm (a *\<^sub>V x))\<^sup>2)\<close>
      apply (subst infsum_Diff)
      using \<open>F \<subseteq> B\<close> a_sum_B by auto
    also have \<open>\<dots> < \<epsilon>\<^sup>2\<close>
      using Fbound
      by (simp add: dist_norm)
    finally show ?thesis
      using \<open>finite_rank b\<close>
      using power_less_imp_less_base that by fastforce
  qed
  then have \<open>\<exists>b. finite_rank b \<and> dist b a < \<epsilon>\<close> if \<open>\<epsilon> > 0\<close> for \<epsilon>
    apply (rule ex_mono[rule_format, rotated])
     apply (auto intro!: that simp: dist_norm)
    using hilbert_schmidt_minus \<open>hilbert_schmidt a\<close> finite_rank_hilbert_schmidt hilbert_schmidt_norm_geq_norm
    by fastforce
  then show ?thesis
    by (simp add: compact_op_finite_rank closure_approachable)
qed

lemma trace_class_compact: \<open>compact_op a\<close> if \<open>trace_class a\<close> 
  for a :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  by (simp add: hilbert_schmidt_compact that trace_class_hilbert_schmidt)


lemma cspan_tc_transfer[transfer_rule]: 
  includes lifting_syntax
  shows \<open>(rel_set cr_trace_class ===> rel_set cr_trace_class) cspan cspan\<close>
proof (intro rel_funI rel_setI)
  fix B :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b) set\<close> and C
  assume \<open>rel_set cr_trace_class B C\<close>
  then have BC: \<open>B = from_trace_class ` C\<close>
    by (auto intro!: simp: cr_trace_class_def image_iff rel_set_def)
      (*     then have tc_B: \<open>B \<subseteq> Collect trace_class\<close> (* TODO used? *)
      by auto *)

  show \<open>\<exists>t\<in>cspan C. cr_trace_class a t\<close> if \<open>a \<in> cspan B\<close> for a
  proof -
    from that obtain F f where \<open>finite F\<close> and \<open>F \<subseteq> B\<close> and a_sum: \<open>a = (\<Sum>x\<in>F. f x *\<^sub>C x)\<close>
      by (auto simp: complex_vector.span_explicit)
    from \<open>F \<subseteq> B\<close>
    obtain F' where \<open>F' \<subseteq> C\<close> and FF': \<open>F = from_trace_class ` F'\<close>
      by (auto elim!: subset_imageE simp: BC)
    define t where \<open>t = (\<Sum>x\<in>F'. f (from_trace_class x) *\<^sub>C x)\<close>
    have \<open>a = from_trace_class t\<close>
      by (simp add: a_sum t_def from_trace_class_sum scaleC_trace_class.rep_eq FF'
          sum.reindex o_def from_trace_class_inject inj_on_def)
    moreover have \<open>t \<in> cspan C\<close>
      by (metis (no_types, lifting) \<open>F' \<subseteq> C\<close> complex_vector.span_clauses(4) complex_vector.span_sum complex_vector.span_superset subsetD t_def)
    ultimately show \<open>\<exists>t\<in>cspan C. cr_trace_class a t\<close>
      by (auto simp: cr_trace_class_def)
  qed

  show \<open>\<exists>a\<in>cspan B. cr_trace_class a t\<close> if \<open>t \<in> cspan C\<close> for t
  proof -
    from that obtain F f where \<open>finite F\<close> and \<open>F \<subseteq> C\<close> and t_sum: \<open>t = (\<Sum>x\<in>F. f x *\<^sub>C x)\<close>
      by (auto simp: complex_vector.span_explicit)
    define a where \<open>a = (\<Sum>x\<in>F. f x *\<^sub>C from_trace_class x)\<close>
    then have \<open>a = from_trace_class t\<close>
      by (simp add: t_sum a_def from_trace_class_sum scaleC_trace_class.rep_eq)
    moreover have \<open>a \<in> cspan B\<close>
      using BC \<open>F \<subseteq> C\<close> 
      by (auto intro!: complex_vector.span_base complex_vector.span_sum complex_vector.span_scale simp: a_def)
    ultimately show ?thesis
      by (auto simp: cr_trace_class_def)
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
  have \<open>((\<lambda>j. Abs_trace_class (tensor_ell2_right (ket j)* o\<^sub>C\<^sub>L from_trace_class \<rho> o\<^sub>C\<^sub>L tensor_ell2_right (ket j))) 
        has_sum partial_trace \<rho>) UNIV\<close>
    using partial_trace_has_sum by force
  then have \<open>((\<lambda>j. x \<bullet>\<^sub>C (from_trace_class (Abs_trace_class (tensor_ell2_right (ket j)* o\<^sub>C\<^sub>L 
                          from_trace_class \<rho> o\<^sub>C\<^sub>L tensor_ell2_right (ket j))) *\<^sub>V y))
        has_sum x\<rho>y) UNIV\<close>
    unfolding x\<rho>y_def
    apply (rule Infinite_Sum.has_sum_bounded_linear[rotated])
    by (intro bounded_clinear.bounded_linear bounded_linear_intros)
  then have \<open>((\<lambda>j. x \<bullet>\<^sub>C (tensor_ell2_right (ket j)* *\<^sub>V from_trace_class \<rho> *\<^sub>V y \<otimes>\<^sub>s ket j)) has_sum
     x\<rho>y) UNIV\<close>
    by (simp add: x\<rho>y_def Abs_trace_class_inverse trace_class_comp_left trace_class_comp_right)
  then show ?thesis
    by (metis (no_types, lifting) cinner_adj_right has_sum_cong tensor_ell2_right_apply x\<rho>y_def)
qed

lemma vector_sandwich_partial_trace:
  \<open>x \<bullet>\<^sub>C (from_trace_class (partial_trace \<rho>) *\<^sub>V y) =
      (\<Sum>\<^sub>\<infinity>z. ((x \<otimes>\<^sub>s ket z) \<bullet>\<^sub>C (from_trace_class \<rho> *\<^sub>V (y \<otimes>\<^sub>s ket z))))\<close>
  by (metis (mono_tags, lifting) infsumI vector_sandwich_partial_trace_has_sum)


(* TODO move *)
lemma partial_trace_plus: \<open>partial_trace (t + u) = partial_trace t + partial_trace u\<close>
proof -
  from partial_trace_has_sum[of t] and partial_trace_has_sum[of u]
  have \<open>((\<lambda>j. Abs_trace_class (tensor_ell2_right (ket j)* o\<^sub>C\<^sub>L from_trace_class t o\<^sub>C\<^sub>L tensor_ell2_right (ket j))
            + Abs_trace_class (tensor_ell2_right (ket j)* o\<^sub>C\<^sub>L from_trace_class u o\<^sub>C\<^sub>L tensor_ell2_right (ket j))) has_sum
           partial_trace t + partial_trace u) UNIV\<close> (is \<open>(?f has_sum _) _\<close>)
    by (rule has_sum_add)
  moreover have \<open>?f j = Abs_trace_class (tensor_ell2_right (ket j)* o\<^sub>C\<^sub>L from_trace_class (t + u) o\<^sub>C\<^sub>L tensor_ell2_right (ket j))\<close> (is \<open>?f j = ?g j\<close>) for j
    by (smt (verit) Abs_trace_class_inverse cblinfun_compose_add_left cblinfun_compose_add_right from_trace_class_inverse mem_Collect_eq plus_trace_class.rep_eq trace_class_comp_left trace_class_comp_right trace_class_from_trace_class)
  ultimately have \<open>(?g has_sum partial_trace t + partial_trace u) UNIV\<close>
    by simp
  moreover have \<open>(?g has_sum partial_trace (t + u)) UNIV\<close>
    by (simp add: partial_trace_has_sum)
  ultimately show ?thesis
    using has_sum_unique by blast
qed



end
