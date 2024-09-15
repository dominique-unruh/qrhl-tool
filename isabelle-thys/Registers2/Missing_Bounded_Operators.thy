theory Missing_Bounded_Operators
  imports Complex_Bounded_Operators.Complex_L2
    Complex_Bounded_Operators.Cblinfun_Code
    Hilbert_Space_Tensor_Product.Hilbert_Space_Tensor_Product
    With_Type.With_Type Misc_Missing
    Hilbert_Space_Tensor_Product.Partial_Trace
    Missing2
begin

unbundle cblinfun_notation
no_notation m_inv ("inv\<index> _" [81] 80)
unbundle jnf_notation
hide_const (open) Finite_Cartesian_Product.vec
hide_const (open) Finite_Cartesian_Product.mat                      
hide_const (open) Order.top
hide_const (open) Coset.kernel
hide_fact (open) Infinite_Set_Sum.abs_summable_on_comparison_test

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
  shows \<open>let 'c::type = permute_and_tensor1_cblinfun_basis R in
            (\<forall>A. sandwich (permute_and_tensor1_cblinfun_U rep_c f R) (A \<otimes>\<^sub>o id_cblinfun) =
            permute_and_tensor1_cblinfun f R A)
            \<and> unitary (permute_and_tensor1_cblinfun_U rep_c f R)\<close>
proof with_type_intro
  define S where \<open>S = permute_and_tensor1_cblinfun_basis R\<close>
  show \<open>S \<noteq> {}\<close>
    by (simp add: permute_and_tensor1_cblinfun_basis_def S_def equiv_R equivp_reflp)
  fix Rep :: \<open>'c \<Rightarrow> 'a set\<close> and abs_ops

  assume \<open>bij_betw Rep UNIV S\<close>
  then interpret type_definition Rep \<open>inv Rep\<close> S
    using type_definition_bij_betw_iff by blast

  assume \<open>WITH_TYPE_REL_type (\<lambda>x y. x = Rep y) () abs_ops\<close>
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
  apply (subst infsum_bounded_linear[symmetric, where f=b and A=X and h=\<open>\<lambda>b. a o\<^sub>C\<^sub>L b\<close>])
  by (auto intro!: bounded_clinear.bounded_linear bounded_clinear_cblinfun_compose_right simp add: assms o_def)
lemma infsum_cblinfun_compose_right:
  assumes \<open>a summable_on X\<close>
  shows \<open>(\<Sum>\<^sub>\<infinity>x\<in>X. a x o\<^sub>C\<^sub>L b) = (\<Sum>\<^sub>\<infinity>x\<in>X. a x) o\<^sub>C\<^sub>L b\<close>
  apply (subst infsum_bounded_linear[symmetric, where f=a and A=X and h=\<open>\<lambda>a. a o\<^sub>C\<^sub>L b\<close>])
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


(* TODO remove? (norm_sgn good enough?) *)
lemma norm_sgn_1: 
  fixes x :: \<open>'a :: {sgn_div_norm, real_normed_vector}\<close>
  assumes \<open>x \<noteq> 0\<close>
  shows \<open>norm (sgn x) = 1\<close>
  by (simp add: assms norm_sgn)




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


(* TODO replace original *) thm infsum_nonneg_complex
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

definition minimal_projection_in :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a) set \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow> bool\<close> where
  \<open>minimal_projection_in A P \<longleftrightarrow> P \<in> A \<and> is_Proj P \<and> P \<noteq> 0 \<and> (\<forall>P'\<in>A. is_Proj P' \<longrightarrow> P' \<le> P \<longrightarrow> P' \<noteq> 0 \<longrightarrow> P' = P)\<close>

lemma minimal_projection_in_UNIV_rank1:
  assumes \<open>minimal_projection_in UNIV a\<close>
  shows \<open>rank1 a\<close>
proof (rule ccontr)
  assume \<open>\<not> rank1 a\<close>
  then have \<open>a \<noteq> 0\<close>
    by fastforce
  then obtain \<psi> where \<open>norm \<psi> = 1\<close> and \<open>\<psi> \<in> space_as_set (a *\<^sub>S \<top>)\<close>
    by (metis Complex_Bounded_Linear_Function.zero_cblinfun_image Proj_compose_cancelI Proj_on_own_range cblinfun_assoc_left(2) cblinfun_image_bot_zero ccsubspace_leI_unit is_Proj_0)
  have \<open>is_Proj (proj \<psi>)\<close>
    by (simp add: \<open>norm \<psi> = 1\<close> butterfly_is_Proj)
  have \<open>proj \<psi> \<noteq> 0\<close>
    by (smt (verit, ccfv_threshold) Proj_0_compl Proj_idempotent Proj_ortho_compl Proj_range Proj_top UNIV_I \<open>norm \<psi> = 1\<close> basic_trans_rules(31) cblinfun_fixes_range ccspan_superset diff_zero norm_eq_zero singletonI top_ccsubspace.rep_eq)
  have \<open>space_as_set (proj \<psi> *\<^sub>S \<top>) \<le> space_as_set (a *\<^sub>S \<top>)\<close>
    by (metis Proj_fixes_image \<open>\<psi> \<in> space_as_set (a *\<^sub>S \<top>)\<close> \<open>norm \<psi> = 1\<close> butterfly_eq_proj cblinfun_comp_butterfly cblinfun_fixes_range space_as_setI_via_Proj subsetI)
  then have \<open>proj \<psi> \<le> a\<close>
    by (metis Proj_mono Proj_on_own_range Proj_range assms ccsubspace_leI minimal_projection_in_def)
  from assms \<open>is_Proj (proj \<psi>)\<close> \<open>proj \<psi> \<le> a\<close> \<open>proj \<psi> \<noteq> 0\<close>
  have \<open>a = proj \<psi>\<close>
    using minimal_projection_in_def by blast
  then have \<open>rank1 a\<close>
    by simp
  with \<open>\<not> rank1 a\<close> show False
    by simp
qed



lemma minimal_projection_in_proj:
  assumes \<open>\<psi> \<noteq> 0\<close> and \<open>proj \<psi> \<in> A\<close>
  shows \<open>minimal_projection_in A (proj \<psi>)\<close>
proof (unfold minimal_projection_in_def, intro conjI impI ballI)
  from assms show \<open>proj \<psi> \<in> A\<close>
    by simp
  show \<open>is_Proj (proj \<psi>)\<close>
    by simp
  from assms show \<open>proj \<psi> \<noteq> 0\<close>
    by (metis Proj_bot Proj_inj bot_ccsubspace.rep_eq ccspan_superset empty_not_insert singleton_insert_inj_eq' subset_singleton_iff)
  show \<open>a = proj \<psi>\<close>
    if \<open>a \<in> A\<close> and \<open>is_Proj a\<close> and \<open>a \<le> proj \<psi>\<close> and \<open>a \<noteq> 0\<close> for a
    by (metis Proj_mono Proj_on_own_range cblinfun_image_bot_zero ccspan_of_empty some_onb_of_ccspan some_onb_of_0 subspace_of_1dim_ccspan that(2) that(3) that(4))
qed


lemma is_Sup_empty_bot[iff]: \<open>is_Sup {} (\<bottom>::_::order_bot)\<close>
  by (simp add: is_Sup_def)

lemma OFCLASS_conditionally_complete_lattice_Sup_orderI:
  assumes \<open>Sup {} = (\<bottom>::'a)\<close>
  shows \<open>OFCLASS('a::{conditionally_complete_lattice, order_bot}, Sup_order_class)\<close>
proof
  show \<open>is_Sup X (\<Squnion> X)\<close> if \<open>has_Sup X\<close> for X :: \<open>'a set\<close>
  proof (cases \<open>X = {}\<close>)
    case True
    then show ?thesis
      by (simp add: assms)
  next
    case False
    with that show ?thesis
      by (auto intro!: is_Sup_cSup has_Sup_bdd_above simp: )
  qed
  show \<open>is_Sup {x, y} (x \<squnion> y)\<close> if \<open>has_Sup {x, y}\<close> for x y :: 'a
  by (simp add: is_Sup_def)
qed

instance nat :: Sup_order
  apply (rule OFCLASS_conditionally_complete_lattice_Sup_orderI)
  by (simp add: bot_nat_def)

lemma (in Sup_order) Sup_eqI:
  "(\<And>y. y \<in> A \<Longrightarrow> y \<le> x) \<Longrightarrow> (\<And>y. (\<And>z. z \<in> A \<Longrightarrow> z \<le> y) \<Longrightarrow> x \<le> y) \<Longrightarrow> \<Squnion>A = x"
  apply (rule is_Sup_eq_Sup[symmetric])
  using local.is_SupI by blast
lemma Sup_upper_has_Sup:
  fixes x :: "'a :: Sup_order"
    and A :: "'a set"
  assumes \<open>has_Sup A\<close>
  assumes "x \<in> A"
  shows "x \<le> \<Squnion> A"
  using assms is_Sup_Sup is_Sup_def by blast

lemma has_Sup_finite:
  fixes X :: \<open>'a::semilattice_sup set\<close>
  assumes \<open>finite X\<close> and \<open>X \<noteq> {}\<close>
  shows \<open>has_Sup X\<close>
proof -
  have \<open>x \<in> X \<Longrightarrow> x \<le> \<Squnion>\<^sub>f\<^sub>i\<^sub>n X\<close> for x
    by (simp add: Sup_fin.coboundedI assms)
  moreover have \<open> (\<And>x. x \<in> X \<Longrightarrow> x \<le> y) \<Longrightarrow> \<Squnion>\<^sub>f\<^sub>i\<^sub>n X \<le> y\<close> for y
    by (auto intro!: Sup_fin.boundedI assms)
  ultimately have \<open>is_Sup X (Sup_fin X)\<close>
    by (rule is_SupI)
  then show \<open>has_Sup X\<close>
    using is_Sup_has_Sup by blast
qed


end
