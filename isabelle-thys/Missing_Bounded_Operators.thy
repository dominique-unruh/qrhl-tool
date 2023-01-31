theory Missing_Bounded_Operators
  imports Complex_Bounded_Operators.Complex_L2 Complex_Bounded_Operators.Cblinfun_Code Complex_Bounded_Operators.BO_Unsorted
    Tensor_Product.Hilbert_Space_Tensor_Product
    With_Type.With_Type
begin

unbundle cblinfun_notation
no_notation m_inv ("inv\<index> _" [81] 80)
unbundle jnf_notation
hide_const (open) Finite_Cartesian_Product.vec
hide_const (open) Finite_Cartesian_Product.mat

declare cindependent_ket[simp]

definition explicit_cblinfun :: \<open>('a \<Rightarrow> 'b \<Rightarrow> complex) \<Rightarrow> ('b ell2, 'a ell2) cblinfun\<close> where
  \<open>explicit_cblinfun m = cblinfun_extension (range ket) (\<lambda>a. Abs_ell2 (\<lambda>j. m j (inv ket a)))\<close>

definition explicit_cblinfun_exists :: \<open>('a \<Rightarrow> 'b \<Rightarrow> complex) \<Rightarrow> bool\<close> where
  \<open>explicit_cblinfun_exists m \<longleftrightarrow> 
    (\<forall>a. has_ell2_norm (\<lambda>j. m j a)) \<and> 
      cblinfun_extension_exists (range ket) (\<lambda>a. Abs_ell2 (\<lambda>j. m j (inv ket a)))\<close>

lemma cblinfun_extension_exists_restrict:
  assumes \<open>B \<subseteq> A\<close>
  assumes \<open>\<And>x. x\<in>B \<Longrightarrow> f x = g x\<close>
  assumes \<open>cblinfun_extension_exists A f\<close>
  shows \<open>cblinfun_extension_exists B g\<close>
  by (metis assms cblinfun_extension_exists_def subset_eq)

lemma norm_ell2_bound_trunc:
  assumes \<open>\<And>M. finite M \<Longrightarrow> norm (trunc_ell2 M \<psi>) \<le> B\<close>
  shows \<open>norm \<psi> \<le> B\<close>
proof -
  note trunc_ell2_lim_at_UNIV[of \<psi>]
  then have \<open>((\<lambda>S. norm (trunc_ell2 S \<psi>)) \<longlongrightarrow> norm \<psi>) (finite_subsets_at_top UNIV)\<close>
    using tendsto_norm by auto
  then show \<open>norm \<psi> \<le> B\<close>
    apply (rule tendsto_upperbound)
    using assms apply (rule eventually_finite_subsets_at_top_weakI)
    by auto
qed

lemma clinear_Rep_ell2[simp]: \<open>clinear (\<lambda>\<psi>. Rep_ell2 \<psi> i)\<close>
  by (simp add: clinearI plus_ell2.rep_eq scaleC_ell2.rep_eq)

lemma explicit_cblinfun_exists_bounded:
  fixes B :: real
  assumes \<open>\<And>S T \<psi>. finite S \<Longrightarrow> finite T \<Longrightarrow> (\<And>a. a\<notin>T \<Longrightarrow> \<psi> a = 0) \<Longrightarrow>
            (\<Sum>b\<in>S. (cmod (\<Sum>a\<in>T. \<psi> a *\<^sub>C m b a))\<^sup>2) \<le> B * (\<Sum>a\<in>T. (cmod (\<psi> a))\<^sup>2)\<close>
  shows \<open>explicit_cblinfun_exists m\<close>
proof -
  define F f where \<open>F = complex_vector.construct (range ket) f\<close>
    and \<open>f = (\<lambda>a. Abs_ell2 (\<lambda>j. m j (inv ket a)))\<close>
  from assms[where S=\<open>{}\<close> and T=\<open>{undefined}\<close> and \<psi>=\<open>\<lambda>x. of_bool (x=undefined)\<close>]
  have \<open>B \<ge> 0\<close>
    by auto
  have has_norm: \<open>has_ell2_norm (\<lambda>b. m b a)\<close> for a
  proof (unfold has_ell2_norm_def, intro nonneg_bdd_above_summable_on bdd_aboveI)
    show \<open>0 \<le> cmod ((m x a)\<^sup>2)\<close> for x
      by simp
    fix B'
    assume \<open>B' \<in> sum (\<lambda>x. cmod ((m x a)\<^sup>2)) ` {F. F \<subseteq> UNIV \<and> finite F}\<close>
    then obtain S where [simp]: \<open>finite S\<close> and B'_def: \<open>B' = (\<Sum>x\<in>S. cmod ((m x a)\<^sup>2))\<close>
      by blast
    from assms[where S=S and T=\<open>{a}\<close> and \<psi>=\<open>\<lambda>x. of_bool (x=a)\<close>]
    show \<open>B' \<le> B\<close>
      by (simp add: norm_power B'_def)
  qed
  have \<open>clinear F\<close>
    by (auto intro!: complex_vector.linear_construct simp: F_def)
  have F_B: \<open>norm (F \<psi>) \<le> (sqrt B) * norm \<psi>\<close> if \<psi>_range_ket: \<open>\<psi> \<in> cspan (range ket)\<close> for \<psi>
  proof -
    from that
    obtain T' where \<open>finite T'\<close> and \<open>T' \<subseteq> range ket\<close> and \<psi>T': \<open>\<psi> \<in> cspan T'\<close>
      by (meson vector_finitely_spanned)
        (*   from that
    obtain T' r where \<open>finite T'\<close> and \<open>T' \<subseteq> range ket\<close> and
      \<psi>T': \<open>\<psi> = (\<Sum>v\<in>T'. r v *\<^sub>C v)\<close>
      unfolding complex_vector.span_explicit
      by blast *)
    then obtain T where T'_def: \<open>T' = ket ` T\<close>
      by (meson subset_image_iff)
    have \<open>finite T\<close>
      by (metis T'_def \<open>finite T'\<close> finite_image_iff inj_ket inj_on_subset subset_UNIV)
    have \<psi>T: \<open>\<psi> \<in> cspan (ket ` T)\<close>
      using T'_def \<psi>T' by blast
    have Rep_\<psi>: \<open>Rep_ell2 \<psi> x = 0\<close> if \<open>x \<notin> T\<close> for x
      using _ _ \<psi>T apply (rule complex_vector.linear_eq_0_on_span)
       apply auto
      by (metis ket.rep_eq that)
    have \<open>norm (trunc_ell2 S (F \<psi>)) \<le> sqrt B * norm \<psi>\<close> if \<open>finite S\<close> for S
    proof -
      have *: \<open>cconstruct (range ket) f \<psi> = (\<Sum>x\<in>T. Rep_ell2 \<psi> x *\<^sub>C f (ket x))\<close>
      proof (rule complex_vector.linear_eq_on[where x=\<psi> and B=\<open>ket ` T\<close>])
        show \<open>clinear (cconstruct (range ket) f)\<close>
          using F_def \<open>clinear F\<close> by blast
        show \<open>clinear (\<lambda>a. \<Sum>x\<in>T. Rep_ell2 a x *\<^sub>C f (ket x))\<close>
          by (auto intro!: clinear_compose[unfolded o_def, OF clinear_Rep_ell2] complex_vector.linear_compose_sum)
        show \<open>\<psi> \<in> cspan (ket ` T)\<close>
          by (simp add: \<psi>T)
        have \<open>f b = (\<Sum>x\<in>T. Rep_ell2 b x *\<^sub>C f (ket x))\<close> 
          if \<open>b \<in> ket ` T\<close> for b
        proof -
          define b' where \<open>b' = inv ket b\<close>
          have bb': \<open>b = ket b'\<close>
            using b'_def that by force
          show ?thesis
            apply (subst sum_single[where i=b'])
            using that by (auto simp add: \<open>finite T\<close> bb' ket.rep_eq)
        qed
        then show \<open>cconstruct (range ket) f b = (\<Sum>x\<in>T. Rep_ell2 b x *\<^sub>C f (ket x))\<close>
          if \<open>b \<in> ket ` T\<close> for b
          apply (subst complex_vector.construct_basis)
          using that by auto
      qed
      have \<open>(norm (trunc_ell2 S (F \<psi>)))\<^sup>2 = (norm (trunc_ell2 S (\<Sum>x\<in>T. Rep_ell2 \<psi> x *\<^sub>C f (ket x))))\<^sup>2\<close>
        apply (rule arg_cong[where f=\<open>\<lambda>x. (norm (trunc_ell2 _ x))\<^sup>2\<close>])
        by (simp add: F_def * )
      also have \<open>\<dots> = (norm (trunc_ell2 S (\<Sum>x\<in>T. Rep_ell2 \<psi> x *\<^sub>C Abs_ell2 (\<lambda>b. m b x))))\<^sup>2\<close>
        by (simp add: f_def)
      also have \<open>\<dots> = (\<Sum>i\<in>S. (cmod (Rep_ell2 (\<Sum>x\<in>T. Rep_ell2 \<psi> x *\<^sub>C Abs_ell2 (\<lambda>b. m b x)) i))\<^sup>2)\<close>
        by (simp add: that norm_trunc_ell2_finite real_sqrt_pow2 sum_nonneg)
      also have \<open>\<dots> = (\<Sum>i\<in>S. (cmod (\<Sum>x\<in>T. Rep_ell2 \<psi> x *\<^sub>C Rep_ell2 (Abs_ell2 (\<lambda>b. m b x)) i))\<^sup>2)\<close>
        by (simp add: complex_vector.linear_sum[OF clinear_Rep_ell2]
            clinear.scaleC[OF clinear_Rep_ell2])
      also have \<open>\<dots> = (\<Sum>i\<in>S. (cmod (\<Sum>x\<in>T. Rep_ell2 \<psi> x *\<^sub>C m i x))\<^sup>2)\<close>
        using has_norm by (simp add: Abs_ell2_inverse)
      also have \<open>\<dots> \<le> B * (\<Sum>x\<in>T. (cmod (Rep_ell2 \<psi> x))\<^sup>2)\<close>
        using \<open>finite S\<close> \<open>finite T\<close> Rep_\<psi> by (rule assms)
      also have \<open>\<dots> = B * ((norm (trunc_ell2 T \<psi>))\<^sup>2)\<close>
        by (simp add: \<open>finite T\<close> norm_trunc_ell2_finite sum_nonneg)
      also have \<open>\<dots> \<le> B * (norm \<psi>)\<^sup>2\<close>
        by (simp add: mult_left_mono \<open>B \<ge> 0\<close> trunc_ell2_reduces_norm)
      finally show ?thesis
        apply (rule_tac power2_le_imp_le)
        by (simp_all add: \<open>0 \<le> B\<close> power_mult_distrib)
    qed
    then show ?thesis
      by (rule norm_ell2_bound_trunc)
  qed
  then have \<open>cblinfun_extension_exists (cspan (range ket)) F\<close>
    apply (rule cblinfun_extension_exists_hilbert[rotated -1])
    by (auto intro: \<open>clinear F\<close> complex_vector.linear_add complex_vector.linear_scale)
  then have ex: \<open>cblinfun_extension_exists (range ket) f\<close>
    apply (rule cblinfun_extension_exists_restrict[rotated -1])
    by (simp_all add: F_def complex_vector.span_superset complex_vector.construct_basis)
  from ex has_norm
  show ?thesis
    using explicit_cblinfun_exists_def f_def by blast
qed

lemma explicit_cblinfun_exists_finite_dim[simp]: \<open>explicit_cblinfun_exists m\<close> for m :: "_::finite \<Rightarrow> _ :: finite \<Rightarrow> _"
  by (auto simp: explicit_cblinfun_exists_def cblinfun_extension_exists_finite_dim)

lemma explicit_cblinfun_ket: \<open>explicit_cblinfun m *\<^sub>V ket a = Abs_ell2 (\<lambda>b. m b a)\<close> if \<open>explicit_cblinfun_exists m\<close>
  using that by (auto simp: explicit_cblinfun_exists_def explicit_cblinfun_def cblinfun_extension_apply)

lemma Rep_ell2_explicit_cblinfun_ket[simp]: \<open>Rep_ell2 (explicit_cblinfun m *\<^sub>V ket a) b = m b a\<close> if \<open>explicit_cblinfun_exists m\<close>
  using that apply (simp add: explicit_cblinfun_ket)
  by (simp add: Abs_ell2_inverse explicit_cblinfun_exists_def)

(* Original enum_idx_bound should say this, and be [simp] *)
lemma enum_idx_bound'[simp]: "enum_idx x < CARD('a)" for x :: "'a::enum"
  using enum_idx_bound unfolding card_UNIV_length_enum by auto

(* basis_enum should define "canonical_basis_length" (or maybe "dimension" or something). Reason: code generation otherwise has to 
    compute the length of canonical_basis each time the dimension is needed.
   Or it could be in the/a type class "finite_dim".
 *)
abbreviation \<open>cdimension (x::'a::basis_enum itself) \<equiv> length (canonical_basis :: 'a list)\<close>


class eenum = enum +
  fixes enum_nth :: \<open>nat \<Rightarrow> 'a\<close>
  fixes enum_index :: \<open>'a \<Rightarrow> nat\<close>
  assumes enum_nth_enum[simp]: \<open>\<And>i. i < CARD('a) \<Longrightarrow> Enum.enum ! i = enum_nth i\<close>
  assumes enum_nth_invalid: \<open>\<And>i. i \<ge> CARD('a) \<Longrightarrow> enum_nth i = enum_nth 0\<close> (* To get enum_index_nth below *)
  assumes enum_nth_index[simp]: \<open>\<And>a. enum_nth (enum_index a) = a\<close>
  assumes enum_index_bound[simp]: \<open>\<And>a. enum_index a < CARD('a)\<close>

lemma inj_enum_index[simp]: \<open>inj enum_index\<close>
  by (metis enum_nth_index injI)

lemma bij_betw_enum_index: \<open>bij_betw (enum_index :: 'a::eenum \<Rightarrow> nat) UNIV {..<CARD('a)}\<close>
proof -
  let ?f = \<open>enum_index :: 'a::eenum \<Rightarrow> nat\<close>
  have \<open>range ?f \<subseteq> {..<CARD('a)}\<close>
    by (simp add: image_subsetI)
  moreover have \<open>card (range ?f) = card {..<CARD('a)}\<close>
    by (simp add: card_image)
  moreover have \<open>finite {..<CARD('a)}\<close>
    by simp
  ultimately have \<open>range ?f = {..<CARD('a)}\<close>
    by (meson card_subset_eq)
  then show ?thesis
    by (simp add: bij_betw_imageI)
qed

lemma inj_on_enum_nth[simp]: \<open>inj_on (enum_nth :: _ \<Rightarrow> 'a::eenum) {..<CARD('a)}\<close>
  by (metis (mono_tags, opaque_lifting) bij_betw_enum_index enum_nth_index f_the_inv_into_f_bij_betw inj_on_inverseI)

lemma enum_index_nth: \<open>enum_index (enum_nth i :: 'a::eenum) = (if i < CARD('a) then i else 0)\<close>
  by (metis bij_betw_enum_index enum_nth_index enum_nth_invalid f_the_inv_into_f_bij_betw lessThan_iff linorder_not_le zero_less_card_finite)

instantiation bool :: eenum begin
definition \<open>enum_index_bool x = (if x then 1 else 0 :: nat)\<close>
definition \<open>enum_nth_bool (i::nat) = (i=1)\<close>
instance 
  apply standard
  apply (auto simp: enum_bool_def enum_index_bool_def enum_nth_bool_def)
  by (metis less_2_cases nth_Cons_0)
end

instantiation prod :: (eenum, eenum) eenum begin
definition \<open>enum_index_prod = (\<lambda>(i::'a,j::'b). enum_index i * CARD('b) + enum_index j)\<close>
definition \<open>enum_nth_prod ij = (let i = ij div CARD('b) in if i < CARD('a) then (enum_nth i, enum_nth (ij mod CARD('b))) else (enum_nth 0, enum_nth 0) :: 'a\<times>'b)\<close>
instance
proof standard
  show \<open>i < CARD('a \<times> 'b) \<Longrightarrow> (Enum.enum ! i :: 'a\<times>'b) = enum_nth i\<close> for i
    apply (auto simp: card_UNIV_length_enum[symmetric] enum_nth_enum enum_prod_def product_nth enum_nth_prod_def Let_def)
    using less_mult_imp_div_less by blast+
  show \<open>CARD('a \<times> 'b) \<le> i \<Longrightarrow> enum_nth i = (enum_nth 0 :: 'a\<times>'b)\<close> for i
    by (auto simp: div_less_iff_less_mult enum_nth_prod_def)
  show \<open>enum_nth (enum_index a) = a\<close> for a :: \<open>'a\<times>'b\<close>
    apply (cases a)
    by (auto simp: div_less_iff_less_mult enum_nth_prod_def enum_index_prod_def)
  show \<open>enum_index a < CARD('a \<times> 'b)\<close> for a :: \<open>'a\<times>'b\<close>
    apply (cases a)
    by (auto simp: enum_index_prod_def)
    (* by (metis (no_types, lifting) add_cancel_right_right div_less div_mult_self3 enum_index_bound less_eq_div_iff_mult_less_eq less_not_refl2 linorder_not_less zero_less_card_finite) *)
qed
end

lemma fst_enum_nth: \<open>fst (enum_nth ij :: 'a::eenum\<times>'b::eenum) = enum_nth (ij div CARD('b))\<close>
  by (auto simp: enum_nth_invalid enum_nth_prod_def Let_def)

lemma snd_enum_nth: \<open>snd (enum_nth ij :: 'a::eenum\<times>'b::eenum) = (if ij < CARD('a\<times>'b) then enum_nth (ij mod CARD('b)) else enum_nth 0)\<close>
  apply (auto simp: enum_nth_prod_def Let_def)
  using div_less_iff_less_mult zero_less_card_finite by blast+

lemma enum_index_fst: \<open>enum_index (fst x) = enum_index x div CARD('b)\<close> for x :: \<open>'a::eenum\<times>'b::eenum\<close>
  by (auto simp add: enum_index_prod_def case_prod_beta)
lemma enum_index_snd: \<open>enum_index (snd x) = enum_index x mod CARD('b)\<close> for x :: \<open>'a::eenum\<times>'b::eenum\<close>
  by (auto simp add: enum_index_prod_def case_prod_beta)

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

lemma enum_nth_injective: \<open>i < CARD('a) \<Longrightarrow> j < CARD('a) \<Longrightarrow> (enum_nth i :: 'a::eenum) = enum_nth j \<longleftrightarrow> i = j\<close>
  by (metis enum_index_nth)

lemma Abs_ell2_inverse_finite[simp]: \<open>Rep_ell2 (Abs_ell2 \<psi>) = \<psi>\<close> for \<psi> :: \<open>_::finite \<Rightarrow> complex\<close>
  by (simp add: Abs_ell2_inverse)

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

(* lemma explicit_cblinfun_Rep_ket: \<open>Rep_ell2 (explicit_cblinfun m *\<^sub>V ket a) b = m b a\<close> for m :: "_ :: finite \<Rightarrow> _ :: finite \<Rightarrow> _"
  by simp *)

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

lemma cblinfun_of_mat_invalid: 
  assumes \<open>M \<notin> carrier_mat (cdimension TYPE('b::{basis_enum,complex_normed_vector})) (cdimension TYPE('a::{basis_enum,complex_normed_vector}))\<close>
  shows \<open>(cblinfun_of_mat M :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'b) = 0\<close>
  apply (transfer fixing: M)
  using assms by simp

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

lemma trunc_ell2_singleton[simp]: \<open>trunc_ell2 {x} \<phi> = Rep_ell2 \<phi> x *\<^sub>C ket x\<close>
  apply (transfer fixing: x)
  by auto

lemma trunc_ell2_insert[simp]: \<open>trunc_ell2 (insert x M) \<phi> = Rep_ell2 \<phi> x *\<^sub>C ket x + trunc_ell2 M \<phi>\<close>
  if \<open>x \<notin> M\<close>
  using trunc_ell2_union_disjoint[where M=\<open>{x}\<close> and N=M]
  using that by auto

lemma ell2_decompose_has_sum: \<open>has_sum (\<lambda>x. Rep_ell2 \<phi> x *\<^sub>C ket x) UNIV \<phi>\<close>
proof (unfold has_sum_def)
  have *: \<open>trunc_ell2 M \<phi> = (\<Sum>x\<in>M. Rep_ell2 \<phi> x *\<^sub>C ket x)\<close> if \<open>finite M\<close> for M
    using that apply induction
    by auto
  show \<open>(sum (\<lambda>x. Rep_ell2 \<phi> x *\<^sub>C ket x) \<longlongrightarrow> \<phi>) (finite_subsets_at_top UNIV)\<close>
    apply (rule Lim_transform_eventually)
     apply (rule trunc_ell2_lim_at_UNIV)
    using * by (rule eventually_finite_subsets_at_top_weakI)
qed

lemma ell2_decompose_infsum: \<open>\<phi> = (\<Sum>\<^sub>\<infinity>x. Rep_ell2 \<phi> x *\<^sub>C ket x)\<close>
  by (metis ell2_decompose_has_sum infsumI)

lemma ell2_decompose_summable: \<open>(\<lambda>x. Rep_ell2 \<phi> x *\<^sub>C ket x) summable_on UNIV\<close>
  using ell2_decompose_has_sum summable_on_def by blast

lemma Rep_ell2_cblinfun_apply_sum: \<open>Rep_ell2 (A *\<^sub>V \<phi>) y = (\<Sum>\<^sub>\<infinity>x. Rep_ell2 \<phi> x * Rep_ell2 (A *\<^sub>V ket x) y)\<close>
proof -
  have 1: \<open>bounded_linear (\<lambda>z. Rep_ell2 (A *\<^sub>V z) y)\<close>
    by (auto intro!: bounded_clinear_compose[unfolded o_def, OF bounded_clinear_Rep_ell2]
        cblinfun.bounded_clinear_right bounded_clinear.bounded_linear)
  have 2: \<open>(\<lambda>x. Rep_ell2 \<phi> x *\<^sub>C ket x) summable_on UNIV\<close>
    by (simp add: ell2_decompose_summable)
  have \<open>Rep_ell2 (A *\<^sub>V \<phi>) y = Rep_ell2 (A *\<^sub>V (\<Sum>\<^sub>\<infinity>x. Rep_ell2 \<phi> x *\<^sub>C ket x)) y\<close>
    by (simp flip: ell2_decompose_infsum)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x. Rep_ell2 (A *\<^sub>V (Rep_ell2 \<phi> x *\<^sub>C ket x)) y)\<close>
    apply (subst infsum_bounded_linear[symmetric, where f=\<open>\<lambda>z. Rep_ell2 (A *\<^sub>V z) y\<close>])
    using 1 2 by (auto simp: o_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>x. Rep_ell2 \<phi> x * Rep_ell2 (A *\<^sub>V ket x) y)\<close>
    by (simp add: cblinfun.scaleC_right scaleC_ell2.rep_eq)
  finally show ?thesis
    by -
qed

lemma is_orthogonal_trunc_ell2: \<open>is_orthogonal (trunc_ell2 M \<psi>) (trunc_ell2 N \<phi>)\<close> if \<open>M \<inter> N = {}\<close>
proof -
  have *: \<open>cnj (if i \<in> M then a else 0) * (if i \<in> N then b else 0) = 0\<close> for a b i
    using that by auto
  show ?thesis
    apply (transfer fixing: M N)
    by (simp add: * )
qed

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


(* TODO replace existing cblinfun_image_INF_leq *)
lemma cblinfun_image_INF_leq[simp]:
  fixes U :: "'b::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'c::cbanach"
    and V :: "'a \<Rightarrow> 'b ccsubspace"
  shows \<open>U *\<^sub>S (INF i\<in>X. V i) \<le> (INF i\<in>X. U *\<^sub>S (V i))\<close>
  apply transfer
  by (simp add: INT_greatest Inter_lower closure_mono image_mono)

(* TODO replace existing cblinfun_image_INF_eq_general *)
lemma cblinfun_image_INF_eq_general:
  fixes V :: "'a \<Rightarrow> 'b::chilbert_space ccsubspace"
    and U :: "'b \<Rightarrow>\<^sub>C\<^sub>L'c::chilbert_space"
    and Uinv :: "'c \<Rightarrow>\<^sub>C\<^sub>L'b"
  assumes UinvUUinv: "Uinv o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L Uinv = Uinv" and UUinvU: "U o\<^sub>C\<^sub>L Uinv o\<^sub>C\<^sub>L U = U"
    \<comment> \<open>Meaning: \<^term>\<open>Uinv\<close> is a Pseudoinverse of \<^term>\<open>U\<close>\<close>
    and V: "\<And>i. V i \<le> Uinv *\<^sub>S top"
    and \<open>X \<noteq> {}\<close>
  shows "U *\<^sub>S (INF i\<in>X. V i) = (INF i\<in>X. U *\<^sub>S V i)"
proof (rule antisym)
  show "U *\<^sub>S (INF i\<in>X. V i) \<le> (INF i\<in>X. U *\<^sub>S V i)"
    by (rule cblinfun_image_INF_leq)
next
  define rangeU rangeUinv where "rangeU = U *\<^sub>S top" and "rangeUinv = Uinv *\<^sub>S top"
  define INFUV INFV where INFUV_def: "INFUV = (INF i\<in>X. U *\<^sub>S V i)" and INFV_def: "INFV = (INF i\<in>X. V i)"
  from assms have "V i \<le> rangeUinv"
    for i
    unfolding rangeUinv_def by simp
  moreover have "(Uinv o\<^sub>C\<^sub>L U) *\<^sub>V \<psi> = \<psi>" if "\<psi> \<in> space_as_set rangeUinv"
    for \<psi>
    using UinvUUinv cblinfun_fixes_range rangeUinv_def that by fastforce
  ultimately have "(Uinv o\<^sub>C\<^sub>L U) *\<^sub>V \<psi> = \<psi>" if "\<psi> \<in> space_as_set (V i)"
    for \<psi> i
    using less_eq_ccsubspace.rep_eq that by blast
  hence d1: "(Uinv o\<^sub>C\<^sub>L U) *\<^sub>S (V i) = (V i)" for i
  proof (transfer fixing: i)
    fix V :: "'a \<Rightarrow> 'b set"
      and Uinv :: "'c \<Rightarrow> 'b"
      and U :: "'b \<Rightarrow> 'c"
    assume "pred_fun \<top> closed_csubspace V"
      and "bounded_clinear Uinv"
      and "bounded_clinear U"
      and "\<And>\<psi> i. \<psi> \<in> V i \<Longrightarrow> (Uinv \<circ> U) \<psi> = \<psi>"
    then show "closure ((Uinv \<circ> U) ` V i) = V i"
    proof auto
      fix x
      from \<open>pred_fun \<top> closed_csubspace V\<close>
      show "x \<in> V i"
        if "x \<in> closure (V i)" 
        using that apply simp
        by (metis orthogonal_complement_of_closure closed_csubspace.subspace double_orthogonal_complement_id closure_is_closed_csubspace)
      with \<open>pred_fun \<top> closed_csubspace V\<close>
      show "x \<in> closure (V i)"
        if "x \<in> V i"
        using that
        using setdist_eq_0_sing_1 setdist_sing_in_set
        by blast
    qed
  qed
  have "U *\<^sub>S V i \<le> rangeU" for i
    by (simp add: cblinfun_image_mono rangeU_def)
  hence "INFUV \<le> rangeU"
    unfolding INFUV_def using \<open>X \<noteq> {}\<close>
    by (metis INF_eq_const INF_lower2)
  moreover have "(U o\<^sub>C\<^sub>L Uinv) *\<^sub>V \<psi> = \<psi>" if "\<psi> \<in> space_as_set rangeU" for \<psi>
    using UUinvU cblinfun_fixes_range rangeU_def that by fastforce
  ultimately have x: "(U o\<^sub>C\<^sub>L Uinv) *\<^sub>V \<psi> = \<psi>" if "\<psi> \<in> space_as_set INFUV" for \<psi>
    by (simp add: in_mono less_eq_ccsubspace.rep_eq that)

  have "closure ((U \<circ> Uinv) ` INFUV) = INFUV"
    if "closed_csubspace INFUV"
      and "bounded_clinear U"
      and "bounded_clinear Uinv"
      and "\<And>\<psi>. \<psi> \<in> INFUV \<Longrightarrow> (U \<circ> Uinv) \<psi> = \<psi>"
    for INFUV :: "'c set"
    using that
  proof auto
    fix x
    show "x \<in> INFUV" if "x \<in> closure INFUV"
      using that \<open>closed_csubspace INFUV\<close>
      by (metis orthogonal_complement_of_closure closed_csubspace.subspace double_orthogonal_complement_id closure_is_closed_csubspace)
    show "x \<in> closure INFUV"
      if "x \<in> INFUV"
      using that \<open>closed_csubspace INFUV\<close>
      using setdist_eq_0_sing_1 setdist_sing_in_set
      by (simp add: closed_csubspace.closed)
  qed
  hence "(U o\<^sub>C\<^sub>L Uinv) *\<^sub>S INFUV = INFUV"
    by (metis (mono_tags, opaque_lifting) x cblinfun_image.rep_eq cblinfun_image_id id_cblinfun_apply image_cong
        space_as_set_inject)
  hence "INFUV = U *\<^sub>S Uinv *\<^sub>S INFUV"
    by (simp add: cblinfun_compose_image)
  also have "\<dots> \<le> U *\<^sub>S (INF i\<in>X. Uinv *\<^sub>S U *\<^sub>S V i)"
    unfolding INFUV_def
    by (metis cblinfun_image_mono cblinfun_image_INF_leq)
  also have "\<dots> = U *\<^sub>S INFV"
    using d1
    by (metis (no_types, lifting) INFV_def cblinfun_assoc_left(2) image_cong)
  finally show "INFUV \<le> U *\<^sub>S INFV".
qed

(* TODO replace existing cblinfun_image_INF_eq *)
lemma cblinfun_image_INF_eq[simp]:
  fixes V :: "'a \<Rightarrow> 'b::chilbert_space ccsubspace"
    and U :: "'b \<Rightarrow>\<^sub>C\<^sub>L 'c::chilbert_space"
  assumes \<open>isometry U\<close> \<open>X \<noteq> {}\<close>
  shows "U *\<^sub>S (INF i\<in>X. V i) = (INF i\<in>X. U *\<^sub>S V i)"
proof -
  from \<open>isometry U\<close> have "U* o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L U* = U*"
    unfolding isometry_def by simp
  moreover from \<open>isometry U\<close> have "U o\<^sub>C\<^sub>L U* o\<^sub>C\<^sub>L U = U"
    unfolding isometry_def
    by (simp add: cblinfun_compose_assoc)
  moreover have "V i \<le> U* *\<^sub>S top" for i
    by (simp add: range_adjoint_isometry assms)
  ultimately show ?thesis
    using \<open>X \<noteq> {}\<close> by (rule cblinfun_image_INF_eq_general)
qed

end
