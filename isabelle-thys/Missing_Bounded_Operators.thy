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

lemma ccspan_closure[simp]: \<open>ccspan (closure X) = ccspan X\<close>
  by (simp add: basic_trans_rules(24) ccspan.rep_eq ccspan_leqI ccspan_mono closure_mono closure_subset complex_vector.span_superset)

lemma tensor_ell2_diff1: \<open>tensor_ell2 (a - b) c = tensor_ell2 a c - tensor_ell2 b c\<close>
  by (simp add: bounded_cbilinear.diff_left bounded_cbilinear_tensor_ell2)

lemma tensor_ell2_diff2: \<open>tensor_ell2 a (b - c) = tensor_ell2 a b - tensor_ell2 a c\<close>
  by (simp add: bounded_cbilinear.diff_right bounded_cbilinear_tensor_ell2)

lemma continuous_tensor_ell2: \<open>continuous_on UNIV (\<lambda>(x::'a ell2, y::'b ell2). x \<otimes>\<^sub>s y)\<close>
proof -
  have cont: \<open>continuous_on UNIV (\<lambda>t. t \<otimes>\<^sub>s x)\<close> for x :: \<open>'b ell2\<close>
    by (intro linear_continuous_on bounded_clinear.bounded_linear bounded_clinear_tensor_ell22)
  have lip: \<open>local_lipschitz (UNIV :: 'a ell2 set) (UNIV :: 'b ell2 set) (\<otimes>\<^sub>s)\<close>
  proof (rule local_lipschitzI)
    fix t :: \<open>'a ell2\<close> and x :: \<open>'b ell2\<close>
    define u L :: real where \<open>u = 1\<close> and \<open>L = norm t + u\<close>
    have \<open>u > 0\<close>
      by (simp add: u_def)
    have [simp]: \<open>L \<ge> 0\<close>
      by (simp add: L_def u_def)
    have *: \<open>norm s \<le> L\<close> if \<open>s\<in>cball t u\<close> for s :: \<open>'a ell2\<close>
      using that
      apply (simp add: L_def dist_norm)
      by (smt (verit) norm_minus_commute norm_triangle_sub)
    have \<open>L-lipschitz_on (cball x u) ((\<otimes>\<^sub>s) s)\<close> if \<open>s\<in>cball t u\<close> for s :: \<open>'a ell2\<close>
      apply (rule lipschitz_onI)
      by (auto intro!: mult_right_mono *[OF that]
          simp add: dist_norm norm_tensor_ell2 simp flip: tensor_ell2_diff2)
    with \<open>u > 0\<close> show \<open>\<exists>u>0. \<exists>L. \<forall>s\<in>cball t u \<inter> UNIV. L-lipschitz_on (cball x u \<inter> UNIV) ((\<otimes>\<^sub>s) s)\<close>
      by force
  qed
  show ?thesis
    apply (subst UNIV_Times_UNIV[symmetric])
    using lip cont by (rule Lipschitz.continuous_on_TimesI)
qed

lemma tensor_ccsubspace_image: \<open>(A *\<^sub>S T) \<otimes>\<^sub>S (B *\<^sub>S U) = (A \<otimes>\<^sub>o B) *\<^sub>S (T \<otimes>\<^sub>S U)\<close>
proof -
  have \<open>(A *\<^sub>S T) \<otimes>\<^sub>S (B *\<^sub>S U) = ccspan ((\<lambda>(\<psi>, \<phi>). \<psi> \<otimes>\<^sub>s \<phi>) ` (space_as_set (A *\<^sub>S T) \<times> space_as_set (B *\<^sub>S U)))\<close>
    by (simp add: tensor_ccsubspace_def set_compr_2_image_collect ccspan.rep_eq)
  also have \<open>\<dots> = ccspan ((\<lambda>(\<psi>, \<phi>). \<psi> \<otimes>\<^sub>s \<phi>) ` closure ((A ` space_as_set T) \<times> (B ` space_as_set U)))\<close>
    by (simp add: cblinfun_image.rep_eq closure_Times)
  also have \<open>\<dots> = ccspan (closure ((\<lambda>(\<psi>, \<phi>). \<psi> \<otimes>\<^sub>s \<phi>) ` ((A ` space_as_set T) \<times> (B ` space_as_set U))))\<close>
    apply (subst closure_image_closure[symmetric])
    using continuous_on_subset continuous_tensor_ell2 by auto
  also have \<open>\<dots> = ccspan ((\<lambda>(\<psi>, \<phi>). \<psi> \<otimes>\<^sub>s \<phi>) ` ((A ` space_as_set T) \<times> (B ` space_as_set U)))\<close>
    by simp
  also have \<open>\<dots> = (A \<otimes>\<^sub>o B) *\<^sub>S ccspan ((\<lambda>(\<psi>, \<phi>). \<psi> \<otimes>\<^sub>s \<phi>) ` (space_as_set T \<times> space_as_set U))\<close>
    by (simp add: cblinfun_image_ccspan image_image tensor_op_ell2 case_prod_beta
        flip: map_prod_image)
  also have \<open>\<dots> = (A \<otimes>\<^sub>o B) *\<^sub>S (T \<otimes>\<^sub>S U)\<close>
    by (simp add: tensor_ccsubspace_def set_compr_2_image_collect)
  finally show ?thesis
    by -
qed

lemma isometry_tensor_op: \<open>isometry (U \<otimes>\<^sub>o V)\<close> if \<open>isometry U\<close> and \<open>isometry V\<close>
  unfolding isometry_def using that by (simp add: tensor_op_adjoint comp_tensor_op)

lemma isometry_tensor_ell2_right: \<open>isometry (tensor_ell2_right \<psi>)\<close> if \<open>norm \<psi> = 1\<close>
  apply (rule norm_preserving_isometry)
  by (simp add: tensor_ell2_right_apply norm_tensor_ell2 that)

lemma isometry_tensor_ell2_left: \<open>isometry (tensor_ell2_left \<psi>)\<close> if \<open>norm \<psi> = 1\<close>
  apply (rule norm_preserving_isometry)
  by (simp add: tensor_ell2_left_apply norm_tensor_ell2 that)

lemma sandwich_isometry_id: \<open>isometry (U*) \<Longrightarrow> sandwich U id_cblinfun = id_cblinfun\<close>
  by (simp add: sandwich_apply isometry_def)

lemma tensor_ell2_right_scale: \<open>tensor_ell2_right (a *\<^sub>C \<psi>) = a *\<^sub>C tensor_ell2_right \<psi>\<close>
  apply transfer by (auto intro!: ext simp: tensor_ell2_scaleC2)
lemma tensor_ell2_left_scale: \<open>tensor_ell2_left (a *\<^sub>C \<psi>) = a *\<^sub>C tensor_ell2_left \<psi>\<close>
  apply transfer by (auto intro!: ext simp: tensor_ell2_scaleC1)

(* TODO same for left *)
lemma tensor_ell2_right_0[simp]: \<open>tensor_ell2_right 0 = 0\<close>
  by (auto intro!: cblinfun_eqI simp: tensor_ell2_right_apply)

lemma tensor_ell2_right_adj_apply[simp]: \<open>(tensor_ell2_right \<psi>*) *\<^sub>V (\<alpha> \<otimes>\<^sub>s \<beta>) = (\<psi> \<bullet>\<^sub>C \<beta>) *\<^sub>C \<alpha>\<close>
  apply (rule cinner_extensionality)
  by (simp add: cinner_adj_right tensor_ell2_right_apply)
lemma tensor_ell2_left_adj_apply[simp]: \<open>(tensor_ell2_left \<psi>*) *\<^sub>V (\<alpha> \<otimes>\<^sub>s \<beta>) = (\<psi> \<bullet>\<^sub>C \<alpha>) *\<^sub>C \<beta>\<close>
  apply (rule cinner_extensionality)
  by (simp add: cinner_adj_right tensor_ell2_right_apply)


(* TODO same for left *)
lemma sandwich_tensor_ell2_right: \<open>sandwich (tensor_ell2_right \<psi>*) *\<^sub>V a \<otimes>\<^sub>o b = (\<psi> \<bullet>\<^sub>C (b *\<^sub>V \<psi>)) *\<^sub>C a\<close>
  apply (rule cblinfun_eqI)
  by (simp add: sandwich_apply tensor_ell2_right_apply tensor_op_ell2)

lemma triple_commutant[simp]: \<open>commutant (commutant (commutant X)) = commutant X\<close>
  by (auto simp: commutant_def)

lemma commutant_adj: \<open>adj ` commutant X = commutant (adj ` X)\<close>
  apply (auto intro!: image_eqI double_adj[symmetric] simp: commutant_def simp flip: adj_cblinfun_compose)
  by (metis adj_cblinfun_compose double_adj)

lemma commutant_empty[simp]: \<open>commutant {} = UNIV\<close>
  by (simp add: commutant_def)

lemma continuous_map_scaleC_weak_star'[continuous_intros]:
  assumes \<open>continuous_map T weak_star_topology f\<close>
  shows \<open>continuous_map T weak_star_topology (\<lambda>x. scaleC c (f x))\<close>
  using continuous_map_compose[OF assms continuous_map_scaleC_weak_star]
  by (simp add: o_def)

lemma continuous_map_uminus_weak_star[continuous_intros]:
  assumes \<open>continuous_map T weak_star_topology f\<close>
  shows \<open>continuous_map T weak_star_topology (\<lambda>x. - f x)\<close>
  apply (subst scaleC_minus1_left[abs_def,symmetric])
  by (intro continuous_map_scaleC_weak_star' assms)

lemma continuous_map_add_weak_star[continuous_intros]: 
  assumes \<open>continuous_map T weak_star_topology f\<close>
  assumes \<open>continuous_map T weak_star_topology g\<close>
  shows \<open>continuous_map T weak_star_topology (\<lambda>x. f x + g x)\<close>
proof -
  have \<open>continuous_map T euclidean (\<lambda>x. trace (t o\<^sub>C\<^sub>L f x))\<close> if \<open>trace_class t\<close> for t
    using assms(1) continuous_on_weak_star_topo_iff_coordinatewise that by auto
  moreover have \<open>continuous_map T euclidean (\<lambda>x. trace (t o\<^sub>C\<^sub>L g x))\<close> if \<open>trace_class t\<close> for t
    using assms(2) continuous_on_weak_star_topo_iff_coordinatewise that by auto
  ultimately show ?thesis
    by (auto intro!: continuous_map_add simp add: continuous_on_weak_star_topo_iff_coordinatewise
        cblinfun_compose_add_right trace_class_comp_left trace_plus)
qed

lemma continuous_map_minus_weak_star[continuous_intros]: 
  assumes \<open>continuous_map T weak_star_topology f\<close>
  assumes \<open>continuous_map T weak_star_topology g\<close>
  shows \<open>continuous_map T weak_star_topology (\<lambda>x. f x - g x)\<close>
  apply (subst diff_conv_add_uminus)
  by (intro assms continuous_intros)

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

(* TODO move to partial_isometry-theory *)
(* TODO might replace partial_isometry_square_proj by this *)
lemma partial_isometry_iff_square_proj:
  \<comment> \<open>@{cite conway2013functional}, Exercise VIII.3.15\<close>
  fixes A :: \<open>'a :: chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b :: chilbert_space\<close>
  shows \<open>partial_isometry A \<longleftrightarrow> is_Proj (A* o\<^sub>C\<^sub>L A)\<close>
proof (rule iffI)
  show \<open>is_Proj (A* o\<^sub>C\<^sub>L A)\<close> if \<open>partial_isometry A\<close>
    by (simp add: partial_isometry_square_proj that)
next
  show \<open>partial_isometry A\<close> if \<open>is_Proj (A* o\<^sub>C\<^sub>L A)\<close>
  proof (rule partial_isometryI)
    fix h
    from that have \<open>norm (A* o\<^sub>C\<^sub>L A) \<le> 1\<close>
      using norm_is_Proj by blast
    then have normA: \<open>norm A \<le> 1\<close> and normAadj: \<open>norm (A*) \<le> 1\<close>
      by (simp_all add: norm_AadjA abs_square_le_1)
    assume \<open>h \<in> space_as_set (- kernel A)\<close>
    also have \<open>\<dots> = space_as_set (- kernel (A* o\<^sub>C\<^sub>L A))\<close>
      by (metis (no_types, lifting) abs_opI is_Proj_algebraic kernel_abs_op positive_cblinfun_squareI that)
    also have \<open>\<dots> = space_as_set ((A* o\<^sub>C\<^sub>L A) *\<^sub>S \<top>)\<close>
      by (simp add: kernel_compl_adj_range)
    finally have \<open>A* *\<^sub>V A *\<^sub>V h = h\<close>
      by (metis Proj_fixes_image Proj_on_own_range that cblinfun_apply_cblinfun_compose)
    then have \<open>norm h = norm (A* *\<^sub>V A *\<^sub>V h)\<close>
      by simp
    also have \<open>\<dots> \<le> norm (A *\<^sub>V h)\<close>
      by (smt (verit) normAadj mult_left_le_one_le norm_cblinfun norm_ge_zero)
    also have \<open>\<dots> \<le> norm h\<close>
      by (smt (verit) normA mult_left_le_one_le norm_cblinfun norm_ge_zero)
    ultimately show \<open>norm (A *\<^sub>V h) = norm h\<close>
      by simp
  qed
qed

lemma tensor_ccsubspace_bot_left[simp]: \<open>\<bottom> \<otimes>\<^sub>S S = \<bottom>\<close>
  by (simp add: tensor_ccsubspace_via_Proj)
lemma tensor_ccsubspace_bot_right[simp]: \<open>S \<otimes>\<^sub>S \<bottom> = \<bottom>\<close>
  by (simp add: tensor_ccsubspace_via_Proj)

lemma ccspan_finite: \<open>space_as_set (ccspan X) = cspan X\<close> if \<open>finite X\<close>
  by (simp add: ccspan.rep_eq that)

lemma swap_ell2_tensor_ccsubspace: \<open>swap_ell2 *\<^sub>S (S \<otimes>\<^sub>S T) = T \<otimes>\<^sub>S S\<close>
  apply (auto intro!: arg_cong[where f=ccspan] 
      simp add: tensor_ccsubspace_def cblinfun_image_ccspan image_image set_compr_2_image_collect)
  by force

lemma tensor_ccsubspace_right1dim_member:
  assumes \<open>\<psi> \<in> space_as_set (S \<otimes>\<^sub>S ccspan{\<phi>})\<close>
  shows \<open>\<exists>\<psi>'. \<psi> = \<psi>' \<otimes>\<^sub>s \<phi>\<close>
proof (cases \<open>\<phi> = 0\<close>)
  case True
  with assms show ?thesis 
    by simp
next
  case False
  have \<open>{\<psi> \<otimes>\<^sub>s \<phi>' |\<psi> \<phi>'. \<psi> \<in> space_as_set S \<and> \<phi>' \<in> space_as_set (ccspan {\<phi>})}
    = {\<psi> \<otimes>\<^sub>s \<phi> | \<psi>. \<psi> \<in> space_as_set S}\<close>
  proof -
    have \<open>\<psi> \<in> space_as_set S \<Longrightarrow> \<exists>\<psi>'. \<psi> \<otimes>\<^sub>s c *\<^sub>C \<phi> = \<psi>' \<otimes>\<^sub>s \<phi> \<and> \<psi>' \<in> space_as_set S\<close> for c \<psi>
      apply (rule exI[where x=\<open>c *\<^sub>C \<psi>\<close>])
      by (auto simp: tensor_ell2_scaleC2 tensor_ell2_scaleC1
          complex_vector.subspace_scale)
    moreover have \<open>\<psi> \<in> space_as_set S \<Longrightarrow>
         \<exists>\<psi>' \<phi>'. \<psi> \<otimes>\<^sub>s \<phi> = \<psi>' \<otimes>\<^sub>s \<phi>' \<and> \<psi>' \<in> space_as_set S \<and> \<phi>' \<in> range (\<lambda>k. k *\<^sub>C \<phi>)\<close> for \<psi>
      apply (rule exI[where x=\<psi>], rule exI[where x=\<phi>])
      by (auto intro!: range_eqI[where x=\<open>1::complex\<close>])
    ultimately show ?thesis
      by (auto simp: ccspan_finite complex_vector.span_singleton)
  qed
  moreover have \<open>csubspace {\<psi> \<otimes>\<^sub>s \<phi> |\<psi>. \<psi> \<in> space_as_set S}\<close>
  proof (rule complex_vector.subspaceI)
    show \<open>0 \<in> {\<psi> \<otimes>\<^sub>s \<phi> |\<psi>. \<psi> \<in> space_as_set S}\<close>
      by (auto intro!: exI[where x=0])
    show \<open>x \<in> {\<psi> \<otimes>\<^sub>s \<phi> |\<psi>. \<psi> \<in> space_as_set S} \<Longrightarrow>
           y \<in> {\<psi> \<otimes>\<^sub>s \<phi> |\<psi>. \<psi> \<in> space_as_set S} \<Longrightarrow> x + y \<in> {\<psi> \<otimes>\<^sub>s \<phi> |\<psi>. \<psi> \<in> space_as_set S}\<close> for x y
      apply (auto simp flip: tensor_ell2_add1)
      apply (rename_tac \<psi> \<psi>', rule_tac x=\<open>\<psi> + \<psi>'\<close> in exI)
      by (auto simp: complex_vector.subspace_add)
    show \<open>x \<in> {\<psi> \<otimes>\<^sub>s \<phi> |\<psi>. \<psi> \<in> space_as_set S} \<Longrightarrow> c *\<^sub>C x \<in> {\<psi> \<otimes>\<^sub>s \<phi> |\<psi>. \<psi> \<in> space_as_set S}\<close> for c x
      apply (auto simp flip: tensor_ell2_scaleC1)
      apply (rename_tac \<psi>, rule_tac x=\<open>c *\<^sub>C \<psi>\<close> in exI)
      by (auto simp: complex_vector.subspace_scale tensor_ell2_scaleC2 tensor_ell2_scaleC1)
  qed
  moreover have \<open>closed {\<psi> \<otimes>\<^sub>s \<phi> |\<psi>. \<psi> \<in> space_as_set S}\<close>
  proof (rule closed_sequential_limits[THEN iffD2, rule_format])
    fix x l
    assume asm: \<open>(\<forall>n. x n \<in> {\<psi> \<otimes>\<^sub>s \<phi> |\<psi>. \<psi> \<in> space_as_set S}) \<and> x \<longlonglongrightarrow> l\<close>
    then obtain \<psi>' where x_def: \<open>x n = \<psi>' n \<otimes>\<^sub>s \<phi>\<close> and \<psi>'_S: \<open>\<psi>' n \<in> space_as_set S\<close> for n
      apply atomize_elim apply auto by metis
    from asm have \<open>x \<longlonglongrightarrow> l\<close>
      by simp
    have \<open>Cauchy \<psi>'\<close>
    proof (rule CauchyI)
      fix e :: real assume \<open>e > 0\<close>
      define d where \<open>d = e * norm \<phi>\<close>
      with False \<open>e > 0\<close> have \<open>d > 0\<close>
        by auto
      from \<open>x \<longlonglongrightarrow> l\<close>
      have \<open>Cauchy x\<close>
        using LIMSEQ_imp_Cauchy by blast
      then obtain M where \<open>\<forall>m\<ge>M. \<forall>n\<ge>M. norm (x m - x n) < d\<close>
        using Cauchy_iff \<open>0 < d\<close> by blast
      then show \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (\<psi>' m - \<psi>' n) < e\<close>
        apply (rule_tac exI[of _ M])
        using False by (auto simp add: x_def norm_tensor_ell2 d_def simp flip: tensor_ell2_diff1)
    qed
    then obtain l' where \<open>\<psi>' \<longlonglongrightarrow> l'\<close>
      using convergent_eq_Cauchy by blast
    with \<psi>'_S have l'_S: \<open>l' \<in> space_as_set S\<close>
      by (metis \<open>Cauchy \<psi>'\<close> completeE complete_space_as_set limI)
    from \<open>\<psi>' \<longlonglongrightarrow> l'\<close> have \<open>x \<longlonglongrightarrow> l' \<otimes>\<^sub>s \<phi>\<close>
      by (auto intro: tendsto_eq_intros simp: x_def[abs_def])
    with \<open>x \<longlonglongrightarrow> l\<close> have \<open>l = l' \<otimes>\<^sub>s \<phi>\<close>
      using LIMSEQ_unique by blast
    then show \<open>l \<in> {\<psi> \<otimes>\<^sub>s \<phi> |\<psi>. \<psi> \<in> space_as_set S}\<close>
      using l'_S by auto
  qed
  ultimately have \<open>space_as_set (ccspan {\<psi> \<otimes>\<^sub>s \<phi>' |\<psi> \<phi>'. \<psi> \<in> space_as_set S \<and> \<phi>' \<in> space_as_set (ccspan {\<phi>})})
      = {\<psi> \<otimes>\<^sub>s \<phi> |\<psi>. \<psi> \<in> space_as_set S}\<close> 
    by (simp add: ccspan.rep_eq complex_vector.span_eq_iff[THEN iffD2])
  with assms have \<open>\<psi> \<in> {\<psi> \<otimes>\<^sub>s \<phi> |\<psi>. \<psi> \<in> space_as_set S}\<close>
    by (simp add: tensor_ccsubspace_def)
  then show \<open>\<exists>\<psi>'. \<psi> = \<psi>' \<otimes>\<^sub>s \<phi>\<close>
    by auto
qed

lemma tensor_ccsubspace_left1dim_member:
  assumes \<open>\<psi> \<in> space_as_set (ccspan{\<phi>} \<otimes>\<^sub>S S)\<close>
  shows \<open>\<exists>\<psi>'. \<psi> = \<phi> \<otimes>\<^sub>s \<psi>'\<close>
proof -
  from assms 
  have \<open>swap_ell2 *\<^sub>V \<psi> \<in> space_as_set (swap_ell2 *\<^sub>S (ccspan {\<phi>} \<otimes>\<^sub>S S))\<close>
  by (metis rev_image_eqI space_as_set_image_commute swap_ell2_selfinv)
  then have \<open>swap_ell2 \<psi> \<in> space_as_set (S \<otimes>\<^sub>S ccspan{\<phi>})\<close>
    by (simp add: swap_ell2_tensor_ccsubspace)
  then obtain \<psi>' where \<psi>': \<open>swap_ell2 \<psi> = \<psi>' \<otimes>\<^sub>s \<phi>\<close>
    using tensor_ccsubspace_right1dim_member by blast
  have \<open>\<psi> = swap_ell2 *\<^sub>V swap_ell2 *\<^sub>V \<psi>\<close>
    by (simp flip: cblinfun_apply_cblinfun_compose)
  also have \<open>\<dots> = swap_ell2 *\<^sub>V (\<psi>' \<otimes>\<^sub>s \<phi>)\<close>
    by (simp add: \<psi>')
  also have \<open>\<dots> = \<phi> \<otimes>\<^sub>s \<psi>'\<close>
    by simp
  finally show ?thesis
    by auto
qed

lemma cblinfun_apply_in_image': "A *\<^sub>V \<psi> \<in> space_as_set (A *\<^sub>S S)" if \<open>\<psi> \<in> space_as_set S\<close>
  by (metis cblinfun_image.rep_eq closure_subset image_subset_iff that)

lemma is_Proj_tensor_op: \<open>is_Proj a \<Longrightarrow> is_Proj b \<Longrightarrow> is_Proj (a \<otimes>\<^sub>o b)\<close>
  by (simp add: comp_tensor_op is_Proj_algebraic tensor_op_adjoint)

(* TODO right *)
lemma tensor_ell2_mem_tensor_ccsubspace_left:
  assumes \<open>a \<otimes>\<^sub>s b \<in> space_as_set (S \<otimes>\<^sub>S T)\<close> and \<open>b \<noteq> 0\<close>
  shows \<open>a \<in> space_as_set S\<close>
proof (cases \<open>a = 0\<close>)
  case True
  then show ?thesis 
    by simp
next
  case False
  have \<open>norm (Proj S a) * norm (Proj T b) = norm ((Proj S a) \<otimes>\<^sub>s (Proj T b))\<close>
    by (simp add: norm_tensor_ell2)
  also have \<open>\<dots> = norm (Proj (S \<otimes>\<^sub>S T) (a \<otimes>\<^sub>s b))\<close>
    by (simp add: tensor_ccsubspace_via_Proj Proj_on_own_range is_Proj_tensor_op
        tensor_op_ell2)
  also from assms have \<open>\<dots> = norm (a \<otimes>\<^sub>s b)\<close>
    by (simp add: Proj_fixes_image)
  also have \<open>\<dots> = norm a * norm b\<close>
    by (simp add: norm_tensor_ell2)
  finally have prod_eq: \<open>norm (Proj S *\<^sub>V a) * norm (Proj T *\<^sub>V b) = norm a * norm b\<close>
    by -
  with False \<open>b \<noteq> 0\<close> have Tb_non0: \<open>norm (Proj T *\<^sub>V b) \<noteq> 0\<close>
    by fastforce
  have \<open>norm (Proj S a) = norm a\<close>
  proof (rule ccontr)
    assume asm: \<open>norm (Proj S *\<^sub>V a) \<noteq> norm a\<close>
    have Sa_leq: \<open>norm (Proj S *\<^sub>V a) \<le> norm a\<close>
      by (simp add: is_Proj_reduces_norm)
    have Tb_leq: \<open>norm (Proj T *\<^sub>V b) \<le> norm b\<close>
      by (simp add: is_Proj_reduces_norm)
    from asm Sa_leq have \<open>norm (Proj S *\<^sub>V a) < norm a\<close>
      by simp
    then have \<open>norm (Proj S *\<^sub>V a) * norm (Proj T *\<^sub>V b) < norm a * norm (Proj T *\<^sub>V b)\<close>
      using Tb_non0 by auto
    also from Tb_leq have \<open>\<dots> \<le> norm a * norm b\<close>
      using False by force
    also note prod_eq
    finally show False
      by simp
  qed
  then show \<open>a \<in> space_as_set S\<close>
    using norm_Proj_apply by blast
qed

lemma mem_ortho_ccspanI:
  assumes \<open>\<And>y. y \<in> S \<Longrightarrow> is_orthogonal x y\<close>
  shows \<open>x \<in> space_as_set (- ccspan S)\<close>
proof -
  have \<open>x \<in> space_as_set (ccspan {x})\<close>
    using ccspan_superset by blast
  also have \<open>\<dots> \<subseteq> space_as_set (- ccspan S)\<close>
    apply (simp add: flip: less_eq_ccsubspace.rep_eq)
    apply (rule ccspan_leq_ortho_ccspan)
    using assms by auto
  finally show ?thesis
    by -
qed

lemma trunc_ell2_uminus: \<open>trunc_ell2 (-M) \<psi> = \<psi> - trunc_ell2 M \<psi>\<close>
  by (metis Int_UNIV_left boolean_algebra_class.diff_eq subset_UNIV trunc_ell2_UNIV trunc_ell2_union_Diff)

(* TODO right *)
lemma tensor_ccsubspace_INF_left_top:
  fixes S :: \<open>'a \<Rightarrow> 'b ell2 ccsubspace\<close>
shows \<open>(INF x\<in>X. S x) \<otimes>\<^sub>S (\<top>::'c ell2 ccsubspace) = (INF x\<in>X. S x \<otimes>\<^sub>S \<top>)\<close>
proof (rule antisym[rotated])
  let ?top = \<open>\<top> :: 'c ell2 ccsubspace\<close>
  have \<open>\<psi> \<otimes>\<^sub>s \<phi> \<in> space_as_set (\<Sqinter>x\<in>X. S x \<otimes>\<^sub>S ?top)\<close>
    if \<open>\<psi> \<in> space_as_set (\<Sqinter>x\<in>X. S x)\<close> for \<psi> \<phi>
  proof -
    from that(1) have \<open>\<psi> \<in> space_as_set (S x)\<close> if \<open>x \<in> X\<close> for x
      using that by (simp add: Inf_ccsubspace.rep_eq)
    then have \<open>\<psi> \<otimes>\<^sub>s \<phi> \<in> space_as_set (S x \<otimes>\<^sub>S \<top>)\<close> if \<open>x \<in> X\<close> for x
      using ccspan_superset that apply (auto simp: tensor_ccsubspace_def)
      by fastforce
    then show ?thesis
      by (simp add: Inf_ccsubspace.rep_eq)
  qed
  then show \<open>(INF x\<in>X. S x) \<otimes>\<^sub>S ?top \<le> (INF x\<in>X. S x \<otimes>\<^sub>S ?top)\<close>
    apply (subst tensor_ccsubspace_def)
    apply (rule ccspan_leqI)
    by auto

  show \<open>(\<Sqinter>x\<in>X. S x \<otimes>\<^sub>S ?top) \<le> (\<Sqinter>x\<in>X. S x) \<otimes>\<^sub>S ?top\<close>
  proof (rule ccsubspace_leI_unit)
    fix \<psi>
    assume asm: \<open>\<psi> \<in> space_as_set (\<Sqinter>x\<in>X. S x \<otimes>\<^sub>S ?top)\<close>
    obtain \<psi>' where \<psi>'b_b: \<open>\<psi>' b \<otimes>\<^sub>s ket b = (id_cblinfun \<otimes>\<^sub>o selfbutterket b) *\<^sub>V \<psi>\<close> for b
    proof (atomize_elim, rule choice, intro allI)
      fix b :: 'c
      have \<open>(id_cblinfun \<otimes>\<^sub>o selfbutterket b) *\<^sub>V \<psi> \<in> space_as_set (\<top> \<otimes>\<^sub>S ccspan {ket b})\<close>
        by (simp add: butterfly_eq_proj tensor_ccsubspace_via_Proj)
      then show \<open>\<exists>\<psi>'. \<psi>' \<otimes>\<^sub>s ket b = (id_cblinfun \<otimes>\<^sub>o selfbutterket b) *\<^sub>V \<psi>\<close>
       by (metis tensor_ccsubspace_right1dim_member)
    qed
  
    have \<open>\<psi>' b \<in> space_as_set (S x)\<close> if \<open>x \<in> X\<close> for x b
    proof -
      from asm have \<psi>_ST: \<open>\<psi> \<in> space_as_set (S x \<otimes>\<^sub>S ?top)\<close>
        by (meson INF_lower Set.basic_monos(7) less_eq_ccsubspace.rep_eq that)
      have \<open>\<psi>' b \<otimes>\<^sub>s ket b = (id_cblinfun \<otimes>\<^sub>o selfbutterket b) *\<^sub>V \<psi>\<close>
        by (simp add: \<psi>'b_b)
      also from \<psi>_ST
      have \<open>\<dots> \<in> space_as_set (((id_cblinfun \<otimes>\<^sub>o selfbutterket b)) *\<^sub>S (S x \<otimes>\<^sub>S ?top))\<close>
        by (meson cblinfun_apply_in_image')
      also have \<open>\<dots> = space_as_set (((id_cblinfun \<otimes>\<^sub>o selfbutterket b) o\<^sub>C\<^sub>L (Proj (S x) \<otimes>\<^sub>o id_cblinfun)) *\<^sub>S \<top>)\<close>
        by (simp add: cblinfun_compose_image tensor_ccsubspace_via_Proj)
      also have \<open>\<dots> = space_as_set ((Proj (S x) \<otimes>\<^sub>o (selfbutterket b o\<^sub>C\<^sub>L id_cblinfun)) *\<^sub>S \<top>)\<close>
        by (simp add: comp_tensor_op)
      also have \<open>\<dots> = space_as_set ((Proj (S x) \<otimes>\<^sub>o (id_cblinfun o\<^sub>C\<^sub>L selfbutterket b)) *\<^sub>S \<top>)\<close>
        by simp
      also have \<open>\<dots> = space_as_set (((Proj (S x) \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L (id_cblinfun \<otimes>\<^sub>o selfbutterket b)) *\<^sub>S \<top>)\<close>
        by (simp add: comp_tensor_op)
      also have \<open>\<dots> \<subseteq> space_as_set ((Proj (S x) \<otimes>\<^sub>o id_cblinfun) *\<^sub>S \<top>)\<close>
        by (metis cblinfun_compose_image cblinfun_image_mono less_eq_ccsubspace.rep_eq top_greatest)
      also have \<open>\<dots> = space_as_set (S x \<otimes>\<^sub>S ?top)\<close>
        by (simp add: tensor_ccsubspace_via_Proj)
      finally have \<open>\<psi>' b \<otimes>\<^sub>s ket b \<in> space_as_set (S x \<otimes>\<^sub>S ?top)\<close>
        by -
      then show \<open>\<psi>' b \<in> space_as_set (S x)\<close>
        using tensor_ell2_mem_tensor_ccsubspace_left
        by (metis ket_nonzero)
    qed

    then have \<open>\<psi>' b \<in> space_as_set (\<Sqinter>x\<in>X. S x)\<close> if \<open>x \<in> X\<close> for x b
      using that by (simp add: Inf_ccsubspace.rep_eq)

    then have *: \<open>\<psi>' b \<otimes>\<^sub>s ket b \<in> space_as_set ((\<Sqinter>x\<in>X. S x) \<otimes>\<^sub>S ?top)\<close> for b
      by (auto intro!: ccspan_superset[THEN set_mp] 
          simp add: tensor_ccsubspace_def Inf_ccsubspace.rep_eq)
    
    have \<open>\<psi> \<in> space_as_set (ccspan (range (\<lambda>b. \<psi>' b \<otimes>\<^sub>s ket b)))\<close> (is \<open>\<psi> \<in> ?rhs\<close>)
    proof -
      define \<gamma> where \<open>\<gamma> F = (\<Sum>b\<in>F. (id_cblinfun \<otimes>\<^sub>o selfbutterket b) *\<^sub>V \<psi>)\<close> for F
      have \<gamma>_rhs: \<open>\<gamma> F \<in> ?rhs\<close> for F
        apply (auto intro!: complex_vector.subspace_sum simp add: \<gamma>_def \<psi>'b_b)
        using ccspan_superset by fastforce
      have \<gamma>_trunc: \<open>\<gamma> F = trunc_ell2 (UNIV \<times> F) \<psi>\<close> if \<open>finite F\<close> for F
      proof (rule cinner_ket_eqI)
        fix x :: \<open>'b \<times> 'c\<close> obtain x1 x2 where x_def: \<open>x = (x1,x2)\<close>
          by force
        have *: \<open>ket x \<bullet>\<^sub>C ((id_cblinfun \<otimes>\<^sub>o selfbutterket j) *\<^sub>V \<psi>) = of_bool (j=x2) * Rep_ell2 \<psi> x\<close> for j
          apply (simp add: x_def tensor_op_ell2 tensor_op_adjoint cinner_ket 
              flip: tensor_ell2_ket cinner_adj_left)
          by (simp add: tensor_ell2_ket cinner_ket_left)
        have \<open>ket x \<bullet>\<^sub>C \<gamma> F = of_bool (x2\<in>F) *\<^sub>C Rep_ell2 \<psi> x\<close>
          using that
          apply (simp add: x_def \<gamma>_def complex_vector.linear_sum[of \<open>cinner _\<close>] bounded_clinear_cinner_right 
              bounded_clinear.clinear sum_single[where i=x2] tensor_op_adjoint tensor_op_ell2 cinner_ket
              flip: tensor_ell2_ket cinner_adj_left)
          by (simp add: tensor_ell2_ket cinner_ket_left)
        moreover have \<open>ket x \<bullet>\<^sub>C trunc_ell2 (UNIV \<times> F) \<psi> = of_bool (x2\<in>F) *\<^sub>C Rep_ell2 \<psi> x\<close>
          by (simp add: trunc_ell2.rep_eq cinner_ket_left x_def)
        ultimately show \<open>ket x \<bullet>\<^sub>C \<gamma> F = ket x \<bullet>\<^sub>C trunc_ell2 (UNIV \<times> F) \<psi>\<close>
          by simp
      qed
      have \<open>(\<gamma> \<longlongrightarrow> \<psi>) (finite_subsets_at_top UNIV)\<close>
      proof (rule tendsto_iff[THEN iffD2, rule_format])
        fix e :: real assume \<open>e > 0\<close>
        from trunc_ell2_lim_at_UNIV[of \<psi>]
        have \<open>\<forall>\<^sub>F F in finite_subsets_at_top UNIV. dist (trunc_ell2 F \<psi>) \<psi> < e\<close>
          by (simp add: \<open>0 < e\<close> tendstoD)
        then obtain M where \<open>finite M\<close> and less_e: \<open>finite F \<Longrightarrow> F \<supseteq> M \<Longrightarrow> dist (trunc_ell2 F \<psi>) \<psi> < e\<close> for F
          by (metis (mono_tags, lifting) eventually_finite_subsets_at_top subset_UNIV)
        define M' where \<open>M' = snd ` M\<close>
        have \<open>finite M'\<close>
          using M'_def \<open>finite M\<close> by blast
        have \<open>dist (\<gamma> F') \<psi> < e\<close> if \<open>finite F'\<close> and \<open>F' \<supseteq> M'\<close> for F'
        proof -
          have \<open>dist (\<gamma> F') \<psi> = norm (trunc_ell2 (- (UNIV \<times> F')) \<psi>)\<close>
            using that by (simp only: \<gamma>_trunc dist_norm trunc_ell2_uminus norm_minus_commute)
          also have \<open>\<dots> \<le> norm (trunc_ell2 (- ((fst ` M) \<times> F')) \<psi>)\<close>
            by (meson Compl_anti_mono Set.basic_monos(1) Sigma_mono subset_UNIV trunc_ell2_norm_mono)
          also have \<open>\<dots> = dist (trunc_ell2 ((fst ` M) \<times> F') \<psi>) \<psi>\<close>
            apply (simp add: trunc_ell2_uminus dist_norm)
            using norm_minus_commute by blast
          also have \<open>\<dots> < e\<close>
            apply (rule less_e)
            using \<open>finite F'\<close> \<open>finite M\<close> apply force
            using \<open>F' \<supseteq> M'\<close> M'_def by force
          finally show ?thesis
            by -
        qed
        then show \<open>\<forall>\<^sub>F F' in finite_subsets_at_top UNIV. dist (\<gamma> F') \<psi> < e\<close>
          using \<open>finite M'\<close> by (auto simp add: eventually_finite_subsets_at_top)
      qed
      then show \<open>\<psi> \<in> ?rhs\<close>
        apply (rule Lim_in_closed_set[rotated -1])
        using \<gamma>_rhs by auto 
    qed
    also from * have \<open>\<dots> \<subseteq> space_as_set ((\<Sqinter>x\<in>X. S x) \<otimes>\<^sub>S ?top)\<close>
      by (meson ccspan_leqI image_subset_iff less_eq_ccsubspace.rep_eq)
    
    finally show \<open>\<psi> \<in> space_as_set ((\<Sqinter>x\<in>X. S x) \<otimes>\<^sub>S ?top)\<close>
      by -
  qed
qed

(* TODO: Let some_chilbert_basis abbreviate some_chilbert_basis_of UNIV *)
definition \<open>some_chilbert_basis_of X = (SOME B. is_ortho_set B \<and> (\<forall>b\<in>B. norm b = 1) \<and> ccspan B = X)\<close>

lemma
  fixes X :: \<open>'a::chilbert_space ccsubspace\<close>
  shows some_chilbert_basis_of_is_ortho_set[simp]: \<open>is_ortho_set (some_chilbert_basis_of X)\<close>
    and some_chilbert_basis_of_norm1: \<open>b \<in> some_chilbert_basis_of X \<Longrightarrow> norm b = 1\<close>
    and some_chilbert_basis_of_ccspan[simp]: \<open>ccspan (some_chilbert_basis_of X) = X\<close>
proof -
  let ?P = \<open>\<lambda>B. is_ortho_set B \<and> (\<forall>b\<in>B. norm b = 1) \<and> ccspan B = X\<close>
  have \<open>Ex ?P\<close>
    using orthonormal_subspace_basis_exists[where S=\<open>{}\<close> and V=X]
    by auto
  then have \<open>?P (some_chilbert_basis_of X)\<close>
    by (simp add: some_chilbert_basis_of_def verit_sko_ex)
  then show is_ortho_set_some_chilbert_basis_of: \<open>is_ortho_set (some_chilbert_basis_of X)\<close>
    and \<open>b \<in> some_chilbert_basis_of X \<Longrightarrow> norm b = 1\<close>
    and \<open>ccspan (some_chilbert_basis_of X) = X\<close>
    by auto
qed

lemma ccsubspace_as_whole_type:
  fixes X :: \<open>'a::chilbert_space ccsubspace\<close>
  assumes \<open>X \<noteq> 0\<close>
  shows \<open>\<forall>\<^sub>\<tau> 'b::type = some_chilbert_basis_of X.
         \<exists>U::'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a. isometry U \<and> U *\<^sub>S \<top> = X\<close>
proof (rule with_typeI)
  show \<open>fst (some_chilbert_basis_of X, ()) \<noteq> {}\<close>
    using some_chilbert_basis_of_ccspan[of X] assms
    by (auto simp del: some_chilbert_basis_of_ccspan)
  show \<open>fst with_type_type_class (fst (some_chilbert_basis_of X, ()))
     (snd (some_chilbert_basis_of X, ()))\<close>
    by (simp add: with_type_type_class_def)
  show \<open>with_type_compat_rel (fst with_type_type_class) (fst (some_chilbert_basis_of X, ()))
     (snd with_type_type_class)\<close>
    by (auto simp add: with_type_type_class_def with_type_compat_rel_def)
  fix Rep :: \<open>'b \<Rightarrow> 'a\<close> and Abs
  assume \<open>type_definition Rep Abs (fst (some_chilbert_basis_of X, ()))\<close>
  then interpret type_definition Rep Abs \<open>some_chilbert_basis_of X\<close>
    by simp
  define U where \<open>U = cblinfun_extension (range ket) (Rep o inv ket)\<close>
  have [simp]: \<open>Rep i \<bullet>\<^sub>C Rep j = 0\<close> if \<open>i \<noteq> j\<close> for i j
    using Rep some_chilbert_basis_of_is_ortho_set[unfolded is_ortho_set_def] that
    by (smt (verit) Rep_inverse)
  moreover have [simp]: \<open>norm (Rep i) = 1\<close> for i
    using Rep[of i] some_chilbert_basis_of_norm1
    by auto
  ultimately have \<open>cblinfun_extension_exists (range ket) (Rep o inv ket)\<close>
    apply (rule_tac cblinfun_extension_exists_ortho)
    by auto
  then have U_ket[simp]: \<open>U (ket i) = Rep i\<close> for i
    by (auto simp: cblinfun_extension_apply U_def)
  have \<open>isometry U\<close>
    apply (rule orthogonal_on_basis_is_isometry[where B=\<open>range ket\<close>])
    by (auto simp: cinner_ket simp flip: cnorm_eq_1)
  moreover have \<open>U *\<^sub>S ccspan (range ket) = X\<close>
    apply (subst cblinfun_image_ccspan)
    by (simp add: Rep_range image_image)
  ultimately show \<open>\<exists>U :: 'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a. isometry U \<and> U *\<^sub>S \<top> = X\<close>
    by auto
qed

(* TODO right *)
lemma tensor_ccsubspace_INF_left: \<open>(INF x\<in>X. S x) \<otimes>\<^sub>S T = (INF x\<in>X. S x \<otimes>\<^sub>S T)\<close> if \<open>X \<noteq> {}\<close>
proof (cases \<open>T=0\<close>)
  case True
  then show ?thesis 
    using that by simp
next
  case False
  from ccsubspace_as_whole_type[OF False]
  have \<open>\<forall>\<^sub>\<tau> 't::type = some_chilbert_basis_of T.
        (INF x\<in>X. S x) \<otimes>\<^sub>S T = (INF x\<in>X. S x \<otimes>\<^sub>S T)\<close>
  proof (rule with_type_mp)
    fix Rep :: \<open>'t \<Rightarrow> 'c ell2\<close> and Abs
    assume \<open>type_definition Rep Abs (some_chilbert_basis_of T)\<close>
    then interpret type_definition Rep Abs \<open>some_chilbert_basis_of T\<close>
      by simp
    assume \<open>\<exists>U :: 't ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2. isometry U \<and> U *\<^sub>S \<top> = T\<close>
    then obtain U :: \<open>'t ell2 \<Rightarrow>\<^sub>C\<^sub>L 'c ell2\<close> where [simp]: \<open>isometry U\<close> and imU: \<open>U *\<^sub>S \<top> = T\<close>
      by auto
    have \<open>(id_cblinfun \<otimes>\<^sub>o U) *\<^sub>S ((\<Sqinter>x\<in>X. S x) \<otimes>\<^sub>S \<top>) = (id_cblinfun \<otimes>\<^sub>o U) *\<^sub>S (\<Sqinter>x\<in>X. S x \<otimes>\<^sub>S \<top>)\<close>
      apply (rule arg_cong[where f=\<open>\<lambda>x. _ *\<^sub>S x\<close>])  
      by (rule tensor_ccsubspace_INF_left_top)
    then show \<open>(\<Sqinter>x\<in>X. S x) \<otimes>\<^sub>S T = (\<Sqinter>x\<in>X. S x \<otimes>\<^sub>S T)\<close>
      using that by (simp add: imU cblinfun_image_INF_eq isometry_tensor_op
          flip: tensor_ccsubspace_image)
  qed
  from this[cancel_with_type]
  show ?thesis
    by -
qed

lemma abs_op_square: \<open>(abs_op A)* o\<^sub>C\<^sub>L abs_op A = A* o\<^sub>C\<^sub>L A\<close>
  by (simp add: abs_op_def positive_cblinfun_squareI)

(* TODO move to polar_decomposition-definition theory *)
lemma polar_decomposition_0[simp]: \<open>polar_decomposition 0 = (0 :: 'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space)\<close>
proof -
  have \<open>polar_decomposition (0 :: 'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space) *\<^sub>S \<top> = 0 *\<^sub>S \<top>\<close>
    by (simp add: polar_decomposition_final_space)
  then show ?thesis
    by simp
qed

(* TODO move to BO *)
lemma cblinfun_same_on_image: \<open>A \<psi> = B \<psi>\<close> if eq: \<open>A o\<^sub>C\<^sub>L C = B o\<^sub>C\<^sub>L C\<close> and mem: \<open>\<psi> \<in> space_as_set (C *\<^sub>S \<top>)\<close>
proof -
  have \<open>A \<psi> = B \<psi>\<close> if \<open>\<psi> \<in> range C\<close> for \<psi>
    by (metis (no_types, lifting) eq cblinfun_apply_cblinfun_compose image_iff that)
  moreover have \<open>\<psi> \<in> closure (range C)\<close>
    by (metis cblinfun_image.rep_eq mem top_ccsubspace.rep_eq)
  ultimately show ?thesis
    apply (rule on_closure_eqI)
    by (auto simp: continuous_on_eq_continuous_at)
qed

(* TODO move to polar_decomposition-definition theory *)
lemma polar_decomposition_unique:
  fixes A :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  assumes ker: \<open>kernel X = kernel A\<close>
  assumes comp: \<open>X o\<^sub>C\<^sub>L abs_op A = A\<close>
  shows \<open>X = polar_decomposition A\<close>
proof -
  have \<open>X \<psi> = polar_decomposition A \<psi>\<close> if \<open>\<psi> \<in> space_as_set (kernel A)\<close> for \<psi>
  proof -
    have \<open>\<psi> \<in> space_as_set (kernel X)\<close>
      by (simp add: ker that)
    then have \<open>X \<psi> = 0\<close>
      by (simp add: kernel.rep_eq)
    moreover
    have \<open>\<psi> \<in> space_as_set (kernel (polar_decomposition A))\<close>
      by (simp add: polar_decomposition_initial_space that)
    then have \<open>polar_decomposition A \<psi> = 0\<close>
      by (simp add: kernel.rep_eq del: polar_decomposition_initial_space)
    ultimately show ?thesis
      by simp
  qed
  then have 1: \<open>X o\<^sub>C\<^sub>L Proj (kernel A) = polar_decomposition A o\<^sub>C\<^sub>L Proj (kernel A)\<close>
    by (metis (no_types, opaque_lifting) Proj_idempotent cblinfun_eqI lift_cblinfun_comp(4) norm_Proj_apply)

  have *: \<open>abs_op A *\<^sub>S \<top> = - kernel A\<close>
    by (metis (mono_tags, opaque_lifting) abs_op_pos kernel_abs_op kernel_compl_adj_range ortho_involution positive_hermitianI)
  
  have \<open>X o\<^sub>C\<^sub>L abs_op A = polar_decomposition A o\<^sub>C\<^sub>L abs_op A\<close>
    by (simp add: comp polar_decomposition_correct)
  then have \<open>X \<psi> = polar_decomposition A \<psi>\<close> if \<open>\<psi> \<in> space_as_set (abs_op A *\<^sub>S \<top>)\<close> for \<psi>
    by (simp add: cblinfun_same_on_image that)
  then have 2: \<open>X o\<^sub>C\<^sub>L Proj (- kernel A) = polar_decomposition A o\<^sub>C\<^sub>L Proj (- kernel A)\<close>
    using * by (metis (no_types, opaque_lifting) Proj_idempotent cblinfun_eqI lift_cblinfun_comp(4) norm_Proj_apply)
  from 1 2 have \<open>X o\<^sub>C\<^sub>L Proj (- kernel A) + X o\<^sub>C\<^sub>L Proj (kernel A)
           = polar_decomposition A o\<^sub>C\<^sub>L Proj (- kernel A) + polar_decomposition A o\<^sub>C\<^sub>L Proj (kernel A)\<close>
    by simp
  then show ?thesis
    by (simp add: Proj_ortho_compl flip: cblinfun_compose_add_right)
qed

lemma swap_ell2_ket[simp]: \<open>(swap_ell2 :: ('a\<times>'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L _)*\<^sub>V ket (x,y) = ket (y,x)\<close>
  by (metis swap_ell2_tensor tensor_ell2_ket)

(* TODO move to Tensor *)
lemma tensor_ccsubspace_ccspan: \<open>ccspan X \<otimes>\<^sub>S ccspan Y = ccspan {x \<otimes>\<^sub>s y | x y. x \<in> X \<and> y \<in> Y}\<close>
proof (rule antisym)
  show \<open>ccspan {x \<otimes>\<^sub>s y |x y. x \<in> X \<and> y \<in> Y} \<le> ccspan X \<otimes>\<^sub>S ccspan Y\<close>
    apply (auto intro!: ccspan_mono Collect_mono ex_mono simp add: tensor_ccsubspace_def)
    using ccspan_superset by auto
next
  have \<open>{\<psi> \<otimes>\<^sub>s \<phi> |\<psi> \<phi>. \<psi> \<in> space_as_set (ccspan X) \<and> \<phi> \<in> space_as_set (ccspan Y)}
       \<subseteq> closure {x \<otimes>\<^sub>s y |x y. x \<in> cspan X \<and> y \<in> cspan Y}\<close>
  proof (rule subsetI)
    fix \<gamma>
    assume \<open>\<gamma> \<in> {\<psi> \<otimes>\<^sub>s \<phi> |\<psi> \<phi>. \<psi> \<in> space_as_set (ccspan X) \<and> \<phi> \<in> space_as_set (ccspan Y)}\<close>
    then obtain \<psi> \<phi> where \<psi>: \<open>\<psi> \<in> space_as_set (ccspan X)\<close> and \<phi>: \<open>\<phi> \<in> space_as_set (ccspan Y)\<close> and \<gamma>_def: \<open>\<gamma> = \<psi> \<otimes>\<^sub>s \<phi>\<close>
      by blast
    from \<psi>
    obtain \<psi>' where lim1: \<open>\<psi>' \<longlonglongrightarrow> \<psi>\<close> and \<psi>'X: \<open>\<psi>' n \<in> cspan X\<close> for n
      apply atomize_elim
      apply (auto simp: ccspan.rep_eq)
      using closure_sequential by blast
    from \<phi>
    obtain \<phi>' where lim2: \<open>\<phi>' \<longlonglongrightarrow> \<phi>\<close> and \<phi>'Y: \<open>\<phi>' n \<in> cspan Y\<close> for n
      apply atomize_elim
      apply (auto simp: ccspan.rep_eq)
      using closure_sequential by blast
    interpret tensor: bounded_cbilinear tensor_ell2
      by (rule bounded_cbilinear_tensor_ell2)
    from lim1 lim2 have \<open>(\<lambda>n. \<psi>' n \<otimes>\<^sub>s \<phi>' n) \<longlonglongrightarrow> \<psi> \<otimes>\<^sub>s \<phi>\<close>
      by (rule tensor.tendsto)
    moreover have \<open>\<psi>' n \<otimes>\<^sub>s \<phi>' n \<in> {x \<otimes>\<^sub>s y |x y. x \<in> cspan X \<and> y \<in> cspan Y}\<close> for n
      using \<psi>'X \<phi>'Y by auto
    ultimately show \<open>\<gamma> \<in> closure {x \<otimes>\<^sub>s y |x y. x \<in> cspan X \<and> y \<in> cspan Y}\<close>
      unfolding \<gamma>_def
      by (meson closure_sequential)
  qed
  also have \<open>closure {x \<otimes>\<^sub>s y |x y. x \<in> cspan X \<and> y \<in> cspan Y}
          \<subseteq> closure (cspan {x \<otimes>\<^sub>s y |x y. x \<in> X \<and> y \<in> Y})\<close>
  proof (intro closure_mono subsetI)
    fix \<gamma>
    assume \<open>\<gamma> \<in> {x \<otimes>\<^sub>s y |x y. x \<in> cspan X \<and> y \<in> cspan Y}\<close>
    then obtain x y where \<gamma>_def: \<open>\<gamma> = x \<otimes>\<^sub>s y\<close> and \<open>x \<in> cspan X\<close> and \<open>y \<in> cspan Y\<close>
      by blast
    from \<open>x \<in> cspan X\<close>
    obtain X' x' where \<open>finite X'\<close> and \<open>X' \<subseteq> X\<close> and x_def: \<open>x = (\<Sum>i\<in>X'. x' i *\<^sub>C i)\<close>
      using complex_vector.span_explicit[of X] apply atomize_elim
      by auto
    from \<open>y \<in> cspan Y\<close>
    obtain Y' y' where \<open>finite Y'\<close> and \<open>Y' \<subseteq> Y\<close> and y_def: \<open>y = (\<Sum>j\<in>Y'. y' j *\<^sub>C j)\<close>
      using complex_vector.span_explicit[of Y] apply atomize_elim
      by auto
    from x_def y_def \<gamma>_def
    have \<open>\<gamma> = (\<Sum>i\<in>X'. x' i *\<^sub>C i) \<otimes>\<^sub>s (\<Sum>j\<in>Y'. y' j *\<^sub>C j)\<close>
      by simp
    also have \<open>\<dots> = (\<Sum>i\<in>X'. \<Sum>j\<in>Y'. (x' i *\<^sub>C i) \<otimes>\<^sub>s (y' j *\<^sub>C j))\<close>
      by (smt (verit) sum.cong tensor_ell2_sum_left tensor_ell2_sum_right)
    also have \<open>\<dots> = (\<Sum>i\<in>X'. \<Sum>j\<in>Y'. (x' i * y' j) *\<^sub>C (i \<otimes>\<^sub>s j))\<close>
      by (metis (no_types, lifting) scaleC_scaleC sum.cong tensor_ell2_scaleC1 tensor_ell2_scaleC2)
    also have \<open>\<dots> \<in> cspan {x \<otimes>\<^sub>s y |x y. x \<in> X \<and> y \<in> Y}\<close>
      using \<open>X' \<subseteq> X\<close> \<open>Y' \<subseteq> Y\<close>
      by (auto intro!: complex_vector.span_sum complex_vector.span_scale
          complex_vector.span_base[of \<open>_ \<otimes>\<^sub>s _\<close>])
    finally show \<open>\<gamma> \<in> cspan {x \<otimes>\<^sub>s y |x y. x \<in> X \<and> y \<in> Y}\<close>
      by -
  qed
  also have \<open>\<dots> = space_as_set (ccspan {x \<otimes>\<^sub>s y |x y. x \<in> X \<and> y \<in> Y})\<close>
    using ccspan.rep_eq by blast
  finally show \<open>ccspan X \<otimes>\<^sub>S ccspan Y \<le> ccspan {x \<otimes>\<^sub>s y |x y. x \<in> X \<and> y \<in> Y}\<close>
    by (auto intro!: ccspan_leqI simp add: tensor_ccsubspace_def)
qed

lemma SUP_ccspan: \<open>(SUP x\<in>X. ccspan (S x)) = ccspan (\<Union>x\<in>X. S x)\<close>
proof (rule SUP_eqI)
  show \<open>ccspan (S x) \<le> ccspan (\<Union>x\<in>X. S x)\<close> if \<open>x \<in> X\<close> for x
    apply (rule ccspan_mono)
    using that by auto
  show \<open>ccspan (\<Union>x\<in>X. S x) \<le> y\<close> if \<open>\<And>x. x \<in> X \<Longrightarrow> ccspan (S x) \<le> y\<close> for y
    apply (intro ccspan_leqI UN_least)
    using that ccspan_superset by (auto simp: less_eq_ccsubspace.rep_eq)
qed

lemma tensor_ell2_in_tensor_ccsubspace: \<open>a \<otimes>\<^sub>s b \<in> space_as_set (A \<otimes>\<^sub>S B)\<close> if \<open>a \<in> space_as_set A\<close> and \<open>b \<in> space_as_set B\<close>
  \<comment> \<open>Converse is @{thm [source] tensor_ell2_mem_tensor_ccsubspace_left} and \<open>..._right\<close>.\<close>
  using that by (auto intro!: ccspan_superset[THEN subsetD] simp add: tensor_ccsubspace_def)

lemma tensor_ccsubspace_mono: \<open>A \<otimes>\<^sub>S B \<le> C \<otimes>\<^sub>S D\<close> if \<open>A \<le> C\<close> and \<open>B \<le> D\<close>
  apply (auto intro!: ccspan_mono simp add: tensor_ccsubspace_def)
  using that
  by (auto simp add: less_eq_ccsubspace_def)


lemma basis_projections_reconstruct_has_sum:
  assumes \<open>is_ortho_set B\<close> and normB: \<open>\<And>b. b\<in>B \<Longrightarrow> norm b = 1\<close> and \<psi>B: \<open>\<psi> \<in> space_as_set (ccspan B)\<close>
  shows \<open>has_sum (\<lambda>b. (b \<bullet>\<^sub>C \<psi>) *\<^sub>C b) B \<psi>\<close>
proof (rule has_sumI_metric)
  fix e :: real assume \<open>e > 0\<close>
  define e2 where \<open>e2 = e/2\<close>
  have [simp]: \<open>e2 > 0\<close>
    by (simp add: \<open>0 < e\<close> e2_def)
  define bb where \<open>bb \<phi> b = (b \<bullet>\<^sub>C \<phi>) *\<^sub>C b\<close> for \<phi> and b :: 'a
  have linear_bb: \<open>clinear (\<lambda>\<phi>. bb \<phi> b)\<close> for b
    by (simp add: bb_def cinner_add_right clinear_iff scaleC_left.add)
  from \<psi>B obtain \<phi> where dist\<phi>\<psi>: \<open>dist \<phi> \<psi> < e2\<close> and \<phi>B: \<open>\<phi> \<in> cspan B\<close>
    apply atomize_elim apply (simp add: ccspan.rep_eq closure_approachable)
    using \<open>0 < e2\<close> by blast
  from \<phi>B obtain F where \<open>finite F\<close> and \<open>F \<subseteq> B\<close> and \<phi>F: \<open>\<phi> \<in> cspan F\<close>
    by (meson vector_finitely_spanned)
  have \<open>dist (sum (bb \<psi>) G) \<psi> < e\<close> 
    if \<open>finite G\<close> and \<open>F \<subseteq> G\<close> and \<open>G \<subseteq> B\<close> for G
  proof -
    have sum\<phi>: \<open>sum (bb \<phi>) G = \<phi>\<close>
    proof -
      from \<phi>F \<open>F \<subseteq> G\<close> have \<phi>G: \<open>\<phi> \<in> cspan G\<close>
        using complex_vector.span_mono by blast
      then obtain f where \<phi>sum: \<open>\<phi> = (\<Sum>b\<in>G. f b *\<^sub>C b)\<close>
        using complex_vector.span_finite[OF \<open>finite G\<close>] 
        by auto
      have \<open>sum (bb \<phi>) G = (\<Sum>c\<in>G. \<Sum>b\<in>G. bb (f b *\<^sub>C b) c)\<close>
        apply (simp add: \<phi>sum)
        apply (rule sum.cong, simp)
        apply (rule complex_vector.linear_sum[where f=\<open>\<lambda>x. bb x _\<close>])
        by (rule linear_bb)
      also have \<open>\<dots> = (\<Sum>(c,b)\<in>G\<times>G. bb (f b *\<^sub>C b) c)\<close>
        by (simp add: sum.cartesian_product)
      also have \<open>\<dots> = (\<Sum>b\<in>G. f b *\<^sub>C b)\<close>
        apply (rule sym)
        apply (rule sum.reindex_bij_witness_not_neutral
            [where j=\<open>\<lambda>b. (b,b)\<close> and i=fst and T'=\<open>G\<times>G - (\<lambda>b. (b,b)) ` G\<close> and S'=\<open>{}\<close>])
        using \<open>finite G\<close> apply (auto simp: bb_def)
         apply (metis (no_types, lifting) assms(1) imageI is_ortho_set_antimono is_ortho_set_def that(3))
        using normB \<open>G \<subseteq> B\<close> cnorm_eq_1 by blast
      also have \<open>\<dots> = \<phi>\<close>
        by (simp flip: \<phi>sum)
      finally show ?thesis
        by -
    qed
    have \<open>dist (sum (bb \<phi>) G) (sum (bb \<psi>) G) < e2\<close>
    proof -
      define \<gamma> where \<open>\<gamma> = \<phi> - \<psi>\<close>
      have \<open>(dist (sum (bb \<phi>) G) (sum (bb \<psi>) G))\<^sup>2 = (norm (sum (bb \<gamma>) G))\<^sup>2\<close>
        by (simp add: dist_norm \<gamma>_def complex_vector.linear_diff[OF linear_bb] sum_subtractf)
      also have \<open>\<dots> = (norm (sum (bb \<gamma>) G))\<^sup>2 + (norm (\<gamma> - sum (bb \<gamma>) G))\<^sup>2 - (norm (\<gamma> - sum (bb \<gamma>) G))\<^sup>2\<close>
        by simp
      also have \<open>\<dots> = (norm (sum (bb \<gamma>) G + (\<gamma> - sum (bb \<gamma>) G)))\<^sup>2 - (norm (\<gamma> - sum (bb \<gamma>) G))\<^sup>2\<close>
      proof -
        have \<open>(\<Sum>b\<in>G. bb \<gamma> b \<bullet>\<^sub>C bb \<gamma> c) = bb \<gamma> c \<bullet>\<^sub>C \<gamma>\<close> if \<open>c \<in> G\<close> for c
          apply (subst sum_single[where i=c])
          using that apply (auto intro!: \<open>finite G\<close> simp: bb_def)
           apply (metis \<open>G \<subseteq> B\<close> \<open>is_ortho_set B\<close> is_ortho_set_antimono is_ortho_set_def)
          using \<open>G \<subseteq> B\<close> normB cnorm_eq_1 by blast
        then have \<open>is_orthogonal (sum (bb \<gamma>) G) (\<gamma> - sum (bb \<gamma>) G)\<close>
          by (simp add: cinner_sum_left cinner_diff_right cinner_sum_right)
        then show ?thesis
          apply (rule_tac arg_cong[where f=\<open>\<lambda>x. x - _\<close>])
          by (rule pythagorean_theorem[symmetric])
      qed
      also have \<open>\<dots> = (norm \<gamma>)\<^sup>2 - (norm (\<gamma> - sum (bb \<gamma>) G))\<^sup>2\<close>
        by simp
      also have \<open>\<dots> \<le> (norm \<gamma>)\<^sup>2\<close>
        by simp
      also have \<open>\<dots> = (dist \<phi> \<psi>)\<^sup>2\<close>
        by (simp add: \<gamma>_def dist_norm)
      also have \<open>\<dots> < e2\<^sup>2\<close>
        using dist\<phi>\<psi> apply (rule power_strict_mono)
        by auto
      finally show ?thesis
        by (smt (verit) \<open>0 < e2\<close> power_mono)
    qed
    with sum\<phi> dist\<phi>\<psi> show \<open>dist (sum (bb \<psi>) G) \<psi> < e\<close>
      apply (rule_tac dist_triangle_lt[where z=\<phi>])
      by (simp add: e2_def dist_commute)
  qed
  with \<open>finite F\<close> and \<open>F \<subseteq> B\<close> 
  show \<open>\<exists>F. finite F \<and>
             F \<subseteq> B \<and> (\<forall>G. finite G \<and> F \<subseteq> G \<and> G \<subseteq> B \<longrightarrow> dist (sum (bb \<psi>) G) \<psi> < e)\<close>
    by (auto intro!: exI[of _ F])
qed

lemma basis_projections_reconstruct:
  assumes \<open>is_ortho_set B\<close> and \<open>\<And>b. b\<in>B \<Longrightarrow> norm b = 1\<close> and \<open>\<psi> \<in> space_as_set (ccspan B)\<close>
  shows \<open>(\<Sum>\<^sub>\<infinity>b\<in>B. (b \<bullet>\<^sub>C \<psi>) *\<^sub>C b) = \<psi>\<close>
  using assms basis_projections_reconstruct_has_sum infsumI by blast

lemma basis_projections_reconstruct_summable:
  assumes \<open>is_ortho_set B\<close> and \<open>\<And>b. b\<in>B \<Longrightarrow> norm b = 1\<close> and \<open>\<psi> \<in> space_as_set (ccspan B)\<close>
  shows \<open>(\<lambda>b. (b \<bullet>\<^sub>C \<psi>) *\<^sub>C b) summable_on B\<close>
  by (simp add: assms basis_projections_reconstruct basis_projections_reconstruct_has_sum summable_iff_has_sum_infsum)

(* TODO move (this replaces Trace_Class.parseval_infsum) *)
lemma has_sum_norm_on_basis:
  assumes \<open>is_ortho_set B\<close> and normB: \<open>\<And>b. b\<in>B \<Longrightarrow> norm b = 1\<close> and \<open>\<psi> \<in> space_as_set (ccspan B)\<close>
  shows \<open>has_sum (\<lambda>b. (norm (b \<bullet>\<^sub>C \<psi>))\<^sup>2) B ((norm \<psi>)\<^sup>2)\<close>
proof -
  have *: \<open>(\<lambda>v. (norm v)\<^sup>2) (\<Sum>b\<in>F. (b \<bullet>\<^sub>C \<psi>) *\<^sub>C b) = (\<Sum>b\<in>F. (norm (b \<bullet>\<^sub>C \<psi>))\<^sup>2)\<close> if \<open>finite F\<close> and \<open>F \<subseteq> B\<close> for F
    apply (subst pythagorean_theorem_sum)
    using \<open>is_ortho_set B\<close> normB that
      apply (auto intro!: sum.cong[OF refl] simp: is_ortho_set_def)
    by blast
  
  from assms have \<open>has_sum (\<lambda>b. (b \<bullet>\<^sub>C \<psi>) *\<^sub>C b) B \<psi>\<close>
    by (simp add: basis_projections_reconstruct_has_sum)
  then have \<open>((\<lambda>F. \<Sum>b\<in>F. (b \<bullet>\<^sub>C \<psi>) *\<^sub>C b) \<longlongrightarrow> \<psi>) (finite_subsets_at_top B)\<close>
    by (simp add: has_sum_def)
  then have \<open>((\<lambda>F. (\<lambda>v. (norm v)\<^sup>2) (\<Sum>b\<in>F. (b \<bullet>\<^sub>C \<psi>) *\<^sub>C b)) \<longlongrightarrow> (norm \<psi>)\<^sup>2) (finite_subsets_at_top B)\<close>
    apply (rule isCont_tendsto_compose[rotated])
    by simp
  then have \<open>((\<lambda>F. (\<Sum>b\<in>F. (norm (b \<bullet>\<^sub>C \<psi>))\<^sup>2)) \<longlongrightarrow> (norm \<psi>)\<^sup>2) (finite_subsets_at_top B)\<close>
    apply (rule tendsto_cong[THEN iffD2, rotated])
    apply (rule eventually_finite_subsets_at_top_weakI)
    by (simp add: *)
  then show \<open>has_sum (\<lambda>b. (norm (b \<bullet>\<^sub>C \<psi>))\<^sup>2) B ((norm \<psi>)\<^sup>2)\<close>
    by (simp add: has_sum_def)
qed

lemma summable_on_norm_on_basis:
  assumes \<open>is_ortho_set B\<close> and \<open>\<And>b. b\<in>B \<Longrightarrow> norm b = 1\<close> and \<open>\<psi> \<in> space_as_set (ccspan B)\<close>
  shows \<open>(\<lambda>b. (norm (b \<bullet>\<^sub>C \<psi>))\<^sup>2) summable_on B\<close>
  using has_sum_norm_on_basis[OF assms] summable_onI by blast

lemma infsum_norm_on_basis:
  assumes \<open>is_ortho_set B\<close> and \<open>\<And>b. b\<in>B \<Longrightarrow> norm b = 1\<close> and \<open>\<psi> \<in> space_as_set (ccspan B)\<close>
  shows \<open>(\<Sum>\<^sub>\<infinity>b\<in>B. (norm (b \<bullet>\<^sub>C \<psi>))\<^sup>2) = (norm \<psi>)\<^sup>2\<close>
  using has_sum_norm_on_basis[OF assms]
  using infsumI by blast

lemma tensor_ccsubspace_element_as_infsum:
  fixes A :: \<open>'a ell2 ccsubspace\<close> and B :: \<open>'b ell2 ccsubspace\<close>
  assumes \<open>\<psi> \<in> space_as_set (A \<otimes>\<^sub>S B)\<close>
  shows \<open>\<exists>\<phi> \<delta>. (\<forall>n::nat. \<phi> n \<in> space_as_set A) \<and> (\<forall>n. \<delta> n \<in> space_as_set B)
       \<and> has_sum (\<lambda>n. \<phi> n \<otimes>\<^sub>s \<delta> n) UNIV \<psi>\<close>
proof -
  obtain A' where spanA': \<open>ccspan A' = A\<close> and orthoA': \<open>is_ortho_set A'\<close> and normA': \<open>a \<in> A' \<Longrightarrow> norm a = 1\<close> for a
    using some_chilbert_basis_of_ccspan some_chilbert_basis_of_is_ortho_set some_chilbert_basis_of_norm1
    by blast
  obtain B' where spanB': \<open>ccspan B' = B\<close> and orthoB': \<open>is_ortho_set B'\<close> and normB': \<open>b \<in> B' \<Longrightarrow> norm b = 1\<close> for b
    using some_chilbert_basis_of_ccspan some_chilbert_basis_of_is_ortho_set some_chilbert_basis_of_norm1
    by blast
  define AB' where \<open>AB' = {a \<otimes>\<^sub>s b | a b. a \<in> A' \<and> b \<in> B'}\<close>
  define ABnon0 where \<open>ABnon0 = {ab \<in> AB'. (ab \<bullet>\<^sub>C \<psi>) *\<^sub>C ab \<noteq> 0}\<close>
  have ABnon0_def': \<open>ABnon0 = {ab \<in> AB'. (norm (ab \<bullet>\<^sub>C \<psi>))\<^sup>2 \<noteq> 0}\<close>
    by (auto simp: ABnon0_def)
  have \<open>is_ortho_set AB'\<close>
    by (simp add: AB'_def orthoA' orthoB' tensor_ell2_is_ortho_set)
  have normAB': \<open>ab \<in> AB' \<Longrightarrow> norm ab = 1\<close> for ab
    by (auto simp add: AB'_def norm_tensor_ell2 normA' normB')
  have spanAB': \<open>ccspan AB' = A \<otimes>\<^sub>S B\<close>
    by (simp add: tensor_ccsubspace_ccspan AB'_def flip: spanA' spanB')
  have sum1: \<open>has_sum (\<lambda>ab. (ab \<bullet>\<^sub>C \<psi>) *\<^sub>C ab) AB' \<psi>\<close>
    apply (rule basis_projections_reconstruct_has_sum)
    by (simp_all add: spanAB' \<open>is_ortho_set AB'\<close> normAB' assms)
  have \<open>(\<lambda>ab. (norm (ab \<bullet>\<^sub>C \<psi>))\<^sup>2) summable_on AB'\<close>
    apply (rule summable_on_norm_on_basis)
    by (simp_all add: spanAB' \<open>is_ortho_set AB'\<close> normAB' assms)
  then have \<open>countable ABnon0\<close>
    using ABnon0_def' summable_countable_real by blast
  obtain f and N :: \<open>nat set\<close> where bij_f: \<open>bij_betw f N ABnon0\<close>
    using \<open>countable ABnon0\<close> countableE_bij by blast
  then obtain \<phi>0 \<delta>0 where f_def: \<open>f n = \<phi>0 n \<otimes>\<^sub>s \<delta>0 n\<close> and \<phi>0A': \<open>\<phi>0 n \<in> A'\<close> and \<delta>0B': \<open>\<delta>0 n \<in> B'\<close> if \<open>n \<in> N\<close> for n
    apply atomize_elim 
    apply (subst all_conj_distrib[symmetric] choice_iff[symmetric])+
    apply (simp add: bij_betw_def ABnon0_def)
    using AB'_def \<open>bij_betw f N ABnon0\<close> bij_betwE mem_Collect_eq by blast
  define c where \<open>c n = (\<phi>0 n \<otimes>\<^sub>s \<delta>0 n) \<bullet>\<^sub>C \<psi>\<close> for n
  from sum1 have \<open>has_sum (\<lambda>ab. (ab \<bullet>\<^sub>C \<psi>) *\<^sub>C ab) ABnon0 \<psi>\<close>
    apply (rule has_sum_cong_neutral[THEN iffD1, rotated -1])
    by (auto simp: ABnon0_def)
  then have \<open>has_sum (\<lambda>n. (f n \<bullet>\<^sub>C \<psi>) *\<^sub>C f n) N \<psi>\<close>
    by (rule has_sum_reindex_bij_betw[OF bij_f, THEN iffD2])
  then have sum2: \<open>has_sum (\<lambda>n. c n *\<^sub>C (\<phi>0 n \<otimes>\<^sub>s \<delta>0 n)) N \<psi>\<close>
    apply (rule has_sum_cong[THEN iffD1, rotated])
    by (simp add: f_def c_def)
  define \<phi> \<delta> where \<open>\<phi> n = (if n\<in>N then c n *\<^sub>C \<phi>0 n else 0)\<close> and \<open>\<delta> n = (if n\<in>N then \<delta>0 n else 0)\<close> for n
  then have 1: \<open>\<phi> n \<in> space_as_set A\<close> and 2: \<open>\<delta> n \<in> space_as_set B\<close> for n
    using \<phi>0A' \<delta>0B' spanA' spanB' ccspan_superset 
    by (auto intro!: complex_vector.subspace_scale simp: \<phi>_def \<delta>_def)
  from sum2 have sum3: \<open>has_sum (\<lambda>n. \<phi> n \<otimes>\<^sub>s \<delta> n) UNIV \<psi>\<close>
    apply (rule has_sum_cong_neutral[THEN iffD2, rotated -1])
    by (auto simp: \<phi>_def \<delta>_def tensor_ell2_scaleC1)
  from 1 2 sum3 show ?thesis
    by auto
qed

lemma ccspan_superset': \<open>x \<in> X \<Longrightarrow> x \<in> space_as_set (ccspan X)\<close>
  using ccspan_superset by auto

(* TODO move *)
lemma kernel_apply_self: \<open>A *\<^sub>S kernel A = 0\<close>
proof transfer
  fix A :: \<open>'b \<Rightarrow> 'a\<close>
  assume \<open>bounded_clinear A\<close>
  then have \<open>A 0 = 0\<close>
    by (simp add: bounded_clinear_def complex_vector.linear_0)
  then have \<open>A ` A -` {0} = {0}\<close>
    by fastforce
  then show \<open>closure (A ` A -` {0}) = {0}\<close>
    by auto
qed

(* TODO move *)
lemma leq_kernel_iff: 
  shows \<open>A \<le> kernel B \<longleftrightarrow> B *\<^sub>S A = 0\<close>
proof (rule iffI)
  assume \<open>A \<le> kernel B\<close>
  then have \<open>B *\<^sub>S A \<le> B *\<^sub>S kernel B\<close>
    by (simp add: cblinfun_image_mono)
  also have \<open>\<dots> = 0\<close>
    by (simp add: kernel_apply_self)
  finally show \<open>B *\<^sub>S A = 0\<close>
    by (simp add: bot.extremum_unique)
next
  assume \<open>B *\<^sub>S A = 0\<close>
  then show \<open>A \<le> kernel B\<close>
    apply transfer
    by (metis closure_subset image_subset_iff_subset_vimage)
qed

(* TODO move *)
lemma cblinfun_image_kernel:
  assumes \<open>C *\<^sub>S A *\<^sub>S kernel B \<le> kernel B\<close>
  assumes \<open>A o\<^sub>C\<^sub>L C = id_cblinfun\<close>
  shows \<open>A *\<^sub>S kernel B = kernel (B o\<^sub>C\<^sub>L C)\<close>
proof (rule antisym)
  show \<open>A *\<^sub>S kernel B \<le> kernel (B o\<^sub>C\<^sub>L C)\<close>
    using assms(1) by (simp add: leq_kernel_iff cblinfun_compose_image)
  show \<open>kernel (B o\<^sub>C\<^sub>L C) \<le> A *\<^sub>S kernel B\<close>
  proof (insert assms(2), transfer, intro subsetI)
    fix A :: \<open>'a \<Rightarrow> 'b\<close> and B :: \<open>'a \<Rightarrow> 'c\<close> and C :: \<open>'b \<Rightarrow> 'a\<close> and x
    assume \<open>x \<in> (B \<circ> C) -` {0}\<close>
    then have BCx: \<open>B (C x) = 0\<close>
      by simp
    assume \<open>A \<circ> C = (\<lambda>x. x)\<close>
    then have \<open>x = A (C x)\<close>
      apply (simp add: o_def)
      by metis
    then show \<open>x \<in> closure (A ` B -` {0})\<close>
      using \<open>B (C x) = 0\<close> closure_subset by fastforce
  qed
qed

(* TODO move *)
lemma cblinfun_image_kernel_unitary:
  assumes \<open>unitary U\<close>
  shows \<open>U *\<^sub>S kernel B = kernel (B o\<^sub>C\<^sub>L U*)\<close>
  apply (rule cblinfun_image_kernel)
  using assms by (auto simp flip: cblinfun_compose_image)

(* TODO move *)
lemma kernel_cblinfun_compose:
  assumes \<open>kernel B = 0\<close>
  shows \<open>kernel A = kernel (B o\<^sub>C\<^sub>L A)\<close>
  using assms apply transfer by auto

(* TODO move *)
lemma swap_ell2_commute_tensor_op: 
  \<open>swap_ell2 o\<^sub>C\<^sub>L (a \<otimes>\<^sub>o b) = (b \<otimes>\<^sub>o a) o\<^sub>C\<^sub>L swap_ell2\<close>
  by (auto intro!: tensor_ell2_extensionality simp: tensor_op_ell2)

lemma isometry_tensor_id_right[simp]:
  fixes U :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
  shows \<open>isometry (U \<otimes>\<^sub>o (id_cblinfun :: 'c ell2 \<Rightarrow>\<^sub>C\<^sub>L _)) \<longleftrightarrow> isometry U\<close>
proof (rule iffI)
  assume \<open>isometry U\<close>
  then show \<open>isometry (U \<otimes>\<^sub>o id_cblinfun)\<close>
    unfolding isometry_def
    by (auto simp add: tensor_op_adjoint comp_tensor_op)
next
  let ?id = \<open>id_cblinfun :: 'c ell2 \<Rightarrow>\<^sub>C\<^sub>L _\<close>
  assume asm: \<open>isometry (U \<otimes>\<^sub>o ?id)\<close>
  then have \<open>(U* o\<^sub>C\<^sub>L U) \<otimes>\<^sub>o ?id = id_cblinfun \<otimes>\<^sub>o ?id\<close>
    by (simp add: isometry_def tensor_op_adjoint comp_tensor_op)
  then have \<open>U* o\<^sub>C\<^sub>L U = id_cblinfun\<close>
    apply (rule inj_tensor_left[of ?id, unfolded inj_def, rule_format, rotated])
    by simp
  then show \<open>isometry U\<close>
    by (simp add: isometry_def)
qed

lemma isometry_tensor_id_left[simp]: 
  fixes U :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
  shows \<open>isometry ((id_cblinfun :: 'c ell2 \<Rightarrow>\<^sub>C\<^sub>L _) \<otimes>\<^sub>o U) \<longleftrightarrow> isometry U\<close>
proof (rule iffI)
  assume \<open>isometry U\<close>
  then show \<open>isometry (id_cblinfun \<otimes>\<^sub>o U)\<close>
    unfolding isometry_def
    by (auto simp add: tensor_op_adjoint comp_tensor_op)
next
  let ?id = \<open>id_cblinfun :: 'c ell2 \<Rightarrow>\<^sub>C\<^sub>L _\<close>
  assume asm: \<open>isometry (?id \<otimes>\<^sub>o U)\<close>
  then have \<open>?id \<otimes>\<^sub>o (U* o\<^sub>C\<^sub>L U) = ?id \<otimes>\<^sub>o id_cblinfun\<close>
    by (simp add: isometry_def tensor_op_adjoint comp_tensor_op)
  then have \<open>U* o\<^sub>C\<^sub>L U = id_cblinfun\<close>
    apply (rule inj_tensor_right[of ?id, unfolded inj_def, rule_format, rotated])
    by simp
  then show \<open>isometry U\<close>
    by (simp add: isometry_def)
qed

lemma unitary_tensor_id_right[simp]: \<open>unitary (U \<otimes>\<^sub>o id_cblinfun) \<longleftrightarrow> unitary U\<close>
  unfolding unitary_twosided_isometry
  by (simp add: tensor_op_adjoint)

lemma unitary_tensor_id_left[simp]: \<open>unitary (id_cblinfun \<otimes>\<^sub>o U) \<longleftrightarrow> unitary U\<close>
  unfolding unitary_twosided_isometry
  by (simp add: tensor_op_adjoint)

lemma cblinfun_image_eigenspace_isometry:
  assumes [simp]: \<open>isometry A\<close> and \<open>c \<noteq> 0\<close>
  shows \<open>A *\<^sub>S eigenspace c B = eigenspace c (sandwich A B)\<close>
proof (rule antisym)
  show \<open>A *\<^sub>S eigenspace c B \<le> eigenspace c (sandwich A B)\<close>
  proof (unfold cblinfun_image_def2, rule ccspan_leqI, rule subsetI)
    fix x assume \<open>x \<in> (*\<^sub>V) A ` space_as_set (eigenspace c B)\<close>
    then obtain y where x_def: \<open>x = A y\<close> and \<open>y \<in> space_as_set (eigenspace c B)\<close>
      by auto
    then have \<open>B y = c *\<^sub>C y\<close>
      by (simp add: eigenspace_memberD)
    then have \<open>sandwich A B x = c *\<^sub>C x\<close>
      apply (simp add: sandwich_apply x_def cblinfun_compose_assoc 
          flip: cblinfun_apply_cblinfun_compose)
      by (simp add: cblinfun.scaleC_right)
    then show \<open>x \<in> space_as_set (eigenspace c (sandwich A B))\<close>
      by (simp add: eigenspace_memberI)
  qed
  show \<open>eigenspace c (sandwich A *\<^sub>V B) \<le> A *\<^sub>S eigenspace c B\<close>
  proof (rule ccsubspace_leI_unit)
    fix x
    assume \<open>x \<in> space_as_set (eigenspace c (sandwich A B))\<close>
    then have *: \<open>sandwich A B x = c *\<^sub>C x\<close>
      by (simp add: eigenspace_memberD)
    then have \<open>c *\<^sub>C x \<in> range A\<close>
      apply (simp add: sandwich_apply)
      by (metis rangeI)
    then have \<open>(inverse c * c) *\<^sub>C x \<in> range A\<close>
      apply (simp flip: scaleC_scaleC)
      by (metis (no_types, lifting) cblinfun.scaleC_right rangeE rangeI)
    with \<open>c \<noteq> 0\<close> have \<open>x \<in> range A\<close>
      by simp
    then obtain y where x_def: \<open>x = A y\<close>
      by auto
    have \<open>B *\<^sub>V y = A* *\<^sub>V sandwich A B x\<close>
      apply (simp add: sandwich_apply x_def)
      by (metis assms cblinfun_apply_cblinfun_compose id_cblinfun.rep_eq isometryD)
    also have \<open>\<dots> = c *\<^sub>C y\<close>
      apply (simp add: * cblinfun.scaleC_right)
      apply (simp add: x_def)
      by (metis assms(1) cblinfun_apply_cblinfun_compose id_cblinfun_apply isometry_def)
    finally have \<open>y \<in> space_as_set (eigenspace c B)\<close>
      by (simp add: eigenspace_memberI)
    then show \<open>x \<in> space_as_set (A *\<^sub>S eigenspace c B) \<close>
      by (simp add: x_def cblinfun_apply_in_image')
  qed
qed

lemma unitary_image_ortho_compl: 
  fixes U :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  assumes [simp]: \<open>unitary U\<close>
  shows \<open>U *\<^sub>S (- A) = - (U *\<^sub>S A)\<close>
proof -
  have \<open>Proj (U *\<^sub>S (- A)) = sandwich U (Proj (- A))\<close>
    by (simp add: Proj_sandwich)
  also have \<open>\<dots> = sandwich U (id_cblinfun - Proj A)\<close>
    by (simp add: Proj_ortho_compl)
  also have \<open>\<dots> = id_cblinfun - sandwich U (Proj A)\<close>
    by (metis assms cblinfun.diff_right sandwich_isometry_id unitary_twosided_isometry)
  also have \<open>\<dots> = id_cblinfun - Proj (U *\<^sub>S A)\<close>
    by (simp add: Proj_sandwich)
  also have \<open>\<dots> = Proj (- (U *\<^sub>S A))\<close>
    by (simp add: Proj_ortho_compl)
  finally show ?thesis
    by (simp add: Proj_inj)
qed


lemma ortho_tensor_ccsubspace_right: \<open>- (\<top> \<otimes>\<^sub>S A) = \<top> \<otimes>\<^sub>S (- A)\<close>
proof -
  have [simp]: \<open>is_Proj (id_cblinfun \<otimes>\<^sub>o Proj X)\<close> for X
    by (metis Proj_is_Proj Proj_top is_Proj_tensor_op)
  
  have \<open>Proj (- (\<top> \<otimes>\<^sub>S A)) = id_cblinfun - Proj (\<top> \<otimes>\<^sub>S A)\<close>
    by (simp add: Proj_ortho_compl)
  also have \<open>\<dots> = id_cblinfun - (id_cblinfun \<otimes>\<^sub>o Proj A)\<close>
    by (simp add: tensor_ccsubspace_via_Proj Proj_on_own_range)
  also have \<open>\<dots> = id_cblinfun \<otimes>\<^sub>o (id_cblinfun - Proj A)\<close>
    by (metis cblinfun.diff_right left_amplification.rep_eq tensor_id)
  also have \<open>\<dots> = Proj \<top> \<otimes>\<^sub>o Proj (- A)\<close>
    by (simp add: Proj_ortho_compl)
  also have \<open>\<dots> = Proj (\<top> \<otimes>\<^sub>S (- A))\<close>
    by (simp add: tensor_ccsubspace_via_Proj Proj_on_own_range)
  finally show ?thesis
    using Proj_inj by blast
qed

lemma ortho_tensor_ccsubspace_left: \<open>- (A \<otimes>\<^sub>S \<top>) = (- A) \<otimes>\<^sub>S \<top>\<close>
proof -
  have \<open>- (A \<otimes>\<^sub>S \<top>) = swap_ell2 *\<^sub>S (- (\<top> \<otimes>\<^sub>S A))\<close>
    by (simp add: unitary_image_ortho_compl swap_ell2_tensor_ccsubspace)
  also have \<open>\<dots> = swap_ell2 *\<^sub>S (\<top> \<otimes>\<^sub>S (- A))\<close>
    by (simp add: ortho_tensor_ccsubspace_right)
  also have \<open>\<dots> = (- A) \<otimes>\<^sub>S \<top>\<close>
    by (simp add: swap_ell2_tensor_ccsubspace)
  finally show ?thesis
    by -
qed

(* TODO _right *)
lemma kernel_tensor_id_left: \<open>kernel (id_cblinfun \<otimes>\<^sub>o A) = \<top> \<otimes>\<^sub>S kernel A\<close>
proof -
  have \<open>kernel (id_cblinfun \<otimes>\<^sub>o A) = - ((id_cblinfun \<otimes>\<^sub>o A)* *\<^sub>S \<top>)\<close>
    by (rule kernel_compl_adj_range)
  also have \<open>\<dots> = - (id_cblinfun *\<^sub>S \<top> \<otimes>\<^sub>S A* *\<^sub>S \<top>)\<close>
    by (metis cblinfun_image_id id_cblinfun_adjoint tensor_ccsubspace_image tensor_ccsubspace_top tensor_op_adjoint)
  also have \<open>\<dots> = \<top> \<otimes>\<^sub>S (- (A* *\<^sub>S \<top>))\<close>
    by (simp add: ortho_tensor_ccsubspace_right)
  also have \<open>\<dots> = \<top> \<otimes>\<^sub>S kernel A\<close>
    by (simp add: kernel_compl_adj_range)
  finally show ?thesis
    by -
qed

(* TODO _right *)
lemma eigenspace_tensor_id_left: \<open>eigenspace c (id_cblinfun \<otimes>\<^sub>o A) = \<top> \<otimes>\<^sub>S eigenspace c A\<close>
proof -
  have \<open>eigenspace c (id_cblinfun \<otimes>\<^sub>o A) = kernel (id_cblinfun \<otimes>\<^sub>o (A - c *\<^sub>C id_cblinfun))\<close>
    apply (simp add: eigenspace_def)
    by (metis (no_types, lifting) complex_vector.scale_minus_left tensor_id tensor_op_right_add tensor_op_scaleC_right uminus_add_conv_diff)
  also have \<open>kernel (id_cblinfun \<otimes>\<^sub>o (A - c *\<^sub>C id_cblinfun)) = \<top> \<otimes>\<^sub>S kernel (A - c *\<^sub>C id_cblinfun)\<close>
    by (simp add: kernel_tensor_id_left)
  also have \<open>\<dots> = \<top> \<otimes>\<^sub>S eigenspace c A\<close>
    by (simp add: eigenspace_def)
  finally show ?thesis
    by -
qed

lemma summable_on_bounded_linear:
  assumes \<open>bounded_linear f\<close>
  assumes \<open>g summable_on S\<close>
  shows \<open>(f o g) summable_on S\<close>
  by (metis assms(1) assms(2) has_sum_bounded_linear infsum_bounded_linear summable_iff_has_sum_infsum)

lemma infsum_cblinfun_apply_isometry:
  assumes \<open>isometry A\<close>
  shows \<open>infsum (\<lambda>x. A *\<^sub>V g x) S = A *\<^sub>V (infsum g S)\<close>
proof -
  consider (summable) \<open>g summable_on S\<close> | (summable') \<open>(\<lambda>x. A *\<^sub>V g x) summable_on S\<close>
    | (not_summable) \<open>\<not> g summable_on S\<close> \<open>\<not> (\<lambda>x. A *\<^sub>V g x) summable_on S\<close>
    by auto
  then show ?thesis
  proof cases
    case summable
    then show ?thesis
      using infsum_cblinfun_apply by blast
  next
    case summable'
    then have \<open>(\<lambda>x. A* *\<^sub>V A *\<^sub>V g x) summable_on S\<close>
      apply (rule summable_on_bounded_linear[unfolded o_def, where f=\<open>\<lambda>x. A* *\<^sub>V x\<close>, rotated])
      by (intro bounded_linear_intros)
    with \<open>isometry A\<close> have \<open>g summable_on S\<close>
      by (simp add: flip: cblinfun_apply_cblinfun_compose)
    then show ?thesis
      using infsum_cblinfun_apply by blast
  next
    case not_summable
    then show ?thesis 
      by (simp add: infsum_not_exists)
  qed
qed

lemma summable_on_tensor_ell2_right: \<open>\<phi> summable_on A \<Longrightarrow> (\<lambda>x. \<psi> \<otimes>\<^sub>s \<phi> x) summable_on A\<close>
  apply (rule summable_on_bounded_linear[unfolded o_def, where f=\<open>\<lambda>x. \<psi> \<otimes>\<^sub>s x\<close>])
  by (intro bounded_linear_intros)

lemma summable_on_tensor_ell2_left: \<open>\<phi> summable_on A \<Longrightarrow> (\<lambda>x. \<phi> x \<otimes>\<^sub>s \<psi>) summable_on A\<close>
  apply (rule summable_on_bounded_linear[unfolded o_def, where f=\<open>\<lambda>x. x \<otimes>\<^sub>s \<psi>\<close>])
  by (intro bounded_linear_intros)

lemma infsum_tensor_ell2_right: \<open>\<psi> \<otimes>\<^sub>s (\<Sum>\<^sub>\<infinity>x\<in>A. \<phi> x) = (\<Sum>\<^sub>\<infinity>x\<in>A. \<psi> \<otimes>\<^sub>s \<phi> x)\<close>
proof -
  consider (summable) \<open>\<phi> summable_on A\<close> | (summable') \<open>\<psi> \<noteq> 0\<close> \<open>(\<lambda>x. \<psi> \<otimes>\<^sub>s \<phi> x) summable_on A\<close>
    | (\<psi>0) \<open>\<psi> = 0\<close>
    | (not_summable) \<open>\<not> \<phi> summable_on A\<close> \<open>\<not> (\<lambda>x. \<psi> \<otimes>\<^sub>s \<phi> x) summable_on A\<close>
    by auto
  then show ?thesis
  proof cases
    case summable
    then show ?thesis
      apply (rule infsum_bounded_linear[symmetric, unfolded o_def, rotated])
      by (intro bounded_linear_intros)
  next
    case summable'
    then have *: \<open>(\<psi> /\<^sub>R (norm \<psi>)\<^sup>2) \<bullet>\<^sub>C \<psi> = 1\<close>
      by (simp add: scaleR_scaleC cdot_square_norm)
    from summable'(2) have \<open>(\<lambda>x. (tensor_ell2_left (\<psi> /\<^sub>R (norm \<psi>)\<^sup>2))* *\<^sub>V (\<psi> \<otimes>\<^sub>s \<phi> x)) summable_on A\<close>
      apply (rule summable_on_bounded_linear[unfolded o_def, rotated])
      by (intro bounded_linear_intros)
    with * have \<open>\<phi> summable_on A\<close>
      by (simp add: tensor_ell2_left_adj_apply)
    then show ?thesis
      apply (rule infsum_bounded_linear[symmetric, unfolded o_def, rotated])
      by (intro bounded_linear_intros)
  next
    case \<psi>0
    then show ?thesis
      by simp
  next
    case not_summable
    then show ?thesis 
      by (simp add: infsum_not_exists)
  qed
qed

lemma infsum_tensor_ell2_left: \<open>(\<Sum>\<^sub>\<infinity>x\<in>A. \<phi> x) \<otimes>\<^sub>s \<psi> = (\<Sum>\<^sub>\<infinity>x\<in>A. \<phi> x \<otimes>\<^sub>s \<psi>)\<close>
proof -
  from infsum_tensor_ell2_right
  have \<open>swap_ell2 *\<^sub>V (\<psi> \<otimes>\<^sub>s (\<Sum>\<^sub>\<infinity>x\<in>A. \<phi> x)) = swap_ell2 *\<^sub>V (\<Sum>\<^sub>\<infinity>x\<in>A. \<psi> \<otimes>\<^sub>s \<phi> x)\<close>
    by metis
  then show ?thesis
    by (simp add: flip: infsum_cblinfun_apply_isometry)
qed

lemma infsum_in_closed_csubspaceI:
  assumes \<open>\<And>x. x\<in>X \<Longrightarrow> f x \<in> A\<close>
  assumes \<open>closed_csubspace A\<close>
  shows \<open>infsum f X \<in> A\<close>
proof (cases \<open>f summable_on X\<close>)
  case True
  then have lim: \<open>(sum f \<longlongrightarrow> infsum f X) (finite_subsets_at_top X)\<close>
    by (simp add: infsum_tendsto)
  have sumA: \<open>sum f F \<in> A\<close> if \<open>finite F\<close> and \<open>F \<subseteq> X\<close> for F
    apply (rule complex_vector.subspace_sum)
    using that assms by auto
  from lim show \<open>infsum f X \<in> A\<close>
    apply (rule Lim_in_closed_set[rotated -1])
    using assms sumA by (auto intro!: closed_csubspace.closed eventually_finite_subsets_at_top_weakI)
next
  case False
  then show ?thesis
    using assms by (auto intro!: closed_csubspace.closed complex_vector.subspace_0 simp add: infsum_not_exists)
qed

lemma closed_csubspace_space_as_set[simp]: \<open>closed_csubspace (space_as_set X)\<close>
  using space_as_set by simp

lemma unitary_nonzero[simp]: \<open>\<not> unitary (0 :: 'a::{chilbert_space, not_singleton} \<Rightarrow>\<^sub>C\<^sub>L _)\<close>
  by (simp add: unitary_def)

lemma kernel_member_iff: \<open>x \<in> space_as_set (kernel A) \<longleftrightarrow> A *\<^sub>V x = 0\<close>
  using kernel_memberD kernel_memberI by blast

end
