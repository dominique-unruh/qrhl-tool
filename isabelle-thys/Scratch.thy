theory Scratch
  imports QRHL.QRHL
begin

no_notation m_inv ("inv\<index> _" [81] 80)
unbundle no_vec_syntax
unbundle jnf_notation

derive (eq) ceq bit
derive (compare) ccompare bit
derive (dlist) set_impl bit

ML \<open>open Prog_Variables\<close>

definition explicit_cblinfun :: \<open>('a \<Rightarrow> 'b \<Rightarrow> complex) \<Rightarrow> ('b ell2, 'a ell2) cblinfun\<close> where
  \<open>explicit_cblinfun m = cblinfun_extension (range ket) (\<lambda>a. Abs_ell2 (\<lambda>j. m j (inv ket a)))\<close>

lemma explicit_cblinfun_ket[simp]: \<open>explicit_cblinfun m *\<^sub>V ket a = Abs_ell2 (\<lambda>b. m b a)\<close> for m :: "_ \<Rightarrow> _ :: finite \<Rightarrow> _"
  by (auto simp: cblinfun_extension_exists_finite_dim explicit_cblinfun_def cblinfun_extension_apply)

(* TODO: move to bounded operators *)
lemma Abs_ell2_inverse_finite[simp]: \<open>Rep_ell2 (Abs_ell2 \<psi>) = \<psi>\<close> for \<psi> :: \<open>_::finite \<Rightarrow> complex\<close>
  by (simp add: Abs_ell2_inverse)

lemma explicit_cblinfun_Rep_ket: \<open>Rep_ell2 (explicit_cblinfun m *\<^sub>V ket a) b = m b a\<close> for m :: "_ :: finite \<Rightarrow> _ :: finite \<Rightarrow> _"
  by simp

definition same_outside_cregister :: \<open>('a,'b) cregister \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool\<close> where
  \<open>same_outside_cregister F x y \<longleftrightarrow> x = setter F (getter F x) y\<close>

lemma same_outside_cregister_non_cregister[simp]: \<open>same_outside_cregister non_cregister = (=)\<close>
  unfolding same_outside_cregister_def
  by simp

lemma equivp_same_outside_cregister[simp]: \<open>equivp (same_outside_cregister F)\<close>
proof (cases \<open>cregister F\<close>)
  case False
  then have [simp]: \<open>F = non_cregister\<close>
    using non_cregister by force
  show ?thesis
    using identity_equivp by simp
next
  case True
  have \<open>reflp (same_outside_cregister F)\<close>
    by (simp add: same_outside_cregister_def reflpI)
  moreover have \<open>symp (same_outside_cregister F)\<close>
    by (metis same_outside_cregister_def setter_getter_same setter_setter_same sympI)
  moreover have \<open>transp (same_outside_cregister F)\<close>
    by (smt (verit, del_insts) same_outside_cregister_def setter_setter_same transpI)
  ultimately show ?thesis
    by (rule equivpI)
qed

lift_definition qregister_of_cregister :: \<open>('a,'b) cregister \<Rightarrow> ('a,'b) qregister\<close> is
  \<open>\<lambda>F a. if cregister F then 
      explicit_cblinfun (\<lambda>i j. if same_outside_cregister F i j then Rep_ell2 (a *\<^sub>V ket (getter F j)) (getter F i) else 0)
    else 0\<close>
  sorry

thm qregister_of_cregister.rep_eq[of F]

lemma apply_qregister_of_cregister:
  assumes \<open>cregister F\<close>
  shows \<open>apply_qregister (qregister_of_cregister F) a = explicit_cblinfun
            (\<lambda>i j. if same_outside_cregister F i j then Rep_ell2 (a \<cdot> ket (getter F j)) (getter F i) else 0)\<close>
  unfolding qregister_of_cregister.rep_eq using assms by simp


lemma non_cregister'[simp]: \<open>\<not> cregister non_cregister\<close>
  by (simp add: non_cregister)

lemma qregister_of_cregister_Fst: \<open>qregister_of_cregister cFst = qFst\<close>
  sorry
lemma qregister_of_cregister_Snd: \<open>qregister_of_cregister cSnd = qSnd\<close>
  sorry
lemma qregister_of_cregister_non_register: \<open>qregister_of_cregister non_cregister = non_qregister\<close>
proof -
  define t where \<open>t = non_cregister\<close>
  show \<open>qregister_of_cregister t = non_qregister\<close>
    apply (transfer fixing: t)
    apply (simp add: t_def)
    using non_qregister_raw_def by fastforce
qed
lemma qregister_of_cregister_compatible: \<open>ccompatible x y \<longleftrightarrow> qcompatible (qregister_of_cregister x) (qregister_of_cregister y)\<close>
  sorry
lemma qregister_of_cregister_pair: \<open>qregister_of_cregister (cregister_pair x y) = qregister_pair (qregister_of_cregister x) (qregister_of_cregister y)\<close>
  sorry
lemma qregister_of_cregister_chain: \<open>qregister_of_cregister (cregister_chain x y) = qregister_chain (qregister_of_cregister x) (qregister_of_cregister y)\<close>
  sorry

lemma cregister_chain_is_cregister[simp]: \<open>cregister (cregister_chain F G) \<longleftrightarrow> cregister F \<and> cregister G\<close>
  by (metis Cccompatible_CREGISTER_of Cccompatible_comp_right ccompatible_CCcompatible cregister.rep_eq cregister_chain.rep_eq non_cregister_raw)

(* lemma cregister_chain_is_cregisterXXX[simp]: \<open>cregister F \<Longrightarrow> cregister G \<Longrightarrow> cregister (cregister_chain F G)\<close>
  by (meson Cccompatible_CREGISTER_of Cccompatible_comp_right ccompatible_register1 non_cregister) *)

lemma getter_pair: 
  assumes \<open>cregister F\<close> \<open>cregister G\<close>
  shows \<open>getter (cregister_pair F G) = (\<lambda>m. (getter F m, getter G m))\<close>
  sorry

lemma setter_pair:
  assumes \<open>cregister F\<close> \<open>cregister G\<close>
  shows \<open>setter (cregister_pair F G) = (\<lambda>(x,y). setter F x o setter G y)\<close>
  sorry

lemma getter_chain:
  assumes \<open>cregister F\<close>
  shows \<open>getter (cregister_chain F G) = getter G o getter F\<close>
  sorry

(* lemma setter_chain:
  assumes \<open>cregister F\<close> \<open>cregister G\<close>
  shows \<open>setter (cregister_chain F G) a m = setter F (setter G a (getter F m)) m\<close>
  by (simp add: assms(1) assms(2) setter_chain)
  sorry *)

lemma apply_qregister_Fst: \<open>apply_qregister qFst x = x \<otimes> id_cblinfun\<close>
  sorry

lemma apply_qregister_Snd: \<open>apply_qregister qSnd x = id_cblinfun \<otimes> x\<close>
  sorry



lemma butterfly_tensor: \<open>butterfly (a \<otimes> b) (c \<otimes> d) = butterfly a c \<otimes> butterfly b d\<close>
  sorry

lemma clinear_tensorOp_left[simp]: \<open>clinear (\<lambda>x. x \<otimes> y)\<close> for y :: \<open>(_,_) cblinfun\<close>
  sorry

lemma clinear_tensorOp_right[simp]: \<open>clinear (\<lambda>y. x \<otimes> y)\<close> for x :: \<open>(_,_) cblinfun\<close>
  sorry

lemma bounded_clinear_apply_qregister[simp]: \<open>bounded_clinear (apply_qregister F)\<close>
  apply transfer
  apply (auto simp: non_qregister_raw_def[abs_def])
  sorry

lemma clinear_apply_qregister[simp]: \<open>clinear (apply_qregister F)\<close>
  using bounded_clinear.clinear bounded_clinear_apply_qregister by blast

lemma qregister_conversion_id[simp]: \<open>qregister_conversion F qregister_id = F\<close>
  apply transfer by auto

lemma qregister_chain_pair:
  shows "qregister_pair (qregister_chain F G) (qregister_chain F H) = qregister_chain F (qregister_pair G H)"
  sorry

lemma qregister_chain_pair_Fst[simp]:
  assumes \<open>qregister G\<close>
  shows \<open>qregister_chain (qregister_pair F G) qFst = F\<close>
  sorry

lemma qregister_chain_pair_Fst_chain[simp]:
  assumes \<open>qregister G\<close>
  shows \<open>qregister_chain (qregister_pair F G) (qregister_chain qFst H) = qregister_chain F H\<close>
  by (metis Scratch.qregister_chain_pair_Fst assms qregister_chain_assoc)

lemma qregister_chain_pair_Snd[simp]:
  assumes \<open>qregister F\<close>
  shows \<open>qregister_chain (qregister_pair F G) qSnd = G\<close>
  sorry

lemma qregister_chain_pair_Snd_chain[simp]:
  assumes \<open>qregister F\<close>
  shows \<open>qregister_chain (qregister_pair F G) (qregister_chain qSnd H) = qregister_chain G H\<close>
  by (metis Scratch.qregister_chain_pair_Snd assms qregister_chain_assoc)

(* lift_definition qregister_all :: \<open>('a,'a) qregister\<close> is id
  by simp

lemma qregister_chain_all_left[simp]: \<open>qregister_chain qregister_all F = F\<close>
  apply transfer by auto

lemma qregister_chain_all_right[simp]: \<open>qregister_chain F qregister_all = F\<close>
  apply transfer by auto *)

lemma rew1: \<open>qregister_le F G \<Longrightarrow> apply_qregister F x = apply_qregister G (apply_qregister (qregister_conversion F G) x)\<close>
  apply (subst qregister_chain_conversion[where F=F and G=G, symmetric])
  by auto

lemma lepairI: \<open>qregister_le F H \<Longrightarrow> qregister_le G H \<Longrightarrow> qcompatible F G \<Longrightarrow> qregister_le (qregister_pair F G) H\<close>
  unfolding qregister_le_def
  sorry

lemma lepairI1: \<open>qregister_le F G \<Longrightarrow> qcompatible G H \<Longrightarrow> qregister_le F (qregister_pair G H)\<close>
  sorry
lemma lepairI2: \<open>qregister_le F H \<Longrightarrow> qcompatible G H \<Longrightarrow> qregister_le F (qregister_pair G H)\<close>
  sorry
lemma lerefl: \<open>qregister F \<Longrightarrow> qregister_le F F\<close>
  unfolding qregister_le_def by simp

lemma qregister_conversion_chain: 
  assumes \<open>qregister_le F G\<close> \<open>qregister_le G H\<close>
  shows \<open>qregister_chain (qregister_conversion G H) (qregister_conversion F G) = qregister_conversion F H\<close>
  using assms unfolding qregister_le_def apply (transfer fixing: F G H) apply transfer
  by (auto intro!: ext qregister_conversion_raw_register simp: f_inv_into_f range_subsetD)

lemma [simp]: \<open>register_conversion F non_qregister = non_qregister\<close>
  apply transfer by (auto simp add: non_qregister_raw)

lemma [simp]: \<open>register_conversion non_qregister F = non_qregister\<close>
  apply transfer by (auto simp add: non_qregister_raw)

lemma inv_eq_move: \<open>inv f o g = h\<close> if \<open>inj f\<close> and \<open>g = f o h\<close> for f g
  using that(1) that(2) by fastforce

lemma qregister_conversion_rename: 
  fixes F :: \<open>('a,'c) qregister\<close> and G :: \<open>('b,'c) qregister\<close> and H :: \<open>('d, 'c) qregister\<close> and F' G'
  assumes \<open>qregister H\<close>
  assumes \<open>F = qregister_chain H F'\<close> \<open>G = qregister_chain H G'\<close>
  shows \<open>qregister_conversion F G = qregister_conversion F' G'\<close>
proof (cases \<open>qregister F'\<close>, cases \<open>qregister G'\<close>)
  assume \<open>\<not> qregister G'\<close>
  then have [simp]: \<open>G' = non_qregister\<close>
    using non_qregister by blast
  then show ?thesis
    by (simp add: \<open>G = qregister_chain H G'\<close>)
next
  assume \<open>\<not> qregister F'\<close>
  then have [simp]: \<open>F' = non_qregister\<close>
    using non_qregister by blast
  then show ?thesis
    by (simp add: \<open>F = qregister_chain H F'\<close>)
next
  have range_le_preserve: \<open>range F' \<subseteq> range G'\<close> if \<open>range (\<lambda>x. H (F' x)) \<subseteq> range (\<lambda>x. H (G' x))\<close> and \<open>qregister_raw H\<close> 
    for H :: \<open>'d qupdate \<Rightarrow> 'c qupdate\<close> and F' :: \<open>'a qupdate \<Rightarrow> 'd qupdate\<close> and G' :: \<open>'b qupdate \<Rightarrow> 'd qupdate\<close>
    using qregister_raw_inj[OF \<open>qregister_raw H\<close>] using that(1)
    by (smt (verit, best) image_subset_iff inj_def rangeE rangeI)
  have H_cancel: \<open>inv (H \<circ> G') \<circ> (H \<circ> F') = inv G' \<circ> F'\<close> if \<open>qregister_raw H\<close> and \<open>qregister_raw G'\<close>
    and \<open>range F' \<subseteq> range G'\<close>
    for H :: \<open>'d qupdate \<Rightarrow> 'c qupdate\<close> and F' :: \<open>'a qupdate \<Rightarrow> 'd qupdate\<close> and G' :: \<open>'b qupdate \<Rightarrow> 'd qupdate\<close>
    apply (rule inv_eq_move)
    using qregister_raw_inj[OF \<open>qregister_raw H\<close>] qregister_raw_inj[OF \<open>qregister_raw G'\<close>]
    using inj_compose that by (auto simp add: ext f_inv_into_f subset_iff)
  assume [simp]: \<open>qregister F'\<close> \<open>qregister G'\<close>
  then show ?thesis
    using assms apply transfer
    using range_le_preserve H_cancel by (auto simp: qregister_raw_chain)
qed

lemma qregister_conversion_rename': 
  fixes F :: \<open>('a,'c) qregister\<close> and F' G'
  assumes \<open>qregister G\<close>
  assumes \<open>F = qregister_chain G F'\<close>
  shows \<open>qregister_conversion F G = F'\<close>
  apply (subst qregister_conversion_rename[where H=G and G'=qregister_id and F'=F'])
  using assms by auto

lemma tensor_ext2: 
  assumes \<open>\<And>x y. apply_qregister F (x\<otimes>y) = apply_qregister G (x\<otimes>y)\<close>
  shows \<open>F = G\<close>
  sorry

lemma tensor_ext3: 
  assumes \<open>\<And>x y z. apply_qregister F (x\<otimes>y\<otimes>z) = apply_qregister G (x\<otimes>y\<otimes>z)\<close>
  shows \<open>F = G\<close>
  sorry

lemma qcompatible_Abs_qregister[simp]:
  assumes \<open>qregister_raw F\<close> \<open>qregister_raw G\<close>
  (* assumes \<open>qcommuting_raw F G\<close> *)
  shows \<open>qcompatible (Abs_qregister F) (Abs_qregister G) \<longleftrightarrow> qcommuting_raw F G\<close>
  using assms by (simp add: eq_onp_same_args qcompatible.abs_eq qcompatible_raw_def qcommuting_raw_def)

lemma qcompatible_Abs_qregister_id_tensor_left[simp]:
  shows \<open>qcommuting_raw (\<lambda>x. id_cblinfun \<otimes> f x) (\<lambda>x. g x \<otimes> id_cblinfun)\<close>
  by (auto simp: qcommuting_raw_def)

lemma qcompatible_Abs_qregister_id_tensor_right[simp]:
  shows \<open>qcommuting_raw (\<lambda>x. g x \<otimes> id_cblinfun) (\<lambda>x. id_cblinfun \<otimes> f x)\<close>
  by (auto simp: qcommuting_raw_def)

lemma qcompatible_Abs_qregister_id_tensor_idid_tensor_left[simp]:
  shows \<open>qcommuting_raw (\<lambda>x. id_cblinfun \<otimes> f x) (\<lambda>x. id_cblinfun \<otimes> g x) \<longleftrightarrow> qcommuting_raw f g\<close>
  sorry

lemma qcompatible_Abs_qregister_id_tensor_idid_tensor_right[simp]:
  shows \<open>qcommuting_raw (\<lambda>x. f x \<otimes> id_cblinfun) (\<lambda>x. g x \<otimes> id_cblinfun) \<longleftrightarrow> qcommuting_raw f g\<close>
  sorry

lemma qregister_raw_tensor_left[simp]:
  shows \<open>qregister_raw (\<lambda>x. id_cblinfun \<otimes> F x) \<longleftrightarrow> qregister_raw F\<close>
  sorry

lemma qregister_raw_tensor_right[intro!, simp]:
  shows \<open>qregister_raw (\<lambda>x. F x \<otimes> id_cblinfun) \<longleftrightarrow> qregister_raw F\<close>
  sorry

lemma qregister_raw_id'[simp]: \<open>qregister_raw (\<lambda>x. x)\<close>
  by (metis eq_id_iff qregister_raw_id)



lemma mat_of_cblinfun_explicit_cblinfun[code,simp]:
  fixes m :: \<open>'a::enum \<Rightarrow> 'b::enum \<Rightarrow> complex\<close>
  defines \<open>m' \<equiv> (\<lambda>(i,j). m (Enum.enum!i) (Enum.enum!j))\<close>
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

definition reorder_cblinfun :: \<open>('d \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> ('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2) \<Rightarrow> ('c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2)\<close> where
  \<open>reorder_cblinfun r c A = explicit_cblinfun (\<lambda>i j. Rep_ell2 (A *\<^sub>V ket (c j)) (r i))\<close>

abbreviation "reorder_cblinfun2 f \<equiv> reorder_cblinfun f f"

lemma reorder_cblinfun_ket[simp]: \<open>Rep_ell2 (reorder_cblinfun r c A *\<^sub>V ket a) b = Rep_ell2 (A *\<^sub>V ket (c a)) (r b)\<close> for a b :: \<open>_::finite\<close>
  by (simp add: reorder_cblinfun_def)


lemma clinear_reorder_cblinfun[simp]: \<open>clinear (reorder_cblinfun r c)\<close> for r c :: \<open>_::finite \<Rightarrow> _\<close>
proof (rule clinearI)
  show \<open>reorder_cblinfun r c (A + B) = reorder_cblinfun r c A + reorder_cblinfun r c B\<close> for A B
    apply (rule equal_ket)
    by (auto simp: plus_ell2.rep_eq cblinfun.add_left simp flip: Rep_ell2_inject)
  show \<open>reorder_cblinfun r c (s *\<^sub>C A) = s *\<^sub>C reorder_cblinfun r c A\<close> for s A
    apply (rule equal_ket)
    by (auto simp: scaleC_ell2.rep_eq simp flip: Rep_ell2_inject)
qed

lemma reorder_cblinfun_butterfly: 
  fixes r c :: \<open>_::finite \<Rightarrow> _::finite\<close>
  assumes \<open>bij r\<close> \<open>bij c\<close>
  shows \<open>reorder_cblinfun r c (butterket a b) = butterket (inv r a) (inv c b)\<close>
proof (rule equal_ket, rule Rep_ell2_inject[THEN iffD1], rule ext)
  fix i j
  have \<open>Rep_ell2 (reorder_cblinfun r c (butterket a b) \<cdot> ket i) j = Rep_ell2 ((ket b \<bullet>\<^sub>C ket (c i)) *\<^sub>C ket a) (r j)\<close>
    by auto
  also have \<open>\<dots> = (if b=c i then 1 else 0) * (if a=r j then 1 else 0)\<close>
    by (simp add: scaleC_ell2.rep_eq ket.rep_eq)
  also have \<open>\<dots> = (if inv c b=i then 1 else 0) * (if inv r a=j then 1 else 0)\<close>
    by (smt (verit, del_insts) assms(1) assms(2) bij_inv_eq_iff)
  also have \<open>\<dots> = Rep_ell2 ((ket (inv c b) \<bullet>\<^sub>C ket i) *\<^sub>C ket (inv r a)) j\<close>
    by (simp add: scaleC_ell2.rep_eq ket.rep_eq)
  also have \<open>\<dots> = Rep_ell2 (butterket (inv r a) (inv c b) \<cdot> ket i) j\<close>
    by auto
  finally show \<open>Rep_ell2 (reorder_cblinfun r c (butterket a b) \<cdot> ket i) j = Rep_ell2 (butterket (inv r a) (inv c b) \<cdot> ket i) j\<close>
    by -
qed

lemma reorder_cblinfun2_butterfly: 
  fixes f :: \<open>_::finite \<Rightarrow> _::finite\<close>
  assumes \<open>bij f\<close>
  shows \<open>reorder_cblinfun2 f (butterket a b) = butterket (inv f a) (inv f b)\<close>
  by (simp add: assms reorder_cblinfun_butterfly)

definition reorder_mat :: \<open>nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> complex mat \<Rightarrow> complex mat\<close> where 
  \<open>reorder_mat n m r c A = Matrix.mat n m (\<lambda>(i, j). A $$ (r i, c j))\<close>

(* TODO: to bounded operators *)
declare enum_idx_correct[simp]

lemma mat_of_cblinfun_reorder[code]: 
  fixes r :: \<open>'a::enum \<Rightarrow> 'c::enum\<close> and c :: \<open>'b::enum \<Rightarrow> 'd::enum\<close>
  shows \<open>mat_of_cblinfun (reorder_cblinfun r c A) = reorder_mat CARD('a) CARD('b)
(\<lambda>i. enum_idx (r (enum_class.enum ! i))) (\<lambda>j. enum_idx (c (enum_class.enum ! j))) (mat_of_cblinfun A)\<close>
proof -
  have aux: \<open>Rep_ell2 \<psi> i = vec_of_basis_enum \<psi> $ (enum_idx i)\<close> if \<open>enum_idx i < CARD('z)\<close> 
    for \<psi> :: \<open>'z::enum ell2\<close> and i
    apply (subst vec_of_basis_enum_ell2_component)
    using that by auto

  show ?thesis
    apply (subst reorder_cblinfun_def)
    apply (subst mat_of_cblinfun_explicit_cblinfun)
    apply (subst aux)
     apply (simp add: card_UNIV_length_enum enum_idx_bound)
    apply (subst mat_of_cblinfun_cblinfun_apply)
    apply (subst vec_of_basis_enum_ket)
    apply (subst mat_entry_explicit)
    by (auto simp add: card_UNIV_length_enum enum_idx_bound reorder_mat_def)
qed

lemma enum_idx_correct': \<open>enum_idx (enum_class.enum ! i :: 'a::enum) = i\<close> if \<open>i < CARD('a)\<close>
  sorry

definition \<open>enum_idx_enum_nth_code n (_::'a::enum itself) i = (if i < n then i else 
    Code.abort STR ''enum_idx_enum_nth_code: index out of bounds'' (\<lambda>_. enum_idx (enum_class.enum ! i :: 'a)))\<close>

lemma enum_idx_enum_nth_code: \<open>enum_idx (enum_class.enum ! i :: 'a::enum) = enum_idx_enum_nth_code CARD('a) TYPE('a) i\<close>
  unfolding enum_idx_enum_nth_code_def
  apply (cases \<open>i < CARD('a)\<close>)
   apply (subst enum_idx_correct', simp, simp)
  by auto

lemma enum_idx_pair: \<open>enum_idx (a,b) = enum_idx a * CARD('b) + enum_idx b\<close> for a :: \<open>'a::enum\<close> and b :: \<open>'b::enum\<close>
proof -
  let ?enumab = \<open>Enum.enum :: ('a \<times> 'b) list\<close>
  let ?enuma = \<open>Enum.enum :: 'a list\<close>
  let ?enumb = \<open>Enum.enum :: 'b list\<close>
  have bound: \<open>i < CARD('a) \<Longrightarrow> j < CARD('b) \<Longrightarrow> i * CARD('b) + j < CARD('a) * CARD('b)\<close> for i j
    sorry
  have *: \<open>?enumab ! (i * CARD('b) + j) = (?enuma ! i, ?enumb ! j)\<close> 
    if \<open>i < CARD('a)\<close> \<open>j < CARD('b)\<close> for i j
    unfolding enum_prod_def 
    apply (subst List.product_nth)
    using that bound by (auto simp flip: card_UNIV_length_enum)
  note ** = *[where i=\<open>enum_idx a\<close> and j=\<open>enum_idx b\<close>, simplified, symmetric]
  show ?thesis
    apply (subst **)
    using enum_idx_bound[of a] enum_idx_bound[of b]
    by (auto simp: bound enum_idx_correct' simp flip: card_UNIV_length_enum)
qed

lemma enum_idx_fst: \<open>enum_idx (fst ab) = enum_idx ab div CARD('b)\<close> for ab :: \<open>'a::enum \<times> 'b::enum\<close>
  apply (cases ab, hypsubst_thin)
  apply (subst enum_idx_pair)
  using enum_idx_bound
  by (auto intro!: div_less simp flip: card_UNIV_length_enum)

lemma enum_idx_snd: \<open>enum_idx (snd ab) = enum_idx ab mod CARD('b)\<close> for ab :: \<open>'a::enum \<times> 'b::enum\<close>
  apply (cases ab, hypsubst_thin)
  apply (subst enum_idx_pair)
  using enum_idx_bound
  by (auto intro!: mod_less[symmetric] simp flip: card_UNIV_length_enum)

term qregister_pair

lemma prod_eqI': \<open>x = fst z \<Longrightarrow> y = snd z \<Longrightarrow> (x,y) = z\<close>
  by auto

ML \<open>
local
open Conv
val ctxt = \<^context> (* TODO remove *)
val reg = \<^term>\<open>(qregister_pair \<lbrakk>#1,#3.\<rbrakk> \<lbrakk>#2\<rbrakk>) :: ((bit*bit)*bit, _) qregister\<close>
fun mk_tuple (\<^Const_>\<open>qregister_pair T1 _ T2 for t u\<close>) x = 
      \<^Const>\<open>Pair T1 T2\<close> $ (mk_tuple t x) $ (mk_tuple u x)
  | mk_tuple (\<^Const_>\<open>qFst T1 T2\<close>) x = \<^Const>\<open>fst T1 T2\<close> $ x
  | mk_tuple (\<^Const_>\<open>qSnd T1 T2\<close>) x = \<^Const>\<open>snd T2 T1\<close> $ x
  | mk_tuple (\<^Const_>\<open>qregister_chain _ _ _\<close> $ t $ u) x = 
      mk_tuple u (mk_tuple t x)
  | mk_tuple t x = raise TERM ("mk_fun", [t, x])
fun mk_fun t = let
  val \<^Type>\<open>qregister _ T\<close> = fastype_of t
  val tuple = mk_tuple t (Bound 0)
  in Abs("m", T, tuple) end
val f = mk_fun reg |> Thm.cterm_of ctxt
val domainT = Thm.ctyp_of_cterm f |> Thm.dest_ctyp0
val rangeT = Thm.ctyp_of_cterm f |> Thm.dest_ctyp1
val goal_fog = \<^instantiate>\<open>f and 'a=domainT and 'b=rangeT in cprop (schematic) \<open>(f::'a\<Rightarrow>'b) o g = id\<close>\<close>
val rewr_fst_snd_conv = bottom_rewrs_conv @{thms fst_conv[THEN eq_reflection] snd_conv[THEN eq_reflection]}
val rewr_fst_snd_tac = CONVERSION (rewr_fst_snd_conv ctxt) 1
(* Raw_Simplifier.rewrite_goal_tac ctxt @{thms fst_conv[THEN eq_reflection] snd_conv[THEN eq_reflection]} 1 *)
val resolve_fst_snd_tac = resolve_tac ctxt @{thms prod_eqI' fst_conv snd_conv refl} 1
val ext_tac = resolve_tac ctxt @{thms ext} 1
val rewr_o_id = Raw_Simplifier.rewrite_goal_tac ctxt @{thms o_def[THEN eq_reflection] id_def[THEN eq_reflection]} 1
val tac = ext_tac THEN rewr_o_id THEN REPEAT (rewr_fst_snd_tac THEN resolve_fst_snd_tac)
val thm_fog = Goal.prove_internal ctxt [] goal_fog (K tac)
val thm_fog = thm_fog |> (rewr_fst_snd_conv ctxt |> arg_conv |> arg1_conv |> arg_conv |> fconv_rule)
val g = thm_fog |> Thm.cprop_of |> Thm.dest_arg |> Thm.dest_arg1 |> Thm.dest_arg
val goal_gof = \<^instantiate>\<open>f=f and g=g and 'a=domainT and 'b=rangeT in cprop (schematic) \<open>g o (f::'a\<Rightarrow>'b) = id\<close>\<close>
(* val thm_bij = @{thm o_bij} OF [thm_gof, thm_fog] *)
in
val thm_fog = thm_fog
val thm_gof = Goal.prove_internal ctxt [] goal_gof (K (ext_tac THEN simp_tac ctxt 1))
end
\<close>

ML \<open>
structure MLThmAttribData = Proof_Data (
  type T = Proof.context -> thm -> thm
  fun init _ _ thm = raise THM ("uninitialized MLThmAttribData", 0, [thm])
)
\<close>

ML MLThmAttribData.put
ML "Context.>>"

text \<open>Invoked as \<open>thm[ML_thm \<open>mlcode\<close>]\<close> or \<open>[[ML_thm \<open>mlcode\<close>]]\<close> where \<open>mlcode\<close> is of type \<open>Proof.context -> thm -> thm\<close>,
  it runs \<open>mlcode\<close> on the theorem \<open>thm\<close> (or on a dummy fact) and returns the resulting theorem.
  Optionally, after \<open>mlcode\<close>, we can give \<open>(is \<open>pattern\<close>)\<close> to bind schematic variables by pattern 
  matching the theorem.
\<close>
attribute_setup ML_thm = 
  \<open>Args.context -- Scan.lift Args.text_input 
      -- Scan.lift (Scan.optional (Parse.$$$ "(" |-- Parse.!!! (Scan.repeat1 (Parse.$$$ "is" |-- Parse.prop) --| Parse.$$$ ")")) []) 
      >> (fn ((ctxt,source),is_props) =>
  let
    val function = 
        ctxt |> Context.Proof
        |> ML_Context.expression (Input.pos_of source)
              (ML_Lex.read "Context.>> (Context.map_proof (MLThmAttribData.put ((" @
                 ML_Lex.read_source source @ ML_Lex.read ") : Proof.context -> thm -> thm)))")
        |> Context.the_proof
        |> MLThmAttribData.get
    val is_props = is_props |> map (Syntax.read_prop (Proof_Context.set_mode Proof_Context.mode_pattern ctxt))
    val attrib = Thm.mixed_attribute (fn (context,thm) => let
        val thm' = function (Context.proof_of context) thm
        val context = if null is_props then context else let
val _ = \<^print> (thm', is_props)
                        val binds = Proof_Context.simult_matches ctxt (Thm.prop_of thm', is_props)
                      in Context.map_proof (fold Proof_Context.bind_term binds) context end
        in (context,thm') end)
  in
    attrib
  end
  )\<close> 
  "Apply ML function to the given fact"


lemma [code]: \<open>vec_of_ell2 (Abs_ell2 f) = vec CARD('a) (\<lambda>n. f (Enum.enum ! n))\<close> for f :: \<open>'a::enum \<Rightarrow> complex\<close>
  by (auto simp: vec_of_ell2_def vec_eq_iff vec_of_basis_enum_ell2_component)

lemma [code]: \<open>Rep_ell2 \<psi> i = vec_of_ell2 \<psi> $ (enum_idx i)\<close> for i :: \<open>'a::enum\<close>
  by (auto simp: vec_of_ell2_def vec_eq_iff vec_of_basis_enum_ell2_component card_UNIV_length_enum enum_idx_bound)

experiment fixes a :: \<open>bool qvariable\<close> and b :: \<open>bit qvariable\<close> and c :: \<open>3 qvariable\<close>
  assumes xxx[variable]: \<open>qregister \<lbrakk>a,b,c\<rbrakk>\<close> begin

lemma qregister_chain_empty_right[simp]: \<open>qregister_chain F empty_qregister = empty_qregister\<close>
  sorry
lemma qregister_chain_empty_left[simp]: \<open>qregister_chain empty_qregister F = empty_qregister\<close>
  sorry

lemma qregister_chain_unit_right[simp]: \<open>qregister_chain F qvariable_unit = qvariable_unit\<close>
  by (simp add: qvariable_unit_def)
lemma qregister_chain_unit_left[simp]: \<open>qregister_chain qvariable_unit F = qvariable_unit\<close>
  by (simp add: qvariable_unit_def)

ML \<open>
fun is_empty_qregisterT ctxt (\<^Type>\<open>qregister T _\<close>) = Sign.of_sort (Proof_Context.theory_of ctxt) (T,\<^sort>\<open>CARD_1\<close>)
  | is_empty_qregisterT _ T = raise TYPE("is_empty_qregisterT: not a qregister type", [T], [])
fun is_empty_qregister ctxt t = is_empty_qregisterT ctxt (fastype_of t)
  handle TYPE(_, Ts, _) => raise TYPE("is_empty_qregister: not a qregister type", Ts, [t])
;;
is_empty_qregister \<^context> \<^term>\<open>bla :: 1 qvariable\<close>
\<close>

(* declare [[ML_source_trace]] *)
ML \<open>
fun mk_ct_equals ct1 ct2 = let
  val eq = \<^instantiate>\<open>'a=\<open>Thm.ctyp_of_cterm ct1\<close> in cterm Pure.eq\<close>
  in
    Thm.apply (Thm.apply eq ct1) ct2
  end
;;
mk_ct_equals \<^cterm>\<open>1::nat\<close> \<^cterm>\<open>2::nat\<close>
\<close>



(* declare [[ML_source_trace]] *)
ML \<open>
local
val ctxt = \<^context>
val ct = \<^cterm>\<open>\<lbrakk>a,c \<mapsto> a,b,c,\<lbrakk>\<rbrakk>\<rbrakk>\<close>
val (lhs,rhs) = case Thm.term_of ct of Const(\<^const_name>\<open>qregister_conversion\<close>,_) $ lhs $ rhs => (lhs,rhs)
                                     | _ => raise CTERM ("qregister_conversion_to_register_conv: not a register conversion", [ct])
fun add_to_path prefix path = if Term.is_dummy_pattern path then prefix else
  let val (prefix_inT, _) = Prog_Variables.dest_qregisterT (fastype_of prefix)
      val (path_inT, path_outT) = Prog_Variables.dest_qregisterT (fastype_of path)
  in \<^Const>\<open>qregister_chain path_inT path_outT prefix_inT\<close> $ path $ prefix end
fun get_rhs_registers (\<^Const_>\<open>qregister_pair T1 _ T2\<close> $ r1 $ r2) path found = 
    found |> get_rhs_registers r1 (add_to_path \<^Const>\<open>qFst T1 T2\<close> path)
          |> get_rhs_registers r2 (add_to_path \<^Const>\<open>qSnd T2 T1\<close> path)
 | get_rhs_registers reg path found = 
    if is_empty_qregister ctxt reg then found
    else (reg,path) :: found
val rhs_registers = get_rhs_registers rhs Term.dummy []
fun map_lhs (Const(\<^const_name>\<open>qregister_pair\<close>,_) $ r1 $ r2) : term = let
  val r1' = map_lhs r1
  val r2' = map_lhs r2
  val (r1'in, r1'out) = dest_qregisterT (fastype_of r1')
  val (r2'in, _) = dest_qregisterT (fastype_of r2')
  in
    \<^Const>\<open>qregister_pair r1'in r1'out r2'in for r1' r2'\<close>
  end
  | map_lhs r = 
    (case AList.lookup (op aconv) rhs_registers r of
      NONE => raise TERM ("qregister_conversion_to_register_conv: could not find register from lhs in rhs", [r,Thm.term_of ct])
    | SOME path => path)
val new_reg = map_lhs lhs |> Thm.cterm_of ctxt
(* TODO simplify new_reg (at least with associativity) *)
in
(* val xxx = rhs_registers |> map (apply2 (Thm.cterm_of ctxt)) *)
val goal = mk_ct_equals ct new_reg
end
\<close>

lemma qcompatible_empty_left[simp]: \<open>qcompatible (U::(_::CARD_1,_) qregister) F = qregister U \<and> qregister F\<close>
  sorry
lemma qcompatible_empty_right[simp]: \<open>qcompatible F (U::(_::CARD_1,_) qregister) = qregister U \<and> qregister F\<close>
  sorry


(* Experiment for previous ML code, remove *)
lemma \<open>register_conversion (variable_concat a c)
     (variable_concat a (variable_concat b (variable_concat c variable_unit))) \<equiv>
    variable_concat Fst (register_chain (register_chain Snd Snd) Fst)\<close>
  apply (rule qregister_conversion_rename'[THEN eq_reflection])
   apply simp
  by (simp flip: qregister_chain_pair qregister_chain_assoc)
  

lemma Test
proof -
  fix a b c

  have t[variable]: \<open>qregister (\<lbrakk>a,b,c\<rbrakk> :: (bit*bit*bit) qvariable)\<close> sorry

  have le: \<open>\<lbrakk>a,c \<le> a,b,c\<rbrakk>\<close>
    by (auto intro!: lepairI lerefl simp: lepairI1 lepairI2 lepairI lerefl)

  define CNOT' where \<open>CNOT' = apply_qregister \<lbrakk>a,c \<mapsto> a,b,c\<rbrakk> CNOT\<close>

  have \<open>apply_qregister \<lbrakk>a,c\<rbrakk> CNOT = apply_qregister \<lbrakk>a,b,c\<rbrakk> CNOT'\<close>
    apply (subst rew1[where G=\<open>\<lbrakk>a,b,c\<rbrakk>\<close>])
     apply (fact le)
    by (simp add: CNOT'_def)

(* TODO: simproc *)
  have rename: \<open>\<lbrakk>a,c \<mapsto> a,b,c\<rbrakk> = \<lbrakk>#1,#3.\<rbrakk>\<close>
    apply (rule qregister_conversion_rename')
     apply simp
    by (simp flip: qregister_chain_pair)

(* TODO: simproc *)
  have renameu: \<open>\<lbrakk>a,c,\<lbrakk>\<rbrakk> \<mapsto> a,b,c\<rbrakk> = \<lbrakk>#1,#3.,\<lbrakk>\<rbrakk>\<rbrakk>\<close>
    apply (rule qregister_conversion_rename')
     apply simp
    by (simp flip: qregister_chain_pair)


  have CNOT'_13: \<open>CNOT' = apply_qregister \<lbrakk>#1,#3.\<rbrakk> CNOT\<close>
    unfolding CNOT'_def rename by simp


  have \<open>apply_qregister \<lbrakk>#1,#3.\<rbrakk> CNOT *\<^sub>V ket (1,1,1) = (ket (1,1,0) :: (bit*bit*bit) ell2)\<close>
    using if_weak_cong[cong del] apply fail?
    apply (simp 

        add:  apply_qregister_of_cregister getter_pair getter_chain setter_chain setter_pair setter_Fst
    case_prod_beta setter_Snd

same_outside_cregister_def
prod_eq_iff

        flip: qregister_of_cregister_Fst qregister_of_cregister_Snd
        qregister_of_cregister_pair qregister_of_cregister_chain

    )
    by normalization

  have \<open>apply_qregister (qregister_pair \<lbrakk>#1,#3.\<rbrakk> \<lbrakk>#2\<rbrakk>) (CNOT \<otimes> id_cblinfun) *\<^sub>V ket (1,1,1) = (ket (1,1,0) :: (bit*bit*bit) ell2)\<close>
    using if_weak_cong[cong del] apply fail?
    apply (simp 

        add:  apply_qregister_of_cregister getter_pair getter_chain setter_chain setter_pair setter_Fst
        case_prod_beta setter_Snd

        same_outside_cregister_def
        prod_eq_iff

        flip: qregister_of_cregister_Fst qregister_of_cregister_Snd
        qregister_of_cregister_pair qregister_of_cregister_chain

    )
    by normalization


  note [[show_types]]
  note fog = [[ML_thm \<open>thm_fog |> K |> K\<close> (is \<open>?f o ?g = id\<close>)]]
  note gof = [[ML_thm \<open>thm_gof |> K |> K\<close>]]

  (* define f g where \<open>f = (\<lambda>(a::bit,b::bit,c::bit). ((a,c),b))\<close> and \<open>g = (\<lambda>((a::bit,c::bit),b::bit). (a,b,c))\<close> *)
  (* Those are copy&pasted from fog. Can be automated *)
  (* let ?f = \<open>(\<lambda>m::bit \<times> bit \<times> bit. ((fst m, snd (snd m)), fst (snd m)))\<close> *)
  (* let ?g = \<open>(\<lambda>x::(bit \<times> bit) \<times> bit. (fst (fst x), snd x, snd (fst x)))\<close> *)

(*   have \<open>f o g = id\<close> \<open>g o f = id\<close>
    unfolding f_def g_def by auto *)
  have [simp]: \<open>bij ?f\<close>
    using gof fog by (rule o_bij)
  have [simp]: \<open>inv ?f = ?g\<close>
    using fog gof inv_unique_comp by blast

  have \<open>apply_qregister \<lbrakk>#1,#3.\<rbrakk> CNOT = apply_qregister (qregister_pair \<lbrakk>#1,#3.\<rbrakk> \<lbrakk>#2\<rbrakk>) (CNOT \<otimes> id_cblinfun)\<close>
    apply (subst apply_qregister_pair)
    by auto

  also have \<open>\<dots> = reorder_cblinfun2 ?f (CNOT \<otimes> id_cblinfun)\<close> 
    apply (rule fun_cong[where x=\<open>CNOT \<otimes> id_cblinfun\<close>])
    apply (rule clinear_eq_butterfly_ketI)
      apply simp
     apply simp
    apply (auto simp: ket_product butterfly_tensor apply_qregister_pair apply_qregister_Fst apply_qregister_Snd)
    apply (auto simp flip: ket_product butterfly_tensor)
    apply (subst reorder_cblinfun2_butterfly)
    by auto

  finally have CNOT'_reorder: \<open>CNOT' = reorder_cblinfun2 ?f (CNOT \<otimes> id_cblinfun)\<close>
    using CNOT'_13 by fastforce

(*   have 1: \<open>enum_idx (f i) = xxx\<close> for i
    unfolding f_def
    apply (cases i, hypsubst_thin)
    apply (auto simp: enum_idx_pair)

 *)

  have *: \<open>enum_idx (?f (enum_class.enum ! i)) = 4 * (enum_idx_enum_nth_code 8 TYPE(bit \<times> bit \<times> bit) i div 4) +
    enum_idx_enum_nth_code 8 TYPE(bit \<times> bit \<times> bit) i mod 4 mod 2 * 2 +
    enum_idx_enum_nth_code 8 TYPE(bit \<times> bit \<times> bit) i mod 4 div 2\<close> for i
    apply (subst surjective_pairing)
    apply (subst surjective_pairing)
    apply (auto simp: case_prod_beta)
    apply (subst enum_idx_pair)+
    apply (subst enum_idx_fst enum_idx_snd)+
    apply (auto simp: case_prod_beta enum_idx_enum_nth_code)
    by -

  value \<open>mat_of_cblinfun CNOT'\<close>

  have mat_of_cblinfun_CNOT': \<open>mat_of_cblinfun CNOT' = undefined\<close>
    unfolding CNOT'_reorder mat_of_cblinfun_reorder
    apply (simp add: *)
    apply normalization

  oops
