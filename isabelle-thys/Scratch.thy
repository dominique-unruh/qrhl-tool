theory Scratch
  imports QRHL
 (* "HOL-ex.Sketch_and_Explore" *) 
(* "HOL-Eisbach.Eisbach" *)
(* QRHL_Operations  *)
begin

no_notation eq_closure_of ("closure'_of\<index>")

ML "open Prog_Variables"

abbreviation \<open>upfst x \<equiv> apfst (\<lambda>_. x)\<close>
abbreviation \<open>upsnd x \<equiv> apsnd (\<lambda>_. x)\<close>

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

definition \<open>valid_qregister_range_aux f a \<longleftrightarrow> 
    (\<forall>x y. snd (f x) \<noteq> snd (f y) \<longrightarrow> ket x \<bullet>\<^sub>C (a *\<^sub>V ket y) = 0)
      \<and> (\<forall>x y x' y'. fst (f x) = fst (f x') \<longrightarrow> fst (f y) = fst (f y') \<longrightarrow> 
                     snd (f x) = snd (f y) \<longrightarrow> snd (f x') = snd (f y') \<longrightarrow>
                         ket x \<bullet>\<^sub>C (a *\<^sub>V ket y) = ket x' \<bullet>\<^sub>C (a *\<^sub>V ket y'))\<close>
definition valid_qregister_range_new :: \<open>'a qupdate set \<Rightarrow> bool\<close> where
  \<open>valid_qregister_range_new \<FF> \<longleftrightarrow> (\<exists>(f :: 'a \<Rightarrow> 'a\<times>'a) U L R. unitary U \<and> 
    inj f \<and> range f = L \<times> R \<and>
    \<FF> = {sandwich U a | a. valid_qregister_range_aux f a})\<close>

lemma valid_qregister_range_aux_sandwich:
  assumes \<open>\<And>x. U *\<^sub>V ket x = ket (f x)\<close>
  assumes \<open>unitary U\<close>
  assumes \<open>bij f\<close>
  shows \<open>valid_qregister_range_aux id (sandwich U a) \<longleftrightarrow> valid_qregister_range_aux f a\<close>
proof -
  have [simp]: \<open>U* *\<^sub>V ket x = ket (inv f x)\<close> for x
    by (metis (mono_tags, lifting) \<open>bij f\<close> assms(1) assms(2) bij_betw_imp_surj_on cinner_adj_right cinner_ket_eqI isometry_cinner_both_sides surj_f_inv_f unitary_isometry)

  have \<open>bij (inv f)\<close>
    by (simp add: \<open>bij f\<close> bij_imp_bij_inv)

  show ?thesis
    using assms
    apply (auto simp: sandwich_apply valid_qregister_range_aux_def bij_betw_imp_surj_on surj_f_inv_f
        simp flip: cinner_adj_left)
     apply (metis \<open>bij f\<close>  bij_betw_imp_inj_on invI surjective_pairing)
    by (smt (verit) \<open>bij f\<close>  bij_betw_imp_inj_on inv_f_f surjective_pairing)
qed

lemma Collect_valid_qregister_range_aux_id:
  \<open>{a. valid_qregister_range_aux id a} = range (\<lambda>\<theta>. \<theta> \<otimes>\<^sub>o id_cblinfun)\<close>
proof (intro Set.set_eqI iffI)
  fix a :: \<open>('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'c) ell2\<close>
  assume \<open>a \<in> range (\<lambda>\<theta>. \<theta> \<otimes>\<^sub>o id_cblinfun)\<close>
  then show \<open>a \<in> {a. valid_qregister_range_aux id a}\<close>
    by (auto simp: tensor_op_ell2 tensor_ell2_inner_prod valid_qregister_range_aux_def
        simp flip: tensor_ell2_ket)
next
  fix a
  assume asm: \<open>a \<in> {a. valid_qregister_range_aux id a}\<close>
  define \<theta> where \<open>\<theta> = tensor_ell2_right (ket undefined)* o\<^sub>C\<^sub>L a o\<^sub>C\<^sub>L tensor_ell2_right (ket undefined)\<close>
  have \<open>a = \<theta> \<otimes>\<^sub>o id_cblinfun\<close>
    using asm
    by (auto intro!: equal_ket cinner_ket_eqI 
        simp: tensor_op_ell2 tensor_ell2_inner_prod cinner_ket
        \<theta>_def cinner_adj_right valid_qregister_range_aux_def
        simp flip: tensor_ell2_ket)
  then show \<open>a \<in> range (\<lambda>\<theta>. \<theta> \<otimes>\<^sub>o id_cblinfun)\<close>
    by auto
qed

lemma qregister_has_valid_qregister_range:
  fixes F :: \<open>('a,'b) qregister\<close>
  assumes \<open>qregister F\<close>
  shows \<open>valid_qregister_range_new (range (apply_qregister F))\<close>
proof -
  define \<FF> where \<open>\<FF> = range (apply_qregister F)\<close>
  have \<open>qregister_raw (apply_qregister F)\<close>
    using assms by auto
  from register_decomposition[OF this]
  have \<open>\<forall>\<^sub>\<tau> 'c::type = qregister_decomposition_basis F.
        valid_qregister_range_new \<FF>\<close>
  proof (rule with_type_mp)
    assume \<open>\<exists>V :: ('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2. unitary V \<and> (\<forall>\<theta>. apply_qregister F \<theta> = sandwich V *\<^sub>V (\<theta> \<otimes>\<^sub>o id_cblinfun))\<close>
    then obtain V :: \<open>('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close> where [simp]: \<open>unitary V\<close> and F_decomp: \<open>apply_qregister F \<theta> = sandwich V *\<^sub>V (\<theta> \<otimes>\<^sub>o id_cblinfun)\<close> for \<theta>
      by auto

    obtain g :: \<open>'a \<times> 'c \<Rightarrow> 'b\<close> where [simp]: \<open>bij g\<close>
    proof (atomize_elim, rule exI)
      note bij_betw_trans[trans]
      have \<open>bij_betw ket UNIV (range ket)\<close>
        by (simp add: bij_betw_def)
      also have \<open>bij_betw V (range ket) (V ` range ket)\<close>
        by (auto intro!: inj_on_imp_bij_betw unitary_inj)
      also have \<open>bij_betw (bij_between_bases (V ` range ket) (range ket)) (V ` range ket) (range ket)\<close>
        by (auto intro!: bij_between_bases_bij unitary_image_onb)
      also have \<open>bij_betw (inv ket) (range ket) UNIV\<close>
        by (simp add: inj_imp_bij_betw_inv)
      finally show \<open>bij (inv ket o bij_between_bases (V ` range ket) (range ket) o V o ket)\<close>
        by (simp add: comp_assoc)
    qed
    have [simp]: \<open>range (inv g) = UNIV\<close>
      by (simp add: bij_betw_inv_into bij_is_surj)

    define G where \<open>G = classical_operator (Some o g)\<close>

    obtain ia :: \<open>'a \<Rightarrow> 'b\<close> where \<open>inj ia\<close>
      apply (atomize_elim, rule exI[where x=\<open>\<lambda>a. g (a,undefined)\<close>])
      by (smt (verit) Pair_inject UNIV_I \<open>bij g\<close> bij_betw_iff_bijections injI)
    obtain ic :: \<open>'c \<Rightarrow> 'b\<close> where \<open>inj ic\<close>
      apply (atomize_elim, rule exI[where x=\<open>\<lambda>c. g (undefined,c)\<close>])
      by (smt (verit) UNIV_I \<open>bij g\<close> bij_betw_iff_bijections injI prod.simps(1))
      
    define L R where \<open>L = range ia\<close> and \<open>R = range ic\<close>

    define f :: \<open>'b \<Rightarrow> 'b \<times> 'b\<close> where \<open>f = map_prod ia ic o inv g\<close>

    have [simp]: \<open>fst (f x) = fst (f y) \<longleftrightarrow> fst (inv g x) = fst (inv g y)\<close> for x y
      using \<open>inj ia\<close> f_def injD by fastforce
    have [simp]: \<open>snd (f x) = snd (f y) \<longleftrightarrow> snd (inv g x) = snd (inv g y)\<close> for x y
      using \<open>inj ic\<close> f_def injD by fastforce

    define U :: \<open>'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
      where \<open>U = V o\<^sub>C\<^sub>L G*\<close>

    have [simp]: \<open>unitary G\<close>
      by (simp add: G_def)
    have \<open>G (ket x) = ket (g x)\<close> for x
      by (simp add: G_def bij_is_inj classical_operator_ket classical_operator_exists_inj)
    then have Gadj_ket: \<open>G* *\<^sub>V (ket x) = ket (inv g x)\<close> for x
      apply (subst unitary_adj_inv)
      by (simp_all add: bij_is_surj inv_f_eq surj_f_inv_f unitary_inj)
    have bij_sandwich_G: \<open>bij (sandwich G)\<close>
      by (auto intro!: o_bij[where g=\<open>sandwich (G*)\<close>] simp: sandwich_compose simp flip: cblinfun_compose.rep_eq)
    have inv_sandwich_G: \<open>inv (sandwich G) = sandwich (G*)\<close>
      by (auto intro!: inv_unique_comp simp: sandwich_compose simp flip: cblinfun_compose.rep_eq)

    have \<open>\<FF> = sandwich V ` range (\<lambda>\<theta>. \<theta> \<otimes>\<^sub>o id_cblinfun)\<close>
      by (simp add: \<FF>_def F_decomp image_image)
    also have \<open>\<dots> = sandwich V ` {a. valid_qregister_range_aux id a}\<close>
      by (simp add: Collect_valid_qregister_range_aux_id)
    also have \<open>\<dots> = sandwich U ` sandwich G ` {a. valid_qregister_range_aux id a}\<close>
      by (simp add: U_def image_image sandwich_compose cblinfun_assoc_right unitaryD1
          flip: cblinfun_apply_cblinfun_compose)
    also have \<open>\<dots> = sandwich U ` {a. valid_qregister_range_aux id (sandwich (G*) a)}\<close>
      by (simp add: bij_image_Collect_eq bij_sandwich_G inv_sandwich_G)
    also have \<open>\<dots> = sandwich U ` {a. valid_qregister_range_aux (inv g) a}\<close>
      by (simp add: valid_qregister_range_aux_sandwich Gadj_ket bij_imp_bij_inv)
    also have \<open>\<dots> = sandwich U ` {a. valid_qregister_range_aux f a}\<close>
      by (simp add: valid_qregister_range_aux_def)
    also have \<open>\<dots> = {sandwich U a | a. valid_qregister_range_aux f a}\<close>
      by auto
    finally have \<FF>_eq: \<open>\<FF> = {sandwich U a | a. valid_qregister_range_aux f a}\<close>
      by -
    moreover have inj_f: \<open>inj f\<close>
      by (auto intro!: inj_compose prod.inj_map
          simp add: bij_betw_inv_into bij_is_inj f_def \<open>inj ia\<close> \<open>inj ic\<close>)
    moreover have range_f: \<open>range f = L \<times> R\<close>
      by (auto simp add: f_def L_def R_def simp flip: image_image)
    moreover have unitary_U: \<open>unitary U\<close>
      by (auto intro!: unitary_cblinfun_compose
          simp add: U_def)
    show \<open>valid_qregister_range_new \<FF>\<close>
      unfolding valid_qregister_range_new_def
      apply (rule exI[of _ f], rule exI[of _ U], rule exI[of _ L], rule exI[of _ R])
      by (simp only: unitary_U inj_f range_f \<FF>_eq)
  qed
  from this[cancel_with_type]
  show \<open>valid_qregister_range_new \<FF>\<close>
    by -
qed

definition \<open>valid_qregister_range_content \<FF> = (SOME L::'a set.
    \<exists>(f :: 'a \<Rightarrow> 'a\<times>'a) U R. unitary U \<and> 
        inj f \<and> range f = L \<times> R \<and>
        \<FF> = {sandwich U a | a. valid_qregister_range_aux f a})\<close>
  for \<FF> :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2) set\<close>

lemma bij_betw_map_prod:
  assumes \<open>bij_betw f A B\<close>
  assumes \<open>bij_betw g C D\<close>
  shows \<open>bij_betw (map_prod f g) (A \<times> C) (B \<times> D)\<close>
  apply (rule bij_betw_byWitness[where f'=\<open>map_prod (inv_into A f) (inv_into C g)\<close>])
  using assms by (auto simp: bij_betw_def)

lemma valid_qregister_range_ex_register:
  fixes \<FF> :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2) set\<close>
  assumes \<open>valid_qregister_range_new \<FF>\<close>
  shows \<open>\<forall>\<^sub>\<tau> 'l::type = valid_qregister_range_content \<FF>.
         \<exists>F :: ('l, 'a) qregister. range (apply_qregister F) = \<FF>\<close>
proof (rule with_typeI)
  define L where \<open>L = valid_qregister_range_content \<FF>\<close>
  have \<open>\<exists>(f :: 'a \<Rightarrow> 'a\<times>'a) U R. unitary U \<and> 
        inj f \<and> range f = L \<times> R \<and>
        \<FF> = {sandwich U a | a. valid_qregister_range_aux f a}\<close>
    unfolding L_def valid_qregister_range_content_def apply (rule someI_ex)
    using assms unfolding valid_qregister_range_new_def 
    by blast
  then obtain f :: \<open>'a \<Rightarrow> 'a\<times>'a\<close> and U R where \<open>unitary U\<close> and \<open>inj f\<close> and range_f: \<open>range f = L \<times> R\<close>
    and \<FF>_eq: \<open>\<FF> = {sandwich U a | a. valid_qregister_range_aux f a}\<close>
    by auto
  from range_f have \<open>L \<noteq> {}\<close> and \<open>R \<noteq> {}\<close>
    by auto
  then show \<open>fst (L, ()) \<noteq> {}\<close>
    by simp
  show \<open>fst with_type_type_class (fst (L, ())) (snd (L, ()))\<close>
    by (simp add: with_type_type_class_def)
  show \<open>with_type_compat_rel (fst with_type_type_class) (fst (L, ()))
     (snd with_type_type_class)\<close>
    by (simp add: with_type_compat_rel_type)
  fix RepL :: \<open>'l \<Rightarrow> 'a\<close> and AbsL
  assume \<open>type_definition RepL AbsL (fst (L, ()))\<close>
  then interpret L: type_definition RepL AbsL L
    by simp
  have \<open>\<forall>\<^sub>\<tau> 'r::type = R. \<exists>F :: ('l, 'a) qregister. range (apply_qregister F) = \<FF>\<close>
  proof (rule with_typeI)
    from \<open>R \<noteq> {}\<close> show \<open>fst (R, ()) \<noteq> {}\<close>
      by simp
    show \<open>fst with_type_type_class (fst (R, ())) (snd (R, ()))\<close>
      by (simp add: with_type_type_class_def)
    show \<open>with_type_compat_rel (fst with_type_type_class) (fst (R, ())) (snd with_type_type_class)\<close>
      by (simp add: with_type_compat_rel_type)
    fix RepR :: \<open>'r \<Rightarrow> 'a\<close> and AbsR
    assume \<open>type_definition RepR AbsR (fst (R, ()))\<close>
    then interpret R: type_definition RepR AbsR R
      by simp
    define f' where \<open>f' = map_prod AbsL AbsR o f\<close>
    have \<open>bij f'\<close>
    proof -
      note bij_betw_trans[trans]
      have \<open>bij_betw f UNIV (L \<times> R)\<close>
        by (simp add: \<open>inj f\<close> bij_betw_def range_f)
      also have \<open>bij_betw (map_prod AbsL AbsR) (L \<times> R) (UNIV \<times> UNIV)\<close>
        apply (rule bij_betw_map_prod)
         apply (metis bij_betw_def inj_on_def L.Abs_image L.Abs_inject)
        by (metis bij_betw_def inj_on_def R.Abs_image R.Abs_inject)
      finally show ?thesis
        by (simp add: f'_def)
    qed
    define V where \<open>V = classical_operator (Some o f')\<close>
    have [simp]: \<open>unitary V\<close>
      by (simp add: V_def unitary_classical_operator \<open>bij f'\<close>)
    have V_ket: \<open>V *\<^sub>V ket x = ket (f' x)\<close> for x
      by (simp add: V_def classical_operator_ket classical_operator_exists_inj inj_map_total bij_is_inj \<open>bij f'\<close>)
    then have Vadj_ket: \<open>V* *\<^sub>V ket x = ket (inv f' x)\<close> for x
      apply (subst unitary_adj_inv)
      by (simp_all add: \<open>bij f'\<close> bij_is_surj inv_f_eq surj_f_inv_f unitary_inj)
    have bij_sandwich_Vadj: \<open>bij (sandwich (V*))\<close>
      by (auto intro!: o_bij[where g=\<open>sandwich V\<close>] simp: sandwich_compose simp flip: cblinfun_compose.rep_eq)
    have inv_sandwich_Vadj: \<open>inv (sandwich (V*)) = sandwich V\<close>
      by (auto intro!: inv_unique_comp simp: sandwich_compose simp flip: cblinfun_compose.rep_eq)

    define F where \<open>F = qregister_chain (transform_qregister (U o\<^sub>C\<^sub>L V*)) qFst\<close>
    have \<open>qregister F\<close>
      by (auto intro!: qregister_transform_qregister unitary_cblinfun_compose
          simp: F_def \<open>unitary U\<close>)
    have \<open>range (apply_qregister F) = \<FF>\<close>
    proof -
      have aux1: \<open>fst (f' x) = fst (f' y) \<longleftrightarrow> fst (f x) = fst (f y)\<close> for x y
        by (metis L.Abs_inverse comp_apply eq_fst_iff f'_def fst_map_prod mem_Sigma_iff rangeI range_f)
      have aux2: \<open>snd (f' x) = snd (f' y) \<longleftrightarrow> snd (f x) = snd (f y)\<close> for x y
        by (metis R.type_definition_axioms SigmaD2 comp_eq_dest_lhs f'_def rangeI range_f snd_map_prod surjective_pairing type_definition.Abs_inject)

      have \<open>range (apply_qregister F) = sandwich U ` sandwich (V*) ` range (\<lambda>x. x \<otimes>\<^sub>o id_cblinfun)\<close>
        by (auto simp add: F_def apply_qregister_fst apply_qregister_transform_qregister \<open>unitary U\<close>
            simp flip: sandwich_compose)
      also have \<open>\<dots> = sandwich U ` sandwich (V*) ` {a. valid_qregister_range_aux id a}\<close>
        by (simp add: Collect_valid_qregister_range_aux_id)
      also have \<open>\<dots> = sandwich U ` {a. valid_qregister_range_aux id (sandwich V a)}\<close>
        by (simp add: bij_image_Collect_eq bij_sandwich_Vadj inv_sandwich_Vadj)
      also have \<open>\<dots> = sandwich U ` {a. valid_qregister_range_aux f' a}\<close>
        apply (subst valid_qregister_range_aux_sandwich)
        by (simp_all add: V_ket \<open>unitary V\<close> \<open>bij f'\<close>)
      also have \<open>\<dots> = sandwich U ` {a. valid_qregister_range_aux f a}\<close>
        apply (rule arg_cong[where f=\<open>\<lambda>a. sandwich U ` Collect a\<close>], rule ext)
        by (simp add: valid_qregister_range_aux_def aux1 aux2)
      also have \<open>\<dots> = {sandwich U a | a. valid_qregister_range_aux f a}\<close>
        by blast
      finally show ?thesis
        by (simp add: \<FF>_eq)
    qed
    then show \<open>\<exists>F :: ('l, 'a) qregister. range (apply_qregister F) = \<FF>\<close>
      by auto
  qed
  from this[cancel_with_type]
  show \<open>\<exists>F :: ('l, 'a) qregister. range (apply_qregister F) = \<FF>\<close>
    by -
qed


lemma valid_qregister_range_def_sot:
  \<open>valid_qregister_range \<FF> \<longleftrightarrow> 
      (\<forall>a\<in>\<FF>. a* \<in> \<FF>) \<and> csubspace \<FF> \<and> (\<forall>a\<in>\<FF>. \<forall>b\<in>\<FF>. a o\<^sub>C\<^sub>L b \<in> \<FF>) \<and> id_cblinfun \<in> \<FF> \<and>
      closedin cstrong_operator_topology \<FF>\<close>
  by (simp add: valid_qregister_range_def von_neumann_algebra_def_sot)

(* TODO: valid_qregister_range could be a corollary of this *)
lemma valid_qregister_range_pres:
  assumes qreg: \<open>qregister F\<close>
  assumes valid: \<open>valid_qregister_range A\<close>
  shows \<open>valid_qregister_range (apply_qregister F ` A)\<close>
proof (intro valid_qregister_range_def_sot[THEN iffD2] conjI ballI)
  show \<open>a \<in> apply_qregister F ` A \<Longrightarrow> a* \<in> apply_qregister F ` A\<close> for a
    using assms unfolding valid_qregister_range_def von_neumann_algebra_def by fastforce
  show \<open>csubspace (apply_qregister F ` A)\<close>
    using valid
    by (metis clinear_apply_qregister complex_vector.linear_subspace_image csubspace_commutant
        valid_qregister_range_def von_neumann_algebra_def)
  show \<open>a o\<^sub>C\<^sub>L b \<in> apply_qregister F ` A\<close>
    if \<open>a \<in> apply_qregister F ` A\<close> and \<open>b \<in> apply_qregister F ` A\<close> for a b
  proof -
    from that obtain a' where a': \<open>a' \<in> A\<close> and a_def: \<open>a = apply_qregister F a'\<close>
      by auto
    from that obtain b' where b': \<open>b' \<in> A\<close> and b_def: \<open>b = apply_qregister F b'\<close>
      by auto
    from valid have \<open>a' o\<^sub>C\<^sub>L b' \<in> A\<close>
      using that a' b' by (simp add: valid_qregister_range_def_sot)
    then show ?thesis
      using qreg by (simp add: a_def b_def register_mult)
  qed
  show \<open>id_cblinfun \<in> apply_qregister F ` A\<close>
    using assms 
    by (metis id_in_commutant imageI lift_id_cblinfun valid_qregister_range_def von_neumann_algebra_def)
  show \<open>closedin cstrong_operator_topology (apply_qregister F ` A)\<close>
  proof -
    have \<open>closedin cstrong_operator_topology A\<close>
      using valid valid_qregister_range_def_sot by blast
    moreover have \<open>closed_map cstrong_operator_topology cstrong_operator_topology (apply_qregister F)\<close>
      using qreg
      by (simp add: closed_map_sot_register)
    ultimately show ?thesis
      using closed_map_def by blast
  qed
qed

lemma qregister_Abs_qregister: \<open>qregister_raw F \<Longrightarrow> qregister (Abs_qregister F)\<close>
  by (simp add: Abs_qregister_inverse flip: qregister_raw_apply_qregister)
  
lemma qregister_apply_Abs: \<open>qregister_raw F \<Longrightarrow> apply_qregister (Abs_qregister F) = F\<close>
  by (simp add: Abs_qregister_inverse)

lemma valid_qregister_range_pres_raw:
  assumes qreg: \<open>qregister_raw F\<close>
  assumes valid: \<open>valid_qregister_range A\<close>
  shows \<open>valid_qregister_range (F ` A)\<close>
  by (metis assms(1) assms(2) qregister_Abs_qregister qregister_apply_Abs valid_qregister_range_pres)

(* lemma valid_qregister_range_raw:
  assumes \<open>qregister_raw F\<close>
  shows \<open>valid_qregister_range (range F)\<close>
  by (simp add: assms valid_qregister_range_UNIV valid_qregister_range_pres_raw) *)

lift_definition QREGISTER_chain :: \<open>('a,'b) qregister \<Rightarrow> 'a QREGISTER \<Rightarrow> 'b QREGISTER\<close> is
  \<open>\<lambda>F \<GG>. if qregister_raw F then F ` \<GG> else empty_qregister_range\<close>
  by (auto simp: non_qregister_raw  
      intro!: valid_qregister_range_pres_raw valid_empty_qregister_range)

lift_definition QREGISTER_fst :: \<open>('a\<times>'b) QREGISTER\<close> is
  \<open>(\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) ` UNIV\<close>
  using valid_qregister_range[of qFst]
  by (simp add: apply_qregister_fst[abs_def])
lift_definition QREGISTER_snd :: \<open>('a\<times>'b) QREGISTER\<close> is
  \<open>(\<lambda>a. id_cblinfun \<otimes>\<^sub>o a) ` UNIV\<close>
  using valid_qregister_range[of qSnd]
  by (simp add: apply_qregister_snd[abs_def])

lemma apply_qregister_empty_qregister_range: \<open>qregister F \<Longrightarrow> apply_qregister F ` empty_qregister_range = empty_qregister_range\<close>
  by (auto simp add: image_image empty_qregister_range_def apply_qregister_scaleC)

lemma QREGISTER_of_qregister_chain: \<open>QREGISTER_of (qregister_chain F G) = QREGISTER_chain F (QREGISTER_of G)\<close>
  apply (rule Rep_QREGISTER_inject[THEN iffD1])
  by (auto simp add: QREGISTER_of.rep_eq QREGISTER_chain.rep_eq apply_qregister_empty_qregister_range)

lemma QREGISTER_of_qFst: \<open>QREGISTER_of qFst = QREGISTER_fst\<close>
  apply (rule Rep_QREGISTER_inject[THEN iffD1])
  by (simp add: QREGISTER_of.rep_eq QREGISTER_fst.rep_eq apply_qregister_fst)
lemma QREGISTER_of_qSnd: \<open>QREGISTER_of qSnd = QREGISTER_snd\<close>
  apply (rule Rep_QREGISTER_inject[THEN iffD1])
  by (simp add: QREGISTER_of.rep_eq QREGISTER_snd.rep_eq apply_qregister_snd)

lemma QREGISTER_pair_sym: \<open>QREGISTER_pair F G = QREGISTER_pair G F\<close>
  apply (rule Rep_QREGISTER_inject[THEN iffD1])
  by (simp add: QREGISTER_pair.rep_eq Un_ac(3))

lemma double_commutant_hull: \<open>commutant (commutant X) = (\<lambda>X. commutant (commutant X) = X) hull X\<close>
  by (smt (verit) commutant_antimono double_commutant_grows hull_unique triple_commutant)

lemma commutant_adj_closed: \<open>(\<And>x. x \<in> X \<Longrightarrow> x* \<in> X) \<Longrightarrow> x \<in> commutant X \<Longrightarrow> x* \<in> commutant X\<close>
  by (metis (no_types, opaque_lifting) commutant_adj commutant_antimono double_adj imageI subset_iff)

(* TODO restate in terms of  von_neumann_algebra *)
lemma double_commutant_hull':
  assumes \<open>\<And>x. x \<in> X \<Longrightarrow> x* \<in> X\<close>
  shows \<open>commutant (commutant X) = valid_qregister_range hull X\<close>
proof (rule antisym)
  show \<open>commutant (commutant X) \<subseteq> valid_qregister_range hull X\<close>
    apply (subst double_commutant_hull)
    apply (rule hull_antimono)
    by (simp add: valid_qregister_range_def von_neumann_algebra_def)
  show \<open>valid_qregister_range hull X \<subseteq> commutant (commutant X)\<close>
    apply (rule hull_minimal)
    by (simp_all add: valid_qregister_range_def von_neumann_algebra_def assms commutant_adj_closed)
qed

lemma QREGISTER_pair_valid_qregister_range_hull:
  \<open>Rep_QREGISTER (QREGISTER_pair F G) = valid_qregister_range hull (Rep_QREGISTER F \<union> Rep_QREGISTER G)\<close>
  apply (simp add: QREGISTER_pair.rep_eq)
  apply (subst double_commutant_hull')
  using Rep_QREGISTER valid_qregister_range_def  von_neumann_algebra_def by auto

lemma hull_cong_restricted: \<open>X = Y \<Longrightarrow> P hull X = P hull Y\<close>
  by simp

(* TODO needed? *)
lemma double_commutant_Un_left: \<open>commutant (commutant (commutant (commutant X) \<union> Y)) = commutant (commutant (X \<union> Y))\<close>
  apply (simp add: double_commutant_hull cong: hull_cong_restricted)
  using hull_Un_left by fastforce

(* TODO needed? *)
lemma double_commutant_Un_right: \<open>commutant (commutant (X \<union> commutant (commutant Y))) = commutant (commutant (X \<union> Y))\<close>
  by (metis Un_ac(3) double_commutant_Un_left)

lemma Rep_QREGISTER_Un_empty1[simp]: \<open>Rep_QREGISTER X \<union> empty_qregister_range = Rep_QREGISTER X\<close>
  using QREGISTER_unit_smallest bot_QREGISTER.rep_eq less_eq_QREGISTER.rep_eq by blast
lemma Rep_QREGISTER_Un_empty2[simp]: \<open>empty_qregister_range \<union> Rep_QREGISTER X = Rep_QREGISTER X\<close>
  using Rep_QREGISTER_Un_empty1 by blast

lemma QREGISTER_chain_non_qregister[simp]: \<open>QREGISTER_chain non_qregister F = bot\<close>
  apply (rule Rep_QREGISTER_inject[THEN iffD1])
  by (simp add: QREGISTER_chain.rep_eq bot_QREGISTER.rep_eq)

lemma QREGISTER_pair_bot_left[simp]: \<open>QREGISTER_pair \<bottom> F = F\<close>
  apply (rule Rep_QREGISTER_inject[THEN iffD1])
  apply (simp add: QREGISTER_pair.rep_eq bot_QREGISTER.rep_eq)
  by (metis QREGISTER_pair.rep_eq QREGISTER_pair_valid_qregister_range_hull Rep_QREGISTER Un_absorb hull_same mem_Collect_eq)

lemma QREGISTER_pair_bot_right[simp]: \<open>QREGISTER_pair F \<bottom> = F\<close>
  by (metis QREGISTER_pair_bot_left QREGISTER_pair_sym)

lemma Rep_QREGISTER_pair_sot: \<open>Rep_QREGISTER (QREGISTER_pair F G) = cstrong_operator_topology closure_of (cspan (Rep_QREGISTER F \<union> Rep_QREGISTER G))\<close>
  sorry

lemma
  shows \<open>continuous_map cstrong_operator_topology cstrong_operator_topology (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun)\<close>
proof (rule continuous_map_iff_preserves_convergence)
  fix F :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2) filter\<close> and a :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
  assume \<open>limitin cstrong_operator_topology id a F\<close>
  show \<open>limitin cstrong_operator_topology (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) (a \<otimes>\<^sub>o id_cblinfun) F\<close>
  proof (unfold limitin_cstrong_operator_topology, intro allI)
    fix \<psi> :: \<open>('a \<times> 'd) ell2\<close>
    have \<open>(\<lambda>x. (x \<otimes>\<^sub>o id_cblinfun) *\<^sub>V \<psi> - (a \<otimes>\<^sub>o id_cblinfun) *\<^sub>V \<psi>)\<close>

    have \<open>((\<lambda>a. (a \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket (x,y)) \<longlongrightarrow> (a \<otimes>\<^sub>o id_cblinfun) *\<^sub>V ket (x,y)) F\<close> for x and y :: 'd
      by-
    
    show \<open>((\<lambda>a. (a \<otimes>\<^sub>o id_cblinfun) *\<^sub>V \<psi>) \<longlongrightarrow> (a \<otimes>\<^sub>o id_cblinfun) *\<^sub>V \<psi>) F\<close>
      apply (subst ell2_decompose_infsum[of \<psi>])
      apply (subst (2) ell2_decompose_infsum[of \<psi>])
      apply(subst infsum_cblinfun_apply[symmetric])
      apply (simp add: ell2_decompose_summable)
      apply(subst infsum_cblinfun_apply[symmetric])
      apply (simp add: ell2_decompose_summable)
      
      
      show ?thesis
    apply (rule continuous_map_iff_preserves_convergence)

proof (unfold continuous_on_cstrong_operator_topo_iff_coordinatewise, intro allI)


lemma homeomorphic_map_apply_qregister_sot:
  assumes \<open>qregister F\<close>
  shows \<open>homeomorphic_map cstrong_operator_topology (subtopology cstrong_operator_topology (range (apply_qregister F))) (apply_qregister F)\<close>
proof (rule homeomorphic_maps_imp_map[where g=\<open>inv (apply_qregister F)\<close>], unfold homeomorphic_maps_def, 
    intro conjI ballI)
  show 1: \<open>inv (apply_qregister F) (apply_qregister F x) = x\<close> for x
    by (simp add: assms inj_qregister)
  show 2: \<open>apply_qregister F (inv (apply_qregister F) y) = y\<close> if \<open>y \<in> topspace (subtopology cstrong_operator_topology (range (apply_qregister F)))\<close> for y
    using that by (simp add: f_inv_into_f)
  show \<open>continuous_map (subtopology cstrong_operator_topology (range (apply_qregister F)))
     cstrong_operator_topology (inv (apply_qregister F))\<close>
  try0
  by -
  show 3: \<open>continuous_map cstrong_operator_topology
     (subtopology cstrong_operator_topology (range (apply_qregister F))) (apply_qregister F)\<close>
  try0
  by -
qed

lemma QREGISTER_pair_QREGISTER_chain: \<open>QREGISTER_pair (QREGISTER_chain F G) (QREGISTER_chain F H)
            = QREGISTER_chain F (QREGISTER_pair G H)\<close>
proof (cases \<open>qregister F\<close>)
  case True
  show ?thesis
    apply (rule_tac Rep_QREGISTER_inject[THEN iffD1])
    apply (simp add: Rep_QREGISTER_pair_sot QREGISTER_chain.rep_eq True complex_vector.linear_span_image
 flip: image_Un)
    apply (subst)
     apply simp

  by -

    apply (transfer fixing: )
    apply (auto simp)
    apply (rule_tac Rep_QREGISTER_inject[THEN iffD1])
    apply (simp add: QREGISTER_pair.rep_eq QREGISTER_chain.rep_eq)
next
  case False
  then show ?thesis
    by (simp add: non_qregister)
qed

  apply (simp add: QREGISTER_pair_valid_qregister_range_hull)
  sorry

lemma QREGISTER_pair_assoc:
  \<open>QREGISTER_pair (QREGISTER_pair F G) H = QREGISTER_pair F (QREGISTER_pair G H)\<close>
  apply (rule Rep_QREGISTER_inject[THEN iffD1])
  by (simp add: QREGISTER_pair_valid_qregister_range_hull Un_ac(1)
      flip: hull_Un_left hull_Un_right)

lemma x4: \<open>QREGISTER_pair (QREGISTER_chain A F) (QREGISTER_pair (QREGISTER_chain A G) B)
            = QREGISTER_pair B (QREGISTER_chain A (QREGISTER_pair F G))\<close>
  apply (simp flip: QREGISTER_pair_QREGISTER_chain)
  using QREGISTER_pair_assoc QREGISTER_pair_sym
  by metis

lemma x2: \<open>QREGISTER_pair (QREGISTER_chain A F) (QREGISTER_pair B (QREGISTER_chain A G))
            = QREGISTER_pair B (QREGISTER_chain A (QREGISTER_pair F G))\<close>
  apply (simp flip: QREGISTER_pair_QREGISTER_chain)
  using QREGISTER_pair_assoc QREGISTER_pair_sym
  by metis


lemma empty_qregister_range_subset_valid_range: \<open>valid_qregister_range A \<Longrightarrow> empty_qregister_range \<subseteq> A\<close>
  by (auto simp: valid_qregister_range_def_sot empty_qregister_range_def complex_vector.subspace_scale)

instance QREGISTER :: (type) order_bot
  apply intro_classes
  apply transfer
  using empty_qregister_range_subset_valid_range by simp

instance QREGISTER :: (type) order_top
  apply intro_classes
  apply transfer
  by simp

lemma QREGISTER_pair_unit_left: \<open>QREGISTER_pair QREGISTER_unit F = F\<close>
  apply (rule Rep_QREGISTER_inject[THEN iffD1])
  using empty_qregister_range_subset_valid_range[of \<open>Rep_QREGISTER F\<close>] QREGISTER.Rep_QREGISTER[of F]
  by (simp add: QREGISTER_pair.rep_eq bot_QREGISTER.rep_eq Un_absorb1 valid_qregister_range_def von_neumann_algebra_def)

lemma QREGISTER_pair_unit_right: \<open>QREGISTER_pair F QREGISTER_unit = F\<close>
  apply (subst QREGISTER_pair_sym)
  by (rule QREGISTER_pair_unit_left)


lemma commutant_id_mult: \<open>commutant (range (\<lambda>c. c *\<^sub>C id_cblinfun :: _ \<Rightarrow>\<^sub>C\<^sub>L 'a::chilbert_space)) = UNIV\<close>
  by (metis commutant_UNIV commutant_empty triple_commutant)

lemma QREGISTER_pair_all_left: \<open>QREGISTER_pair QREGISTER_all F = QREGISTER_all\<close>
  apply (rule Rep_QREGISTER_inject[THEN iffD1])
  by (simp add: QREGISTER_pair.rep_eq top_QREGISTER.rep_eq
      commutant_id_mult commutant_UNIV)

lemma QREGISTER_pair_all_right: \<open>QREGISTER_pair F QREGISTER_all = QREGISTER_all\<close>
  apply (subst QREGISTER_pair_sym)
  by (rule QREGISTER_pair_all_left)

lemma QREGISTER_chain_id_left: \<open>QREGISTER_chain qregister_id F = F\<close>
  apply (rule Rep_QREGISTER_inject[THEN iffD1])
  by (simp add: QREGISTER_chain.rep_eq)

lemma QREGISTER_chain_all_right: \<open>QREGISTER_chain F QREGISTER_all = QREGISTER_of F\<close>
  apply (rule Rep_QREGISTER_inject[THEN iffD1])
  by (simp add: QREGISTER_chain.rep_eq QREGISTER_of.rep_eq top_QREGISTER.rep_eq)

lemma QREGISTER_pair_fst_snd: \<open>QREGISTER_pair QREGISTER_fst QREGISTER_snd = QREGISTER_all\<close>
  by (simp add: flip: QREGISTER_of_qFst QREGISTER_of_qSnd QREGISTER_of_qregister_pair
      QREGISTER_of_qregister_id)
lemma QREGISTER_pair_snd_fst: \<open>QREGISTER_pair QREGISTER_snd QREGISTER_fst = QREGISTER_all\<close>
  apply (subst QREGISTER_pair_sym)
  by (rule QREGISTER_pair_fst_snd)

lemma QREGISTER_chain_unit_left: \<open>QREGISTER_chain empty_qregister F = QREGISTER_unit\<close>
  apply (rule antisym)
   apply transfer
  by (auto simp: Quantum_Extra2.empty_var_def empty_qregister_range_def)

lemma QREGISTER_chain_unit_right: \<open>QREGISTER_chain F QREGISTER_unit = QREGISTER_unit\<close>
  apply (rule Rep_QREGISTER_inject[THEN iffD1])
  by (auto simp add: QREGISTER_chain.rep_eq bot_QREGISTER.rep_eq empty_qregister_range_def
      image_image apply_qregister_scaleC)

ML \<open>
(* Brings an INDEX-REGISTER into normal form. *)
local
  val rules = (map (fn thm => thm RS @{thm eq_reflection}) @{thms 
    x2 QREGISTER_pair_QREGISTER_chain QREGISTER_pair_assoc x4 QREGISTER_pair_unit_left QREGISTER_pair_unit_right
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


(* (* TODO used? *)
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
qed *)



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
  by (simp add: QREGISTER_of.rep_eq bot_QREGISTER.rep_eq)

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


