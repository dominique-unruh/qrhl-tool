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

definition \<open>actual_qregister_range_aux f a \<longleftrightarrow> 
    (\<forall>x y. snd (f x) \<noteq> snd (f y) \<longrightarrow> ket x \<bullet>\<^sub>C (a *\<^sub>V ket y) = 0)
      \<and> (\<forall>x y x' y'. fst (f x) = fst (f x') \<longrightarrow> fst (f y) = fst (f y') \<longrightarrow> 
                     snd (f x) = snd (f y) \<longrightarrow> snd (f x') = snd (f y') \<longrightarrow>
                         ket x \<bullet>\<^sub>C (a *\<^sub>V ket y) = ket x' \<bullet>\<^sub>C (a *\<^sub>V ket y'))\<close>

text \<open>The following definition captures all \<^typ>\<open>_ QREGISTER\<close> that actually correspond to
  some register (see theorems \<open>qregister_has_actual_qregister_range\<close> and
  \<open>actual_qregister_range_ex_register\<close> below).
  Most likely, this is just equal to saying \<^term>\<open>\<FF>\<close> is a von Neumann type I factor,
  but we use this more elementary but rather unreadable definition instead
  because otherwise we would need to prove more properties about von Neumann type I
  factors.\<close>
definition actual_qregister_range :: \<open>'a qupdate set \<Rightarrow> bool\<close> where
  \<open>actual_qregister_range \<FF> \<longleftrightarrow> (\<exists>(f :: 'a \<Rightarrow> 'a\<times>'a) U L R. unitary U \<and> 
    inj f \<and> range f = L \<times> R \<and>
    \<FF> = {sandwich U a | a. actual_qregister_range_aux f a})\<close>

lemma actual_qregister_range_aux_sandwich:
  assumes \<open>\<And>x. U *\<^sub>V ket x = ket (f x)\<close>
  assumes \<open>unitary U\<close>
  assumes \<open>bij f\<close>
  shows \<open>actual_qregister_range_aux id (sandwich U a) \<longleftrightarrow> actual_qregister_range_aux f a\<close>
proof -
  have [simp]: \<open>U* *\<^sub>V ket x = ket (inv f x)\<close> for x
    by (metis (mono_tags, lifting) \<open>bij f\<close> assms(1) assms(2) bij_betw_imp_surj_on cinner_adj_right cinner_ket_eqI isometry_cinner_both_sides surj_f_inv_f unitary_isometry)

  have \<open>bij (inv f)\<close>
    by (simp add: \<open>bij f\<close> bij_imp_bij_inv)

  show ?thesis
    using assms
    apply (auto simp: sandwich_apply actual_qregister_range_aux_def bij_betw_imp_surj_on surj_f_inv_f
        simp flip: cinner_adj_left)
     apply (metis \<open>bij f\<close>  bij_betw_imp_inj_on invI surjective_pairing)
    by (smt (verit) \<open>bij f\<close>  bij_betw_imp_inj_on inv_f_f surjective_pairing)
qed

lemma Collect_actual_qregister_range_aux_id:
  \<open>{a. actual_qregister_range_aux id a} = range (\<lambda>\<theta>. \<theta> \<otimes>\<^sub>o id_cblinfun)\<close>
proof (intro Set.set_eqI iffI)
  fix a :: \<open>('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'c) ell2\<close>
  assume \<open>a \<in> range (\<lambda>\<theta>. \<theta> \<otimes>\<^sub>o id_cblinfun)\<close>
  then show \<open>a \<in> {a. actual_qregister_range_aux id a}\<close>
    by (auto simp: tensor_op_ell2 tensor_ell2_inner_prod actual_qregister_range_aux_def
        simp flip: tensor_ell2_ket)
next
  fix a
  assume asm: \<open>a \<in> {a. actual_qregister_range_aux id a}\<close>
  define \<theta> where \<open>\<theta> = tensor_ell2_right (ket undefined)* o\<^sub>C\<^sub>L a o\<^sub>C\<^sub>L tensor_ell2_right (ket undefined)\<close>
  have \<open>a = \<theta> \<otimes>\<^sub>o id_cblinfun\<close>
    using asm
    by (auto intro!: equal_ket cinner_ket_eqI 
        simp: tensor_op_ell2 tensor_ell2_inner_prod cinner_ket
        \<theta>_def cinner_adj_right actual_qregister_range_aux_def
        simp flip: tensor_ell2_ket)
  then show \<open>a \<in> range (\<lambda>\<theta>. \<theta> \<otimes>\<^sub>o id_cblinfun)\<close>
    by auto
qed

lemma qregister_has_actual_qregister_range:
  fixes F :: \<open>('a,'b) qregister\<close>
  assumes \<open>qregister F\<close>
  shows \<open>actual_qregister_range (range (apply_qregister F))\<close>
proof -
  define \<FF> where \<open>\<FF> = range (apply_qregister F)\<close>
  have \<open>qregister_raw (apply_qregister F)\<close>
    using assms by auto
  from register_decomposition[OF this]
  have \<open>\<forall>\<^sub>\<tau> 'c::type = qregister_decomposition_basis F.
        actual_qregister_range \<FF>\<close>
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
    also have \<open>\<dots> = sandwich V ` {a. actual_qregister_range_aux id a}\<close>
      by (simp add: Collect_actual_qregister_range_aux_id)
    also have \<open>\<dots> = sandwich U ` sandwich G ` {a. actual_qregister_range_aux id a}\<close>
      by (simp add: U_def image_image sandwich_compose cblinfun_assoc_right unitaryD1
          flip: cblinfun_apply_cblinfun_compose)
    also have \<open>\<dots> = sandwich U ` {a. actual_qregister_range_aux id (sandwich (G*) a)}\<close>
      by (simp add: bij_image_Collect_eq bij_sandwich_G inv_sandwich_G)
    also have \<open>\<dots> = sandwich U ` {a. actual_qregister_range_aux (inv g) a}\<close>
      by (simp add: actual_qregister_range_aux_sandwich Gadj_ket bij_imp_bij_inv)
    also have \<open>\<dots> = sandwich U ` {a. actual_qregister_range_aux f a}\<close>
      by (simp add: actual_qregister_range_aux_def)
    also have \<open>\<dots> = {sandwich U a | a. actual_qregister_range_aux f a}\<close>
      by auto
    finally have \<FF>_eq: \<open>\<FF> = {sandwich U a | a. actual_qregister_range_aux f a}\<close>
      by -
    moreover have inj_f: \<open>inj f\<close>
      by (auto intro!: inj_compose prod.inj_map
          simp add: bij_betw_inv_into bij_is_inj f_def \<open>inj ia\<close> \<open>inj ic\<close>)
    moreover have range_f: \<open>range f = L \<times> R\<close>
      by (auto simp add: f_def L_def R_def simp flip: image_image)
    moreover have unitary_U: \<open>unitary U\<close>
      by (auto intro!: unitary_cblinfun_compose
          simp add: U_def)
    show \<open>actual_qregister_range \<FF>\<close>
      unfolding actual_qregister_range_def
      apply (rule exI[of _ f], rule exI[of _ U], rule exI[of _ L], rule exI[of _ R])
      by (simp only: unitary_U inj_f range_f \<FF>_eq)
  qed
  from this[cancel_with_type]
  show \<open>actual_qregister_range \<FF>\<close>
    by -
qed

definition \<open>actual_qregister_range_content \<FF> = (SOME L::'a set.
    \<exists>(f :: 'a \<Rightarrow> 'a\<times>'a) U R. unitary U \<and> 
        inj f \<and> range f = L \<times> R \<and>
        \<FF> = {sandwich U a | a. actual_qregister_range_aux f a})\<close>
  for \<FF> :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2) set\<close>

lemma actual_qregister_range_ex_register:
  fixes \<FF> :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2) set\<close>
  assumes \<open>actual_qregister_range \<FF>\<close>
  shows \<open>\<forall>\<^sub>\<tau> 'l::type = actual_qregister_range_content \<FF>.
         \<exists>F :: ('l, 'a) qregister. qregister F \<and> range (apply_qregister F) = \<FF>\<close>
proof (rule with_typeI)
  define L where \<open>L = actual_qregister_range_content \<FF>\<close>
  have \<open>\<exists>(f :: 'a \<Rightarrow> 'a\<times>'a) U R. unitary U \<and> 
        inj f \<and> range f = L \<times> R \<and>
        \<FF> = {sandwich U a | a. actual_qregister_range_aux f a}\<close>
    unfolding L_def actual_qregister_range_content_def apply (rule someI_ex)
    using assms unfolding actual_qregister_range_def 
    by blast
  then obtain f :: \<open>'a \<Rightarrow> 'a\<times>'a\<close> and U R where \<open>unitary U\<close> and \<open>inj f\<close> and range_f: \<open>range f = L \<times> R\<close>
    and \<FF>_eq: \<open>\<FF> = {sandwich U a | a. actual_qregister_range_aux f a}\<close>
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
  have \<open>\<forall>\<^sub>\<tau> 'r::type = R. \<exists>F :: ('l, 'a) qregister. qregister F \<and> range (apply_qregister F) = \<FF>\<close>
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
    moreover have \<open>range (apply_qregister F) = \<FF>\<close>
    proof -
      have aux1: \<open>fst (f' x) = fst (f' y) \<longleftrightarrow> fst (f x) = fst (f y)\<close> for x y
        by (metis L.Abs_inverse comp_apply eq_fst_iff f'_def fst_map_prod mem_Sigma_iff rangeI range_f)
      have aux2: \<open>snd (f' x) = snd (f' y) \<longleftrightarrow> snd (f x) = snd (f y)\<close> for x y
        by (metis R.type_definition_axioms SigmaD2 comp_eq_dest_lhs f'_def rangeI range_f snd_map_prod surjective_pairing type_definition.Abs_inject)

      have \<open>range (apply_qregister F) = sandwich U ` sandwich (V*) ` range (\<lambda>x. x \<otimes>\<^sub>o id_cblinfun)\<close>
        by (auto simp add: F_def apply_qregister_fst apply_qregister_transform_qregister \<open>unitary U\<close>
            simp flip: sandwich_compose)
      also have \<open>\<dots> = sandwich U ` sandwich (V*) ` {a. actual_qregister_range_aux id a}\<close>
        by (simp add: Collect_actual_qregister_range_aux_id)
      also have \<open>\<dots> = sandwich U ` {a. actual_qregister_range_aux id (sandwich V a)}\<close>
        by (simp add: bij_image_Collect_eq bij_sandwich_Vadj inv_sandwich_Vadj)
      also have \<open>\<dots> = sandwich U ` {a. actual_qregister_range_aux f' a}\<close>
        apply (subst actual_qregister_range_aux_sandwich)
        by (simp_all add: V_ket \<open>unitary V\<close> \<open>bij f'\<close>)
      also have \<open>\<dots> = sandwich U ` {a. actual_qregister_range_aux f a}\<close>
        apply (rule arg_cong[where f=\<open>\<lambda>a. sandwich U ` Collect a\<close>], rule ext)
        by (simp add: actual_qregister_range_aux_def aux1 aux2)
      also have \<open>\<dots> = {sandwich U a | a. actual_qregister_range_aux f a}\<close>
        by blast
      finally show ?thesis
        by (simp add: \<FF>_eq)
    qed
    ultimately show \<open>\<exists>F :: ('l, 'a) qregister. qregister F \<and> range (apply_qregister F) = \<FF>\<close>
      by auto
  qed
  from this[cancel_with_type]
  show \<open>\<exists>F :: ('l, 'a) qregister. qregister F \<and> range (apply_qregister F) = \<FF>\<close>
    by -
qed


lemma actual_qregister_range_is_valid:
  assumes \<open>actual_qregister_range \<FF>\<close>
  shows \<open>valid_qregister_range \<FF>\<close>
proof -
  from actual_qregister_range_ex_register[OF assms]
  have \<open>\<forall>\<^sub>\<tau> 'c::type = actual_qregister_range_content \<FF>. valid_qregister_range \<FF>\<close>
  proof (rule with_type_mp)
    assume \<open>\<exists>F :: ('b, 'a) qregister. qregister F \<and> range (apply_qregister F) = \<FF>\<close>
    then obtain F :: \<open>('b, 'a) qregister\<close> where \<open>qregister F\<close> and \<open>range (apply_qregister F) = \<FF>\<close>
      by auto
    then show \<open>valid_qregister_range \<FF>\<close>
      using valid_qregister_range by blast
  qed
  from this[cancel_with_type]
  show ?thesis
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
  \<open>\<lambda>F \<GG>. if qregister_raw F then F ` \<GG> else one_algebra\<close>
  by (auto simp: non_qregister_raw  
      intro!: valid_qregister_range_pres_raw valid_one_algebra)

lift_definition QREGISTER_fst :: \<open>('a\<times>'b) QREGISTER\<close> is
  \<open>(\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) ` UNIV\<close>
  using valid_qregister_range[of qFst]
  by (simp add: apply_qregister_fst[abs_def])
lift_definition QREGISTER_snd :: \<open>('a\<times>'b) QREGISTER\<close> is
  \<open>(\<lambda>a. id_cblinfun \<otimes>\<^sub>o a) ` UNIV\<close>
  using valid_qregister_range[of qSnd]
  by (simp add: apply_qregister_snd[abs_def])

lemma apply_qregister_one_algebra: \<open>qregister F \<Longrightarrow> apply_qregister F ` one_algebra = one_algebra\<close>
  by (auto simp add: image_image one_algebra_def apply_qregister_scaleC)

lemma QREGISTER_of_qregister_chain: \<open>QREGISTER_of (qregister_chain F G) = QREGISTER_chain F (QREGISTER_of G)\<close>
  apply (rule Rep_QREGISTER_inject[THEN iffD1])
  by (auto simp add: QREGISTER_of.rep_eq QREGISTER_chain.rep_eq apply_qregister_one_algebra)

lemma QREGISTER_of_qFst: \<open>QREGISTER_of qFst = QREGISTER_fst\<close>
  apply (rule Rep_QREGISTER_inject[THEN iffD1])
  by (simp add: QREGISTER_of.rep_eq QREGISTER_fst.rep_eq apply_qregister_fst)
lemma QREGISTER_of_qSnd: \<open>QREGISTER_of qSnd = QREGISTER_snd\<close>
  apply (rule Rep_QREGISTER_inject[THEN iffD1])
  by (simp add: QREGISTER_of.rep_eq QREGISTER_snd.rep_eq apply_qregister_snd)

lemma QREGISTER_pair_sym: \<open>QREGISTER_pair F G = QREGISTER_pair G F\<close>
  apply (rule Rep_QREGISTER_inject[THEN iffD1])
  by (simp add: QREGISTER_pair.rep_eq Un_ac(3))

lemma QREGISTER_pair_valid_qregister_range_hull:
  \<open>Rep_QREGISTER (QREGISTER_pair F G) = valid_qregister_range hull (Rep_QREGISTER F \<union> Rep_QREGISTER G)\<close>
  apply (simp add: QREGISTER_pair.rep_eq)
  apply (subst double_commutant_hull')
  using Rep_QREGISTER unfolding valid_qregister_range_def von_neumann_algebra_def by auto

lemma Rep_QREGISTER_Un_empty1[simp]: \<open>Rep_QREGISTER X \<union> one_algebra = Rep_QREGISTER X\<close>
  using QREGISTER_unit_smallest bot_QREGISTER.rep_eq less_eq_QREGISTER.rep_eq by blast
lemma Rep_QREGISTER_Un_empty2[simp]: \<open>one_algebra \<union> Rep_QREGISTER X = Rep_QREGISTER X\<close>
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

lemma register_double_commutant_commute:
  assumes \<open>qregister F\<close>
  shows \<open>commutant (commutant (apply_qregister F ` X)) = apply_qregister F ` commutant (commutant X)\<close>
proof -
  have \<open>qregister_raw (apply_qregister F)\<close>
    using assms qregister.rep_eq by blast
  from register_decomposition[OF this]
  have \<open>\<forall>\<^sub>\<tau> 'c::type = qregister_decomposition_basis F. ?thesis\<close>
  proof (rule with_type_mp)
    assume \<open>\<exists>U :: ('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2. unitary U \<and> (\<forall>\<theta>. apply_qregister F \<theta> = sandwich U *\<^sub>V \<theta> \<otimes>\<^sub>o id_cblinfun)\<close>
    then obtain U :: \<open>('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close> where [simp]: \<open>unitary U\<close> and F_decomp: \<open>apply_qregister F \<theta> = sandwich U *\<^sub>V (\<theta> \<otimes>\<^sub>o id_cblinfun)\<close> for \<theta>
      by auto
    have \<open>commutant (commutant (apply_qregister F ` X))
        = commutant (commutant (sandwich U ` (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) ` X))\<close>
      by (simp add: image_image F_decomp)
    also have \<open>\<dots> = sandwich U ` commutant (commutant ((\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) ` X))\<close>
      by (simp add: sandwich_unitary_complement)
    also have \<open>\<dots> = sandwich U ` (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) ` commutant (commutant (X))\<close>
      using amplification_double_commutant_commute by blast
    also have \<open>\<dots> = apply_qregister F ` commutant (commutant X)\<close>
      by (simp add: image_image F_decomp)
    finally show \<open>commutant (commutant (apply_qregister F ` X)) = apply_qregister F ` commutant (commutant X)\<close>
      by -
  qed
  from this[cancel_with_type]
  show ?thesis
    by -
qed

lemma QREGISTER_pair_QREGISTER_chain: \<open>QREGISTER_pair (QREGISTER_chain F G) (QREGISTER_chain F H)
            = QREGISTER_chain F (QREGISTER_pair G H)\<close>
proof (cases \<open>qregister F\<close>)
  case True
  show ?thesis
    apply (rule_tac Rep_QREGISTER_inject[THEN iffD1])
    by (simp add: QREGISTER_pair.rep_eq QREGISTER_chain.rep_eq
        register_double_commutant_commute
        True complex_vector.linear_span_image
        flip: image_Un)
next
  case False
  then show ?thesis
    by (simp add: non_qregister)
qed

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


lemma one_algebra_subset_valid_range: \<open>valid_qregister_range A \<Longrightarrow> one_algebra \<subseteq> A\<close>
  by (auto simp: valid_qregister_range_def_sot one_algebra_def complex_vector.subspace_scale)

instance QREGISTER :: (type) order_bot
  apply intro_classes
  apply transfer
  using one_algebra_subset_valid_range by simp

instance QREGISTER :: (type) order_top
  apply intro_classes
  apply transfer
  by simp

lemma QREGISTER_pair_unit_left: \<open>QREGISTER_pair QREGISTER_unit F = F\<close>
  apply (rule Rep_QREGISTER_inject[THEN iffD1])
  using one_algebra_subset_valid_range[of \<open>Rep_QREGISTER F\<close>] QREGISTER.Rep_QREGISTER[of F]
  by (simp add: QREGISTER_pair.rep_eq bot_QREGISTER.rep_eq Un_absorb1 valid_qregister_range_def von_neumann_algebra_def)

lemma QREGISTER_pair_unit_right: \<open>QREGISTER_pair F QREGISTER_unit = F\<close>
  apply (subst QREGISTER_pair_sym)
  by (rule QREGISTER_pair_unit_left)

lemma QREGISTER_pair_all_left: \<open>QREGISTER_pair QREGISTER_all F = QREGISTER_all\<close>
  apply (rule Rep_QREGISTER_inject[THEN iffD1])
  by (simp add: QREGISTER_pair.rep_eq top_QREGISTER.rep_eq
      commutant_one_algebra commutant_UNIV)

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
  by (auto simp: Quantum_Extra2.empty_var_def one_algebra_def)

lemma QREGISTER_chain_unit_right[simp]: \<open>QREGISTER_chain F QREGISTER_unit = QREGISTER_unit\<close>
  apply (rule Rep_QREGISTER_inject[THEN iffD1])
  by (auto simp add: QREGISTER_chain.rep_eq bot_QREGISTER.rep_eq one_algebra_def
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

lemma qcomplements_via_rangeI:
  assumes \<open>qregister F\<close>
  assumes \<open>range (apply_qregister G) = commutant (range (apply_qregister F))\<close>
  shows \<open>qcomplements F G\<close>
proof (cases \<open>qregister G\<close>)
  case True
  have \<open>qregister_raw (apply_qregister F)\<close>
    using assms(1) by auto
  from complement_exists[OF this]
  have \<open>\<forall>\<^sub>\<tau> 'g::type = qregister_decomposition_basis F. qcomplements F G\<close>
  proof (rule with_type_mp)
    assume \<open>\<exists>G :: 'g qupdate \<Rightarrow> _. complements (apply_qregister F) G\<close>
    then obtain G' :: \<open>'g qupdate \<Rightarrow> _\<close> where compl: \<open>complements (apply_qregister F) G'\<close>
      by auto
    then have \<open>range G' = commutant (range (apply_qregister F))\<close>
      by (simp add: register_range_complement_commutant)
    with assms have \<open>range G' = range (apply_qregister G)\<close>
      by simp
    then have \<open>equivalent_registers (apply_qregister G) G'\<close>
      by (metis Laws_Complement_Quantum.complement_unique Laws_Quantum.equivalent_registers_register_right True compl qregister.rep_eq same_range_equivalent)
    with compl have \<open>complements (apply_qregister F) (apply_qregister G)\<close>
      using Laws_Quantum.equivalent_registers_sym equivalent_complements by blast
    then show \<open>qcomplements F G\<close>
      by (simp add: qcomplements.rep_eq)
  qed
  from this[cancel_with_type]
  show ?thesis 
    by -
next
  case False
  then have \<open>id_cblinfun \<notin> range (apply_qregister G)\<close>
    by (simp add: non_qregister)
  moreover have \<open>id_cblinfun \<in> commutant (range (apply_qregister F))\<close>
    by simp
  ultimately have False
    using assms by metis
  then show ?thesis
    by simp
qed

lemma z1:
  assumes F: \<open>qregister F\<close>
  assumes CF: \<open>QCOMPLEMENT (QREGISTER_of F) = QREGISTER_of G\<close>
  assumes G: \<open>qregister G\<close>
  shows \<open>qcomplements F G\<close>
  using F apply (rule qcomplements_via_rangeI)
  using assms(2)[THEN Rep_QREGISTER_inject[THEN iffD2]]
  by (simp add: QCOMPLEMENT.rep_eq QREGISTER_of.rep_eq F G)

definition tensor_vn (infixr "\<otimes>\<^sub>v\<^sub>N" 70) where
  \<open>tensor_vn X Y = commutant (commutant ((\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) ` X \<union> (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a) ` Y))\<close>

lemma von_neumann_algebra_adj_image: \<open>von_neumann_algebra X \<Longrightarrow> adj ` X = X\<close>
  by (auto simp: von_neumann_algebra_def intro!: image_eqI[where x=\<open>_*\<close>])

lemma von_neumann_algebra_tensor_vn:
  assumes \<open>von_neumann_algebra X\<close>
  assumes \<open>von_neumann_algebra Y\<close>
  shows \<open>von_neumann_algebra (X \<otimes>\<^sub>v\<^sub>N Y)\<close>
proof (rule von_neumann_algebraI)
  have \<open>adj ` (X \<otimes>\<^sub>v\<^sub>N Y) = commutant (commutant ((\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) ` adj ` X \<union> (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a) ` adj ` Y))\<close>
    by (simp add: tensor_vn_def commutant_adj image_image image_Un tensor_op_adjoint)
  also have \<open>\<dots> = commutant (commutant ((\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) ` X \<union> (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a) ` Y))\<close>
    using assms by (simp add: von_neumann_algebra_adj_image)
  also have \<open>\<dots> = X \<otimes>\<^sub>v\<^sub>N Y\<close>
    by (simp add: tensor_vn_def)
  finally show \<open>a* \<in> X \<otimes>\<^sub>v\<^sub>N Y\<close> if \<open>a \<in> X \<otimes>\<^sub>v\<^sub>N Y\<close> for a
    using that by blast
  show \<open>commutant (commutant (X \<otimes>\<^sub>v\<^sub>N Y)) \<subseteq> X \<otimes>\<^sub>v\<^sub>N Y\<close>
    by (simp add: tensor_vn_def)
qed

lemma tensor_vn_one_one[simp]: \<open>one_algebra \<otimes>\<^sub>v\<^sub>N one_algebra = one_algebra\<close>
  apply (simp add: tensor_vn_def one_algebra_def image_image
      tensor_op_scaleC_left tensor_op_scaleC_right)
  by (simp add: commutant_one_algebra commutant_UNIV flip: one_algebra_def)

lemma sandwich_swap_tensor_vn: \<open>sandwich swap_ell2 ` (X \<otimes>\<^sub>v\<^sub>N Y) = Y \<otimes>\<^sub>v\<^sub>N X\<close>
  by (simp add: tensor_vn_def sandwich_unitary_complement image_Un image_image Un_commute)

lemma tensor_vn_one_left: \<open>one_algebra \<otimes>\<^sub>v\<^sub>N X = (\<lambda>x. id_cblinfun \<otimes>\<^sub>o x) ` X\<close> if \<open>von_neumann_algebra X\<close>
proof -
  have \<open>one_algebra \<otimes>\<^sub>v\<^sub>N X = commutant
     (commutant ((\<lambda>a. id_cblinfun \<otimes>\<^sub>o a) ` X))\<close>
    apply (simp add: tensor_vn_def one_algebra_def image_image)
    by (metis (no_types, lifting) Un_commute Un_empty_right commutant_UNIV commutant_empty double_commutant_Un_right image_cong one_algebra_def tensor_id tensor_op_scaleC_left)
  also have \<open>\<dots> = (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a) ` commutant (commutant X)\<close>
    by (simp add: amplification_double_commutant_commute')
  also have \<open>\<dots> = (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a) ` X\<close>
    using that von_neumann_algebra_def by blast
  finally show ?thesis
    by -
qed
lemma tensor_vn_one_right: \<open>X \<otimes>\<^sub>v\<^sub>N one_algebra = (\<lambda>x. x \<otimes>\<^sub>o id_cblinfun) ` X\<close> if \<open>von_neumann_algebra X\<close>
proof -
  have \<open>X \<otimes>\<^sub>v\<^sub>N one_algebra = sandwich swap_ell2 ` (one_algebra \<otimes>\<^sub>v\<^sub>N X)\<close>
    by (simp add: sandwich_swap_tensor_vn)
  also have \<open>\<dots> = sandwich swap_ell2 ` (\<lambda>x. id_cblinfun \<otimes>\<^sub>o x) ` X\<close>
    by (simp add: tensor_vn_one_left that)
  also have \<open>\<dots> = (\<lambda>x. x \<otimes>\<^sub>o id_cblinfun) ` X\<close>
    by (simp add: image_image)
  finally show ?thesis
    by -
qed

lemma double_commutant_in_vn_algI: \<open>commutant (commutant X) \<subseteq> Y\<close>
  if \<open>von_neumann_algebra Y\<close> and \<open>X \<subseteq> Y\<close>
  by (metis commutant_antimono that(1) that(2) von_neumann_algebra_def)

lemma cblinfun_cinner_tensor_eqI:
  assumes \<open>\<And>\<psi> \<phi>. (\<psi> \<otimes>\<^sub>s \<phi>) \<bullet>\<^sub>C (A *\<^sub>V (\<psi> \<otimes>\<^sub>s \<phi>)) = (\<psi> \<otimes>\<^sub>s \<phi>) \<bullet>\<^sub>C (B *\<^sub>V (\<psi> \<otimes>\<^sub>s \<phi>))\<close>
  shows \<open>A = B\<close>
proof -
  define C where \<open>C = A - B\<close>
  from assms have assmC: \<open>(\<psi> \<otimes>\<^sub>s \<phi>) \<bullet>\<^sub>C (C *\<^sub>V (\<psi> \<otimes>\<^sub>s \<phi>)) = 0\<close> for \<psi> \<phi>
    by (simp add: C_def cblinfun.diff_left cinner_simps(3))

  have \<open>(x \<otimes>\<^sub>s y) \<bullet>\<^sub>C (C *\<^sub>V (z \<otimes>\<^sub>s w)) = 0\<close> for x y z w
  proof -
    define d e f g h j k l m n p q
      where defs: \<open>d = (x \<otimes>\<^sub>s y) \<bullet>\<^sub>C (C *\<^sub>V z \<otimes>\<^sub>s w)\<close>
        \<open>e = (z \<otimes>\<^sub>s y) \<bullet>\<^sub>C (C *\<^sub>V x \<otimes>\<^sub>s y)\<close>
        \<open>f = (x \<otimes>\<^sub>s w) \<bullet>\<^sub>C (C *\<^sub>V x \<otimes>\<^sub>s y)\<close>
        \<open>g = (z \<otimes>\<^sub>s w) \<bullet>\<^sub>C (C *\<^sub>V x \<otimes>\<^sub>s y)\<close>
        \<open>h = (x \<otimes>\<^sub>s y) \<bullet>\<^sub>C (C *\<^sub>V z \<otimes>\<^sub>s y)\<close>
        \<open>j = (x \<otimes>\<^sub>s w) \<bullet>\<^sub>C (C *\<^sub>V z \<otimes>\<^sub>s y)\<close>
        \<open>k = (z \<otimes>\<^sub>s w) \<bullet>\<^sub>C (C *\<^sub>V z \<otimes>\<^sub>s y)\<close>
        \<open>l = (z \<otimes>\<^sub>s w) \<bullet>\<^sub>C (C *\<^sub>V x \<otimes>\<^sub>s w)\<close>
        \<open>m = (x \<otimes>\<^sub>s y) \<bullet>\<^sub>C (C *\<^sub>V x \<otimes>\<^sub>s w)\<close>
        \<open>n = (z \<otimes>\<^sub>s y) \<bullet>\<^sub>C (C *\<^sub>V x \<otimes>\<^sub>s w)\<close>
        \<open>p = (z \<otimes>\<^sub>s y) \<bullet>\<^sub>C (C *\<^sub>V z \<otimes>\<^sub>s w)\<close>
        \<open>q = (x \<otimes>\<^sub>s w) \<bullet>\<^sub>C (C *\<^sub>V z \<otimes>\<^sub>s w)\<close>

    have constraint: \<open>cnj \<alpha> * e + cnj \<beta> * f + cnj \<beta> * cnj \<alpha> * g + \<alpha> * h + \<alpha> * cnj \<beta> * j +
          \<alpha> * cnj \<beta> * cnj \<alpha> * k + \<beta> * m + \<beta> * cnj \<alpha> * n + \<beta> * cnj \<beta> * cnj \<alpha> * l +
          \<beta> * \<alpha> * d + \<beta> * \<alpha> * cnj \<alpha> * p + \<beta> * \<alpha> * cnj \<beta> * q = 0\<close>
      (is \<open>?lhs = _\<close>) for \<alpha> \<beta>
    proof -
      from assms 
      have \<open>0 = ((x + \<alpha> *\<^sub>C z) \<otimes>\<^sub>s (y + \<beta> *\<^sub>C w)) \<bullet>\<^sub>C (C *\<^sub>V ((x + \<alpha> *\<^sub>C z) \<otimes>\<^sub>s (y + \<beta> *\<^sub>C w)))\<close>
        by (simp add: assmC)
      also have \<open>\<dots> = ?lhs\<close>
        apply (simp add: tensor_ell2_add1 tensor_ell2_add2 cinner_add_right cinner_add_left
            cblinfun.add_right tensor_ell2_scaleC1 tensor_ell2_scaleC2 semiring_class.distrib_left
            cblinfun.scaleC_right
            flip: add.assoc mult.assoc)
        apply (simp add: assmC)
        by (simp flip: defs)
      finally show ?thesis
        by simp
    qed

    have aux1: \<open>a = 0 \<Longrightarrow> b = 0 \<Longrightarrow> a + b = 0\<close> for a b :: complex
      by auto
    have aux2: \<open>a = 0 \<Longrightarrow> b = 0 \<Longrightarrow> a - b = 0\<close> for a b :: complex
      by auto
    have aux3: \<open>- (x * k) - x * j = x * (- k - j)\<close> for x k :: complex
      by (simp add: right_diff_distrib')
    have aux4: \<open>2 * a = 0 \<longleftrightarrow> a = 0\<close> for a :: complex
      by auto
    have aux5: \<open>8 = 2 * 2 * (2::complex)\<close>
      by simp

    from constraint[of 1 0]
    have 1: \<open>e + h = 0\<close>
      by simp
    from constraint[of \<i> 0]
    have 2: \<open>h = e\<close>
      by simp
    from 1 2
    have [simp]: \<open>e = 0\<close> \<open>h = 0\<close>
      by auto
    from constraint[of 0 1]
    have 3: \<open>f + m = 0\<close>
      by simp
    from constraint[of 0 \<i>]
    have 4: \<open>m = f\<close>
      by simp
    from 3 4
    have [simp]: \<open>m = 0\<close> \<open>f = 0\<close>
      by auto
    from constraint[of 1 1]
    have 5: \<open>g + j + k + n + l + d + p + q = 0\<close>
      by simp
    from constraint[of 1 \<open>-1\<close>]
    have 6: \<open>- g - j - k - n + l - d - p + q = 0\<close>
      by simp
    from aux1[OF 5 6]
    have 7: \<open>l + q = 0\<close>
      apply simp
      by (metis distrib_left_numeral mult_eq_0_iff zero_neq_numeral)
    from aux2[OF 5 7]
    have 8: \<open>g + j + k + n + d + p = 0\<close>
      by (simp add: algebra_simps)
    from constraint[of 1 \<i>]
    have 9: \<open>- (\<i> * g) - \<i> * j - \<i> * k + \<i> * n + l + \<i> * d + \<i> * p + q = 0\<close>
      by simp
    from constraint[of 1 \<open>-\<i>\<close>]
    have 10: \<open>\<i> * g + \<i> * j + \<i> * k - \<i> * n + l - \<i> * d - \<i> * p + q = 0\<close>
      by simp
    from aux2[OF 9 10]
    have 11: \<open>n + d + p - k - j - g = 0\<close>
      apply (simp add: aux3 flip: right_diff_distrib semiring_class.distrib_left distrib_left_numeral 
          del: mult_minus_right right_diff_distrib_numeral)
      by (simp add: algebra_simps)
    from aux2[OF 8 11]
    have 12: \<open>g + j + k = 0\<close>
      apply (simp add: aux3 flip: right_diff_distrib semiring_class.distrib_left distrib_left_numeral 
          del: mult_minus_right right_diff_distrib_numeral)
      by (simp add: algebra_simps)
    from aux1[OF 8 11]
    have 13: \<open>n + d + p = 0\<close>
      apply simp
      using 12 8 by fastforce
    from constraint[of \<i> 1]
    have 14: \<open>\<i> * j - \<i> * g + k - \<i> * n - \<i> * l + \<i> * d + p + \<i> * q = 0\<close>
      by simp
    from constraint[of \<i> \<open>-1\<close>]
    have 15: \<open>\<i> * g - \<i> * j - k + \<i> * n - \<i> * l - \<i> * d - p + \<i> * q = 0\<close>
      by simp
    from aux1[OF 14 15]
    have [simp]: \<open>q = l\<close>
      by simp
    from 7
    have [simp]: \<open>q = 0\<close> \<open>l = 0\<close>
      by auto
    from 14
    have 16: \<open>\<i> * j - \<i> * g + k - \<i> * n + \<i> * d + p = 0\<close>
      by simp
    from constraint[of \<open>-\<i>\<close> 1]
    have 17: \<open>\<i> * g - \<i> * j + k + \<i> * n - \<i> * d + p = 0\<close>
      by simp
    from aux1[OF 16 17]
    have [simp]: \<open>k = - p\<close>
      apply simp
      by (metis add_eq_0_iff2 add_scale_eq_noteq is_num_normalize(8) mult_2 zero_neq_numeral)
    from aux2[OF 16 17]
    have 18: \<open>j + d - n - g = 0\<close>
      apply (simp add: aux3 flip: right_diff_distrib semiring_class.distrib_left distrib_left_numeral 
          del: mult_minus_right right_diff_distrib_numeral)
      by (simp add: algebra_simps)
    from constraint[of \<open>-\<i>\<close> 1]
    have 19: \<open>\<i> * g - \<i> * j + \<i> * n - \<i> * d = 0\<close>
      by (simp add: algebra_simps)
    from constraint[of \<open>-\<i>\<close> \<open>-1\<close>]
    have 20: \<open>\<i> * j - \<i> * g - \<i> * n + \<i> * d = 0\<close>
      by (simp add: algebra_simps)
    from constraint[of \<i> \<i>]
    have 21: \<open>j - g + n - d + 2 * \<i> * p = 0\<close>
      by (simp add: algebra_simps)
    from constraint[of \<i> \<open>-\<i>\<close>]
    have 22: \<open>g - j - n + d - 2 * \<i> * p = 0\<close>
      by (simp add: algebra_simps)
    from constraint[of 2 1]
    have 23: \<open>g + j + n + d = 0\<close>
      apply simp
      by (metis "12" "13" \<open>k = - p\<close> add_eq_0_iff2 is_num_normalize(1))
    from aux2[OF 23 18]
    have [simp]: \<open>g = - n\<close>
      apply simp
      by (simp only: aux4 add_eq_0_iff2 flip: distrib_left)
    from 23
    have [simp]: \<open>j = - d\<close>
      by (simp add: add_eq_0_iff2)
    from constraint[of 2 \<i>]
    have 24: \<open>2 * p + d + n = 0\<close>
      apply simp
      apply (simp only: aux5 aux4 add_eq_0_iff2 flip: distrib_left)
      by (smt (z3) "13" add.commute add_cancel_right_left add_eq_0_iff2 complex_i_not_zero eq_num_simps(6) more_arith_simps(8) mult_2 mult_right_cancel no_zero_divisors num.distinct(1) numeral_Bit0 numeral_eq_iff)
    from aux2[OF 24 13]
    have [simp]: \<open>p = 0\<close>
      by simp
    then have [simp]: \<open>k = 0\<close>
      by auto
    from 12
    have \<open>g = - j\<close>
      by simp
    from 21
    have \<open>d = - g\<close>
      by auto

    show \<open>d = 0\<close>
      using refl[of d]
      apply (subst (asm) \<open>d = - g\<close>)
      apply (subst (asm) \<open>g = - j\<close>)
      apply (subst (asm) \<open>j = - d\<close>)
      by simp
  qed
  then show ?thesis
    by (auto intro!: equal_ket cinner_ket_eqI
        simp: C_def cblinfun.diff_left cinner_diff_right
        simp flip: tensor_ell2_ket)
qed

lemma von_neumann_algebra_compose:
  assumes \<open>von_neumann_algebra M\<close>
  assumes \<open>x \<in> M\<close> and \<open>y \<in> M\<close>
  shows \<open>x o\<^sub>C\<^sub>L y \<in> M\<close>
  using assms apply (auto simp: von_neumann_algebra_def commutant_def)
  by (metis (no_types, lifting) assms(1) commutant_mult von_neumann_algebra_def)

lemma von_neumann_algebra_id:
  assumes \<open>von_neumann_algebra M\<close>
  shows \<open>id_cblinfun \<in> M\<close>
  using assms by (auto simp: von_neumann_algebra_def)

(* TODO: replace *) thm sqrt_op_square (* with this *)
lemma sqrt_op_square[simp]: \<open>a \<ge> 0 \<Longrightarrow> sqrt_op a o\<^sub>C\<^sub>L sqrt_op a = a\<close>
  by (metis positive_hermitianI sqrt_op_pos sqrt_op_square)

definition cstar_algebra where \<open>cstar_algebra A \<longleftrightarrow> csubspace A \<and> (\<forall>x\<in>A. \<forall>y\<in>A. x o\<^sub>C\<^sub>L y \<in> A) \<and> (\<forall>x\<in>A. x* \<in> A) \<and> closed A\<close>

lemma sqrt_op_in_cstar_algebra:
  assumes \<open>cstar_algebra A\<close>
  assumes \<open>id_cblinfun \<in> A\<close>
  assumes \<open>a \<in> A\<close>
  shows \<open>sqrt_op a \<in> A\<close>
proof -
  have *: \<open>cblinfun_power a n \<in> A\<close> for n
    apply (induction n)
    using assms by (auto simp: cblinfun_power_Suc cstar_algebra_def)
  have \<open>sqrt_op a \<in> closure (cspan (range (cblinfun_power a)))\<close>
    by (rule sqrt_op_in_closure)
  also have \<open>\<dots> \<subseteq> closure (cspan A)\<close>
    apply (intro closure_mono complex_vector.span_mono)
    by (auto intro!: * )
  also have \<open>\<dots> = closure A\<close>
    using \<open>cstar_algebra A\<close>
    apply (simp add: cstar_algebra_def)
    by (metis closure_closed complex_vector.span_eq_iff)
  also have \<open>\<dots> = A\<close>
    using \<open>cstar_algebra A\<close>
    by (simp add: cstar_algebra_def)
  finally show \<open>sqrt_op a \<in> A\<close>
    by -
qed

lemma cstar_decompose_four_unitaries:
  \<comment> \<open>@{cite takesaki}, Proposition I.4.9\<close>
  fixes M :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'a::chilbert_space) set\<close>
  assumes \<open>cstar_algebra M\<close>
  assumes [simp]: \<open>id_cblinfun \<in> M\<close>
  assumes \<open>x \<in> M\<close>
  shows \<open>\<exists>a1 a2 a3 a4 u1 u2 u3 u4. u1 \<in> M \<and> u2 \<in> M \<and> u3 \<in> M \<and> u4 \<in> M
              \<and> unitary u1 \<and> unitary u2 \<and> unitary u3 \<and> unitary u4
              \<and> x = a1 *\<^sub>C u1 + a2 *\<^sub>C u2 + a3 *\<^sub>C u3 + a4 *\<^sub>C u4\<close>
proof -
  have herm: \<open>\<exists>u1 u2 a1 a2. u1 \<in> M \<and> u2 \<in> M \<and> unitary u1 \<and> unitary u2 \<and> h = a1 *\<^sub>C u1 + a2 *\<^sub>C u2\<close> 
    if \<open>h \<in> M\<close> and \<open>h* = h\<close> for h
  proof (cases \<open>h = 0\<close>)
    case True
    show ?thesis 
      apply (rule exI[of _ id_cblinfun]; rule exI[of _  id_cblinfun])
      apply (rule exI[of _ 0]; rule exI[of _ 0])
      by (simp add: True)
  next
    case False
    define h' where \<open>h' = sgn h\<close>
    from False have [simp]: \<open>h' \<in> M\<close> and [simp]: \<open>h'* = h'\<close> and \<open>norm h' = 1\<close>
        using \<open>cstar_algebra M\<close>
        by (auto simp: h'_def sgn_cblinfun_def complex_vector.subspace_scale norm_inverse that
            cstar_algebra_def)
    define u where \<open>u = h' + imaginary_unit *\<^sub>C sqrt_op (id_cblinfun - (h' o\<^sub>C\<^sub>L h'))\<close>
    have [simp]: \<open>u \<in> M\<close>
    proof -
      have \<open>id_cblinfun - h' o\<^sub>C\<^sub>L h' \<in> M\<close>
        using \<open>cstar_algebra M\<close>
        by (simp add: complex_vector.subspace_diff cstar_algebra_def)
      then have \<open>sqrt_op (id_cblinfun - h' o\<^sub>C\<^sub>L h') \<in> M\<close>
        apply (rule sqrt_op_in_cstar_algebra[rotated -1])
        using \<open>cstar_algebra M\<close> by auto
      then show ?thesis
        using \<open>cstar_algebra M\<close>
        by (auto simp: u_def cstar_algebra_def intro!: complex_vector.subspace_add complex_vector.subspace_scale)
    qed
    then have [simp]: \<open>u* \<in> M\<close>
      using \<open>cstar_algebra M\<close>
      by (simp add: cstar_algebra_def)
    have *: \<open>h' o\<^sub>C\<^sub>L h' \<le> id_cblinfun\<close>
      sorry
    have **: \<open>h' o\<^sub>C\<^sub>L sqrt_op (id_cblinfun - h' o\<^sub>C\<^sub>L h') = sqrt_op (id_cblinfun - h' o\<^sub>C\<^sub>L h') o\<^sub>C\<^sub>L h'\<close>
      apply (rule sqrt_op_commute[symmetric])
      by (auto simp: * cblinfun_compose_minus_right cblinfun_compose_minus_left cblinfun_compose_assoc)
    have [simp]: \<open>unitary u\<close>
      by (auto intro!: unitary_def[THEN iffD2] simp: * ** u_def cblinfun_compose_add_right
          cblinfun_compose_add_left adj_plus cblinfun_compose_minus_left cblinfun_compose_minus_right
          positive_hermitianI[symmetric] sqrt_op_pos scaleC_diff_right scaleC_add_right)
    have [simp]: \<open>u + u* = h' + h'\<close>
      by (simp add: * u_def adj_plus positive_hermitianI[symmetric] sqrt_op_pos)
    show ?thesis
      apply (rule exI[of _ u]; rule exI[of _ \<open>u*\<close>])
      apply (rule exI[of _ \<open>of_real (norm h) / 2\<close>]; rule exI[of _ \<open>of_real (norm h) / 2\<close>])
      by (auto simp flip: scaleC_add_right scaleC_2 simp: h'_def)
  qed
  obtain a1 a2 u1 u2 where \<open>u1 \<in> M\<close> and \<open>u2 \<in> M\<close> and \<open>unitary u1\<close> and \<open>unitary u2\<close> and decomp1: \<open>x + x* = a1 *\<^sub>C u1 + a2 *\<^sub>C u2\<close>
    apply atomize_elim
    apply (rule herm)
    using \<open>cstar_algebra M\<close>
    by (simp_all add: \<open>x \<in> M\<close> complex_vector.subspace_add adj_plus cstar_algebra_def)
  obtain a3 a4 u3 u4 where \<open>u3 \<in> M\<close> and \<open>u4 \<in> M\<close> and \<open>unitary u3\<close> and \<open>unitary u4\<close> 
    and decomp2: \<open>\<i> *\<^sub>C (x - x*) = a3 *\<^sub>C u3 + a4 *\<^sub>C u4\<close>
    apply atomize_elim
    apply (rule herm)
    using \<open>cstar_algebra M\<close>
    by (simp_all add: \<open>x \<in> M\<close> adj_minus complex_vector.subspace_diff complex_vector.subspace_scale cstar_algebra_def flip: scaleC_minus_right)
  have \<open>x = (1/2) *\<^sub>C (x + x*) + (-\<i>/2) *\<^sub>C (\<i> *\<^sub>C (x - x*))\<close>
    by (simp add: scaleC_add_right scaleC_diff_right flip: scaleC_add_left)
  also have \<open>\<dots> = (a1 / 2) *\<^sub>C u1 + (a2 / 2) *\<^sub>C u2 + (- \<i> * a3 / 2) *\<^sub>C u3 + (- \<i> * a4 / 2) *\<^sub>C u4\<close>
    apply (simp only: decomp1 decomp2)
    by (simp add: scaleC_add_right scaleC_diff_right)
  finally show ?thesis
    using \<open>u1 \<in> M\<close> \<open>u2 \<in> M\<close> \<open>u3 \<in> M\<close> \<open>u4 \<in> M\<close>
      \<open>unitary u1\<close> \<open>unitary u2\<close> \<open>unitary u3\<close> \<open>unitary u4\<close>
    by blast
qed

(* lemma xxx:
  \<comment> \<open>@{cite takesaki}, Proposition II.3.10\<close>
  fixes M :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a) set\<close> and e :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  assumes \<open>von_neumann_algebra M\<close>
  assumes \<open>isometry (e* )\<close>
  assumes \<open>e* o\<^sub>C\<^sub>L e \<in> M\<close>
  shows \<open>von_neumann_algebra (sandwich e ` M)\<close>
    and \<open>von_neumann_algebra (sandwich e ` commutant M)\<close>
    and \<open>commutant (sandwich e ` M) = sandwich e ` commutant M\<close>
proof -
  have \<open>von_neumann_algebra (sandwich e ` M)\<close>
  proof (unfold von_neumann_algebra_def_sot, intro conjI ballI)
    

  by - *)

(* lemma commutant_tensor_vn:
  \<comment> \<open>@{cite takesaki}, Theorem IV.5.9\<close>
  assumes \<open>von_neumann_algebra M\<close>
  assumes \<open>von_neumann_algebra N\<close>
  shows \<open>commutant (tensor_vn M N) = commutant M \<otimes>\<^sub>v\<^sub>N commutant N\<close>
proof -
  write commutant (\<open>_''\<close> [120] 120)
       \<open>Notation \<^term>\<open>M '\<close> for \<^term>\<open>commutant M\<close>\<close>
  write id_cblinfun (\<open>\<one>\<close>)

  have 1: \<open>x o\<^sub>C\<^sub>L y = y o\<^sub>C\<^sub>L x\<close> if \<open>x \<in> (M ' \<otimes>\<^sub>v\<^sub>N N ')'\<close> and \<open>y \<in> (M \<otimes>\<^sub>v\<^sub>N N)'\<close> for x y
  proof (intro cblinfun_cinner_tensor_eqI)
    fix \<xi> :: \<open>'a ell2\<close> and \<eta> :: \<open>'b ell2\<close>
    define e where \<open>e = Proj (ccspan ((\<lambda>m. m *\<^sub>V \<xi>) ` M))\<close>
    define f where \<open>f = Proj (ccspan ((\<lambda>n. n *\<^sub>V \<eta>) ` N))\<close>
    have \<open>e \<in> M '\<close> and \<open>e *\<^sub>S \<top> \<noteq> 0\<close>
      if e_def: \<open>e = Proj (ccspan ((\<lambda>m. m *\<^sub>V \<xi>) ` M))\<close> and \<open>von_neumann_algebra M\<close>
      for e M and \<xi> :: \<open>'x ell2\<close>
    proof (rule commutant_memberI)
      fix y assume \<open>y \<in> M\<close>
      then have \<open>y* \<in> M\<close>
        by (metis that(2) imageI von_neumann_algebra_adj_image)
      have *: \<open>e o\<^sub>C\<^sub>L y o\<^sub>C\<^sub>L e = y o\<^sub>C\<^sub>L e\<close> if \<open>y \<in> M\<close> for y
      proof -
        have \<open>y *\<^sub>S e *\<^sub>S \<top> = y *\<^sub>S ccspan ((\<lambda>m. m *\<^sub>V \<xi>) ` M)\<close>
          by (simp add: e_def)
        also have \<open>\<dots> = ccspan ((\<lambda>x. y *\<^sub>V x *\<^sub>V \<xi>) ` M)\<close>
          by (simp add: cblinfun_image_ccspan image_image)
        also have \<open>\<dots> \<le> ccspan ((\<lambda>m. m *\<^sub>V \<xi>) ` M)\<close>
          using von_neumann_algebra_compose[OF \<open>von_neumann_algebra M\<close> \<open>y \<in> M\<close>]
          by (auto intro!: ccspan_mono simp: simp flip: cblinfun_apply_cblinfun_compose)
        finally have \<open>e o\<^sub>C\<^sub>L (y o\<^sub>C\<^sub>L e) = y o\<^sub>C\<^sub>L e\<close>
          apply (subst e_def)
          by (auto simp: cblinfun_compose_image Proj_compose_cancelI)
        then show ?thesis
          by (simp add: cblinfun_compose_assoc)
      qed
      have \<open>e o\<^sub>C\<^sub>L y = (y* o\<^sub>C\<^sub>L e)*\<close>
        by (simp add: e_def adj_Proj)
      also have \<open>\<dots> = (e o\<^sub>C\<^sub>L y* o\<^sub>C\<^sub>L e)*\<close>
        by (auto simp: * \<open>y* \<in> M\<close>)
      also have \<open>\<dots> = e o\<^sub>C\<^sub>L y o\<^sub>C\<^sub>L e\<close>
        by (simp add: e_def adj_Proj cblinfun_compose_assoc)
      also have \<open>\<dots> = y o\<^sub>C\<^sub>L e\<close>
        by (auto simp: * \<open>y \<in> M\<close>)
      finally show \<open>e o\<^sub>C\<^sub>L y = y o\<^sub>C\<^sub>L e\<close>
        by -
    next
      have \<open>\<xi> \<in> space_as_set (e *\<^sub>S \<top>)\<close>
        by (auto intro!: ccspan_superset' image_eqI[where x=id_cblinfun] von_neumann_algebra_id 
            simp: e_def \<open>von_neumann_algebra M\<close>)
      moreover have \<open>\<xi> \<noteq> 0\<close>
        sorry
      ultimately show \<open>e *\<^sub>S \<top> \<noteq> 0\<close>
        by auto
    qed
    from this[OF e_def assms(1)] and this[OF f_def assms(2)]
    have eM': \<open>e \<in> M '\<close> and e0: \<open>e *\<^sub>S \<top> \<noteq> 0\<close> and fN': \<open>f \<in> N '\<close> and f0: \<open>f *\<^sub>S \<top> \<noteq> 0\<close>
      by -
    let ?goal = \<open>(\<xi> \<otimes>\<^sub>s \<eta>) \<bullet>\<^sub>C ((x o\<^sub>C\<^sub>L y) *\<^sub>V (\<xi> \<otimes>\<^sub>s \<eta>)) = (\<xi> \<otimes>\<^sub>s \<eta>) \<bullet>\<^sub>C ((y o\<^sub>C\<^sub>L x) *\<^sub>V (\<xi> \<otimes>\<^sub>s \<eta>))\<close>

    from ccsubspace_as_whole_type[OF e0]
    have \<open>\<forall>\<^sub>\<tau> 'e::type = some_chilbert_basis_of (e *\<^sub>S \<top>). ?goal\<close>
    proof (rule with_type_mp)
      assume \<open>\<exists>Ue :: 'e ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2. isometry Ue \<and> Ue *\<^sub>S \<top> = e *\<^sub>S \<top>\<close>
      then obtain Ue :: \<open>'e ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close> where \<open>isometry Ue\<close> and \<open>Ue *\<^sub>S \<top> = e *\<^sub>S \<top>\<close>
        by auto
      from ccsubspace_as_whole_type[OF f0]
      have \<open>\<forall>\<^sub>\<tau> 'f::type = some_chilbert_basis_of (f *\<^sub>S \<top>). ?goal\<close>
      proof (rule with_type_mp)
        assume \<open>\<exists>Uf :: 'f ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2. isometry Uf \<and> Uf *\<^sub>S \<top> = f *\<^sub>S \<top>\<close>
        then obtain Uf :: \<open>'f ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close> where \<open>isometry Uf\<close> and \<open>Uf *\<^sub>S \<top> = f *\<^sub>S \<top>\<close>
          by auto
        show ?goal
          by -
      qed
      from this[cancel_with_type]
      show ?goal
        by -
    qed
    from this[cancel_with_type]
    show ?goal
      by -
  qed
  have 2: \<open>M \<otimes>\<^sub>v\<^sub>N N \<subseteq> (M ' \<otimes>\<^sub>v\<^sub>N N ')'\<close>
  proof -
    have \<open>((\<lambda>a. a \<otimes>\<^sub>o \<one>) ` M \<union> (\<otimes>\<^sub>o) \<one> ` N) \<subseteq> ((\<lambda>a. a \<otimes>\<^sub>o \<one>) ` M ' \<union> (\<otimes>\<^sub>o) \<one> ` N ')'\<close>
      by (auto intro!: commutant_memberI simp: comp_tensor_op commutant_def)
    also have \<open>\<dots> = (M ' \<otimes>\<^sub>v\<^sub>N N ')'\<close>
      by (simp add: tensor_vn_def)
    finally show ?thesis
      apply (subst tensor_vn_def)
      apply (rule double_commutant_in_vn_algI)
      by (auto intro!: von_neumann_algebra_commutant von_neumann_algebra_tensor_vn assms)
  qed
  have 3: \<open>M ' \<otimes>\<^sub>v\<^sub>N N ' \<subseteq> (M \<otimes>\<^sub>v\<^sub>N N)'\<close>
  proof -
    have \<open>((\<lambda>a. a \<otimes>\<^sub>o \<one>) ` M ' \<union> (\<otimes>\<^sub>o) \<one> ` N ') \<subseteq> ((\<lambda>a. a \<otimes>\<^sub>o \<one>) ` M \<union> (\<otimes>\<^sub>o) \<one> ` N)'\<close>
      by (auto intro!: commutant_memberI simp: comp_tensor_op commutant_def)
    also have \<open>\<dots> = (M \<otimes>\<^sub>v\<^sub>N N)'\<close>
      by (simp add: tensor_vn_def)
    finally show ?thesis
      apply (subst tensor_vn_def)
      apply (rule double_commutant_in_vn_algI)
      by (auto intro!: von_neumann_algebra_commutant von_neumann_algebra_tensor_vn assms)
  qed
  from 1 2 3 show ?thesis
    by (smt (verit) Un_Int_assoc_eq Un_absorb assms(1) assms(2) basic_trans_rules(24) commutant_memberI inf.absorb_iff1 subset_Un_eq subset_iff sup.absorb_iff1 von_neumann_algebra_commutant von_neumann_algebra_commutant von_neumann_algebra_def von_neumann_algebra_tensor_vn)
qed *)

lemma commutant_cspan: \<open>commutant (cspan A) = commutant A\<close>
  by (meson basic_trans_rules(24) commutant_antimono complex_vector.span_superset cspan_in_double_commutant dual_order.trans)

lemma cspan_compose_closed:
  assumes \<open>\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> a o\<^sub>C\<^sub>L b \<in> A\<close>
  assumes \<open>a \<in> cspan A\<close> and \<open>b \<in> cspan A\<close>
  shows \<open>a o\<^sub>C\<^sub>L b \<in> cspan A\<close>
proof -
  from \<open>a \<in> cspan A\<close>
  obtain F f where \<open>finite F\<close> and \<open>F \<subseteq> A\<close> and a_def: \<open>a = (\<Sum>x\<in>F. f x *\<^sub>C x)\<close>
    by (smt (verit, del_insts) complex_vector.span_explicit mem_Collect_eq)
  from \<open>b \<in> cspan A\<close>
  obtain G g where \<open>finite G\<close> and \<open>G \<subseteq> A\<close> and b_def: \<open>b = (\<Sum>x\<in>G. g x *\<^sub>C x)\<close>
    by (smt (verit, del_insts) complex_vector.span_explicit mem_Collect_eq)
  have \<open>a o\<^sub>C\<^sub>L b = (\<Sum>(x,y)\<in>F\<times>G. (f x *\<^sub>C x) o\<^sub>C\<^sub>L (g y *\<^sub>C y))\<close>
    apply (simp add: a_def b_def cblinfun_compose_sum_left)
    by (auto intro!: sum.cong simp add: cblinfun_compose_sum_right scaleC_sum_right sum.cartesian_product case_prod_beta)
  also have \<open>\<dots> = (\<Sum>(x,y)\<in>F\<times>G. (f x * g y) *\<^sub>C (x o\<^sub>C\<^sub>L y))\<close>
    by (metis (no_types, opaque_lifting) cblinfun_compose_scaleC_left cblinfun_compose_scaleC_right scaleC_scaleC)
  also have \<open>\<dots> \<in> cspan A\<close>
    using assms \<open>G \<subseteq> A\<close> \<open>F \<subseteq> A\<close>
    apply (auto intro!: complex_vector.span_sum complex_vector.span_scale 
        simp: complex_vector.span_clauses)
    using complex_vector.span_clauses(1) by blast
  finally show ?thesis
    by -
qed

lemma cspan_adj_closed:
  assumes \<open>\<And>a. a \<in> A \<Longrightarrow> a* \<in> A\<close>
  assumes \<open>a \<in> cspan A\<close>
  shows \<open>a* \<in> cspan A\<close>
proof -
  from \<open>a \<in> cspan A\<close>
  obtain F f where \<open>finite F\<close> and \<open>F \<subseteq> A\<close> and \<open>a = (\<Sum>x\<in>F. f x *\<^sub>C x)\<close>
    by (smt (verit, del_insts) complex_vector.span_explicit mem_Collect_eq)
  then have \<open>a* = (\<Sum>x\<in>F. cnj (f x) *\<^sub>C x*)\<close>
    by (auto simp: sum_adj)
  also have \<open>\<dots> \<in> cspan A\<close>
    using assms \<open>F \<subseteq> A\<close>
    by (auto intro!: complex_vector.span_sum complex_vector.span_scale simp: complex_vector.span_clauses)
  finally show ?thesis
    by -
qed

lemma double_commutant_theorem_span:
  fixes A :: \<open>('a::{chilbert_space} \<Rightarrow>\<^sub>C\<^sub>L 'a) set\<close>
  assumes mult: \<open>\<And>a a'. a \<in> A \<Longrightarrow> a' \<in> A \<Longrightarrow> a o\<^sub>C\<^sub>L a' \<in> A\<close>
  assumes id: \<open>id_cblinfun \<in> A\<close>
  assumes adj: \<open>\<And>a. a \<in> A \<Longrightarrow> a* \<in> A\<close>
  shows \<open>commutant (commutant A) = cstrong_operator_topology closure_of (cspan A)\<close>
proof -
  have \<open>commutant (commutant A) = commutant (commutant (cspan A))\<close>
    by (simp add: commutant_cspan)
  also have \<open>\<dots> = cstrong_operator_topology closure_of (cspan A)\<close>
    apply (rule double_commutant_theorem)
    using assms
    apply (auto simp: cspan_compose_closed cspan_adj_closed)
    using complex_vector.span_clauses(1) by blast
  finally show ?thesis
    by -
qed

lemma double_commutant_grows': \<open>x \<in> X \<Longrightarrow> x \<in> commutant (commutant X)\<close>
  using double_commutant_grows by blast

lemma tensor_vn_UNIV[simp]: \<open>UNIV \<otimes>\<^sub>v\<^sub>N UNIV = (UNIV :: (('a\<times>'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L _) set)\<close>
proof -
  have \<open>(UNIV \<otimes>\<^sub>v\<^sub>N UNIV :: (('a\<times>'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L _) set) = 
        commutant (commutant (range (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) \<union> range (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a)))\<close> (is \<open>_ = ?rhs\<close>)
    by (simp add: tensor_vn_def commutant_cspan)
  also have \<open>\<dots> \<supseteq> commutant (commutant {a \<otimes>\<^sub>o b |a b. True})\<close> (is \<open>_ \<supseteq> \<dots>\<close>)
  proof (rule double_commutant_in_vn_algI)
    show vn: \<open>von_neumann_algebra ?rhs\<close>
      by (metis calculation von_neumann_algebra_UNIV von_neumann_algebra_tensor_vn)
    show \<open>{a \<otimes>\<^sub>o b |(a :: 'a ell2 \<Rightarrow>\<^sub>C\<^sub>L _) (b :: 'b ell2 \<Rightarrow>\<^sub>C\<^sub>L _). True} \<subseteq> ?rhs\<close>
    proof (rule subsetI)
      fix x :: \<open>('a \<times> 'b) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'b) ell2\<close>
      assume \<open>x \<in> {a \<otimes>\<^sub>o b |a b. True}\<close>
      then obtain a b where \<open>x = a \<otimes>\<^sub>o b\<close>
        by auto
      then have \<open>x = (a \<otimes>\<^sub>o id_cblinfun) o\<^sub>C\<^sub>L (id_cblinfun \<otimes>\<^sub>o b)\<close>
        by (simp add: comp_tensor_op)
      also have \<open>\<dots> \<in> ?rhs\<close>
      proof -
        have \<open>a \<otimes>\<^sub>o id_cblinfun \<in> ?rhs\<close>
          by (auto intro!: double_commutant_grows')
        moreover have \<open>id_cblinfun \<otimes>\<^sub>o b \<in> ?rhs\<close>
          by (auto intro!: double_commutant_grows')
        ultimately show ?thesis
          using commutant_mult by blast
      qed
      finally show \<open>x \<in> ?rhs\<close>
        by -
    qed
  qed
  also have \<open>\<dots> = cstrong_operator_topology closure_of (cspan {a \<otimes>\<^sub>o b |a b. True})\<close>
    apply (rule double_commutant_theorem_span)
      apply (auto simp: comp_tensor_op tensor_op_adjoint)
    using tensor_id[symmetric] by blast+
  also have \<open>\<dots> = UNIV\<close>
    using tensor_op_dense by blast
  finally show ?thesis
    by auto
qed

lemma Rep_QREGISTER_pair_fst_snd:
  \<open>Rep_QREGISTER (QREGISTER_pair (QREGISTER_chain qFst F) (QREGISTER_chain qSnd G))
      = tensor_vn (Rep_QREGISTER F) (Rep_QREGISTER G)\<close>
  by (simp add: QREGISTER_pair.rep_eq QREGISTER_chain.rep_eq apply_qregister_fst apply_qregister_snd tensor_vn_def)

(* TODO: Just add an assumption and a comment that the assumption is not strictly necessary by Takesaki? *)
lemma y2:
  \<open>QCOMPLEMENT (QREGISTER_pair (QREGISTER_chain qFst F) (QREGISTER_chain qSnd G))
    = QREGISTER_pair (QREGISTER_chain qFst (QCOMPLEMENT F)) (QREGISTER_chain qSnd (QCOMPLEMENT G))\<close>
  apply (rule Rep_QREGISTER_inject[THEN iffD1])
  apply (simp add: QCOMPLEMENT.rep_eq Rep_QREGISTER_pair_fst_snd)
  apply (subst commutant_tensor_vn)
  using Rep_QREGISTER Rep_QREGISTER
  by (force simp add: valid_qregister_range_def)+

lemma QREGISTER_chain_fst_top[simp]: \<open>QREGISTER_chain qFst \<top> = QREGISTER_fst\<close>
  apply (rule Rep_QREGISTER_inject[THEN iffD1])
  by (simp add: QREGISTER_chain.rep_eq QREGISTER_fst.rep_eq top_QREGISTER.rep_eq
      apply_qregister_fst)

lemma QREGISTER_chain_snd_top[simp]: \<open>QREGISTER_chain qSnd \<top> = QREGISTER_snd\<close>
  apply (rule Rep_QREGISTER_inject[THEN iffD1])
  by (simp add: QREGISTER_chain.rep_eq QREGISTER_snd.rep_eq top_QREGISTER.rep_eq
      apply_qregister_snd)

lemma QCOMPLEMENT_top[simp]: \<open>QCOMPLEMENT \<top> = \<bottom>\<close>
  apply (rule Rep_QREGISTER_inject[THEN iffD1])
  by (simp add: QCOMPLEMENT.rep_eq top_QREGISTER.rep_eq bot_QREGISTER.rep_eq
      commutant_UNIV one_algebra_def)

lemma QCOMPLEMENT_bot[simp]: \<open>QCOMPLEMENT \<bottom> = \<top>\<close>
  apply (rule Rep_QREGISTER_inject[THEN iffD1])
  by (simp add: QCOMPLEMENT.rep_eq top_QREGISTER.rep_eq bot_QREGISTER.rep_eq
      commutant_one_algebra)

lemma y1:
  \<open>QCOMPLEMENT (QREGISTER_pair QREGISTER_fst (QREGISTER_chain qSnd F))
    = QREGISTER_chain qSnd (QCOMPLEMENT F)\<close>
  using y2[where F=\<top> and G=F]
  by simp

lemma y3:
  \<open>QCOMPLEMENT (QREGISTER_pair (QREGISTER_chain qFst F) QREGISTER_snd)
    = QREGISTER_chain qFst (QCOMPLEMENT F)\<close>
  using y2[where F=F and G=\<top>]
  by simp

lemma QCOMPLEMENT_fst: \<open>QCOMPLEMENT QREGISTER_fst = QREGISTER_snd\<close>
  apply (rule Rep_QREGISTER_inject[THEN iffD1])
  by (simp add: QCOMPLEMENT.rep_eq QREGISTER_snd.rep_eq QREGISTER_fst.rep_eq commutant_tensor1)

lemma QCOMPLEMENT_snd: \<open>QCOMPLEMENT QREGISTER_snd = QREGISTER_fst\<close>
  apply (rule Rep_QREGISTER_inject[THEN iffD1])
  by (simp add: QCOMPLEMENT.rep_eq QREGISTER_snd.rep_eq QREGISTER_fst.rep_eq commutant_tensor1')

lemma QCOMPLEMENT_twice: \<open>QCOMPLEMENT (QCOMPLEMENT F) = F\<close>
  apply (rule Rep_QREGISTER_inject[THEN iffD1])
  using Rep_QREGISTER
  by (auto simp: QCOMPLEMENT.rep_eq valid_qregister_range_def von_neumann_algebra_def)

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


