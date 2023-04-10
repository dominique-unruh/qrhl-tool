theory Scratch
  imports QRHL
 (* "HOL-ex.Sketch_and_Explore" *) 
(* "HOL-Eisbach.Eisbach" *)
(* QRHL_Operations  *)
begin

no_notation eq_closure_of ("closure'_of\<index>")

ML "open Prog_Variables"


lemma QCOMPLEMENT_twice: \<open>QCOMPLEMENT (QCOMPLEMENT F) = F\<close>
  apply (rule Rep_QREGISTER_inject[THEN iffD1])
  using Rep_QREGISTER
  by (auto simp: uminus_QREGISTER.rep_eq valid_qregister_range_def von_neumann_algebra_def)

lemma QCOMPLEMENT_antimono: \<open>QCOMPLEMENT F \<ge> QCOMPLEMENT G\<close> if \<open>F \<le> G\<close>
  using that apply transfer
  by (metis commutant_antimono)

lemma QREGISTER_pair_valid_qregister_range_hull:
  \<open>Rep_QREGISTER (QREGISTER_pair F G) = valid_qregister_range hull (Rep_QREGISTER F \<union> Rep_QREGISTER G)\<close>
  apply (simp add: sup_QREGISTER.rep_eq)
  apply (subst double_commutant_hull')
  using Rep_QREGISTER unfolding valid_qregister_range_def von_neumann_algebra_def by auto

(* TODO: also for CREGISTER *)
instantiation QREGISTER :: (type) semilattice_sup begin
instance
proof intro_classes
  fix x y z :: \<open>'a QREGISTER\<close>
  show \<open>x \<le> x \<squnion> y\<close>
    apply transfer
    by (meson Un_subset_iff double_commutant_grows)
  show \<open>y \<le> x \<squnion> y\<close>
    apply transfer
    by (meson Un_subset_iff double_commutant_grows)
  show \<open>y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x\<close>
    apply transfer
    apply auto
    by (meson double_commutant_in_vn_algI le_sup_iff subsetD valid_qregister_range_def)
qed
end

instantiation QREGISTER :: (type) lattice begin
(* TODO: If we would change valid_qregister_range to mean von Neumann factor, we would even get orthocomplemented_lattice.
   But we don't have a proof that the intersection of two factors is a factor. *)
lift_definition inf_QREGISTER :: \<open>'a QREGISTER \<Rightarrow> 'a QREGISTER \<Rightarrow> 'a QREGISTER\<close> is Set.inter
  apply simp
  by (smt (verit, best) double_commutant_in_vn_algI inf_le1 inf_le2 le_inf_iff mem_simps(4) valid_qregister_rangeI valid_qregister_range_def von_neumann_algebra_def)
instance
proof intro_classes
  fix x y z :: \<open>'a QREGISTER\<close>
  show \<open>x \<sqinter> y \<le> x\<close>
    apply transfer by simp
  show \<open>x \<sqinter> y \<le> y\<close>
    apply transfer by simp
  show \<open>x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> y \<sqinter> z\<close>
    apply transfer by simp
qed
end

instantiation QREGISTER :: (type) bounded_lattice begin
instance
proof intro_classes
  fix x y :: \<open>'a QREGISTER\<close>
  show \<open>\<bottom> \<le> x\<close>
    apply transfer
    by (metis commutant_UNIV commutant_antimono mem_Collect_eq top.extremum valid_qregister_range_def von_neumann_algebra_def)
  show \<open>x \<le> \<top>\<close>
    apply transfer
    by simp
qed
end


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
  by (simp add: sup_QREGISTER.rep_eq Un_ac(3))

lemma Rep_QREGISTER_Un_empty1[simp]: \<open>Rep_QREGISTER X \<union> one_algebra = Rep_QREGISTER X\<close>
  using QREGISTER_unit_smallest bot_QREGISTER.rep_eq less_eq_QREGISTER.rep_eq by blast
lemma Rep_QREGISTER_Un_empty2[simp]: \<open>one_algebra \<union> Rep_QREGISTER X = Rep_QREGISTER X\<close>
  using Rep_QREGISTER_Un_empty1 by blast

lemma QREGISTER_chain_non_qregister[simp]: \<open>QREGISTER_chain non_qregister F = bot\<close>
  apply (rule Rep_QREGISTER_inject[THEN iffD1])
  by (simp add: QREGISTER_chain.rep_eq bot_QREGISTER.rep_eq)

lemma QREGISTER_pair_bot_left[simp]: \<open>QREGISTER_pair \<bottom> F = F\<close>
  by simp

lemma QREGISTER_pair_bot_right[simp]: \<open>QREGISTER_pair F \<bottom> = F\<close>
  by simp

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
    by (simp add: sup_QREGISTER.rep_eq QREGISTER_chain.rep_eq
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

instance QREGISTER :: (type) order_bot..

instance QREGISTER :: (type) order_top..

lemma QREGISTER_pair_unit_left: \<open>QREGISTER_pair QREGISTER_unit F = F\<close>
  by simp

lemma QREGISTER_pair_unit_right: \<open>QREGISTER_pair F QREGISTER_unit = F\<close>
  by simp

lemma QREGISTER_pair_all_left: \<open>QREGISTER_pair QREGISTER_all F = QREGISTER_all\<close>
  by simp

lemma QREGISTER_pair_all_right: \<open>QREGISTER_pair F QREGISTER_all = QREGISTER_all\<close>
  by simp

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
  by (simp add: uminus_QREGISTER.rep_eq QREGISTER_of.rep_eq F G)


lemma Rep_QREGISTER_pair_fst_snd:
  \<open>Rep_QREGISTER (QREGISTER_pair (QREGISTER_chain qFst F) (QREGISTER_chain qSnd G))
      = tensor_vn (Rep_QREGISTER F) (Rep_QREGISTER G)\<close>
  by (simp add: sup_QREGISTER.rep_eq QREGISTER_chain.rep_eq apply_qregister_fst apply_qregister_snd tensor_vn_def)

lift_definition ACTUAL_QREGISTER :: \<open>'a QREGISTER \<Rightarrow> bool\<close> is \<open>actual_qregister_range\<close>.

lemma ACTUAL_QREGISTER_QREGISTER_of: \<open>ACTUAL_QREGISTER (QREGISTER_of F)\<close> if \<open>qregister F\<close>
  by (simp add: ACTUAL_QREGISTER.rep_eq QREGISTER_of.rep_eq qregister_has_actual_qregister_range that)

definition \<open>ACTUAL_QREGISTER_content \<FF> = actual_qregister_range_content (Rep_QREGISTER \<FF>)\<close>

lemma ACTUAL_QREGISTER_ex_register:
  fixes \<FF> :: \<open>'a QREGISTER\<close>
  assumes \<open>ACTUAL_QREGISTER \<FF>\<close>
  shows \<open>\<forall>\<^sub>\<tau> 'l::type = ACTUAL_QREGISTER_content \<FF>.
         \<exists>F :: ('l, 'a) qregister. qregister F \<and> QREGISTER_of F = \<FF>\<close>
  by (smt (verit, ccfv_threshold) ACTUAL_QREGISTER.rep_eq ACTUAL_QREGISTER_content_def QREGISTER_of.rep_eq Rep_QREGISTER_inject actual_qregister_range_ex_register assms with_type_mp)

lemma ACTUAL_QREGISTER_chain:
  assumes \<open>qregister F\<close>
  assumes \<open>ACTUAL_QREGISTER \<GG>\<close>
  shows \<open>ACTUAL_QREGISTER (QREGISTER_chain F \<GG>)\<close>
proof -
  have \<open>actual_qregister_range (Rep_QREGISTER \<GG>)\<close>
    using assms by transfer
  from ACTUAL_QREGISTER_ex_register[OF assms(2)]
  have \<open>\<forall>\<^sub>\<tau> 'c::type = ACTUAL_QREGISTER_content \<GG>.
       ACTUAL_QREGISTER (QREGISTER_chain F \<GG>)\<close>
  proof (rule with_type_mp)
    assume \<open>\<exists>G :: ('c, 'a) qregister. qregister G \<and> QREGISTER_of G = \<GG>\<close>
    then obtain G :: \<open>('c, 'a) qregister\<close> where [simp]: \<open>qregister G\<close>
      and rangeG: \<open>QREGISTER_of G = \<GG>\<close>
      by auto
    have \<open>QREGISTER_chain F \<GG> = QREGISTER_of (qregister_chain F G)\<close>
      apply (rule Rep_QREGISTER_inject[THEN iffD1])
      by (simp add: QREGISTER_chain.rep_eq assms QREGISTER_of.rep_eq image_image flip: rangeG)
    also have \<open>ACTUAL_QREGISTER \<dots>\<close>
      by (simp add: ACTUAL_QREGISTER_QREGISTER_of assms(1))
    finally show \<open>ACTUAL_QREGISTER (QREGISTER_chain F \<GG>)\<close>
      by -
  qed
  from this[cancel_with_type]
  show ?thesis
    by -
qed

lemma ACTUAL_QREGISTER_fst[simp]: \<open>ACTUAL_QREGISTER QREGISTER_fst\<close>
  by (metis ACTUAL_QREGISTER_QREGISTER_of QREGISTER_of_qFst qFst_register)

lemma ACTUAL_QREGISTER_snd[simp]: \<open>ACTUAL_QREGISTER QREGISTER_snd\<close>
  by (metis ACTUAL_QREGISTER_QREGISTER_of QREGISTER_of_qSnd qSnd_register)

lemma ACTUAL_QREGISTER_top[simp]: \<open>ACTUAL_QREGISTER \<top>\<close>
  by (metis ACTUAL_QREGISTER_QREGISTER_of QREGISTER_of_qregister_id qregister_id)

lemma ACTUAL_QREGISTER_bot[simp]: \<open>ACTUAL_QREGISTER \<bottom>\<close>
proof -
  have *: \<open>a \<in> range (\<lambda>c. c *\<^sub>C id_cblinfun)\<close> 
    if offdiag: \<open>\<And>x y. x \<noteq> y \<Longrightarrow> is_orthogonal |x\<rangle> (a *\<^sub>V |y\<rangle>)\<close> 
      and diag: \<open>\<And>x y. |x\<rangle> \<bullet>\<^sub>C (a *\<^sub>V |x\<rangle>) = |y\<rangle> \<bullet>\<^sub>C (a *\<^sub>V |y\<rangle>)\<close>
    for a :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close>
  proof -
    define c where \<open>c = ket undefined \<bullet>\<^sub>C (a *\<^sub>V ket undefined)\<close>
    from diag have diag_simp: \<open>|x\<rangle> \<bullet>\<^sub>C (a *\<^sub>V |x\<rangle>) = |undefined\<rangle> \<bullet>\<^sub>C (a *\<^sub>V |undefined\<rangle>)\<close> if \<open>NO_MATCH undefined x\<close> for x
      by simp
    let ?id = \<open>id_cblinfun :: 'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close>
    have \<open>|x\<rangle> \<bullet>\<^sub>C (a *\<^sub>V |y\<rangle>) = |x\<rangle> \<bullet>\<^sub>C ((c *\<^sub>C ?id) *\<^sub>V |y\<rangle>)\<close> for x y
      apply (cases \<open>x = y\<close>)
      by (auto simp add: diag_simp c_def offdiag)
    then have \<open>a = c *\<^sub>C ?id\<close>
      by (meson cinner_ket_eqI equal_ket)
    then show ?thesis
      by auto
  qed
  show ?thesis
    apply transfer
    unfolding actual_qregister_range_def
    apply (rule exI[of _ \<open>\<lambda>x. (undefined,x)\<close>])
    apply (rule exI[of _ id_cblinfun])
    by (auto simp: actual_qregister_range_aux_def one_algebra_def * intro!: injI)
qed

lemma ACTUAL_QREGISTER_pair[simp]:
  assumes actualF: \<open>ACTUAL_QREGISTER \<FF>\<close>
  assumes actualG: \<open>ACTUAL_QREGISTER \<GG>\<close>
  assumes comp: \<open>QQcompatible \<FF> \<GG>\<close>
  shows \<open>ACTUAL_QREGISTER (QREGISTER_pair \<FF> \<GG>)\<close>
proof -
  from ACTUAL_QREGISTER_ex_register[OF actualF]
  have \<open>\<forall>\<^sub>\<tau> 'f::type = ACTUAL_QREGISTER_content \<FF>.
       ACTUAL_QREGISTER (QREGISTER_pair \<FF> \<GG>)\<close>
  proof (rule with_type_mp)
    assume \<open>\<exists>F :: ('f, 'a) qregister. qregister F \<and> QREGISTER_of F = \<FF>\<close>
    then obtain F :: \<open>('f, 'a) qregister\<close> where [simp]: \<open>qregister F\<close> and qregF: \<open>QREGISTER_of F = \<FF>\<close>
      by auto
    from ACTUAL_QREGISTER_ex_register[OF actualG]
    have \<open>\<forall>\<^sub>\<tau> 'g::type = ACTUAL_QREGISTER_content \<GG>.
       ACTUAL_QREGISTER (QREGISTER_pair \<FF> \<GG>)\<close>
    proof (rule with_type_mp)
      assume \<open>\<exists>G :: ('g, 'a) qregister. qregister G \<and> QREGISTER_of G = \<GG>\<close>
      then obtain G :: \<open>('g, 'a) qregister\<close> where [simp]: \<open>qregister G\<close> and qregG: \<open>QREGISTER_of G = \<GG>\<close>
        by auto
      from comp have comp': \<open>qcompatible F G\<close>
        by (simp add: qcompatible_QQcompatible flip: qregG qregF)
      then have \<open>QREGISTER_pair \<FF> \<GG> = QREGISTER_of \<lbrakk>F, G\<rbrakk>\<^sub>q\<close>
        by (simp add: QREGISTER_of_qregister_pair qregF qregG)
      also have \<open>ACTUAL_QREGISTER \<dots>\<close>
        by (simp add: ACTUAL_QREGISTER_QREGISTER_of comp')
      finally show \<open>ACTUAL_QREGISTER (QREGISTER_pair \<FF> \<GG>)\<close>
        by -
    qed
    from this[cancel_with_type]
    show \<open>ACTUAL_QREGISTER (QREGISTER_pair \<FF> \<GG>)\<close>
      by -
  qed
  from this[cancel_with_type]
  show \<open>ACTUAL_QREGISTER (QREGISTER_pair \<FF> \<GG>)\<close>
    by -
qed


lemma QCOMPLEMENT_QREGISTER_of_eqI:
  assumes \<open>qcomplements F G\<close>
  shows \<open>QCOMPLEMENT (QREGISTER_of F) = QREGISTER_of G\<close>
  by (metis uminus_QREGISTER.rep_eq QREGISTER_of.rep_eq Rep_QREGISTER_inverse assms iso_qregister_def qcompatible_QQcompatible qcomplements.rep_eq qcomplements_def' register_range_complement_commutant)

lemma ACTUAL_QREGISTER_complement: \<open>ACTUAL_QREGISTER (QCOMPLEMENT \<FF>)\<close> if \<open>ACTUAL_QREGISTER \<FF>\<close>
proof -
  let ?goal = ?thesis
  from ACTUAL_QREGISTER_ex_register[OF \<open>ACTUAL_QREGISTER \<FF>\<close>]
  have \<open>\<forall>\<^sub>\<tau> 'f::type = ACTUAL_QREGISTER_content \<FF>. ?goal\<close>
  proof (rule with_type_mp)
    assume \<open>\<exists>F :: ('f, 'a) qregister. qregister F \<and> QREGISTER_of F = \<FF>\<close>
    then obtain F :: \<open>('f, 'a) qregister\<close> where [simp]: \<open>qregister F\<close> and qregF: \<open>QREGISTER_of F = \<FF>\<close>
      by auto
    from qcomplement_exists[OF \<open>qregister F\<close>]
    have \<open>\<forall>\<^sub>\<tau> 'g::type = qregister_decomposition_basis F. ?goal\<close>
    proof (rule with_type_mp)
      assume \<open>\<exists>G :: ('g, 'a) qregister. qcomplements F G\<close>
      then obtain G :: \<open>('g, 'a) qregister\<close> where \<open>qcomplements F G\<close>
        by auto
      then have \<open>qregister G\<close>
        using Laws_Quantum.compatible_register2 complements_def qcomplements.rep_eq qregister_raw_apply_qregister by blast
      then have \<open>ACTUAL_QREGISTER (QREGISTER_of G)\<close>
        by (simp add: ACTUAL_QREGISTER_QREGISTER_of)
      also from \<open>qcomplements F G\<close> have \<open>QREGISTER_of G = QCOMPLEMENT (QREGISTER_of F)\<close>
        using QCOMPLEMENT_QREGISTER_of_eqI by fastforce
      also have \<open>\<dots> = QCOMPLEMENT \<FF>\<close>
        by (simp add: qregF)
      finally show ?goal
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


lemma ACTUAL_QREGISTER_complement_iff: \<open>ACTUAL_QREGISTER (QCOMPLEMENT \<FF>) \<longleftrightarrow> ACTUAL_QREGISTER \<FF>\<close>
  by (metis ACTUAL_QREGISTER_complement uminus_QREGISTER.rep_eq Rep_QREGISTER Rep_QREGISTER_inverse mem_Collect_eq valid_qregister_range_def von_neumann_algebra_def)

lift_definition equivalent_qregisters :: \<open>('a,'c) qregister \<Rightarrow> ('b,'c) qregister \<Rightarrow> bool\<close> is equivalent_registers.

lemma equivalent_qregisters_trans[trans]:
  assumes \<open>equivalent_qregisters F G\<close>
  assumes \<open>equivalent_qregisters G H\<close>
  shows \<open>equivalent_qregisters F H\<close>
  using assms apply transfer
  using Laws_Quantum.equivalent_registers_trans by blast

lemma equivalent_qregisters_sym[sym]:
  assumes \<open>equivalent_qregisters F G\<close>
  shows \<open>equivalent_qregisters G F\<close>
  using assms apply transfer
  using Laws_Quantum.equivalent_registers_sym by blast

lemma equivalent_qregisters_triple1:
  assumes \<open>qregister \<lbrakk>a,b,c\<rbrakk>\<close>
  shows \<open>equivalent_qregisters \<lbrakk>a,\<lbrakk>b,c\<rbrakk>\<rbrakk> \<lbrakk>\<lbrakk>a,b\<rbrakk>,c\<rbrakk>\<close>
proof -
  define a' b' c' where abc'_def: \<open>a' = apply_qregister a\<close> \<open>b' = apply_qregister b\<close> \<open>c' = apply_qregister c\<close>
  have [simp]: \<open>qcompatible_raw a' b'\<close>
    using abc'_def(1) abc'_def(2) assms qcompatible3' qcompatible_def by blast
  have [simp]: \<open>qcompatible_raw b' c'\<close>
    by (metis abc'_def(2) abc'_def(3) assms qcompatible_def)
  have [simp]: \<open>qcompatible_raw a' (b';c')\<close>
    by (metis abc'_def(1) abc'_def(2) abc'_def(3) assms qcompatible_def qregister_pair.rep_eq)
  have [simp]: \<open>qcompatible_raw (a';b') c'\<close>
    using Laws_Quantum.compatible3 \<open>qcompatible_raw a' b'\<close> \<open>qcompatible_raw b' c'\<close> abc'_def(1) abc'_def(3) assms qcompatible3' qcompatible_def by blast

  have \<open>Laws_Quantum.equivalent_registers (a';(b';c')) ((a';b');c')\<close>
    by (metis Laws_Quantum.equivalent_registers_assoc \<open>qcompatible_raw a' b'\<close> \<open>qcompatible_raw b' c'\<close> abc'_def(1) abc'_def(3) assms qcompatible3' qcompatible_def)
  then show ?thesis
    by (simp add: equivalent_qregisters.rep_eq qregister_pair.rep_eq flip: abc'_def)
qed

lemma equivalent_qregisters_triple2:
  assumes \<open>qregister \<lbrakk>F,G,H\<rbrakk>\<close>
  shows \<open>equivalent_qregisters \<lbrakk>\<lbrakk>F,G\<rbrakk>,H\<rbrakk> \<lbrakk>F,\<lbrakk>G,H\<rbrakk>\<rbrakk>\<close>
  using assms equivalent_qregisters_sym equivalent_qregisters_triple1 by blast

lemma equivalent_qregisters_swap:
  assumes \<open>qregister \<lbrakk>F,G\<rbrakk>\<close>
  shows \<open>equivalent_qregisters \<lbrakk>F,G\<rbrakk> \<lbrakk>G,F\<rbrakk>\<close>
  using assms apply transfer
  apply (rule equivalent_registersI[where I=swap])
  by (auto simp: non_qregister_raw Laws_Quantum.compatible_sym)

lemma equivalent_qregisters_refl: \<open>equivalent_qregisters F F\<close> if \<open>qregister F\<close>
  using that apply transfer
  using Laws_Quantum.equivalent_registers_refl by blast

lemma equivalent_qregisters_pair:
  assumes \<open>equivalent_qregisters F F'\<close>
  assumes \<open>equivalent_qregisters G G'\<close>
  assumes \<open>qregister \<lbrakk>F,G\<rbrakk>\<close>
  shows \<open>equivalent_qregisters \<lbrakk>F,G\<rbrakk> \<lbrakk>F',G'\<rbrakk>\<close>
proof -
  from assms(1) obtain I where [simp]: \<open>iso_register I\<close> and FI: \<open>apply_qregister F o I = apply_qregister F'\<close>
    using Laws_Quantum.equivalent_registers_def equivalent_qregisters.rep_eq by blast
  from assms(2) obtain J where [simp]: \<open>iso_register J\<close> and GJ: \<open>apply_qregister G o J = apply_qregister G'\<close>
    using Laws_Quantum.equivalent_registers_def equivalent_qregisters.rep_eq by blast
  have isoIJ: \<open>iso_register (I \<otimes>\<^sub>r J)\<close>
    by simp
  have FG[simp]: \<open>qregister_raw (apply_qregister \<lbrakk>F,G\<rbrakk>)\<close>
    using assms(3) by auto
  have FG2[simp]: \<open>qcompatible_raw (apply_qregister F) (apply_qregister G)\<close>
    using assms(3) qcompatible_def by blast
  have [simp]: \<open>qregister \<lbrakk>F',G'\<rbrakk>\<close>
    by (metis Laws_Quantum.equivalent_registers_compatible1 Laws_Quantum.equivalent_registers_compatible2 Laws_Quantum.equivalent_registers_def FG2 assms(1) assms(2) equivalent_qregisters.rep_eq equivalent_qregisters_sym qcompatible_def qregister_raw_apply_qregister)
  then have F'G'[simp]: \<open>qregister_raw (apply_qregister \<lbrakk>F',G'\<rbrakk>)\<close>
    apply transfer by simp
  have [simp]: \<open>qcompatible_raw (apply_qregister F') (apply_qregister G')\<close>
    by (metis F'G' non_qregister_raw qregister_pair.rep_eq)
  have \<open>apply_qregister \<lbrakk>F,G\<rbrakk> o (I \<otimes>\<^sub>r J) = apply_qregister \<lbrakk>F',G'\<rbrakk>\<close>
    by (simp add: qregister_pair.rep_eq Laws_Quantum.iso_register_is_register Laws_Quantum.pair_o_tensor FI GJ)
  with isoIJ FG
  have \<open>equivalent_registers (apply_qregister \<lbrakk>F,G\<rbrakk>) (apply_qregister \<lbrakk>F',G'\<rbrakk>)\<close>
    using Laws_Quantum.equivalent_registersI by blast
  then show ?thesis
    apply transfer by simp
qed

lemma equivalent_qregisters_chain:
  assumes \<open>equivalent_qregisters F G\<close>
  assumes \<open>qregister H\<close>
  shows \<open>equivalent_qregisters (qregister_chain H F) (qregister_chain H G)\<close>
  using assms apply transfer
  by (simp add: Laws_Quantum.equivalent_registers_comp Laws_Quantum.equivalent_registers_register_left Laws_Quantum.equivalent_registers_register_right)
  
lemma iso_qregister_equivalent_id:
  \<open>iso_qregister F \<longleftrightarrow> equivalent_qregisters F qregister_id\<close>
  unfolding iso_qregister_def
  apply transfer
  by (metis Laws_Quantum.equivalent_registers_sym Laws_Quantum.iso_register_def Laws_Quantum.iso_register_equivalent_id Un_iff mem_Collect_eq)

(* TODO: Just add an assumption and a comment that the assumption is not strictly necessary by Takesaki? *)
lemma y2:
  assumes \<open>ACTUAL_QREGISTER F\<close> \<open>ACTUAL_QREGISTER G\<close> (* TODO comment on assumptions *)
  shows \<open>QCOMPLEMENT (QREGISTER_pair (QREGISTER_chain qFst F) (QREGISTER_chain qSnd G))
    = QREGISTER_pair (QREGISTER_chain qFst (QCOMPLEMENT F)) (QREGISTER_chain qSnd (QCOMPLEMENT G))\<close>
(* 
  apply (rule Rep_QREGISTER_inject[THEN iffD1])
  apply (simp add: uminus_QREGISTER.rep_eq Rep_QREGISTER_pair_fst_snd)
  apply (subst commutant_tensor_vn)
  using Rep_QREGISTER Rep_QREGISTER
  by (force simp add: valid_qregister_range_def)+
 *)
proof -
  let ?goal = ?thesis
  from ACTUAL_QREGISTER_ex_register[OF \<open>ACTUAL_QREGISTER F\<close>]
  have \<open>\<forall>\<^sub>\<tau> 'f::type = ACTUAL_QREGISTER_content F. ?goal\<close>
  proof (rule with_type_mp)
    assume \<open>\<exists>A :: ('f, 'a) qregister. qregister A \<and> QREGISTER_of A = F\<close>
    then obtain A :: \<open>('f, 'a) qregister\<close> where [simp]: \<open>qregister A\<close> and qregF: \<open>QREGISTER_of A = F\<close>
      by auto
    from ACTUAL_QREGISTER_ex_register[OF \<open>ACTUAL_QREGISTER G\<close>]
    have \<open>\<forall>\<^sub>\<tau> 'g::type = ACTUAL_QREGISTER_content G. ?goal\<close>
    proof (rule with_type_mp)
      assume \<open>\<exists>B :: ('g, 'b) qregister. qregister B \<and> QREGISTER_of B = G\<close>
      then obtain B :: \<open>('g, 'b) qregister\<close> where [simp]: \<open>qregister B\<close> and qregG: \<open>QREGISTER_of B = G\<close>
        by auto
      from qcomplement_exists[OF \<open>qregister A\<close>]
      have \<open>\<forall>\<^sub>\<tau> 'i::type = qregister_decomposition_basis A. ?goal\<close>
      proof (rule with_type_mp)
        assume \<open>\<exists>AC :: ('i, 'a) qregister. qcomplements A AC\<close>
        then obtain AC :: \<open>('i, 'a) qregister\<close> where \<open>qcomplements A AC\<close>
          by auto
        from qcomplement_exists[OF \<open>qregister B\<close>]
        have \<open>\<forall>\<^sub>\<tau> 'j::type = qregister_decomposition_basis B. ?goal\<close>
        proof (rule with_type_mp)
          assume \<open>\<exists>BC :: ('j, 'b) qregister. qcomplements B BC\<close>
          then obtain BC :: \<open>('j, 'b) qregister\<close> where \<open>qcomplements B BC\<close>
            by auto
          from \<open>qcomplements A AC\<close>
          have [simp]: \<open>qregister AC\<close>
            using iso_qregister_def qcompatible_register2 qcomplements_def' by blast
          from \<open>qcomplements A AC\<close>
          have [simp]: \<open>qcompatible A AC\<close>
            using iso_qregister_def qcomplements_def' by blast
          from \<open>qcomplements B BC\<close>
          have [simp]: \<open>qregister BC\<close>
            using iso_qregister_def qcompatible_register2 qcomplements_def' by blast
          from \<open>qcomplements B BC\<close>
          have [simp]: \<open>qcompatible B BC\<close>
            using iso_qregister_def qcomplements_def' by blast
          have [simp]: \<open>iso_qregister \<lbrakk>A, AC\<rbrakk>\<close>
            using \<open>qcomplements A AC\<close> qcomplements_def' by blast
          have [simp]: \<open>iso_qregister \<lbrakk>B, BC\<rbrakk>\<close>
            using \<open>qcomplements B BC\<close> qcomplements_def' by blast
          have QCOMPLEMENT_A: \<open>QCOMPLEMENT (QREGISTER_of A) = QREGISTER_of AC\<close>
            by (auto intro!: QCOMPLEMENT_QREGISTER_of_eqI \<open>qcomplements A AC\<close>)
          have QCOMPLEMENT_B: \<open>QCOMPLEMENT (QREGISTER_of B) = QREGISTER_of BC\<close>
            by (auto intro!: QCOMPLEMENT_QREGISTER_of_eqI \<open>qcomplements B BC\<close>)
          have \<open>qcomplements \<lbrakk>qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q A, qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q B\<rbrakk>\<^sub>q
                             \<lbrakk>qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q AC, qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q BC\<rbrakk>\<^sub>q\<close>
          proof -
            write equivalent_qregisters (infix "\<approx>" 50)
            have \<open>\<lbrakk> \<lbrakk>qregister_chain qFst A, qregister_chain qSnd B\<rbrakk>,
                    \<lbrakk>qregister_chain qFst AC, qregister_chain qSnd BC\<rbrakk> \<rbrakk>
                \<approx> \<lbrakk> \<lbrakk>qregister_chain qFst A, qregister_chain qSnd B\<rbrakk>,
                    \<lbrakk>qregister_chain qSnd BC, qregister_chain qFst AC\<rbrakk> \<rbrakk>\<close>
              apply (rule equivalent_qregisters_pair)
                apply (rule equivalent_qregisters_refl)
                apply simp
               apply (rule equivalent_qregisters_swap)
              by simp_all
            also have \<open>\<dots> \<approx> \<lbrakk>qregister_chain qFst A, \<lbrakk>qregister_chain qSnd B,
                    \<lbrakk>qregister_chain qSnd BC, qregister_chain qFst AC\<rbrakk>\<rbrakk>\<rbrakk>\<close>
              apply (rule equivalent_qregisters_triple2)
              by simp
            also have \<open>\<dots> \<approx> \<lbrakk>qregister_chain qFst A, \<lbrakk>\<lbrakk>qregister_chain qSnd B,
                    qregister_chain qSnd BC\<rbrakk>, qregister_chain qFst AC\<rbrakk>\<rbrakk>\<close>
              apply (rule equivalent_qregisters_pair)
                apply (rule equivalent_qregisters_refl)
                apply simp
              apply (rule equivalent_qregisters_triple1)
              by simp_all
            also have \<open>\<dots> = \<lbrakk>qregister_chain qFst A, 
                              \<lbrakk>qregister_chain qSnd \<lbrakk>B,BC\<rbrakk>, qregister_chain qFst AC\<rbrakk>\<rbrakk>\<close>
              by (simp add: pair_chain_fst_snd)
            also have \<open>\<dots> \<approx> \<lbrakk>qregister_chain qFst A, 
                    \<lbrakk>qregister_chain qFst AC, qregister_chain qSnd \<lbrakk>B,BC\<rbrakk>\<rbrakk>\<rbrakk>\<close>
              apply (rule equivalent_qregisters_pair)
                apply (rule equivalent_qregisters_refl)
                apply simp
               apply (rule equivalent_qregisters_swap)
              by simp_all
            also have \<open>\<dots> \<approx> \<lbrakk>\<lbrakk>qregister_chain qFst A, qregister_chain qFst AC\<rbrakk>, 
                             qregister_chain qSnd \<lbrakk>B,BC\<rbrakk>\<rbrakk>\<close>
              apply (rule equivalent_qregisters_triple1)
              by simp
            also have \<open>\<dots> = \<lbrakk>qregister_chain qFst \<lbrakk>A,AC\<rbrakk>, 
                             qregister_chain qSnd \<lbrakk>B,BC\<rbrakk>\<rbrakk>\<close>
              by (simp add: pair_chain_fst_snd)
            also have \<open>\<dots> \<approx> \<lbrakk>qregister_chain qFst qregister_id, 
                             qregister_chain qSnd qregister_id\<rbrakk>\<close>
              apply (rule equivalent_qregisters_pair)
                apply (rule equivalent_qregisters_chain)
                 apply (simp flip: iso_qregister_equivalent_id)
              apply simp
               apply (rule equivalent_qregisters_chain)
              by (simp_all flip: iso_qregister_equivalent_id)
            also have \<open>\<dots> = qregister_id\<close>
              by simp
            finally show ?thesis
              by (simp add: iso_qregister_equivalent_id qcomplements_def')
          qed
          then show ?goal
            by (auto intro!: QCOMPLEMENT_QREGISTER_of_eqI
                simp add: QCOMPLEMENT_A QCOMPLEMENT_B
                simp flip: QREGISTER_of_qregister_chain QREGISTER_of_qregister_pair qregF qregG)
        qed
        from this[cancel_with_type]
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
  from this[cancel_with_type]
  show ?goal
    by -
qed


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
  by (simp add: uminus_QREGISTER.rep_eq top_QREGISTER.rep_eq bot_QREGISTER.rep_eq
      commutant_UNIV one_algebra_def)

lemma QCOMPLEMENT_bot[simp]: \<open>QCOMPLEMENT \<bottom> = \<top>\<close>
  apply (rule Rep_QREGISTER_inject[THEN iffD1])
  by (simp add: uminus_QREGISTER.rep_eq top_QREGISTER.rep_eq bot_QREGISTER.rep_eq
      commutant_one_algebra)

lemma y1:
  assumes \<open>ACTUAL_QREGISTER F\<close>
  shows \<open>QCOMPLEMENT (QREGISTER_pair QREGISTER_fst (QREGISTER_chain qSnd F))
    = QREGISTER_chain qSnd (QCOMPLEMENT F)\<close>
  using y2[where F=\<top> and G=F] assms
  by simp

lemma y3:
  assumes \<open>ACTUAL_QREGISTER F\<close>
  shows \<open>QCOMPLEMENT (QREGISTER_pair (QREGISTER_chain qFst F) QREGISTER_snd)
    = QREGISTER_chain qFst (QCOMPLEMENT F)\<close>
  using y2[where F=F and G=\<top>] assms
  by simp

lemma QCOMPLEMENT_fst: \<open>QCOMPLEMENT QREGISTER_fst = QREGISTER_snd\<close>
  apply (rule Rep_QREGISTER_inject[THEN iffD1])
  by (simp add: uminus_QREGISTER.rep_eq QREGISTER_snd.rep_eq QREGISTER_fst.rep_eq commutant_tensor1)

lemma QCOMPLEMENT_snd: \<open>QCOMPLEMENT QREGISTER_snd = QREGISTER_fst\<close>
  apply (rule Rep_QREGISTER_inject[THEN iffD1])
  by (simp add: uminus_QREGISTER.rep_eq QREGISTER_snd.rep_eq QREGISTER_fst.rep_eq commutant_tensor1')

lemma QREGISTER_of_non_qregister[simp]: \<open>QREGISTER_of non_qregister = \<bottom>\<close>
  by (simp add: QREGISTER_of.abs_eq bot_QREGISTER_def)

lemma QREGISTER_demorgan1: \<open>- (X \<squnion> Y) = (- X \<sqinter> - Y)\<close> for X Y :: \<open>_ QREGISTER\<close>
  apply transfer
  by (auto simp: valid_qregister_range_def commutant_def)

lemma QCOMPLEMENT_chain: \<open>QCOMPLEMENT (QREGISTER_chain F G)
        = QREGISTER_pair (QCOMPLEMENT (QREGISTER_of F)) (QREGISTER_chain F (QCOMPLEMENT G))\<close>
proof (cases \<open>qregister F\<close>)
  case True
  have 1: \<open>- QREGISTER_of F \<le> - QREGISTER_chain F G\<close>
    by (metis QCOMPLEMENT_antimono QREGISTER_chain_all_right QREGISTER_pair_QREGISTER_chain sup.absorb_iff2 top.extremum)
  have 2: \<open>QREGISTER_chain F (- G) \<le> - QREGISTER_chain F G\<close>
  proof (intro less_eq_QREGISTER.rep_eq[THEN iffD2] Set.subsetI)
    fix Fx assume \<open>Fx \<in> Rep_QREGISTER (QREGISTER_chain F (- G))\<close>
    then obtain x where xG': \<open>x \<in> Rep_QREGISTER (-G)\<close> and Fx_def: \<open>Fx = apply_qregister F x\<close>
      by (auto simp: QREGISTER_chain.rep_eq True)
    show \<open>Fx \<in> Rep_QREGISTER (- QREGISTER_chain F G)\<close>
    proof (unfold uminus_QREGISTER.rep_eq, rule commutant_memberI)
      fix Fy assume \<open>Fy \<in> Rep_QREGISTER (QREGISTER_chain F G)\<close>
      then obtain y where yG: \<open>y \<in> Rep_QREGISTER G\<close> and Fy_def: \<open>Fy = apply_qregister F y\<close>
        by (auto simp: QREGISTER_chain.rep_eq True)
      from xG' yG have \<open>x o\<^sub>C\<^sub>L y = y o\<^sub>C\<^sub>L x\<close>
        by (simp add: uminus_QREGISTER.rep_eq commutant_def)
      then show \<open>Fx o\<^sub>C\<^sub>L Fy = Fy o\<^sub>C\<^sub>L Fx\<close>
        by (simp add: Fx_def Fy_def)
    qed
  qed
  have 3: \<open>- QREGISTER_chain F G \<le> - QREGISTER_of F \<squnion> QREGISTER_chain F (- G)\<close>
  proof -
    have \<open>- (- QREGISTER_of F \<squnion> QREGISTER_chain F (- G))
        = QREGISTER_of F \<sqinter> - QREGISTER_chain F (- G)\<close>
      by (simp add: QREGISTER_demorgan1 QCOMPLEMENT_twice)
    also have \<open>\<dots> \<le> QREGISTER_chain F G\<close>
    proof (intro less_eq_QREGISTER.rep_eq[THEN iffD2] Set.subsetI)
      fix Fx assume asm: \<open>Fx \<in> Rep_QREGISTER (QREGISTER_of F \<sqinter> - QREGISTER_chain F (- G))\<close>
      then obtain x where Fx_def: \<open>Fx = apply_qregister F x\<close>
        by (metis IntE QREGISTER_of.rep_eq True imageE inf_QREGISTER.rep_eq)
      with asm have Fx_FG'': \<open>apply_qregister F x \<in> commutant (apply_qregister F ` Rep_QREGISTER (- G))\<close>
        by (simp add: inf_QREGISTER.rep_eq uminus_QREGISTER.rep_eq QREGISTER_chain.rep_eq True)
      have \<open>x \<in> commutant (Rep_QREGISTER (-G))\<close>
      proof (rule commutant_memberI)
        fix y assume asm_y:\<open>y \<in> Rep_QREGISTER (- G)\<close>
        then have \<open>apply_qregister F y \<in> apply_qregister F ` Rep_QREGISTER (- G)\<close>
          by blast
        with Fx_FG'' asm_y
        have \<open>apply_qregister F x o\<^sub>C\<^sub>L apply_qregister F y = apply_qregister F y o\<^sub>C\<^sub>L apply_qregister F x\<close>
          by (auto simp add: commutant_def)
        with True show \<open>x o\<^sub>C\<^sub>L y = y o\<^sub>C\<^sub>L x\<close>
          by simp
      qed
      then have \<open>x \<in> Rep_QREGISTER G\<close>
        by (metis QCOMPLEMENT_twice uminus_QREGISTER.rep_eq)
      then show \<open>Fx \<in> Rep_QREGISTER (QREGISTER_chain F G)\<close>
        by (simp add: QREGISTER_chain.rep_eq True Fx_def)
    qed
    finally show ?thesis
      by (metis QCOMPLEMENT_antimono QCOMPLEMENT_twice)
  qed
  show ?thesis
    by (auto intro!: antisym 1 2 3)
next
  case False
  then have \<open>F = non_qregister\<close>
    by (simp add: non_qregister)
  then show ?thesis
    by simp
qed

(*
ML \<open>
(* Rewrites QCOMPLEMENT (INDEX-QREGISTER) into an INDEX-QREGISTER *)
local
  val rules = (map (fn thm => thm RS @{thm eq_reflection}) @{thms 
      y1 y2 y3 QCOMPLEMENT_chain QCOMPLEMENT_snd QCOMPLEMENT_fst QREGISTER_of_qFst QREGISTER_of_qSnd
      QREGISTER_pair_fst_snd QREGISTER_pair_snd_fst QCOMPLEMENT_bot QCOMPLEMENT_top})
in
fun QCOMPLEMENT_INDEX_REGISTER_conv ctxt = Raw_Simplifier.rewrite ctxt false rules
end
\<close>
*)

lemma zz0: \<open>ACTUAL_QREGISTER (QREGISTER_pair (QREGISTER_chain qFst F) (QREGISTER_chain qSnd G))\<close> if \<open>ACTUAL_QREGISTER F\<close> and \<open>ACTUAL_QREGISTER G\<close>
proof -
  let ?goal = ?thesis
  from ACTUAL_QREGISTER_ex_register[OF \<open>ACTUAL_QREGISTER F\<close>]
  have \<open>\<forall>\<^sub>\<tau> 'f::type = ACTUAL_QREGISTER_content F. ?goal\<close>
  proof (rule with_type_mp)
    assume \<open>\<exists>A :: ('f, 'a) qregister. qregister A \<and> QREGISTER_of A = F\<close>
    then obtain A :: \<open>('f, 'a) qregister\<close> where [simp]: \<open>qregister A\<close> and qregF: \<open>QREGISTER_of A = F\<close>
      by auto
    from ACTUAL_QREGISTER_ex_register[OF \<open>ACTUAL_QREGISTER G\<close>]
    have \<open>\<forall>\<^sub>\<tau> 'g::type = ACTUAL_QREGISTER_content G. ?goal\<close>
    proof (rule with_type_mp)
      assume \<open>\<exists>B :: ('g, 'b) qregister. qregister B \<and> QREGISTER_of B = G\<close>
      then obtain B :: \<open>('g, 'b) qregister\<close> where [simp]: \<open>qregister B\<close> and qregG: \<open>QREGISTER_of B = G\<close>
        by auto
      have \<open>QREGISTER_pair (QREGISTER_chain qFst F) (QREGISTER_chain qSnd G)
          = QREGISTER_of (qregister_pair (qregister_chain qFst A) (qregister_chain qSnd B))\<close>
        by (simp add: QREGISTER_of_qregister_pair QREGISTER_of_qregister_chain qregG qregF)
      then show ?goal
        by (auto intro!: ACTUAL_QREGISTER_QREGISTER_of)
    qed
    from this[cancel_with_type]
    show ?goal
      by -
  qed
  from this[cancel_with_type]
  show ?goal
    by -
qed

lemma zz0': \<open>ACTUAL_QREGISTER (QREGISTER_pair (QREGISTER_chain qSnd G) (QREGISTER_chain qFst F))\<close> if \<open>ACTUAL_QREGISTER F \<and> ACTUAL_QREGISTER G\<close>
  by (simp add: QREGISTER_pair_sym that zz0)
lemma zz1: \<open>ACTUAL_QREGISTER (QREGISTER_pair QREGISTER_fst (QREGISTER_chain qSnd F))\<close> if \<open>ACTUAL_QREGISTER F\<close>
  by (metis ACTUAL_QREGISTER_top QREGISTER_chain_fst_top that zz0)
lemma zz2: \<open>ACTUAL_QREGISTER (QREGISTER_pair QREGISTER_snd (QREGISTER_chain qFst F))\<close> if \<open>ACTUAL_QREGISTER F\<close>
  by (metis ACTUAL_QREGISTER_top QREGISTER_chain_snd_top that zz0')
lemma zz3: \<open>ACTUAL_QREGISTER (QREGISTER_pair (QREGISTER_chain qSnd F) QREGISTER_fst)\<close> if \<open>ACTUAL_QREGISTER F\<close>
  by (simp add: QREGISTER_pair_sym that zz1)
lemma zz4: \<open>ACTUAL_QREGISTER (QREGISTER_pair (QREGISTER_chain qFst F) QREGISTER_snd)\<close> if \<open>ACTUAL_QREGISTER F\<close>
  by (simp add: QREGISTER_pair_sym that zz2)

ML \<open>
local
  val simpset = \<^context>  addsimps @{thms 
       ACTUAL_QREGISTER_fst ACTUAL_QREGISTER_snd ACTUAL_QREGISTER_chain
       ACTUAL_QREGISTER_bot ACTUAL_QREGISTER_top ACTUAL_QREGISTER_pair
       zz0 zz0' zz1 zz2 zz3 zz4
    distinct_cvars_split2 ccompatible3 ccompatible3'
    distinct_qvars_split1 distinct_qvars_split2 qcompatible3 qcompatible3'
    Cccompatible_CREGISTER_of Qqcompatible_QREGISTER_of}
    |> simpset_of
in
(* Proves "ACTUAL_QREGISTER INDEX-QREGISTER" *)
fun ACTUAL_QREGISTER_tac ctxt =
  (* K (Misc.print_here_tac ctxt \<^here>) THEN'  *)
  let
  val ctxt = ctxt |> Config.put Simplifier.simp_trace false
                  |> put_simpset simpset
  in Misc.succeed_or_error_tac' (SOLVED' (simp_tac ctxt)) ctxt (fn t => "Cannot prove (using simp): " ^ Syntax.string_of_term ctxt t) end
end
\<close>


ML \<open>
(* Rewrites QCOMPLEMENT (INDEX-QREGISTER) into an INDEX-QREGISTER *)
  val simpctxt =
      put_simpset HOL_ss \<^context>
      addsimps
        @{thms 
           y1 y2 y3 QCOMPLEMENT_chain QCOMPLEMENT_snd QCOMPLEMENT_fst QREGISTER_of_qFst QREGISTER_of_qSnd
           QREGISTER_pair_fst_snd QREGISTER_pair_snd_fst QCOMPLEMENT_bot QCOMPLEMENT_top}
  val simpset = Simplifier.simpset_of simpctxt
local
in
fun QCOMPLEMENT_INDEX_REGISTER_conv ctxt = let
  val solver = mk_solver "ACTUAL_QREGISTER" (fn _ => ACTUAL_QREGISTER_tac ctxt)
  val ctxt = Simplifier.put_simpset simpset ctxt 
      addSSolver solver
      addSolver solver
  in
    Simplifier.rewrite ctxt
  end
end
\<close>

ML \<open>
QCOMPLEMENT_INDEX_REGISTER_conv \<^context> \<^cterm>\<open>QCOMPLEMENT
     (QREGISTER_pair QREGISTER_fst
       (QREGISTER_chain \<lbrakk>#2.\<rbrakk>\<^sub>q
         (QREGISTER_pair QREGISTER_fst
           (QREGISTER_chain \<lbrakk>#2.\<rbrakk>\<^sub>q
             (QREGISTER_pair QREGISTER_fst (QREGISTER_chain \<lbrakk>#2.\<rbrakk>\<^sub>q QREGISTER_snd))))))\<close>
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

definition \<open>equivalent_qregisters' F G \<longleftrightarrow> equivalent_qregisters F G \<or> (F = non_qregister \<and> G = non_qregister)\<close>

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
    by (simp add: TTIR_COMPLEMENT_def iso_qregister_def qcomplements_def')
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
    using space_div_space_div_unlifted assms iso_qregister_def qcomplements_def' by blast
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


