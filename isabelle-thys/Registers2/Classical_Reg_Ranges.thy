theory Classical_Reg_Ranges
  imports Classical_Registers
begin


(* Equivalence class of cregisters *)
definition valid_cregister_range :: \<open>'a cupdate set \<Rightarrow> bool\<close> where
  \<open>valid_cregister_range \<FF> \<longleftrightarrow> map_commutant (map_commutant \<FF>) = \<FF>\<close>

definition actual_cregister_range :: \<open>'a cupdate set \<Rightarrow> bool\<close> where
  \<open>actual_cregister_range \<FF> \<longleftrightarrow> valid_cregister_range \<FF> \<and> (\<forall>m m'. \<exists>a\<in>\<FF>. \<exists>b\<in>map_commutant \<FF>. (a \<circ>\<^sub>m b) m = Some m')\<close>

(* TODO move *)
lemma map_comp_Some_map_option: \<open>map_comp (\<lambda>x. Some (f x)) g = map_option f o g\<close>
  by (auto intro!: ext simp: map_comp_def map_option_case)

lemma actual_register_range: 
  fixes F :: \<open>('b,'a) cregister\<close>
  assumes \<open>cregister F\<close>
  shows \<open>actual_cregister_range (range (apply_cregister F))\<close>
proof (insert assms, transfer)
  fix F :: \<open>'b cupdate \<Rightarrow> 'a cupdate\<close>
  assume [simp]: \<open>cregister_raw F\<close>
  define g s where \<open>g = Axioms_Classical.getter F\<close> and \<open>s = Axioms_Classical.setter F\<close>
  define c where \<open>c m = s undefined m\<close> for m
  have [simp]: \<open>g (s a m) = a\<close> for a m
    by (metis \<open>cregister_raw F\<close> g_def s_def valid_getter_setter_def valid_getter_setter_getter_setter)
  have [simp]: \<open>s a (s b m) = s a m\<close> for a b m
    by (metis \<open>cregister_raw F\<close> s_def valid_getter_setter_def valid_getter_setter_getter_setter)
  have [simp]: \<open>s (g m) m = m\<close> for m
    by (metis \<open>cregister_raw F\<close> g_def s_def valid_getter_setter_def valid_getter_setter_getter_setter)
  have [simp]: \<open>c (s a m) = c m\<close> for a m
    by (simp add: c_def)
  have F_gs: \<open>F = register_from_getter_setter g s\<close>
    by (simp add: g_def s_def)

  define Xf X where \<open>Xf f m = (case f (c m) of Some m' \<Rightarrow> Some (s (g m) m') | None \<Rightarrow> None)\<close> and \<open>X = range Xf\<close> for f m
  have 1: \<open>a \<in> map_commutant X\<close> if \<open>a \<in> range F\<close> for a
  proof (unfold map_commutant_def, intro CollectI ballI ext)
    fix x y
    assume \<open>x \<in> X\<close>
    then obtain x' where x_def: \<open>x = Xf x'\<close>
      using X_def Xf_def by blast
    from \<open>a \<in> range F\<close> obtain a' where \<open>a = F a'\<close>
      by fast
    then have a_def: \<open>a = register_from_getter_setter g s a'\<close>
      by (simp add: g_def s_def)
    show \<open>(a \<circ>\<^sub>m x) y = (x \<circ>\<^sub>m a) y\<close>
      apply (cases \<open>x' (c y)\<close>; cases \<open>a' (g y)\<close>)
      by (auto simp: map_comp_def x_def Xf_def a_def register_from_getter_setter_def)
  qed
  have 2: \<open>a \<in> range F\<close> if \<open>a \<in> map_commutant X\<close> for a
  proof -
    fix m0
    define a' where \<open>a' x = map_option g (a (s x m0))\<close> for x
    have \<open>F a' = a\<close>
    proof (rule ext)
      fix m
      have \<open>(\<lambda>m. Some (s (g m) m')) \<in> X\<close>for m'
        by (auto simp: X_def Xf_def intro!: range_eqI[where x=\<open>\<lambda>x. Some m'\<close>])
      then have *: \<open>a \<circ>\<^sub>m (\<lambda>m. Some (s (g m) m')) = (\<lambda>m. Some (s (g m) m')) \<circ>\<^sub>m a\<close> for m'
        using map_commutant_def that by blast

      have \<open>F a' m = map_option (\<lambda>x. s x m) (a' (g m))\<close>
        using register_from_getter_setter_of_getter_setter[OF \<open>cregister_raw F\<close>]
          register_from_getter_setter_def[of g s a' m]
        by (metis g_def map_option_case s_def)
      also have \<open>\<dots> = map_option (\<lambda>x. s (g x) m) ((a \<circ>\<^sub>m (\<lambda>m. Some (s (g m) m0))) m)\<close>
        by (simp add: a'_def option.map_comp o_def)
      also have \<open>\<dots> = map_option (\<lambda>x. s (g x) m) (((\<lambda>m. Some (s (g m) m0)) \<circ>\<^sub>m a) m)\<close>
        by (simp add: *)
      also have \<open>\<dots> = map_option (\<lambda>x. s (g x) m) (a m)\<close>
        by (simp add: map_comp_Some_map_option option.map_comp o_def)
      also have \<open>\<dots> = ((\<lambda>x. Some (s (g x) m)) \<circ>\<^sub>m a) m\<close>
        by (simp add: map_comp_Some_map_option)
      also have \<open>\<dots> = a m\<close>
        by (simp flip: *)
      finally show \<open>F a' m = a m\<close>
        by -
    qed
    then show ?thesis
      by auto
  qed
  from 1 2 have range_F_comm_X: \<open>range F = map_commutant X\<close>
    by auto
  have trans: \<open>\<exists>a\<in>range F. \<exists>b\<in>map_commutant (range F). (a \<circ>\<^sub>m b) m = Some m'\<close> for m m'
  proof -
    define a b where \<open>a n = Some (s (g m') n)\<close> and \<open>b = Xf (\<lambda>_. Some m')\<close> for n
    have \<open>(a \<circ>\<^sub>m b) m = Some m'\<close>
      by (auto intro!: simp: a_def b_def Xf_def)
    moreover have \<open>a \<in> range F\<close>
      by (auto intro!: exI[of _ \<open>\<lambda>_. Some (g m')\<close>]
          simp: a_def[abs_def] F_gs register_from_getter_setter_def image_iff)
    moreover have \<open>b \<in> map_commutant (range F)\<close>
      by (simp add: b_def double_map_commutant_grows local.X_def range_F_comm_X range_subsetD)
    ultimately show ?thesis
      by auto
  qed
  from range_F_comm_X trans show \<open>actual_cregister_range (range F)\<close>
    by (simp add: actual_cregister_range_def valid_cregister_range_def)
qed

lemma valid_cregister_range: 
  fixes F :: \<open>('b,'a) cregister\<close>
  assumes \<open>cregister F\<close>
  shows \<open>valid_cregister_range (range (apply_cregister F))\<close>
  using actual_cregister_range_def actual_register_range assms by blast


definition \<open>empty_cregister_range = {Map.empty, Some}\<close>
lemma valid_empty_cregister_range: \<open>valid_cregister_range empty_cregister_range\<close>
proof -
  have 1: \<open>a \<in> (empty_cregister_range :: 'a cupdate set)\<close>
    if \<open>a \<in> range (apply_cregister (empty_cregister :: (unit,_) cregister))\<close> for a
  proof -
    from that 
    obtain b :: \<open>unit \<rightharpoonup> unit\<close> where ab: \<open>a = apply_cregister (empty_cregister :: (unit,_) cregister) b\<close>
      by auto
    consider (some) \<open>b = Some\<close> | (empty) \<open>b = Map.empty\<close>
      by force
    then show ?thesis
      apply cases
      by (auto simp add: ab empty_cregister_range_def)
  qed

  have \<open>Map.empty \<in> range (apply_cregister (empty_cregister :: (unit,_) cregister))\<close>
    by (auto intro!: range_eqI[of _ _ Map.empty])
  moreover have \<open>Some \<in> range (apply_cregister (empty_cregister :: (unit,_) cregister))\<close>
    by (auto intro!: range_eqI[of _ _ Some])
  ultimately have 2: \<open>range (apply_cregister (empty_cregister :: (unit,_) cregister)) \<supseteq> (empty_cregister_range :: 'a cupdate set)\<close>
    by (auto simp add: empty_cregister_range_def)

  from 1 2 have \<open>range (apply_cregister (empty_cregister :: (unit,_) cregister)) = (empty_cregister_range :: 'a cupdate set)\<close>
    by auto
  then show ?thesis
    by (metis empty_cregister_is_register valid_cregister_range)
qed
lemma valid_cregister_range_UNIV: \<open>valid_cregister_range UNIV\<close>
proof -
  have \<open>range (apply_cregister cregister_id) = UNIV\<close>
    by simp
  then show ?thesis
    using cregister_id valid_cregister_range by fastforce
qed

typedef 'a CREGISTER = \<open>Collect valid_cregister_range :: 'a cupdate set set\<close>
  using valid_empty_cregister_range by blast
setup_lifting type_definition_CREGISTER

lift_definition ACTUAL_CREGISTER :: \<open>'b CREGISTER \<Rightarrow> bool\<close> is
  actual_cregister_range.

lift_definition CREGISTER_of :: \<open>('a,'b) cregister \<Rightarrow> 'b CREGISTER\<close> is
  \<open>\<lambda>F::('a,'b) cregister. if cregister F then range (apply_cregister F) :: 'b cupdate set else empty_cregister_range\<close>
  by (simp add: valid_empty_cregister_range valid_cregister_range)

instantiation CREGISTER :: (type) order begin
lift_definition less_eq_CREGISTER :: \<open>'a CREGISTER \<Rightarrow> 'a CREGISTER \<Rightarrow> bool\<close> is \<open>(\<subseteq>)\<close>.
lift_definition less_CREGISTER :: \<open>'a CREGISTER \<Rightarrow> 'a CREGISTER \<Rightarrow> bool\<close> is \<open>(\<subset>)\<close>.
instance
  apply (intro_classes; transfer)
  by auto
end

instantiation CREGISTER :: (type) bot begin
lift_definition bot_CREGISTER :: \<open>'a CREGISTER\<close> is empty_cregister_range
  by (simp add: valid_empty_cregister_range)
instance..
end

(* LEGACY *)
abbreviation (input) CREGISTER_unit :: \<open>'a CREGISTER\<close> where \<open>CREGISTER_unit \<equiv> bot\<close>

instantiation CREGISTER :: (type) top begin
lift_definition top_CREGISTER :: \<open>'a CREGISTER\<close> is UNIV
  by (simp add: valid_cregister_range_UNIV)
instance..
end

(* LEGACY *)
abbreviation (input) CREGISTER_all :: \<open>'a CREGISTER\<close> where \<open>CREGISTER_all \<equiv> top\<close>


(* lemma valid_cregister_range_Inter: 
  assumes \<open>\<And>x. x \<in> X \<Longrightarrow> valid_cregister_range x\<close>
  shows \<open>valid_cregister_range (\<Inter>X)\<close>
  using assms apply (auto simp: valid_cregister_range_def pairwise_all_def)
  by fast *)

instantiation CREGISTER :: (type) sup begin
lift_definition sup_CREGISTER :: \<open>'a CREGISTER \<Rightarrow> 'a CREGISTER \<Rightarrow> 'a CREGISTER\<close> is
  \<open>\<lambda>\<FF> \<GG> :: 'a cupdate set. map_commutant (map_commutant (\<FF> \<union> \<GG>))\<close>
  by (simp add: valid_cregister_range_def)
instance..
end

abbreviation (* LEGACY *) (input) \<open>CREGISTER_pair \<equiv> (sup :: 'a CREGISTER \<Rightarrow> _ \<Rightarrow> _)\<close>

lift_definition CCcompatible :: \<open>'a CREGISTER \<Rightarrow> 'a CREGISTER \<Rightarrow> bool\<close> is
  \<open>\<lambda>F G. \<forall>a\<in>F. \<forall>b\<in>G. a \<circ>\<^sub>m b = b \<circ>\<^sub>m a\<close>.

lift_definition Cccompatible :: \<open>'a CREGISTER \<Rightarrow> ('b,'a) cregister \<Rightarrow> bool\<close> is
  \<open>\<lambda>F G. cregister_raw G \<and> (\<forall>a\<in>F. \<forall>b. a \<circ>\<^sub>m G b = G b \<circ>\<^sub>m a)\<close>.

lemma Cccompatible_CCcompatible: \<open>Cccompatible F G \<longleftrightarrow> cregister G \<and> CCcompatible F (CREGISTER_of G)\<close>
  by (simp add: Cccompatible.rep_eq CCcompatible.rep_eq CREGISTER_of.rep_eq cregister.rep_eq)

lemma CCcompatible_sym: \<open>CCcompatible F G \<Longrightarrow> CCcompatible G F\<close> for F G :: \<open>'a CREGISTER\<close>
  by (auto simp: CCcompatible_def)

lemma ccompatible_CCcompatible: \<open>ccompatible F G \<longleftrightarrow> cregister F \<and> cregister G \<and> CCcompatible (CREGISTER_of F) (CREGISTER_of G)\<close>
  apply (transfer fixing: F G)
  apply (auto simp add: Laws_Classical.compatible_def ccompatible_def)
  by (simp_all add: cregister.rep_eq)

lemma CCcompatible_CREGISTER_ofI[simp]: \<open>ccompatible F G \<Longrightarrow> CCcompatible (CREGISTER_of F) (CREGISTER_of G)\<close>
  using ccompatible_CCcompatible by auto

lemma valid_cregister_range_mult:
  assumes \<open>valid_cregister_range \<FF>\<close>
  assumes \<open>a \<in> \<FF>\<close> and \<open>b \<in> \<FF>\<close>
  shows \<open>a \<circ>\<^sub>m b \<in> \<FF>\<close>
  using assms map_commutant_mult valid_cregister_range_def by blast
lemma tensor_map_update1: \<open>tensor_map (update1 x y) (update1 z w) = update1 (x,z) (y,w)\<close>
  by (auto intro!: ext simp add: update1_def[abs_def] tensor_update_def)

lemma Cccompatible_comp_right[simp]: "Cccompatible F G \<Longrightarrow> cregister H \<Longrightarrow> Cccompatible F (cregister_chain G H)"
  apply transfer by auto

lemma CREGISTER_mult: \<open>a \<circ>\<^sub>m b \<in> Rep_CREGISTER X\<close> if \<open>a \<in> Rep_CREGISTER X\<close> and \<open>b \<in> Rep_CREGISTER X\<close>
  using that Rep_CREGISTER map_commutant_mult apply (auto simp: valid_cregister_range_def)
  by blast

lemma CREGISTER_of_cregister_pair:
  fixes F :: \<open>('a,'c) cregister\<close> and G :: \<open>('b,'c) cregister\<close>
  assumes [simp]: \<open>ccompatible F G\<close>
  shows \<open>CREGISTER_of (cregister_pair F G) = CREGISTER_pair (CREGISTER_of F) (CREGISTER_of G)\<close>
proof (rule Rep_CREGISTER_inject[THEN iffD1], rule antisym)
  have [simp]: \<open>cregister F\<close> \<open>cregister G\<close>
    using assms ccompatible_register1 ccompatible_register2 by blast+
  define FG \<FF> \<GG> where \<open>FG = cregister_pair F G\<close> and \<open>\<FF> = CREGISTER_of F\<close> and \<open>\<GG> = CREGISTER_of G\<close>
  have [simp]: \<open>cregister FG\<close>
    by (simp add: FG_def)
  show \<open>Rep_CREGISTER (CREGISTER_of FG)
          \<subseteq> Rep_CREGISTER (CREGISTER_pair \<FF> \<GG>)\<close>
  proof (rule subsetI)
    fix c :: \<open>'c cupdate\<close>
    assume \<open>c \<in> Rep_CREGISTER (CREGISTER_of FG)\<close>
    then obtain ab where ab: \<open>c = apply_cregister FG ab\<close>
      apply atomize_elim
      using assms by (auto simp add: CREGISTER_of.rep_eq FG_def)
    define AB where \<open>AB = {(update1 (fst x) (fst y), update1 (snd x) (snd y)) |x y. ab x = Some y}\<close>
    have tensor_AB: \<open>case_prod tensor_map ` AB = {update1 x y |x y. ab x = Some y}\<close>
      apply (simp only: set_compr_2_image_collect AB_def)
      by (simp add: image_image case_prod_beta tensor_map_update1)
    then have ab_AB: \<open>ab = partial_fun_Sup (case_prod tensor_map ` AB)\<close>
      using partial_fun_Sup_update1[of ab] by simp

    from ab_AB have \<open>c = apply_cregister FG (partial_fun_Sup (case_prod tensor_map ` AB))\<close>
      by (simp add: ab)
    also have \<open>\<dots> = partial_fun_Sup ((\<lambda>(a,b). apply_cregister FG (tensor_map a b)) ` AB)\<close>
      apply (subst cregister_partial_fun_Sup[symmetric])
      by (simp_all add: image_image case_prod_beta)
    also have \<open>\<dots> = partial_fun_Sup ((\<lambda>(a,b). apply_cregister F a \<circ>\<^sub>m apply_cregister G b) ` AB)\<close>
      by (simp add: apply_cregister_pair assms FG_def)
    also have \<open>\<dots> \<in> Rep_CREGISTER (CREGISTER_pair \<FF> \<GG>)\<close>
    proof -
      have \<open>apply_cregister F a \<circ>\<^sub>m apply_cregister G b \<in> Rep_CREGISTER (CREGISTER_pair \<FF> \<GG>)\<close> for a b
      proof -
        have Fa: \<open>apply_cregister F a \<in> Rep_CREGISTER (CREGISTER_pair \<FF> \<GG>)\<close>
          using double_map_commutant_grows
          by (force simp: sup_CREGISTER.rep_eq CREGISTER_of.rep_eq \<FF>_def)
        have Gb: \<open>apply_cregister G b \<in> Rep_CREGISTER (CREGISTER_pair \<FF> \<GG>)\<close>
          using double_map_commutant_grows
          by (force simp: sup_CREGISTER.rep_eq CREGISTER_of.rep_eq \<GG>_def)
        from Fa Gb show ?thesis
          by (rule CREGISTER_mult)
      qed
      then have 1: \<open>(\<lambda>(a,b). apply_cregister F a \<circ>\<^sub>m apply_cregister G b) ` AB 
                      \<subseteq> Rep_CREGISTER (CREGISTER_pair \<FF> \<GG>)\<close>
        by fast
      have \<open>pairwise_all partial_fun_compatible ((\<lambda>(a,b). tensor_map a b) ` AB)\<close>
        by (simp only: tensor_AB partial_fun_compatible_update1)
      then have \<open>pairwise_all partial_fun_compatible (apply_cregister FG ` (\<lambda>(a,b). tensor_map a b) ` AB)\<close>
        apply (auto simp: pairwise_all_def)
        by (metis (no_types, opaque_lifting) FG_def assms cregister.rep_eq cregister_partial_fun_compatible prod.simps(2))
      then have 2: \<open>pairwise_all partial_fun_compatible ((\<lambda>(a,b). apply_cregister F a \<circ>\<^sub>m apply_cregister G b) ` AB)\<close>
        by (simp add: apply_cregister_pair FG_def image_image case_prod_beta)
      from 1 2 show ?thesis
        using Rep_CREGISTER[of \<open>CREGISTER_pair \<FF> \<GG>\<close>]
        by (simp add: sup_CREGISTER.rep_eq map_commutant_Sup_closed)
    qed
    finally show \<open>c \<in> \<dots>\<close>
      by -
  qed
  show \<open>Rep_CREGISTER (CREGISTER_pair (CREGISTER_of F) (CREGISTER_of G))
    \<subseteq> Rep_CREGISTER (CREGISTER_of (cregister_pair F G))\<close>
  proof -
    have \<open>c \<in> Rep_CREGISTER (CREGISTER_of (cregister_pair F G))\<close> if \<open>c \<in> Rep_CREGISTER (CREGISTER_of F)\<close> for c
    proof -
      from that obtain a where \<open>c = apply_cregister F a\<close>
        apply atomize_elim
        by (auto simp: CREGISTER_of.rep_eq)
      then show ?thesis
        by (auto intro!: range_eqI[of _ _ \<open>tensor_map a Some\<close>] simp add: CREGISTER_of.rep_eq apply_cregister_pair)
    qed
    moreover have \<open>c \<in> Rep_CREGISTER (CREGISTER_of (cregister_pair F G))\<close> if \<open>c \<in> Rep_CREGISTER (CREGISTER_of G)\<close> for c
    proof -
      from that obtain b where \<open>c = apply_cregister G b\<close>
        apply atomize_elim
        by (auto simp: CREGISTER_of.rep_eq)
      then show ?thesis
        by (auto intro!: range_eqI[of _ _ \<open>tensor_map Some b\<close>] simp add: CREGISTER_of.rep_eq apply_cregister_pair)
    qed
    ultimately 
    have \<open>Rep_CREGISTER (CREGISTER_of F) \<union> Rep_CREGISTER (CREGISTER_of G) 
        \<subseteq> Rep_CREGISTER (CREGISTER_of (cregister_pair F G))\<close>
      by auto
    then have \<open>Rep_CREGISTER (CREGISTER_pair (CREGISTER_of F) (CREGISTER_of G))
             \<subseteq> map_commutant (map_commutant (Rep_CREGISTER (CREGISTER_of (cregister_pair F G))))\<close>
      apply (simp add: sup_CREGISTER.rep_eq)
      apply (intro map_commutant_antimono)
      by simp
    also have \<open>\<dots> = Rep_CREGISTER (CREGISTER_of (cregister_pair F G))\<close>
      using Rep_CREGISTER valid_cregister_range_def by auto
    finally show ?thesis
      by -
  qed
qed

lemma CCcompatible3I[simp]: \<open>CCcompatible F G \<Longrightarrow> CCcompatible G H \<Longrightarrow> CCcompatible F H \<Longrightarrow> CCcompatible (CREGISTER_pair F G) H\<close>
  apply transfer apply (auto simp: map_commutant_def)
  by (metis Un_iff)
lemma CCcompatible3I'[simp]: \<open>CCcompatible F G \<Longrightarrow> CCcompatible F H \<Longrightarrow> CCcompatible G H \<Longrightarrow> CCcompatible F (CREGISTER_pair G H)\<close> 
  using CCcompatible3I CCcompatible_sym by blast

lemma Cccompatible3I[simp]: \<open>CCcompatible F G \<Longrightarrow> Cccompatible G H \<Longrightarrow> Cccompatible F H \<Longrightarrow> Cccompatible (CREGISTER_pair F G) H\<close>
  by (simp add: Cccompatible_CCcompatible)
lemma Cccompatible3I'[simp]: \<open>Cccompatible F G \<Longrightarrow> Cccompatible F H \<Longrightarrow> ccompatible G H \<Longrightarrow> Cccompatible F (cregister_pair G H)\<close>
  by (simp add: Cccompatible_CCcompatible CREGISTER_of_cregister_pair)

lemma CREGISTER_of_iso: \<open>CREGISTER_of I = CREGISTER_all\<close> if \<open>iso_cregister I\<close>
proof -
  have \<open>x \<in> range (apply_cregister I)\<close> for x
    apply (rule range_eqI[where x=\<open>apply_cregister (cregister_inv I) x\<close>])
    by (metis inj_cregister inv_f_eq iso_cregister_def iso_cregister_inv_iso iso_cregister_inv_iso_apply that)
  then show ?thesis
    apply (transfer fixing: I)
    using that by (auto simp: iso_cregister_def)
qed


instantiation CREGISTER :: (type) uminus begin
lift_definition uminus_CREGISTER :: \<open>'a CREGISTER \<Rightarrow> 'a CREGISTER\<close> is map_commutant
  by (simp add: valid_cregister_range_def)
instance..
end

abbreviation (* LEGACY *) (input) \<open>CCOMPLEMENT \<equiv> (uminus :: 'a CREGISTER \<Rightarrow> _)\<close>

lemma Cccompatible_antimono_left: \<open>A \<le> B \<Longrightarrow> Cccompatible B C \<Longrightarrow> Cccompatible A C\<close>
  apply transfer by auto

lemma Cccompatible_CREGISTER_of: \<open>Cccompatible (CREGISTER_of A) B \<longleftrightarrow> ccompatible A B \<or> (cregister B \<and> A = non_cregister)\<close>
  unfolding CREGISTER_of.rep_eq Cccompatible.rep_eq
  apply transfer
  by (auto simp add: non_cregister_raw empty_cregister_range_def ccompatible_raw_def)

lemma Cccompatible_CREGISTER_ofI[simp]: \<open>ccompatible F G \<Longrightarrow> Cccompatible (CREGISTER_of F) G\<close>
  by (simp add: Cccompatible_CREGISTER_of)

definition \<open>cregister_le F G = (cregister F \<and> cregister G \<and> CREGISTER_of F \<le> CREGISTER_of G)\<close>

end