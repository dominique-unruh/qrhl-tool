theory Classical_Reg_Ranges
  imports Classical_Registers
begin


(* Equivalence class of cregisters *)
definition valid_cregister_range :: \<open>'a cupdate set \<Rightarrow> bool\<close> where
  \<open>valid_cregister_range \<FF> \<longleftrightarrow> map_commutant (map_commutant \<FF>) = \<FF>\<close>

(* definition actual_cregister_range :: \<open>'a cupdate set \<Rightarrow> bool\<close> where
  \<open>actual_cregister_range \<FF> \<longleftrightarrow> valid_cregister_range \<FF> \<and> (\<forall>m m'. \<exists>a\<in>\<FF>. \<exists>b\<in>map_commutant \<FF>. (a \<circ>\<^sub>m b) m = Some m')\<close> *)

definition actual_cregister_range :: \<open>'a cupdate set \<Rightarrow> bool\<close> where
  \<open>actual_cregister_range \<FF> \<longleftrightarrow> (\<exists>(f :: 'a \<Rightarrow> 'a\<times>'a) L R. 
    inj f \<and> range f = L \<times> R \<and>
    \<FF> = { inv_map (Some o f) \<circ>\<^sub>m (tensor_map a (Some|`R)) o f | a. dom a \<subseteq> L \<and> ran a \<subseteq> L})\<close>

lemma actual_register_range: 
  fixes F :: \<open>('b,'a) cregister\<close>
  assumes \<open>cregister F\<close>
  shows \<open>actual_cregister_range (range (apply_cregister F))\<close>
proof -
  let ?goal = ?thesis
  from ccomplement_exists[OF assms]
  have \<open>let 'c::type = ccomplement_domain F in ?goal\<close>
  proof with_type_mp
    case with_type_mp
    then obtain G :: \<open>('c, 'a) cregister\<close> where \<open>ccomplements F G\<close>
      by fastforce
    then have [iff]: \<open>iso_cregister (cregister_pair F G)\<close>
      by (simp add: ccomplements.rep_eq complements_def cregister_pair.rep_eq iso_cregister_rep_eq)
    then have [iff]: \<open>cregister (cregister_pair F G)\<close>
      using iso_cregister_def by blast
    then have [iff]: \<open>cregister G\<close>
      using ccompatible_register2 by blast

    define g where \<open>g = getter (cregister_pair F G)\<close>
    have \<open>bij g\<close>
      unfolding g_def
      apply (intro bij_def[THEN iffD2] conjI surj_getter iso_cregister_injective_getter[THEN iffD1])
      by auto
    have g_FG: \<open>g m = (getter F m, getter G m)\<close> for m
      by (simp add: g_def getter_pair)
    define iBA :: \<open>'b \<Rightarrow> 'a\<close> where \<open>iBA b = setter F b undefined\<close> for b
    have \<open>inj iBA\<close>
      apply (simp add: inj_on_def iBA_def getter_setter_same)
      by (metis assms getter_setter_same)
    define iCA :: \<open>'c \<Rightarrow> 'a\<close> where \<open>iCA c = setter G c undefined\<close> for c
    have \<open>inj iCA\<close>
      apply (simp add: inj_on_def iCA_def getter_setter_same)
      by (metis \<open>cregister G\<close> getter_setter_same)
    define L R f where \<open>L = range iBA\<close> and \<open>R = range iCA\<close> and \<open>f m = (iBA (getter F m), iCA (getter G m))\<close> for m
    have 1: \<open>inj f\<close>
      unfolding f_def 
      by (smt (verit, del_insts) g_FG \<open>bij g\<close> \<open>inj iBA\<close> \<open>inj iCA\<close> bij_betw_iff_bijections injD inj_on_def prod.simps(1))
    have 2: \<open>range f = L \<times> R\<close>
    proof -
      have \<open>range f = range (map_prod iBA iCA o g)\<close>
        by (simp add: f_def g_def map_prod_def getter_pair)
      also have \<open>\<dots> = map_prod iBA iCA ` range g\<close>
        by (simp add: image_image)
      also have \<open>\<dots> = range (map_prod iBA iCA)\<close>
        by (metis \<open>bij g\<close> bij_betw_imp_surj_on)
      also have \<open>\<dots> = L \<times> R\<close>
        by (auto simp add: L_def R_def)
      finally show ?thesis
        by -
    qed
    have Fa_rewrite: \<open>(inv_map (Some o f) \<circ>\<^sub>m tensor_map a' (Some |` R) \<circ> f) = apply_cregister F a\<close>
      if \<open>inv_map (Some o iBA) \<circ>\<^sub>m a' \<circ>\<^sub>m (Some o iBA) = a\<close>
      for a a'
    proof -
      have \<open>(inv_map (Some o f) \<circ>\<^sub>m tensor_map a' (Some |` R) \<circ> f)
            = inv_map (Some o f) \<circ>\<^sub>m (tensor_map a' (Some |` R)) \<circ>\<^sub>m (tensor_map (Some o iBA) (Some o iCA))
                    \<circ>\<^sub>m (Some o g)\<close>
        by (auto intro!: ext simp: f_def tensor_update_def g_FG)
      also have \<open>\<dots> = inv_map (tensor_map (Some o iBA) (Some o iCA) \<circ>\<^sub>m (Some o g)) \<circ>\<^sub>m
                   (tensor_map a' (Some |` R)) \<circ>\<^sub>m (tensor_map (Some o iBA) (Some o iCA))
                    \<circ>\<^sub>m (Some o g)\<close>
        by (simp add: f_def[abs_def] tensor_update_def[abs_def] o_def map_comp_def g_FG)
      also have \<open>\<dots> = inv_map (Some o g) \<circ>\<^sub>m inv_map (tensor_map (Some o iBA) (Some o iCA)) \<circ>\<^sub>m
                   (tensor_map a' (Some |` R)) \<circ>\<^sub>m (tensor_map (Some o iBA) (Some o iCA))
                    \<circ>\<^sub>m (Some o g)\<close>
        apply (subst inv_map_comp)
        using \<open>bij g\<close> by (simp_all add: \<open>inj iBA\<close> \<open>inj iCA\<close> inj_map_tensor_update bij_betw_def)
      also have \<open>\<dots> = inv_map (Some o g) \<circ>\<^sub>m tensor_map (inv_map (Some o iBA)) (inv_map (Some o iCA)) \<circ>\<^sub>m
                   (tensor_map a' (Some |` R)) \<circ>\<^sub>m (tensor_map (Some o iBA) (Some o iCA)) \<circ>\<^sub>m (Some o g)\<close>
        apply (subst inv_map_tensor_update)
        using \<open>inj iBA\<close>  \<open>inj iCA\<close> 
        by (auto intro!: simp: )
      also have \<open>\<dots> = inv_map (Some o g) \<circ>\<^sub>m tensor_map (inv_map (Some o iBA) \<circ>\<^sub>m a' \<circ>\<^sub>m (Some o iBA)) (inv_map (Some o iCA) \<circ>\<^sub>m (Some |` R) \<circ>\<^sub>m (Some o iCA))
                          \<circ>\<^sub>m (Some o g)\<close>
        by (simp add: tensor_update_mult[symmetric] comp_update_assoc)
      also have \<open>\<dots> = inv_map (Some o g) \<circ>\<^sub>m tensor_map a (inv_map (Some o iCA) \<circ>\<^sub>m (Some |` R) \<circ>\<^sub>m (Some o iCA)) \<circ>\<^sub>m (Some o g)\<close>
        using that
        by (simp add: comp_update_assoc flip: map_comp_Some_map_option o_def[of Some iBA])
      also have \<open>\<dots> = inv_map (Some o g) \<circ>\<^sub>m tensor_map a Some \<circ>\<^sub>m (Some o g)\<close>
      proof -
        have \<open>inv_map (Some \<circ> iCA) \<circ>\<^sub>m Some |` R \<circ>\<^sub>m (Some \<circ> iCA) = Some\<close>
          apply (auto intro!: ext simp: map_comp_def restrict_map_def inv_map_def R_def o_def)
          apply (subst inv_f_f)
           apply (meson \<open>inj iCA\<close> inj_on_def option.inject)
          by simp
        then show ?thesis
          by simp
      qed
      also have \<open>\<dots> = apply_cregister (cregister_pair F G) (tensor_map a Some)\<close>
        by (simp add: iso_register_from_getter o_def g_def)
      also have \<open>\<dots> = apply_cregister F a\<close>
        by (simp add: apply_cregister_pair apply_cregister_of_id)
      finally show ?thesis
        by -
    qed
    have 3: \<open>range (apply_cregister F) = { inv_map (Some o f) \<circ>\<^sub>m (tensor_map a (Some|`R)) o f | a. dom a \<subseteq> L \<and> ran a \<subseteq> L }\<close>
    proof (intro Set.set_eqI iffI)
      fix b assume \<open>b \<in> range (apply_cregister F)\<close>
      then obtain a where b_a: \<open>b = apply_cregister F a\<close>
        by fastforce
      define a' where \<open>a' = map_option iBA o a \<circ>\<^sub>m inv_map (Some o iBA)\<close>
      have dom: \<open>dom a' \<subseteq> L\<close>
        by (auto simp add: inv_map_def dom_def L_def a'_def map_comp_def split: option.split)
      have ran: \<open>ran a' \<subseteq> L\<close>
        by (auto simp add: ran_def L_def a'_def map_comp_def split: option.split)
      have ba': \<open>b = inv_map (Some o f) \<circ>\<^sub>m tensor_map a' (Some |` R) \<circ> f\<close>
      proof -
        have \<open>inj (Some o iBA)\<close>
          by (simp add: \<open>inj iBA\<close> comp_inj_on)
        then have inv_map: \<open>inv_map (Some \<circ> iBA) \<circ>\<^sub>m (Some \<circ> iBA) = Some\<close>
          apply (simp add: map_comp_def inv_map_def o_def)
          apply (subst inv_f_f)
          by simp_all
        then have \<open>inv_map (Some o iBA) \<circ>\<^sub>m a' \<circ>\<^sub>m (Some o iBA) = a\<close>
          apply (simp add: a'_def comp_update_assoc inv_map flip: map_comp_Some_map_option o_def[of Some iBA])
          by (simp add: inv_map flip: comp_update_assoc)
        then show ?thesis
          by (simp add: Fa_rewrite a'_def b_a)
      qed
      from ran dom ba'
      show \<open>b \<in> { inv_map (Some o f) \<circ>\<^sub>m tensor_map a (Some |` R) \<circ> f |a. dom a \<subseteq> L \<and> ran a \<subseteq> L }\<close>
        by fastforce
    next
      fix b assume \<open>b \<in> { inv_map (Some o f) \<circ>\<^sub>m tensor_map a (Some |` R) \<circ> f |a. dom a \<subseteq> L \<and> ran a \<subseteq> L }\<close>
      then obtain a where b_a: \<open>b = inv_map (Some o f) \<circ>\<^sub>m tensor_map a (Some |` R) \<circ> f\<close> and \<open>dom a \<subseteq> L\<close> and \<open>ran a \<subseteq> L\<close>
        by auto
      define a' :: \<open>'b \<Rightarrow> 'b option\<close> where \<open>a' = inv_map (Some o iBA) \<circ>\<^sub>m a \<circ>\<^sub>m (Some o iBA)\<close>
      have \<open>apply_cregister F a' = b\<close>
        apply (subst Fa_rewrite[symmetric])
        by (simp_all add: a'_def b_a)
      then show \<open>b \<in> range (apply_cregister F)\<close>
        by fast
    qed
    from 1 2 3
    show ?goal
      by (auto intro!: simp: actual_cregister_range_def)
  qed
  from this[cancel_with_type]
  show ?goal
    by -
qed

(* TODO Part of this is for lemma valid_cregister_range below! *)

(* lemma actual_register_range: 
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
        by (simp add: * )
      also have \<open>\<dots> = map_option (\<lambda>x. s (g x) m) (a m)\<close>
        by (simp add: map_comp_Some_map_option option.map_comp o_def)
      also have \<open>\<dots> = ((\<lambda>x. Some (s (g x) m)) \<circ>\<^sub>m a) m\<close>
        by (simp add: map_comp_Some_map_option)
      also have \<open>\<dots> = a m\<close>
        by (simp flip: * )
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
qed *)

lemma valid_cregister_range: 
  fixes F :: \<open>('b,'a) cregister\<close>
  assumes \<open>cregister F\<close>
  shows \<open>valid_cregister_range (range (apply_cregister F))\<close>
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
        by (simp add: * )
      also have \<open>\<dots> = map_option (\<lambda>x. s (g x) m) (a m)\<close>
        by (simp add: map_comp_Some_map_option option.map_comp o_def)
      also have \<open>\<dots> = ((\<lambda>x. Some (s (g x) m)) \<circ>\<^sub>m a) m\<close>
        by (simp add: map_comp_Some_map_option)
      also have \<open>\<dots> = a m\<close>
        by (simp flip: * )
      finally show \<open>F a' m = a m\<close>
        by -
    qed
    then show ?thesis
      by auto
  qed
  from 1 2 have range_F_comm_X: \<open>range F = map_commutant X\<close>
    by auto
  from range_F_comm_X show \<open>valid_cregister_range (range F)\<close>
    by (simp add: actual_cregister_range_def valid_cregister_range_def)
qed


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

instantiation CREGISTER :: (type) inf begin
lift_definition inf_CREGISTER :: \<open>'a CREGISTER \<Rightarrow> 'a CREGISTER \<Rightarrow> 'a CREGISTER\<close> is
  \<open>\<lambda>\<FF> \<GG> :: 'a cupdate set. \<FF> \<inter> \<GG>\<close>
proof (unfold mem_Collect_eq)
  fix F G :: \<open>('a \<Rightarrow> 'a option) set\<close>
  assume \<open>valid_cregister_range F\<close>
  assume \<open>valid_cregister_range G\<close>
  have \<open>map_commutant (map_commutant (F \<inter> G)) \<supseteq> F \<inter> G\<close>
    by (simp add: double_map_commutant_grows)
  moreover have \<open>map_commutant (map_commutant (F \<inter> G)) \<subseteq> F\<close>
    if \<open>valid_cregister_range F\<close> for F G :: \<open>('a \<Rightarrow> 'a option) set\<close>
  proof -
    have \<open>map_commutant (map_commutant (F \<inter> G)) \<subseteq> map_commutant (map_commutant F)\<close>
      by (simp add: map_commutant_antimono)
    also have \<open>\<dots> = F\<close>
      using that valid_cregister_range_def by blast
    finally show ?thesis
      by -
  qed
  ultimately show \<open>valid_cregister_range (F \<inter> G)\<close>
    using \<open>valid_cregister_range F\<close> \<open>valid_cregister_range G\<close>
    apply (auto simp add: valid_cregister_range_def)
    by (metis Int_commute in_mono)
qed
instance..
end

abbreviation (* LEGACY *) (input) \<open>CREGISTER_pair \<equiv> (sup :: 'a CREGISTER \<Rightarrow> _ \<Rightarrow> _)\<close>

instantiation CREGISTER :: (type) Sup begin
lift_definition Sup_CREGISTER :: \<open>'a CREGISTER set \<Rightarrow> 'a CREGISTER\<close> is
  \<open>\<lambda>X :: 'a cupdate set set. map_commutant (map_commutant (\<Union>X))\<close>
  by (auto simp add: valid_cregister_range_def)
instance..
end

instantiation CREGISTER :: (type) Inf begin
lift_definition Inf_CREGISTER :: \<open>'a CREGISTER set \<Rightarrow> 'a CREGISTER\<close> is
  \<open>\<lambda>X :: 'a cupdate set set. \<Inter> X\<close>
proof (unfold mem_Collect_eq)
  fix X :: \<open>('a \<Rightarrow> 'a option) set set\<close>
  assume valid: \<open>valid_cregister_range F\<close> if \<open>F \<in> X\<close> for F
  have \<open>map_commutant (map_commutant (\<Inter> X)) \<supseteq> \<Inter> X\<close>
    by (simp add: double_map_commutant_grows)
  moreover have \<open>map_commutant (map_commutant (\<Inter> X)) \<subseteq> F\<close>
    if \<open>valid_cregister_range F\<close> and \<open>F \<in> X\<close> for F :: \<open>('a \<Rightarrow> 'a option) set\<close>
  proof -
    have \<open>map_commutant (map_commutant (\<Inter> X)) \<subseteq> map_commutant (map_commutant F)\<close>
      using that by (auto intro!: map_commutant_antimono)
    also have \<open>\<dots> = F\<close>
      using that valid_cregister_range_def by blast
    finally show ?thesis
      by -
  qed
  ultimately show \<open>valid_cregister_range (\<Inter> X)\<close>
    using valid
    by (auto simp add: valid_cregister_range_def)
qed
instance..
end


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


instantiation CREGISTER :: (type) \<open>{uminus,minus}\<close> begin
lift_definition uminus_CREGISTER :: \<open>'a CREGISTER \<Rightarrow> 'a CREGISTER\<close> is map_commutant
  by (simp add: valid_cregister_range_def)
lift_definition minus_CREGISTER :: \<open>'a CREGISTER \<Rightarrow> 'a CREGISTER \<Rightarrow> 'a CREGISTER\<close> is
  \<open>\<lambda>F G. F \<inter> map_commutant G\<close>
  by (metis (no_types, lifting) eq_onp_same_args inf_CREGISTER.rsp rel_fun_eq_onp_rel uminus_CREGISTER.rsp)
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

lemma map_commutant_empty_cregister_range[simp]: \<open>map_commutant empty_cregister_range = UNIV\<close>
  by (simp add: map_commutant_def empty_cregister_range_def)

lemma double_complement_CREGISTER[simp]:
  fixes F :: \<open>'a CREGISTER\<close>
  shows \<open>- (- F) = F\<close>
  apply transfer
  by (simp add: valid_cregister_range_def)

lemma demorgan_CREGISTER_sup:
  fixes F G :: \<open>'a CREGISTER\<close>
  shows \<open>F \<squnion> G = - (- F \<sqinter> - G)\<close>
  apply transfer
  by (auto simp: map_commutant_def)

lemma demorgan_CREGISTER_Sup:
  fixes X :: \<open>'a CREGISTER set\<close>
  shows \<open>\<Squnion> X = - \<Sqinter> (uminus ` X)\<close>
  apply transfer
  by (auto simp: map_commutant_def)

instance CREGISTER :: (type) lattice
proof
  fix x y z :: \<open>'a CREGISTER\<close>
  show \<open>x \<sqinter> y \<le> x\<close>
    apply transfer'
    by simp
  show \<open>x \<sqinter> y \<le> y\<close>
    apply transfer'
    by simp
  show \<open>x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> y \<sqinter> z\<close>
    apply transfer'
    by simp
  show \<open>x \<le> x \<squnion> y\<close>
    apply transfer'
    using double_map_commutant_grows by fastforce
  show \<open>y \<le> x \<squnion> y\<close>
    apply transfer'
    using double_map_commutant_grows by fastforce
  show \<open>y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x\<close>
    apply (auto intro!: simp: demorgan_CREGISTER_sup)
    by (metis double_complement_CREGISTER inf_CREGISTER.rep_eq le_infI less_eq_CREGISTER.rep_eq map_commutant_antimono uminus_CREGISTER.rep_eq)
qed

lemma compl_le_compl_iff_CREGISTER:
  fixes x y:: \<open>'a CREGISTER\<close>
  shows \<open>(- x \<le> - y) = (y \<le> x)\<close>
  apply transfer
  by (metis CollectD map_commutant_antimono valid_cregister_range_def)

instance CREGISTER :: (type) bounded_lattice
proof
  fix x :: \<open>'a CREGISTER\<close>
  show bot: \<open>\<bottom> \<le> x\<close>
    apply transfer
    apply auto
    by (smt (z3) UNIV_I map_commutant_def map_commutant_empty_cregister_range mem_Collect_eq valid_cregister_range_def)
  show \<open>x \<le> \<top>\<close> for x :: \<open>'a CREGISTER\<close>
    apply transfer'
    by simp
qed

instance CREGISTER :: (type) complete_lattice
proof
  fix x y z :: \<open>'a CREGISTER\<close> and X :: \<open>'a CREGISTER set\<close>
  show \<open>x \<in> X \<Longrightarrow> \<Sqinter> X \<le> x\<close>
    apply transfer'
    by blast
  show Inf: \<open>(\<And>x. x \<in> X \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> \<Sqinter> X\<close> for z :: \<open>'a CREGISTER\<close> and X :: \<open>'a CREGISTER set\<close>
    apply transfer
    by blast
  show \<open>x \<in> X \<Longrightarrow> x \<le> \<Squnion> X\<close>
    apply transfer
    using double_map_commutant_grows by fastforce
  show \<open>(\<And>x. x \<in> X \<Longrightarrow> x \<le> z) \<Longrightarrow> \<Squnion> X \<le> z\<close>
    apply (rule compl_le_compl_iff_CREGISTER[THEN iffD1])
    by (auto intro!: Inf simp add: demorgan_CREGISTER_Sup compl_le_compl_iff_CREGISTER)
  show Inf_empty: \<open>\<Sqinter> {} = (\<top> :: 'a CREGISTER)\<close>
    apply transfer'
    by simp
  show \<open>\<Squnion> {} = (\<bottom> :: 'a CREGISTER)\<close>
    apply (simp add: demorgan_CREGISTER_Sup Inf_empty)
    apply transfer'
    using valid_cregister_range_def valid_empty_cregister_range by fastforce
qed

(*
Is it one?

instance CREGISTER :: (type) complemented_lattice
proof
  fix x y z :: \<open>'a CREGISTER\<close>
  show \<open>x - y = x \<sqinter> - y\<close>
    apply transfer'
    by blast
  show \<open>x \<sqinter> - x = \<bottom>\<close>
  proof (intro antisym bot_least, transfer, unfold mem_Collect_eq)
    fix x :: \<open>('a \<Rightarrow> 'a option) set\<close>
    assume \<open>valid_cregister_range x\<close>
    show \<open>x \<inter> map_commutant x \<subseteq> empty_cregister_range\<close>
    proof (rule subsetI)
      fix f assume \<open>f \<in> x \<inter> map_commutant x\<close>
      show \<open>f \<in> empty_cregister_range\<close>
        by x
    qed
  qed
  show \<open>x \<squnion> - x = \<top>\<close>
    using \<open>x \<sqinter> - x = \<bottom>\<close>
    by (metis bot_CREGISTER.rep_eq demorgan_CREGISTER_sup double_complement_CREGISTER double_map_commutant_grows inf_absorb1 inf_commute less_eq_CREGISTER.rep_eq map_commutant_empty_cregister_range top_CREGISTER.rep_eq uminus_CREGISTER.rep_eq)
qed
*)

lemma CREGISTER_of_non_cregister[simp]: \<open>CREGISTER_of non_cregister = \<bottom>\<close>
  by (simp add: CREGISTER_of.abs_eq bot_CREGISTER_def)

text \<open>\<^term>\<open>copy_CREGISTER_from F m n\<close> takes the content of \<^term>\<open>F\<close> from m and everything outside of \<^term>\<open>F\<close> from n
  and returns the combination. See \<^term>\<open>copy_CREGISTER_from_CREGISTER_of\<close> below.\<close>
lift_definition copy_CREGISTER_from :: \<open>'a CREGISTER \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> is
  \<open>\<lambda>F m0 m1. SOME m. \<exists>a\<in>F. \<exists>b\<in>map_commutant F. Some m = a m1 \<and> Some m = b m0\<close>.

lemma copy_CREGISTER_from_bot[simp]:
  \<open>copy_CREGISTER_from \<bottom> m0 m1 = m1\<close>
proof -
  have [simp]: \<open>Some \<in> empty_cregister_range\<close>
    by (simp add: empty_cregister_range_def)
  have \<open>\<exists>a\<in>empty_cregister_range. \<exists>b\<in>map_commutant empty_cregister_range. Some m1 = a m1 \<and> Some m1 = b m0\<close>
    apply (rule bexI[of _ Some], rule bexI[of _ \<open>\<lambda>_. Some m1\<close>])
    by auto
  moreover have \<open>m = m1\<close> 
    if \<open>\<exists>a\<in>empty_cregister_range. \<exists>b\<in>map_commutant empty_cregister_range. Some m = a m1 \<and> Some m = b m0\<close> for m
    using that by (simp add: empty_cregister_range_def)
  ultimately have \<open>(SOME m. \<exists>a\<in>empty_cregister_range. \<exists>b\<in>map_commutant empty_cregister_range. Some m = a m1 \<and> Some m = b m0) = m1\<close>
    by (rule some_equality)
  then show ?thesis
    apply (transfer' fixing: m0 m1)
    by simp
qed

lemma map_commutant_range_apply_cregister:
  \<open>map_commutant (range (apply_cregister F)) 
    = range (\<lambda>f m. case f (setter F m0 m) of None \<Rightarrow> None | Some m' \<Rightarrow> Some (setter F (getter F m) m'))\<close>
proof (cases \<open>cregister F\<close>)
  case True
  note [simp] = True
  define g s where \<open>g = getter F\<close> and \<open>s = setter F\<close>
  have [simp]: \<open>g (s x m) = x\<close> for x m
    by (simp add: g_def s_def)
  have [simp]: \<open>s x (s y m) = s x m\<close> for x y m
    by (simp add: s_def)
  have [simp]: \<open>s (g m) m = m\<close> for m
    by (simp add: g_def s_def)
  have F_Some_x: \<open>apply_cregister F (\<lambda>_. Some x) = Some o s x\<close> for x
    apply (subst apply_cregister_getter_setter[OF True, abs_def])
    by (simp add: s_def o_def)
  show ?thesis
  proof (intro Set.set_eqI iffI range_eqI ext)
    fix h
    assume \<open>h \<in> range
              (\<lambda>f m. case f (Classical_Registers.setter F m0 m) of None \<Rightarrow> None
                      | Some m' \<Rightarrow> Some (Classical_Registers.setter F (Classical_Registers.getter F m) m'))\<close>
    then obtain f where h_f: \<open>h m = (case f (Classical_Registers.setter F m0 m) of None \<Rightarrow> None
                      | Some m' \<Rightarrow> Some (Classical_Registers.setter F (Classical_Registers.getter F m) m'))\<close> for m
      by auto
    have \<open>(h \<circ>\<^sub>m apply_cregister F a) m = (apply_cregister F a \<circ>\<^sub>m h) m\<close>
      for m a 
      unfolding map_comp_def h_f apply_cregister_getter_setter[OF True, folded g_def s_def, abs_def] 
        g_def[symmetric] s_def[symmetric]
      apply (cases \<open>a (g m)\<close>; cases \<open>f (s m0 m)\<close>)
      by (auto intro!: ext)
    then show \<open>h \<in> map_commutant (range (apply_cregister F))\<close>
      by (auto intro!: ext simp: map_commutant_def)
  next
    fix h m assume \<open>h \<in> map_commutant (range (apply_cregister F))\<close>
    then have comm: \<open>(h \<circ>\<^sub>m apply_cregister F a) m = (apply_cregister F a \<circ>\<^sub>m h) m\<close> for a m
      by (simp add: map_commutant_def)
    have \<open>(case h (s m0 m) of None \<Rightarrow> None | Some m' \<Rightarrow> Some (s (g m) m'))
        = ((Some o s (g m)) \<circ>\<^sub>m h) (s m0 m)\<close>
      by (simp add: map_comp_def o_def)
    also have \<open>\<dots> = (apply_cregister F (\<lambda>_. Some (g m)) \<circ>\<^sub>m h) (s m0 m)\<close>
      by (simp add: F_Some_x)
    also have \<open>\<dots> = (h \<circ>\<^sub>m apply_cregister F (\<lambda>_. Some (g m))) (s m0 m)\<close>
      by (simp add: comm)
    also have \<open>\<dots> = h m\<close>
      by (simp add: F_Some_x)
    finally show \<open>h m =
           (case h (setter F m0 m) of None \<Rightarrow> None
            | Some m' \<Rightarrow> Some (setter F (getter F m) m'))\<close>
      by (simp add: g_def s_def cong: option.case_cong)
  qed
next
  case False
  then have [simp]: \<open>F = non_cregister\<close>
    using non_cregister by blast
  show ?thesis
    by (simp add: non_cregister.rep_eq non_cregister_raw_def redundant_option_case cong: option.case_cong)
qed

lemma copy_CREGISTER_from_CREGISTER_of:
  fixes F :: \<open>('a,'b) cregister\<close>
  assumes [simp]: \<open>cregister F\<close>
  shows \<open>copy_CREGISTER_from (CREGISTER_of F) m0 m1 = setter F (getter F m0) m1\<close>
proof -
  define g s where \<open>g = getter F\<close> and \<open>s = setter F\<close>
  have [simp]: \<open>g (s x m) = x\<close> for x m
    by (simp add: g_def s_def)
  have [simp]: \<open>s x (s y m) = s x m\<close> for x y m
    by (simp add: s_def)
  have [simp]: \<open>s (g m) m = m\<close> for m
    by (simp add: g_def s_def)
  define F' where \<open>F' = range (apply_cregister F)\<close>
  define m where \<open>m = s (g m0) m1\<close>
  have \<open>\<exists>a\<in>F'. \<exists>b\<in>map_commutant F'. Some m = a m1 \<and> Some m = b m0\<close>
  proof (rule bexI[of _ \<open>\<lambda>m'. Some (s (g m) m')\<close>],
      rule bexI[of _ \<open>\<lambda>m'. Some (s (g m') m1)\<close>], rule conjI)
    show \<open>Some m = Some (s (g m) m1)\<close>
      by (simp add: m_def)
    show \<open>Some m = Some (s (g m0) m1)\<close>
      by (simp add: m_def)
    show \<open>(\<lambda>m'. Some (s (g m') m1)) \<in> map_commutant F'\<close>
    proof -
      have \<open>((\<lambda>m'. Some (s (g m') m1)) \<circ>\<^sub>m apply_cregister F a) x =
           apply_cregister F a (s (g x) m1)\<close> for a x
        apply (cases \<open>a (g x)\<close>)
        by (auto intro!: ext simp add: apply_cregister_getter_setter s_def g_def)
      then show ?thesis
        by (auto intro!: ext simp add: F'_def map_commutant_def)
    qed
    show \<open>(\<lambda>m'. Some (s (g m) m')) \<in> F'\<close>
      by (auto intro!: ext exI[of _ \<open>\<lambda>_. Some (g m)\<close>] simp add: F'_def image_iff apply_cregister_getter_setter s_def g_def)
  qed
  moreover have \<open>\<exists>a\<in>F'. \<exists>b\<in>map_commutant F'. Some m' = a m1 \<and> Some m' = b m0 \<Longrightarrow> m' = m\<close> for m'
  proof (erule bexE, erule bexE)
    fix a b assume a: \<open>a \<in> F'\<close> and \<open>b \<in> map_commutant F'\<close> and m'_ab: \<open>Some m' = a m1 \<and> Some m' = b m0\<close>
    from \<open>a \<in> F'\<close> obtain a' where \<open>a = apply_cregister F a'\<close>
      by (auto simp: F'_def)
    then have a': \<open>a m = (case a' (g m) of None \<Rightarrow> None | Some x \<Rightarrow> Some (s x m))\<close> for m
      by (simp add: apply_cregister_getter_setter g_def option.case_eq_if s_def)
    fix m_fix :: 'a
    from \<open>b \<in> map_commutant F'\<close>
    obtain b' where b': \<open>b m = (case b' (s m_fix m) of None \<Rightarrow> None
         | Some m' \<Rightarrow> Some (s (g m) m'))\<close> for m
      apply atomize_elim
      by (auto simp: map_commutant_range_apply_cregister[of F m_fix, folded F'_def s_def g_def])
    have gmm': \<open>g m' = g m\<close>
    proof -
      from m'_ab have \<open>Some m' = b m0\<close>
        by auto
      then obtain x where \<open>m' = s (g m0) x\<close>
        apply atomize_elim
        apply (cases \<open>b' (s m_fix m0)\<close>)
        by (auto intro!: simp: b')
      then show ?thesis
        by (simp add: m_def)
    qed
    have \<open>s x m = s x m'\<close> for x
    proof -
      from m'_ab have \<open>Some m' = a m1\<close>
        by simp
      then show ?thesis
        apply (cases \<open>a' (g m1)\<close>)
        by (auto simp add: a' m_def)
    qed
    with gmm' have \<open>s (g m) m = s (g m') m'\<close>
      by metis
    then show \<open>m' = m\<close>
      by simp
  qed
  ultimately have \<open>(SOME m. \<exists>a\<in>F'. \<exists>b\<in>map_commutant F'. Some m = a m1 \<and> Some m = b m0) = m\<close>
    by (rule some_equality)
  with assms show ?thesis
    apply (simp only: m_def F'_def s_def g_def)
    apply (transfer' fixing: m0 m1)
    by auto
qed

lemma range_empty_cregister: \<open>range (apply_cregister empty_cregister) = empty_cregister_range\<close>
proof (intro Set.set_eqI iffI)
  fix f :: \<open>'a \<Rightarrow> 'a option\<close> assume \<open>f \<in> range (apply_cregister empty_cregister :: ('b cupdate \<Rightarrow> _))\<close>
  then obtain g :: \<open>'b \<Rightarrow> 'b option\<close> where g: \<open>f = apply_cregister empty_cregister g\<close>
    by auto
  have \<open>g = Some \<or> g = (\<lambda>_. None)\<close>
  proof (cases \<open>g undefined\<close>)
    case None
    then have \<open>g x = None\<close> for x
      apply (subst everything_the_same[of _ undefined])
      by simp
    then show ?thesis 
      by auto
  next
    case (Some a)
    then have \<open>g x = Some a\<close> for x
      apply (subst everything_the_same[of _ undefined])
      by simp
    then show ?thesis
      by auto
  qed
  then have \<open>f = Some \<or> f = (\<lambda>_. None)\<close>
    by (auto simp: g)
  then show \<open>f \<in> empty_cregister_range\<close>
    using empty_cregister_range_def by blast
next
  fix f :: \<open>'a \<Rightarrow> 'a option\<close> assume \<open>f \<in> empty_cregister_range\<close>
  then consider \<open>f = Some\<close> | \<open>f = (\<lambda>_. None)\<close>
    by (auto simp: empty_cregister_range_def)
  then show  \<open>f \<in> range (apply_cregister empty_cregister :: ('b cupdate \<Rightarrow> _))\<close>
    apply cases
     apply (auto intro!: range_eqI[of _ _ Some])[1]
    by (auto intro!: range_eqI[of _ _ \<open>\<lambda>_. None\<close>])
qed

lemma actual_cregister_range_empty[iff]: \<open>actual_cregister_range empty_cregister_range\<close>
  apply (subst range_empty_cregister[symmetric])
  apply (rule actual_register_range)
  by simp

lemma ACTUAL_CREGISTER_CREGISTER_of[iff]: \<open>ACTUAL_CREGISTER (CREGISTER_of F)\<close>
  apply (cases \<open>cregister F\<close>)
   apply (simp add: ACTUAL_CREGISTER.rep_eq CREGISTER_of.rep_eq actual_register_range)
  by (simp add: non_cregister ACTUAL_CREGISTER.rep_eq bot_CREGISTER.rep_eq)



end