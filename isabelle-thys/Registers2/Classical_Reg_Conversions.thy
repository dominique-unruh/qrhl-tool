theory Classical_Reg_Conversions
  imports Classical_Reg_Ranges
begin

lemma cregister_conversion_raw_register:
  fixes F :: \<open>'a cupdate \<Rightarrow> 'c cupdate\<close> and G :: \<open>'b cupdate \<Rightarrow> 'c cupdate\<close>
  assumes regF: \<open>cregister_raw F\<close> and regG: \<open>cregister_raw G\<close> and range: \<open>range F \<subseteq> range G\<close>
  shows \<open>cregister_raw (inv G \<circ> F)\<close>
proof -
  define gF gG sF sG where \<open>gF = Axioms_Classical.getter F\<close> and \<open>gG = Axioms_Classical.getter G\<close>
    and \<open>sF = Axioms_Classical.setter F\<close> and \<open>sG = Axioms_Classical.setter G\<close>
  fix c0
  define g s where \<open>g b = gF (sG b c0)\<close> and \<open>s a b = gG (sF a (sG b c0))\<close> for a b
  (* define C where \<open>C = {sG b c0 | b. True}\<close> *)
  define C where \<open>C = {c. sG (gG c0) c = c0}\<close>

  have [simp]: \<open>gG (sG b c) = b\<close> for b c
    by (metis regG gG_def sG_def valid_getter_setter_def valid_getter_setter_getter_setter)
  have sgG[simp]: \<open>sG (gG c) c = c\<close> for c
    by (metis regG gG_def sG_def valid_getter_setter_def valid_getter_setter_getter_setter)
  have ssG[simp]: \<open>sG b (sG b' c) = sG b c\<close> for b b' c
    by (metis regG gG_def sG_def valid_getter_setter_def valid_getter_setter_getter_setter)
  have [simp]: \<open>gF (sF a c) = a\<close> for a c
    by (metis regF gF_def sF_def valid_getter_setter_def valid_getter_setter_getter_setter)
  have [simp]: \<open>sF (gF c) c = c\<close> for c
    by (metis regF gF_def sF_def valid_getter_setter_def valid_getter_setter_getter_setter)
  have [simp]: \<open>sF a (sF a' c) = sF a c\<close> for a a' c
    by (metis regF gF_def sF_def valid_getter_setter_def valid_getter_setter_getter_setter)

  have ggG: \<open>g (gG c) = gF c\<close> for c
  proof -
    have 1: \<open>gF c' = gF c''\<close> if \<open>gG c' = gG c''\<close> for c' c''
    proof (rule compare_all_eqI)
      fix a
      from range obtain u where u: \<open>G u = F (update1 a a)\<close>
        by (metis UNIV_I image_subset_iff rangeE)
      from that have \<open>u (gG c') \<noteq> None \<longleftrightarrow> u (gG c'') \<noteq> None\<close>
        by simp
      then have \<open>G u c' \<noteq> None \<longleftrightarrow> G u c'' \<noteq> None\<close>
        apply (subst (2) register_from_getter_setter_of_getter_setter[symmetric, OF regG])
        apply (subst register_from_getter_setter_of_getter_setter[symmetric, OF regG])
        by (auto simp add: register_from_getter_setter_def gG_def)
      then have \<open>F (update1 a a) c' \<noteq> None \<longleftrightarrow> F (update1 a a) c'' \<noteq> None\<close>
        by (simp add: u)
      then show \<open>gF c' = a \<longleftrightarrow> gF c'' = a\<close>
        by (simp add: gF_def getter_from_update1[OF regF, of _ a a])
    qed
    have 2:\<open>gG (sG (gG c) c0) = gG c\<close>
      by simp
    from 1 2 have \<open>gF (sG (gG c) c0) = gF c\<close>
      by blast
    then show ?thesis
      by (simp add: g_def)
  qed

  have sg: \<open>b = s (g b) b\<close> for b
    by (simp add: g_def s_def)

  have gs: \<open>g (s a b) = a\<close> for a b
    apply (simp add: g_def s_def)
    apply (simp flip: ggG)
    by (simp add: ggG)

  have sgC: \<open>sG (gG c) c0 = c\<close> if \<open>c \<in> C\<close> for c
    using that apply (simp add: C_def)
    by (metis ssG sgG)

  have \<open>c0 \<in> C\<close>
    by (simp add: C_def)

  have sG_C: \<open>sG b c \<in> C\<close> if \<open>c \<in> C\<close> for b c
    using that by (simp add: C_def)

  have sF_via_G: \<open>\<exists>u. sF a = register_apply G u\<close> for a
  proof -
    from range
    obtain u' where u': \<open>F (\<lambda>b. Some a) = G u'\<close>
      by blast
    have \<open>total_fun (G u')\<close>
      by (metis assms(1) option.simps(3) register_total total_fun_def u')
    then have \<open>total_fun u'\<close>
      by (simp add: regG register_total_iff)
    then obtain u where u: \<open>u' = Some o u\<close>
      apply atomize_elim
      apply (auto simp: total_fun_def o_def)
      by metis
    show ?thesis
      by (auto intro!: exI[of _ u] ext
          simp: sF_def Axioms_Classical.setter_def register_apply_def u' u)
  qed

  have sG_sF: \<open>sG b (sF a c) = sG b c\<close> for a b c
  proof -
    obtain u where u: \<open>sF a = register_apply G u\<close>
      using sF_via_G by blast
    have \<open>sG b (sF a c) = register_apply G (\<lambda>_. b) (register_apply G u c)\<close>
      by (simp add: sG_def Axioms_Classical.setter_def u)
    also have \<open>\<dots> = register_apply G ((\<lambda>_. b) o u) c\<close>
      using register_apply_mult[OF regG, unfolded o_def, THEN fun_cong]
      by simp
    also have \<open>\<dots> = sG b c\<close>
      by (simp add: sG_def Axioms_Classical.setter_def)
    finally show ?thesis
      by -
  qed

  have sF_C: \<open>sF a c \<in> C\<close> if \<open>c \<in> C\<close> for a c
    using that by (simp add: C_def sG_sF)

  have ss: \<open>s a (s a' b) = s a b\<close> for a a' b
    by (simp add: g_def s_def sgC sF_C sG_C \<open>c0 \<in> C\<close>)
  
  from sg gs ss have valid_gs: \<open>valid_getter_setter g s\<close>
    by (simp add: valid_getter_setter_def)

  have GF_gs: \<open>inv G o F = register_from_getter_setter g s\<close>
  proof -
    have gF: \<open>Axioms_Classical.getter (G o register_from_getter_setter g s) = gF\<close>
      apply (simp add: getter_chain_raw regG register_register_from_getter_setter valid_gs
          flip: gG_def)
      by (simp add: ggG o_def)
    have sF: \<open>Axioms_Classical.setter (G o register_from_getter_setter g s) = sF\<close> (is \<open>?lhs = sF\<close>)
    proof (rule ext, rule ext)
      fix a c
      obtain u where u: \<open>sF a = register_apply G u\<close>
        using sF_via_G by blast
      have G_part: \<open>gG (?lhs a c) = gG (sF a c)\<close>
      proof -
        have \<open>gG (?lhs a c) = s a (gG c)\<close>
          apply (simp add: setter_chain_raw regG register_register_from_getter_setter valid_gs
              flip: gG_def sG_def)
          thm s_def
          by -
        also have \<open>s a (gG c) = gG (sF a c)\<close>
          apply (simp add: s_def u getter_register_apply gG_def regG)
          by (simp flip: gG_def)
        finally show ?thesis
          by -
      qed
      have rest: \<open>sG b (?lhs a c) = sG b (sF a c)\<close> for b
        by (simp add: setter_chain_raw regG register_register_from_getter_setter valid_gs sG_sF
            flip: gG_def sG_def)
      from G_part rest show \<open>?lhs a c = sF a c\<close>
        by (metis sgG)
    qed
    from sF gF have \<open>G o register_from_getter_setter g s = F\<close>
      by (metis assms(1) assms(2) cregister_raw_chain gF_def register_from_getter_setter_of_getter_setter register_register_from_getter_setter sF_def valid_gs)
    with this[symmetric] show ?thesis
      using range
      by (simp add: o_def inv_f_f cregister_raw_inj regG)
  qed

  from GF_gs ggG
  show \<open>cregister_raw (inv G o F)\<close>
    by (simp add: valid_gs)
qed

lift_definition cregister_conversion :: \<open>('a,'c) cregister \<Rightarrow> ('b,'c) cregister \<Rightarrow> ('a,'b) cregister\<close> is
  \<open>\<lambda>F G. if cregister_raw F \<and> cregister_raw G \<and> range F \<subseteq> range G then inv G o F else non_cregister_raw\<close>
  by (auto intro: cregister_conversion_raw_register)

lemma cregister_conversion_register: \<open>cregister_le F G \<Longrightarrow> cregister (cregister_conversion F G)\<close>
  apply (auto intro!: cregister_conversion_raw_register 
      simp add: cregister_le_def less_eq_CREGISTER_def CREGISTER_of.rep_eq
      cregister.rep_eq cregister_conversion.rep_eq)
  by auto


lemma cregister_chain_conversion: \<open>cregister_le F G \<Longrightarrow> cregister_chain G (cregister_conversion F G) = F\<close>
  unfolding cregister_le_def
  apply (transfer fixing: F G)
  apply transfer
  by (auto simp: non_cregister_raw cregister_conversion_raw_register f_inv_into_f in_mono intro!: ext)

lemma cregister_apply_conversion:
  assumes \<open>cregister_le F G\<close>
  shows \<open>apply_cregister F x = apply_cregister G (apply_cregister (cregister_conversion F G) x)\<close>
  using assms apply (subst cregister_chain_conversion[where F=F and G=G, symmetric])
  by auto

lemma cregister_conversion_id[simp]: \<open>cregister_conversion F cregister_id = F\<close>
  apply transfer by auto

lemma cregister_conversion_non_reg_right[simp]: \<open>cregister_conversion F non_cregister = non_cregister\<close>
  apply transfer by (auto simp add: non_cregister_raw)

lemma cregister_conversion_non_reg_left[simp]: \<open>cregister_conversion non_cregister F = non_cregister\<close>
  apply transfer by (auto simp add: non_cregister_raw)

lemma cregister_conversion_rename:
  fixes F :: \<open>('a,'c) cregister\<close> and G :: \<open>('b,'c) cregister\<close> and H :: \<open>('d, 'c) cregister\<close> and F' G'
  assumes \<open>cregister H\<close>
  assumes \<open>F = cregister_chain H F'\<close> \<open>G = cregister_chain H G'\<close>
  shows \<open>cregister_conversion F G = cregister_conversion F' G'\<close>
proof (cases \<open>cregister F'\<close>, cases \<open>cregister G'\<close>)
  assume \<open>\<not> cregister G'\<close>
  then have [simp]: \<open>G' = non_cregister\<close>
    using non_cregister by blast
  then show ?thesis
    apply (simp add: \<open>G = cregister_chain H G'\<close>)
    by -
next
  assume \<open>\<not> cregister F'\<close>
  then have [simp]: \<open>F' = non_cregister\<close>
    using non_cregister by blast
  then show ?thesis
    by (simp add: \<open>F = cregister_chain H F'\<close>)
next
  have range_le_preserve: \<open>range F' \<subseteq> range G'\<close> if \<open>range (\<lambda>x. H (F' x)) \<subseteq> range (\<lambda>x. H (G' x))\<close> and \<open>cregister_raw H\<close>
    for H :: \<open>'d cupdate \<Rightarrow> 'c cupdate\<close> and F' :: \<open>'a cupdate \<Rightarrow> 'd cupdate\<close> and G' :: \<open>'b cupdate \<Rightarrow> 'd cupdate\<close>
    using cregister_raw_inj[OF \<open>cregister_raw H\<close>] using that(1)
    by (smt (verit, best) image_subset_iff inj_def rangeE rangeI)
  have H_cancel: \<open>inv (H \<circ> G') \<circ> (H \<circ> F') = inv G' \<circ> F'\<close> if \<open>cregister_raw H\<close> and \<open>cregister_raw G'\<close>
    and \<open>range F' \<subseteq> range G'\<close>
    for H :: \<open>'d cupdate \<Rightarrow> 'c cupdate\<close> and F' :: \<open>'a cupdate \<Rightarrow> 'd cupdate\<close> and G' :: \<open>'b cupdate \<Rightarrow> 'd cupdate\<close>
    apply (rule inv_comp_eqI)
    using cregister_raw_inj[OF \<open>cregister_raw H\<close>] cregister_raw_inj[OF \<open>cregister_raw G'\<close>]
    using inj_compose that by (auto simp add: ext f_inv_into_f subset_iff)
  assume [simp]: \<open>cregister F'\<close> \<open>cregister G'\<close>
  then show ?thesis
    using assms apply transfer
    using range_le_preserve H_cancel by (auto simp: cregister_raw_chain)
qed


lemma cregister_conversion_as_register:
  fixes F :: \<open>('a,'c) cregister\<close> and F' G'
  assumes \<open>cregister G\<close>
  assumes \<open>F = cregister_chain G F'\<close>
  shows \<open>cregister_conversion F G = F'\<close>
  apply (subst cregister_conversion_rename[where H=G and G'=cregister_id and F'=F'])
  using assms by auto


end
