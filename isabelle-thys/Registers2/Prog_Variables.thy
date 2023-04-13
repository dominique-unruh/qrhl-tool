theory Prog_Variables
  imports
    (* Multi_Transfer *)
    HOL.Map
    Registers.Classical_Extra
    Quantum_Registers
    Classical_Registers
    Quantum_Reg_Ranges
    Classical_Reg_Ranges
    Quantum_Reg_Conversions
    Quantum_From_Classical_Reg
  keywords "debug_translate_to_index_registers" :: "diag"
begin

unbundle cblinfun_notation
no_notation m_inv ("inv\<index> _" [81] 80)
hide_const (open) Order.top
no_notation Order.top ("\<top>\<index>")
hide_const (open) Axioms_Classical.getter
hide_const (open) Axioms_Classical.setter
declare [[simproc del: Laws_Quantum.compatibility_warn]]
declare [[simproc del: Laws_Classical.compatibility_warn]]
hide_const (open) Classical_Extra.X Classical_Extra.Y Classical_Extra.x Classical_Extra.y
hide_const (open) Coset.kernel

subsubsection \<open>Wrapper types around registers\<close>



(* TODO: (and also for quantum, also for COMPATIBLE)
lemma ccompatible_register_tensor[simp]: \<open>ccompatible F F' \<Longrightarrow> ccompatible G G' \<Longrightarrow> ccompatible (cregister_tensor F G) (cregister_tensor F' G')\<close> *)

(* TODO move to Registers *)
lemma valid_getter_setter_pair: 
  assumes \<open>Laws_Classical.compatible F G\<close>
  shows \<open>valid_getter_setter (\<lambda>m. (Axioms_Classical.getter F m, Axioms_Classical.getter G m))
           (\<lambda>(a, b) m. Axioms_Classical.setter F a (Axioms_Classical.setter G b m))\<close>
proof -
  have \<open>Axioms_Classical.register F\<close>
    using Laws_Classical.compatible_register1 assms by blast
  have \<open>Axioms_Classical.register G\<close>
    using Laws_Classical.compatible_register2 assms by auto
  have valid_gsF: \<open>valid_getter_setter (Axioms_Classical.getter F) (Axioms_Classical.setter F)\<close>
    by (simp add: \<open>cregister_raw F\<close>)
  have valid_gsG: \<open>valid_getter_setter (Axioms_Classical.getter G) (Axioms_Classical.setter G)\<close>
    by (simp add: \<open>cregister_raw G\<close>)

  have valid: \<open>valid_getter_setter (\<lambda>m. (Axioms_Classical.getter F m, Axioms_Classical.getter G m))
     (\<lambda>(a, b) m. Axioms_Classical.setter F a (Axioms_Classical.setter G b m))\<close>
    using valid_gsF valid_gsG
    apply (auto simp: valid_getter_setter_def)
     apply (metis Laws_Classical.compatible_sym assms getter_setter)
    by (metis Classical_Extra.compatible_setter Laws_Classical.compatible_register1 Laws_Classical.compatible_register2 assms o_def)
  show ?thesis
    using valid by (auto simp: Axioms_Classical.register_pair_def o_def setter_of_register_from_getter_setter)
qed

(* TODO move to Registers session *)
lemma setter_pair_raw: \<open>Axioms_Classical.setter (F;G) = (\<lambda>(x, y). Axioms_Classical.setter F x \<circ> Axioms_Classical.setter G y)\<close>
  if \<open>Laws_Classical.compatible F G\<close>
  using valid_getter_setter_pair[OF that] 
  by (auto simp: Axioms_Classical.register_pair_def o_def)

lemma setter_pair:
  assumes \<open>ccompatible F G\<close>
  shows \<open>setter (cregister_pair F G) = (\<lambda>(x,y). setter F x o setter G y)\<close>
  using assms unfolding ccompatible_def
  apply transfer using setter_pair_raw by auto

(* TODO move to Registers *)
lemma getter_pair_raw:
  assumes \<open>ccompatible_raw F G\<close>
  shows \<open>Axioms_Classical.getter (F;G) = (\<lambda>m. (Axioms_Classical.getter F m, Axioms_Classical.getter G m))\<close>
  using assms by (simp_all add: Axioms_Classical.register_pair_def valid_getter_setter_pair)

lemma getter_pair:
  assumes \<open>ccompatible F G\<close>
  shows \<open>getter (cregister_pair F G) = (\<lambda>m. (getter F m, getter G m))\<close>
  using assms unfolding ccompatible_def
  apply transfer using getter_pair_raw by auto

instantiation QREGISTER :: (type) uminus begin
lift_definition uminus_QREGISTER :: \<open>'a QREGISTER \<Rightarrow> 'a QREGISTER\<close> is commutant
  by (auto simp add: valid_qregister_range_def von_neumann_algebra_commutant)
instance..
end

abbreviation (* LEGACY *) (input) \<open>QCOMPLEMENT \<equiv> (uminus :: 'a QREGISTER \<Rightarrow> _)\<close>

lemma Qqcompatible_antimono_left: \<open>A \<le> B \<Longrightarrow> Qqcompatible B C \<Longrightarrow> Qqcompatible A C\<close>
  apply transfer by auto


lemma register_from_getter_setter_id: \<open>id = register_from_getter_setter (\<lambda>m. m) (\<lambda>a m. a)\<close>
  by (auto intro!: ext simp add: register_from_getter_setter_def option.case_eq_if)
lemma valid_getter_setter_id: \<open>valid_getter_setter (\<lambda>m. m) (\<lambda>a m. a)\<close>
  by (simp add: valid_getter_setter_def)

lemma getter_id: \<open>getter cregister_id m = m\<close>
  apply transfer
  apply (subst (2) register_from_getter_setter_id)
  by (simp add: getter_of_register_from_getter_setter valid_getter_setter_id)
lemma setter_id: \<open>setter cregister_id a m = a\<close>
  apply transfer
  apply (subst (2) register_from_getter_setter_id)
  by (simp add: setter_of_register_from_getter_setter valid_getter_setter_id)

lemma Qqcompatible_QREGISTER_of: \<open>Qqcompatible (QREGISTER_of A) B \<longleftrightarrow> qcompatible A B \<or> (qregister B \<and> A = non_qregister)\<close>
  unfolding QREGISTER_of.rep_eq Qqcompatible.rep_eq
  apply transfer
  by (auto simp add: non_qregister_raw one_algebra_def qcompatible_raw_def)

lemma Qqcompatible_QREGISTER_ofI[simp]: \<open>qcompatible F G \<Longrightarrow> Qqcompatible (QREGISTER_of F) G\<close>
  by (simp add: Qqcompatible_QREGISTER_of)

(* TODO to Registers *)
lemma getter_from_update1: 
  assumes \<open>cregister_raw F\<close>
  shows \<open>Axioms_Classical.getter F m = a \<longleftrightarrow> F (update1 a b) m \<noteq> None\<close>
  apply (subst (2) register_from_getter_setter_of_getter_setter[symmetric, OF assms])
  by (auto simp add: register_from_getter_setter_def update1_def)

(* TODO to Registers *)
lemma register_apply_mult:
  assumes \<open>cregister_raw F\<close>
  shows \<open>register_apply F a o register_apply F b = register_apply F (a o b)\<close>
proof (rule ext)
  fix x
  have FSome: \<open>F (\<lambda>y. Some (w y)) z \<noteq> None\<close> for z w
    by (meson assms option.simps(3) register_total total_fun_def)

  have \<open>Some ((register_apply F a o register_apply F b) x) = F (Some o a) (register_apply F b x)\<close>
    using register_apply[OF assms, THEN fun_cong]
    by (simp add: o_def)
  also have \<open>\<dots> = F (\<lambda>x. Some (a x)) (the (F (\<lambda>x. Some (b x)) x))\<close>
    by (simp add: register_apply_def o_def)
  also have \<open>\<dots> = (F (Some o a) \<circ>\<^sub>m F (Some o b)) x\<close>
    apply (cases \<open>F (\<lambda>x. Some (b x)) x\<close>)
    using FSome by (auto simp: map_comp_def o_def)
  also have \<open>\<dots> = F ((Some o a) \<circ>\<^sub>m (Some o b)) x\<close>
    by (simp add: Axioms_Classical.register_mult assms)
  also have \<open>\<dots> = F (\<lambda>x. Some (a (b x))) x\<close>
    apply (cases \<open>F (\<lambda>x. Some (b x)) x\<close>)
    using FSome by (auto simp: map_comp_def)
  also have \<open>\<dots> = Some (register_apply F (a o b) x)\<close>
    by (simp add: register_apply_def o_def option.collapse[OF FSome])
  finally show \<open>(register_apply F a \<circ> register_apply F b) x = register_apply F (a \<circ> b) x\<close>
    by simp
qed

(* TODO to Registers (replace register_total?) *)
lemma register_total_iff: 
  assumes \<open>cregister_raw F\<close>
  shows \<open>total_fun (F a) \<longleftrightarrow> total_fun a\<close>
proof (rule iffI)
  show \<open>total_fun a \<Longrightarrow> total_fun (F a)\<close>
    using assms register_total by blast
next
  show \<open>total_fun a\<close> if \<open>total_fun (F a)\<close>
  proof (rule ccontr)
    assume \<open>\<not> total_fun a\<close>
    then obtain x where \<open>a x = None\<close>
      using total_fun_def by blast
    then have \<open>a \<circ>\<^sub>m update1 x x = Map.empty\<close>
      by (metis map_comp_None_iff update1_def)
    then have \<open>F a \<circ>\<^sub>m F (update1 x x) = Map.empty\<close>
      by (simp add: Axioms_Classical.register_mult cregister_raw_empty assms)
    with \<open>total_fun (F a)\<close> have \<open>F (update1 x x) = Map.empty\<close>
      by (meson map_comp_None_iff total_fun_def)
    then have \<open>update1 x x = Map.empty\<close>
      by (smt (verit) assms getter_from_update1 valid_getter_setter_def valid_getter_setter_getter_setter)
    then show False
      by (metis option.discI update1_def)
  qed
qed

(* TODO move to Registers *)
lemma register_apply_via_setter_getter:
  assumes [simp]: \<open>cregister_raw F\<close>
  shows \<open>register_apply F f m = Axioms_Classical.setter F (f (Axioms_Classical.getter F m)) m\<close>
  apply (subst register_from_getter_setter_of_getter_setter[symmetric, OF assms])
  by (simp add: register_from_getter_setter_def[abs_def] register_apply_def
      del: register_from_getter_setter_of_getter_setter)

(* TODO move to Registers *)
lemma getter_register_apply:
  assumes [simp]: \<open>cregister_raw F\<close>
  shows \<open>Axioms_Classical.getter F (register_apply F f m) = f (Axioms_Classical.getter F m)\<close>
  apply (simp add: register_apply_via_setter_getter)
  by (metis assms valid_getter_setter_def valid_getter_setter_getter_setter)

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

definition \<open>cregister_le F G = (cregister F \<and> cregister G \<and> CREGISTER_of F \<le> CREGISTER_of G)\<close>

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

(* lift_definition qregister_of_cregister :: \<open>('a,'b) cregister \<Rightarrow> ('a,'b) qregister\<close> is
  \<open>\<lambda>F a. if cregister F then
      explicit_cblinfun (\<lambda>i j. if same_outside_cregister F i j then Rep_ell2 (a *\<^sub>V ket (getter F j)) (getter F i) else 0)
    else 0\<close>
   *)

lemma cregister_eqI_setter_raw: 
  assumes [simp]: \<open>cregister_raw F\<close> \<open>cregister_raw G\<close>
  assumes eq: \<open>\<And>a m. Axioms_Classical.setter F a m = Axioms_Classical.setter G a m\<close>
  shows \<open>F = G\<close>
proof -
  from eq \<open>cregister_raw F\<close> \<open>cregister_raw G\<close> have \<open>Axioms_Classical.getter F = Axioms_Classical.getter G\<close>
    by (auto simp: Axioms_Classical.getter_def)
  with eq[abs_def]
  have \<open>register_from_getter_setter (Axioms_Classical.getter F) (Axioms_Classical.setter F)
      = register_from_getter_setter (Axioms_Classical.getter G) (Axioms_Classical.setter G)\<close>
    by simp
  then show ?thesis
    by (simp add: register_from_getter_setter_of_getter_setter)
qed

lemma cregister_eqI_setter: 
  assumes \<open>cregister F\<close> \<open>cregister G\<close>
  assumes eq: \<open>\<And>a m. setter F a m = setter G a m\<close>
  shows \<open>F = G\<close>
  using assms apply transfer
  by (auto intro!: cregister_eqI_setter_raw)

lemma separating_butterket:
  \<open>Laws_Quantum.separating TYPE('b) (range (case_prod butterket))\<close>
proof -
  thm weak_star_clinear_eq_butterfly_ketI
  have \<open>F = G\<close> if \<open>\<And>a b. F (butterket a b) = G (butterket a b)\<close> 
    and \<open>Axioms_Quantum.preregister F\<close> and \<open>Axioms_Quantum.preregister G\<close> for F G :: \<open>'a qupdate \<Rightarrow> 'b qupdate\<close>
    apply (rule weak_star_clinear_eq_butterfly_ketI[where T=weak_star_topology])
    using that
    by (auto simp: Axioms_Quantum.preregister_def bounded_clinear.clinear)
  then show ?thesis
    by (auto simp add: Laws_Quantum.separating_def)
qed

lemma separating_nonempty: \<open>\<not> (X \<subseteq> {0})\<close> if sep: \<open>separating TYPE('b) X\<close> for X :: \<open>'a qupdate set\<close>
proof (rule notI)
  assume \<open>X \<subseteq> {0}\<close>
  have \<open>Axioms_Quantum.preregister 0\<close>
    by (simp add: Axioms_Quantum.preregister_def zero_fun_def)
  fix x
  define F :: \<open>'a qupdate \<Rightarrow> 'b qupdate\<close> where \<open>F a = (ket x \<bullet>\<^sub>C (a *\<^sub>V ket x)) *\<^sub>C id_cblinfun\<close> for a
  have \<open>bounded_clinear F\<close>
    unfolding F_def[abs_def]
    by (intro bounded_linear_intros)
  moreover have \<open>continuous_map weak_star_topology weak_star_topology F\<close>
  proof -
    note continuous_map_compose[trans]
    have \<open>continuous_map weak_star_topology cweak_operator_topology (\<lambda>f :: 'a qupdate. f)\<close>
      by (simp add: wot_weaker_than_weak_star)
    also have \<open>continuous_map cweak_operator_topology euclidean (\<lambda>a. ket x \<bullet>\<^sub>C (a *\<^sub>V ket x))\<close>
      by (simp add: cweak_operator_topology_continuous_evaluation)
    also have \<open>continuous_map euclidean euclidean (\<lambda>c. c *\<^sub>C (id_cblinfun :: 'b qupdate))\<close>
      by (auto intro!: continuous_map_iff_continuous2[THEN iffD2] continuous_at_imp_continuous_on)
    also have \<open>continuous_map euclidean weak_star_topology (\<lambda>f :: 'b qupdate. f)\<close>
      by (simp add: weak_star_topology_weaker_than_euclidean)
    finally show ?thesis
      by (simp add: o_def F_def[abs_def])
  qed
  ultimately have \<open>Axioms_Quantum.preregister F\<close>
    by (simp add: Axioms_Quantum.preregister_def)
  have \<open>0 a = F a\<close> if \<open>a \<in> X\<close> for a
    using \<open>X \<subseteq> {0}\<close> that
    by (auto simp: F_def)
  with sep have \<open>0 = F\<close>
    by (simp add: Laws_Quantum.register_eqI \<open>Axioms_Quantum.preregister 0\<close> \<open>Axioms_Quantum.preregister F\<close>)
  then have \<open>0 (butterket x x) = F (butterket x x)\<close>
    by simp
  then show False
    by (simp add: F_def)
qed

lemma qregister_eqI_separating:
  fixes F G :: \<open>('a,'b) qregister\<close>
  assumes sep: \<open>Laws_Quantum.separating TYPE('b) X\<close>
  assumes eq: \<open>\<And>x. x\<in>X \<Longrightarrow> apply_qregister F x = apply_qregister G x\<close>
  shows \<open>F = G\<close>
proof -
  obtain x where \<open>x \<in> X\<close> and \<open>x \<noteq> 0\<close>
    using separating_nonempty[OF sep]
    by auto

  consider (reg) \<open>qregister F\<close> \<open>qregister G\<close> | (notreg) \<open>\<not> qregister F\<close> \<open>\<not> qregister G\<close>
    | (notF) \<open>\<not> qregister F\<close> \<open>qregister G\<close> | (notG) \<open>qregister F\<close> \<open>\<not> qregister G\<close>
    by auto
  then show ?thesis
  proof cases
    case reg
    then show ?thesis
      using assms apply transfer
      by (auto simp: Laws_Quantum.separating_def)
  next
    case notreg
    then show ?thesis
      by (simp add: non_qregister)
  next
    case notF
    have \<open>apply_qregister F x = 0\<close>
      using non_qregister notF(1) by force
    moreover have \<open>apply_qregister G x \<noteq> 0\<close>
      using \<open>x \<noteq> 0\<close> inj_qregister[OF notF(2)] injD by fastforce
    moreover have \<open>apply_qregister F x = apply_qregister G x\<close>
      using eq \<open>x \<in> X\<close> by simp
    ultimately have False
      by simp
    then show ?thesis
      by simp
  next
    case notG
    have \<open>apply_qregister G x = 0\<close>
      using non_qregister notG(2) by force
    moreover have \<open>apply_qregister F x \<noteq> 0\<close>
      using \<open>x \<noteq> 0\<close> inj_qregister[OF notG(1)] injD by fastforce
    moreover have \<open>apply_qregister F x = apply_qregister G x\<close>
      using eq \<open>x \<in> X\<close> by simp
    ultimately have False
      by simp
    then show ?thesis
      by simp
  qed
qed

lemmas qregister_eqI_butterket = qregister_eqI_separating[OF separating_butterket]

lemma qregister_eqI_tensor_op:
  assumes \<open>\<And>a b. apply_qregister F (a \<otimes>\<^sub>o b) = apply_qregister G (a \<otimes>\<^sub>o b)\<close> 
  shows \<open>F = G\<close>
  apply (intro qregister_eqI_separating)
   apply (rule separating_tensor)
    apply (rule separating_UNIV)
   apply (rule separating_UNIV)
  using assms by auto

lemma qregister_of_cregister_pair: 
  \<open>qregister_of_cregister (cregister_pair x y) = qregister_pair (qregister_of_cregister x) (qregister_of_cregister y)\<close>
proof (cases \<open>ccompatible x y\<close>)
  case True
  then have [simp]: \<open>ccompatible x y\<close> \<open>cregister x\<close> \<open>cregister y\<close>
    by (auto simp add: ccompatible_def)
  have \<open>apply_qregister (qregister_of_cregister (cregister_pair x y)) (butterket k l) *\<^sub>V ket z =
        apply_qregister (qregister_pair (qregister_of_cregister x) (qregister_of_cregister y)) (butterket k l) *\<^sub>V ket z\<close> for k l z
  proof -
    obtain k1 k2 where [simp]: \<open>k = (k1,k2)\<close>
      by force
    obtain l1 l2 where [simp]: \<open>l = (l1,l2)\<close>
      by force
    show ?thesis
      apply (simp add: apply_qregister_pair flip: tensor_ell2_ket tensor_butterfly)
      by (simp add: apply_qregister_qregister_of_cregister_butterket getter_pair setter_pair
          tensor_ell2_ket tensor_butterfly)
  qed
  then have \<open>apply_qregister (qregister_of_cregister (cregister_pair x y)) (butterket k l) =
        apply_qregister (qregister_pair (qregister_of_cregister x) (qregister_of_cregister y)) (butterket k l)\<close> for k l
    by (simp add: equal_ket)
  then show ?thesis
    apply (rule_tac qregister_eqI_separating[OF separating_butterket])
    by auto
next
  case False
  then have \<open>\<not> qcompatible (qregister_of_cregister x) (qregister_of_cregister y)\<close>
    by simp
  then have 1: \<open>qregister_pair (qregister_of_cregister x) (qregister_of_cregister y) = non_qregister\<close>
    using non_qregister by blast
  from False have 2: \<open>cregister_pair x y = non_cregister\<close>
    using non_cregister by blast
  from 1 2 show ?thesis
    by simp
qed

lemma qregister_of_cregister_chain: \<open>qregister_of_cregister (cregister_chain x y) = qregister_chain (qregister_of_cregister x) (qregister_of_cregister y)\<close>
proof (cases \<open>cregister x \<and> cregister y\<close>)
  case True
  then have [simp]: \<open>cregister x\<close> \<open>cregister y\<close>
    by (auto simp add: ccompatible_def)
  have \<open>apply_qregister (qregister_of_cregister (cregister_chain x y)) (butterket k l) *\<^sub>V ket z =
        apply_qregister (qregister_chain (qregister_of_cregister x) (qregister_of_cregister y)) (butterket k l) *\<^sub>V ket z\<close> for k l z
    apply (auto intro!: Rep_ell2_inject[THEN iffD1] ext 
        simp add: apply_qregister_qregister_of_cregister_butterket getter_chain setter_chain)
     apply (auto simp add: apply_qregister_of_cregister permute_and_tensor1_cblinfun_ket
        permute_and_tensor1_cblinfun_exists_register ket.rep_eq same_outside_cregister_def
        scaleC_ell2.rep_eq cinner_ket zero_ell2.rep_eq)
    by (metis getter_setter_same[OF \<open>cregister x\<close>])
  then have \<open>apply_qregister (qregister_of_cregister (cregister_chain x y)) (butterket k l) =
        apply_qregister (qregister_chain (qregister_of_cregister x) (qregister_of_cregister y)) (butterket k l)\<close> for k l
    by (simp add: equal_ket)
  then show ?thesis
    apply (rule_tac qregister_eqI_separating[OF separating_butterket])
    by auto
next
  case False
  then show ?thesis
    by (auto simp add: non_cregister)
qed

typedecl cl
typedecl qu
instance qu :: default ..

type_synonym 'a cvariable = \<open>('a,cl) cregister\<close>
type_synonym 'a qvariable = \<open>('a,qu) qregister\<close>

type_synonym QVARIABLE = \<open>qu QREGISTER\<close>
type_synonym CVARIABLE = \<open>cl CREGISTER\<close>

lift_definition transform_qregister :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2) \<Rightarrow> ('a,'b) qregister\<close> is
  \<open>\<lambda>(U :: 'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2). if unitary U then cblinfun_apply (sandwich U) else non_qregister_raw\<close>
  by (auto simp: unitary_sandwich_register)

lemma qregister_transform_qregister[simp]: \<open>unitary U \<Longrightarrow> qregister (transform_qregister U)\<close>
  apply (transfer fixing: U) by (auto simp: unitary_sandwich_register)

lemma apply_qregister_transform_qregister: \<open>unitary U \<Longrightarrow> apply_qregister (transform_qregister U) a = sandwich U a\<close>
  apply (transfer fixing: U a) by (auto simp: unitary_sandwich_register sandwich_apply)

(* datatype 'a vtree = VTree_Singleton 'a | VTree_Concat "'a vtree" "'a vtree" | VTree_Unit *)

section \<open>Distinct variables\<close>

abbreviation (input) "distinct_qvars Q == qregister Q" (* LEGACY *)
abbreviation (input) "distinct_cvars Q == cregister Q" (* LEGACY *)

lemma distinct_qvars_split1:
  "distinct_qvars (qregister_pair (qregister_pair Q R) S) = (distinct_qvars (qregister_pair Q R) \<and> distinct_qvars (qregister_pair Q S) \<and> distinct_qvars (qregister_pair R S))"
  using qcompatible3 by blast
lemma distinct_qvars_swap: "distinct_qvars (qregister_pair Q R) \<Longrightarrow> distinct_qvars (qregister_pair R Q)"
  using qcompatible_sym by auto
lemma distinct_qvars_split2: "distinct_qvars (qregister_pair S (qregister_pair Q R)) = (distinct_qvars (qregister_pair Q R) \<and> distinct_qvars (qregister_pair Q S) \<and> distinct_qvars (qregister_pair R S))"
  by (metis qcompatible3 qcompatible_sym)
lemma distinct_qvars_concat_unit1[simp]: "distinct_qvars (qregister_pair Q empty_qregister) = distinct_qvars Q" for Q::"'a qvariable"
  using qcompatible_QQcompatible qcompatible_empty by auto
lemma distinct_qvars_concat_unit2[simp]: "distinct_qvars (qregister_pair empty_qregister Q) = distinct_qvars Q" for Q::"'a::finite qvariable"
  using qcompatible_QQcompatible qcompatible_empty qcompatible_sym by blast
lemma distinct_qvars_unit[simp]: "distinct_qvars empty_qregister"
  by (simp add: )

lemma distinct_qvarsL: "distinct_qvars (qregister_pair Q R) \<Longrightarrow> distinct_qvars Q"
  by (simp add: qcompatible_QQcompatible)
lemma distinct_qvarsR: "distinct_qvars (qregister_pair Q R) \<Longrightarrow> distinct_qvars R"
  by (simp add: qcompatible_def)

lemma distinct_cvars_swap: "distinct_cvars (cregister_pair Q R) \<Longrightarrow> distinct_cvars (cregister_pair R Q)"
  using ccompatible_sym by blast
lemma distinct_cvars_split2: "distinct_cvars (cregister_pair S (cregister_pair Q R)) = (distinct_cvars (cregister_pair Q R) \<and> distinct_cvars (cregister_pair Q S) \<and> distinct_cvars (cregister_pair R S))"
  by (metis ccompatible3 distinct_cvars_swap)

section \<open>Indexed variables\<close>

type_synonym cl2 = \<open>cl \<times> cl\<close>
type_synonym qu2 = \<open>qu \<times> qu\<close>

type_synonym 'a c2variable = \<open>('a,cl2) cregister\<close>
type_synonym 'a q2variable = \<open>('a,qu2) qregister\<close>

definition index_cvar :: \<open>bool \<Rightarrow> 'a cvariable \<Rightarrow> 'a c2variable\<close> where
  \<open>index_cvar b x = cregister_chain (if b then cFst else cSnd) x\<close>
definition index_qvar :: \<open>bool \<Rightarrow> 'a qvariable \<Rightarrow> 'a q2variable\<close> where
  \<open>index_qvar b x = qregister_chain (if b then qFst else qSnd) x\<close>

definition index_flip_cvar :: \<open>'a c2variable \<Rightarrow> 'a c2variable\<close> where
  \<open>index_flip_cvar x = cregister_chain cswap x\<close>
definition index_flip_qvar :: \<open>'a q2variable \<Rightarrow> 'a q2variable\<close> where
  \<open>index_flip_qvar x = qregister_chain qswap x\<close>

lemma index_flip_qvar_register_pair[simp]: \<open>index_flip_qvar (qregister_pair Q R) = qregister_pair (index_flip_qvar Q) (index_flip_qvar R)\<close>
  unfolding index_flip_qvar_def
  apply (cases \<open>qcompatible Q R\<close>)
  by (simp_all add: qregister_chain_pair)

lemma index_flip_qvar_chain[simp]: \<open>index_flip_qvar (qregister_chain Q R) = qregister_chain (index_flip_qvar Q) R\<close>
  unfolding index_flip_qvar_def
  by (simp add: qregister_chain_assoc)

lemma index_flip_qvar_Fst[simp]: \<open>index_flip_qvar qFst = qSnd\<close>
  unfolding index_flip_qvar_def
  by (simp add: qcompatible_Fst_Snd qcompatible_sym qregister_chain_pair_Fst qswap_def)

lemma index_flip_qvar_Snd[simp]: \<open>index_flip_qvar qSnd = qFst\<close>
  by (simp add: index_flip_qvar_def qcompatible_Fst_Snd qcompatible_sym qregister_chain_pair_Snd qswap_def)

definition index_flip_mem2 :: "qu2 \<Rightarrow> qu2" where \<open>index_flip_mem2 = (\<lambda>(x,y). (y,x))\<close>

definition swap_cvariables_mem2 :: "'a c2variable \<Rightarrow> 'a c2variable \<Rightarrow> (cl2 \<Rightarrow> cl2)" where
  \<open>swap_cvariables_mem2 x y m = apply_cregister_total (cregister_pair x y) (\<lambda>(a,b). (b,a)) m\<close>

definition swap_variables_qvars :: \<open>'a q2variable \<Rightarrow> 'a q2variable \<Rightarrow> 'b q2variable \<Rightarrow> 'b q2variable\<close> where
  \<open>swap_variables_qvars Q Q' R = 
    qregister_chain (transform_qregister (apply_qregister (qregister_pair Q Q') swap_ell2)) R\<close>

section \<open>Unsorted\<close>

lemma getter_Snd_chain_swap[simp]: \<open>getter (cregister_chain cSnd G) (prod.swap m) = getter (cregister_chain cFst G) m\<close>
  by (simp add: getter_chain)
lemma getter_Fst_chain_swap[simp]: \<open>getter (cregister_chain cFst G) (prod.swap m) = getter (cregister_chain cSnd G) m\<close>
  by (simp add: getter_chain)

lemma apply_qregister_plus: \<open>apply_qregister X (a+b) = apply_qregister X a + apply_qregister X b\<close>
  using clinear_apply_qregister[of X]
  by (rule complex_vector.linear_add)

lemma apply_qregister_space_of_0: \<open>apply_qregister_space F 0 = 0\<close>
  by (simp add: apply_qregister_space_def)

lemma apply_qregister_space_top: \<open>qregister F \<Longrightarrow> apply_qregister_space F \<top> = \<top>\<close>
  by (simp add: apply_qregister_space_def)

lemma apply_qregister_space_bot: \<open>apply_qregister_space F \<bottom> = \<bottom>\<close>
  by (simp add: apply_qregister_space_def)

lemma apply_qregister_space_scaleC: \<open>qregister F \<Longrightarrow> apply_qregister_space F (c *\<^sub>C A) = c *\<^sub>C apply_qregister_space F A\<close>
  apply (cases \<open>c = 0\<close>)
  by (simp_all add: apply_qregister_space_bot)

lemma apply_qregister_space_scaleR: \<open>qregister F \<Longrightarrow> apply_qregister_space F (c *\<^sub>R A) = c *\<^sub>R apply_qregister_space F A\<close>
  by (simp add: apply_qregister_space_scaleC scaleR_scaleC)

lemma apply_qregister_norm: \<open>qregister F \<Longrightarrow> norm (apply_qregister F A) = norm A\<close>
  by (simp add: qregister.rep_eq register_norm)

lemma apply_qregister_uminus: \<open>apply_qregister F (- A) = - apply_qregister F A\<close>
  apply (subst scaleC_minus1_left[symmetric])
  apply (subst (2) scaleC_minus1_left[symmetric])
  by (simp only: apply_qregister_scaleC)

lemma apply_qregister_minus: \<open>apply_qregister F (A - B) = apply_qregister F A - apply_qregister F B\<close>
  by (simp only: diff_conv_add_uminus apply_qregister_plus apply_qregister_uminus)

lemma apply_qregister_space_image: \<open>apply_qregister_space Q (A *\<^sub>S S) = apply_qregister Q A *\<^sub>S apply_qregister_space Q S\<close>
proof (cases \<open>qregister Q\<close>)
  case False
  then have \<open>Q = non_qregister\<close>
    by (simp add: non_qregister)
  then show ?thesis
    by simp
next
  let ?goal = ?thesis
  case True
  then have \<open>qregister_raw (apply_qregister Q)\<close>
    by (simp add: qregister.rep_eq)
  from register_decomposition[OF this]
  have \<open>\<forall>\<^sub>\<tau> 'c::type = register_decomposition_basis (apply_qregister Q). ?goal\<close>
  proof (rule with_type_mp)
    assume \<open>\<exists>U :: ('b \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2. 
              unitary U \<and> (\<forall>\<theta>. apply_qregister Q \<theta> = sandwich U *\<^sub>V \<theta> \<otimes>\<^sub>o id_cblinfun)\<close>
    then obtain U :: \<open>('b \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close> where
      [simp]: \<open>unitary U\<close> and decomp: \<open>apply_qregister Q \<theta> = sandwich U *\<^sub>V \<theta> \<otimes>\<^sub>o id_cblinfun\<close> for \<theta>
      by auto
    have \<open>apply_qregister Q A *\<^sub>S apply_qregister_space Q S = apply_qregister Q A *\<^sub>S apply_qregister Q (Proj S) *\<^sub>S \<top>\<close>
      by (simp add: apply_qregister_space_def)
    also have \<open>\<dots> = U *\<^sub>S (A \<otimes>\<^sub>o id_cblinfun) *\<^sub>S (Proj S \<otimes>\<^sub>o id_cblinfun) *\<^sub>S U* *\<^sub>S \<top>\<close>
      by (simp add: decomp sandwich_apply lift_cblinfun_comp[OF unitaryD1] cblinfun_compose_image)
    also have \<open>\<dots> = U *\<^sub>S (A \<otimes>\<^sub>o id_cblinfun) *\<^sub>S (Proj S \<otimes>\<^sub>o id_cblinfun) *\<^sub>S \<top>\<close>
      by simp
    also have \<open>\<dots> = U *\<^sub>S (A \<otimes>\<^sub>o id_cblinfun) *\<^sub>S (Proj S \<otimes>\<^sub>o id_cblinfun) *\<^sub>S (\<top> \<otimes>\<^sub>S \<top>)\<close>
      by simp
    also have \<open>\<dots> = U *\<^sub>S (A \<otimes>\<^sub>o id_cblinfun) *\<^sub>S ((Proj S *\<^sub>S \<top>) \<otimes>\<^sub>S \<top>)\<close>
      by (simp add: tensor_ccsubspace_via_Proj)
    also have \<open>\<dots> = U *\<^sub>S ((A *\<^sub>S Proj S *\<^sub>S \<top>) \<otimes>\<^sub>S \<top>)\<close>
      by (metis cblinfun_image_id tensor_ccsubspace_image)
    also have \<open>\<dots> = U *\<^sub>S ((Proj (A *\<^sub>S S) *\<^sub>S \<top>) \<otimes>\<^sub>S \<top>)\<close>
      by simp
    also have \<open>\<dots> = U *\<^sub>S (Proj (A *\<^sub>S S) \<otimes>\<^sub>o id_cblinfun) *\<^sub>S (\<top> \<otimes>\<^sub>S \<top>)\<close>
      by (simp add: tensor_ccsubspace_via_Proj)
    also have \<open>\<dots> = U *\<^sub>S (Proj (A *\<^sub>S S) \<otimes>\<^sub>o id_cblinfun) *\<^sub>S U* *\<^sub>S \<top>\<close>
      by simp
    also have \<open>\<dots> = apply_qregister Q (Proj (A *\<^sub>S S)) *\<^sub>S \<top>\<close>
      by (simp add: cblinfun_compose_image decomp sandwich_apply)
    also have \<open>\<dots> = apply_qregister_space Q (A *\<^sub>S S)\<close>
      by (simp add: apply_qregister_space_def)
    finally show ?goal
      by simp
  qed
  from this[cancel_with_type]
  show ?thesis 
    by -
qed

lemma apply_qregister_inject': \<open>apply_qregister F a = apply_qregister F b \<longleftrightarrow> a = b\<close> if \<open>qregister F\<close>
  using that apply (transfer fixing: a b)
  using qregister_raw_inj[of _ UNIV] injD by fastforce

lemma apply_qregister_adj: \<open>apply_qregister F (A*) = (apply_qregister F A)*\<close>
  apply (cases \<open>qregister F\<close>)
   apply transfer
  by (auto simp add: register_adj non_qregister)

lemma apply_qregister_unitary[simp]: \<open>unitary (apply_qregister F U) \<longleftrightarrow> unitary U\<close> if \<open>qregister F\<close>
  unfolding unitary_def
  apply (subst apply_qregister_inject'[symmetric, OF that, of \<open>U* o\<^sub>C\<^sub>L U\<close>])
  apply (subst apply_qregister_inject'[symmetric, OF that, of \<open>U o\<^sub>C\<^sub>L U*\<close>])
  by (simp add: apply_qregister_adj qregister_compose that del: isometryD)

lemma apply_qregister_isometry[simp]: \<open>isometry (apply_qregister F U) \<longleftrightarrow> isometry U\<close> if \<open>qregister F\<close>
  unfolding isometry_def
  apply (subst apply_qregister_inject'[symmetric, OF that, of \<open>U* o\<^sub>C\<^sub>L U\<close>])
  by (simp add: apply_qregister_adj qregister_compose that del: isometryD)

lemma apply_qregister_is_Proj': \<open>is_Proj P \<Longrightarrow> is_Proj (apply_qregister F P)\<close>
  apply (transfer fixing: P)
  by (auto simp add: register_projector non_qregister_raw_def)

lemma apply_qregister_is_Proj[simp]: \<open>is_Proj (apply_qregister F P) \<longleftrightarrow> is_Proj P\<close> if \<open>qregister F\<close>
  using that
  by (auto simp add: is_Proj_algebraic apply_qregister_inject apply_qregister_inject' 
      simp flip: qregister_compose apply_qregister_adj)

lemma apply_qregister_Proj: \<open>apply_qregister F (Proj S) = Proj (apply_qregister_space F S)\<close>
  by (simp add: Proj_on_own_range apply_qregister_space_def apply_qregister_is_Proj')

lemma kernel_square[simp]: \<open>kernel (A* o\<^sub>C\<^sub>L A) = kernel A\<close>
proof (intro ccsubspace_eqI iffI)
  fix x
  assume \<open>x \<in> space_as_set (kernel A)\<close>
  then show \<open>x \<in> space_as_set (kernel (A* o\<^sub>C\<^sub>L A))\<close>
    by (simp add: kernel.rep_eq)
next
  fix x
  assume \<open>x \<in> space_as_set (kernel (A* o\<^sub>C\<^sub>L A))\<close>
  then have \<open>A* *\<^sub>V A *\<^sub>V x = 0\<close>
    by (simp add: kernel.rep_eq)
  then have \<open>(A *\<^sub>V x) \<bullet>\<^sub>C (A *\<^sub>V x) = 0\<close>
    by (metis cinner_adj_right cinner_zero_right)
  then have \<open>A *\<^sub>V x = 0\<close>
    by auto
  then show \<open>x \<in> space_as_set (kernel A)\<close>
    by (simp add: kernel.rep_eq)
qed


lemma apply_qregister_partial_isometry: \<open>qregister F \<Longrightarrow> partial_isometry (apply_qregister F U) \<longleftrightarrow> partial_isometry U\<close>
  by (simp add: partial_isometry_iff_square_proj flip: apply_qregister_adj qregister_compose)

lemma apply_qregister_mono: 
  assumes [simp]: \<open>qregister Q\<close>
  shows \<open>apply_qregister Q A \<le> apply_qregister Q B \<longleftrightarrow> A \<le> B\<close>
proof (rule iffI)
  assume \<open>A \<le> B\<close>
  then obtain C :: \<open>'a qupdate\<close> where \<open>B - A = C* o\<^sub>C\<^sub>L C\<close>
    by (metis diff_ge_0_iff_ge positive_hermitianI sqrt_op_pos sqrt_op_square)
  then have \<open>apply_qregister Q B - apply_qregister Q A = (apply_qregister Q C)* o\<^sub>C\<^sub>L apply_qregister Q C\<close>
    by (metis apply_qregister_adj apply_qregister_minus qregister_compose)
  then show \<open>apply_qregister Q A \<le> apply_qregister Q B\<close>
    by (metis diff_ge_0_iff_ge positive_cblinfun_squareI)
next
  assume asm: \<open>apply_qregister Q A \<le> apply_qregister Q B\<close>
  have [simp]: \<open>qregister_raw (apply_qregister Q)\<close>
    using assms qregister.rep_eq by blast
  from register_decomposition[OF this]
  have \<open>\<forall>\<^sub>\<tau> 'z::type = register_decomposition_basis (apply_qregister Q). A \<le> B\<close>
  proof (rule with_type_mp)
    assume \<open>\<exists>U::('a \<times> 'z) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2. unitary U \<and> (\<forall>\<theta>. apply_qregister Q \<theta> = sandwich U *\<^sub>V \<theta> \<otimes>\<^sub>o id_cblinfun)\<close>
    then obtain U :: \<open>('a \<times> 'z) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close> where
      [simp]: \<open>unitary U\<close> and decomp: \<open>apply_qregister Q \<theta> = sandwich U *\<^sub>V \<theta> \<otimes>\<^sub>o id_cblinfun\<close> for \<theta>
      by auto
    show \<open>A \<le> B\<close>
    proof (rule cblinfun_leI)
      fix x
      obtain y :: \<open>'z ell2\<close> where \<open>norm y = 1\<close>
        by (meson norm_ket)
      define BA where \<open>BA = B - A\<close>
      from asm have QBA_pos: \<open>apply_qregister Q BA \<ge> 0\<close>
        by (simp add: BA_def apply_qregister_minus)
      have \<open>x \<bullet>\<^sub>C (BA *\<^sub>V x) = (x \<otimes>\<^sub>s y) \<bullet>\<^sub>C ((BA \<otimes>\<^sub>o id_cblinfun) *\<^sub>V (x \<otimes>\<^sub>s y))\<close>
        using \<open>norm y = 1\<close> by (simp add: tensor_op_ell2 cnorm_eq_1)
      also have \<open>\<dots> = (U *\<^sub>V (x \<otimes>\<^sub>s y)) \<bullet>\<^sub>C (apply_qregister Q BA *\<^sub>V U *\<^sub>V (x \<otimes>\<^sub>s y))\<close>
        by (simp add: decomp sandwich_apply lift_cblinfun_comp[OF unitaryD1]
            flip: cinner_adj_right)
      also have \<open>\<dots> \<ge> 0\<close>
        by (meson QBA_pos cinner_pos_if_pos)
      finally show \<open>x \<bullet>\<^sub>C (A *\<^sub>V x) \<le> x \<bullet>\<^sub>C (B *\<^sub>V x)\<close>
        by (simp add: BA_def cblinfun.diff_left cinner_diff_right apply_qregister_minus)
    qed
  qed
  with this[cancel_with_type]
  show \<open>A \<le> B\<close>
    by -
qed

lemma apply_qregister_space_mono: \<open>qregister F \<Longrightarrow> apply_qregister_space F A \<le> apply_qregister_space F B \<longleftrightarrow> A \<le> B\<close>
  by (simp add: apply_qregister_space_def Proj_on_own_range apply_qregister_mono
      flip: Proj_mono)

lemma apply_qregister_space_inject': \<open>apply_qregister_space F a = apply_qregister_space F b \<longleftrightarrow> a = b\<close> if \<open>qregister F\<close>
  by (simp add: apply_qregister_space_mono order_class.order_eq_iff that)

lemma apply_qregister_space_uminus: \<open>qregister F \<Longrightarrow> apply_qregister_space F (- A) = - apply_qregister_space F A\<close>
  apply (simp only: apply_qregister_space_def Proj_ortho_compl apply_qregister_minus apply_qregister_of_id)
  by (simp only: apply_qregister_Proj Proj_range flip: Proj_ortho_compl)

lemma apply_qregister_space_INF: 
  assumes [simp]: \<open>qregister F\<close>
  shows "apply_qregister_space F (INF x\<in>X. S x) = (INF x\<in>X. apply_qregister_space F (S x))"
proof (cases \<open>X = {}\<close>)
  case True
  then show ?thesis
    by (simp add: apply_qregister_space_top)
next
  let ?goal = ?thesis
  case False
  have \<open>qregister_raw (apply_qregister F)\<close>
    using assms qregister.rep_eq by blast
  from register_decomposition[OF this]
  have \<open>\<forall>\<^sub>\<tau> 'z::type = register_decomposition_basis (apply_qregister F).
        ?goal\<close>
  proof (rule with_type_mp)
    assume \<open>\<exists>U::('a \<times> 'z) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2. unitary U \<and> (\<forall>\<theta>. apply_qregister F \<theta> = sandwich U *\<^sub>V \<theta> \<otimes>\<^sub>o id_cblinfun)\<close>
    then obtain U :: \<open>('a \<times> 'z) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close> where
      [simp]: \<open>unitary U\<close> and decomp: \<open>apply_qregister F \<theta> = sandwich U *\<^sub>V \<theta> \<otimes>\<^sub>o id_cblinfun\<close> for \<theta>
      by auto
    from tensor_ccsubspace_INF_left[where X=X and T=\<open>\<top> :: 'z ell2 ccsubspace\<close> and S=S]
    have ?goal if \<open>X \<noteq> {}\<close>
      by (simp add: apply_qregister_space_def decomp sandwich_apply cblinfun_compose_image
          unitary_isometry tensor_ccsubspace_via_Proj False
          flip: cblinfun_image_INF_eq)
    moreover have ?goal if \<open>X = {}\<close>
      using False that by auto
    ultimately show ?goal
      apply (cases \<open>X = {}\<close>) by auto
  qed
  from this[cancel_with_type]
  show ?thesis
    by auto
qed

lemma apply_qregister_space_SUP: "apply_qregister_space F (SUP x\<in>X. S x) = (SUP x\<in>X. apply_qregister_space F (S x))"
  apply (cases \<open>qregister F\<close>)
   apply (rule complement_injective)
   apply (simp add: uminus_SUP apply_qregister_space_INF flip: apply_qregister_space_uminus)
  by (simp add: non_qregister)

lemma apply_qregister_space_inf: \<open>apply_qregister_space F (A \<sqinter> B) = apply_qregister_space F A \<sqinter> apply_qregister_space F B\<close>
  apply (cases \<open>qregister F\<close>)
  using apply_qregister_space_INF[where F=F and X=\<open>{True,False}\<close> and S=\<open>\<lambda> True \<Rightarrow> A | False \<Rightarrow> B\<close>]
  by (auto simp: non_qregister)

lemma apply_qregister_space_sup: \<open>apply_qregister_space F (A \<squnion> B) = apply_qregister_space F A \<squnion> apply_qregister_space F B\<close>
  using apply_qregister_space_SUP[where F=F and X=\<open>{True,False}\<close> and S=\<open>\<lambda> True \<Rightarrow> A | False \<Rightarrow> B\<close>]
  by simp

lemma apply_qregister_space_plus: \<open>apply_qregister_space F (A + B) = apply_qregister_space F A + apply_qregister_space F B\<close>
  by (simp add: plus_ccsubspace_def apply_qregister_space_sup)

lemma apply_qregister_space_minus: \<open>apply_qregister_space F (A - B) = apply_qregister_space F A - apply_qregister_space F B\<close>
  apply (cases \<open>qregister F\<close>)
  by (simp_all add: complemented_lattice_class.diff_eq apply_qregister_space_inf apply_qregister_space_uminus
      non_qregister)

lemma apply_qregister_space_kernel: \<open>qregister F \<Longrightarrow> apply_qregister_space F (Complex_Bounded_Linear_Function.kernel A) = Complex_Bounded_Linear_Function.kernel (apply_qregister F A)\<close>
  by (metis (no_types, lifting) Proj_on_image Proj_top apply_qregister_adj apply_qregister_of_id apply_qregister_space_def apply_qregister_space_image apply_qregister_space_uminus kernel_compl_adj_range)

lemma apply_qregister_space_eigenspace: \<open>qregister F \<Longrightarrow> apply_qregister_space F (eigenspace c A) = eigenspace c (apply_qregister F A)\<close>
  by (simp add: apply_qregister_minus apply_qregister_scaleC apply_qregister_space_kernel eigenspace_def)

lemma apply_qregister_space_orthogonal_spaces: \<open>qregister F \<Longrightarrow> orthogonal_spaces (apply_qregister_space F A) (apply_qregister_space F B) = orthogonal_spaces A B\<close>
  by (metis apply_qregister_space_mono apply_qregister_space_uminus orthogonal_spaces_leq_compl)

lemma apply_qregister_pos: \<open>apply_qregister F A \<ge> 0 \<longleftrightarrow> A \<ge> 0\<close> if \<open>qregister F\<close>
  by (metis that apply_qregister_mono apply_qregister_of_0)

lemma apply_qregister_abs_op: \<open>apply_qregister F (abs_op A) = abs_op (apply_qregister F A)\<close>
proof (cases \<open>qregister F\<close>)
  case True
  note [simp] = this
  show ?thesis
    apply (rule abs_opI)
    by (simp_all add: abs_op_square abs_op_pos apply_qregister_pos flip: apply_qregister_adj qregister_compose)
next
  case False
  then show ?thesis
    by (simp add: non_qregister)
qed

lemma apply_qregister_sqrt_op: \<open>apply_qregister F (sqrt_op A) = sqrt_op (apply_qregister F A)\<close>
proof (cases \<open>qregister F\<close>)
  case True
  note posA[simp] = this
  show ?thesis
  proof (cases \<open>A \<ge> 0\<close>)
    case True
    then have posFA: \<open>0 \<le> apply_qregister F (sqrt_op A)\<close>
      by (simp add: apply_qregister_pos)
    have sq: \<open>apply_qregister F (sqrt_op A)* o\<^sub>C\<^sub>L apply_qregister F (sqrt_op A) = apply_qregister F A\<close>
      using True by (simp_all add: abs_op_square flip: apply_qregister_adj qregister_compose positive_hermitianI)
    from posFA sq
    show ?thesis
      by (rule sqrt_op_unique)
  next
    case False
    then have 1: \<open>sqrt_op A = 0\<close>
      by (rule sqrt_op_nonpos)
    from False
    have \<open>\<not> (0 \<le> apply_qregister F A)\<close>
      by (simp add: apply_qregister_pos)
    then have 2: \<open>sqrt_op (apply_qregister F A) = 0\<close>
      by (rule sqrt_op_nonpos)
    from 1 2
    show ?thesis 
      by simp
  qed
next
  case False
  then show ?thesis
    by (simp add: non_qregister)
qed 

lemma apply_qregister_polar_decomposition: \<open>apply_qregister F (polar_decomposition A) = polar_decomposition (apply_qregister F A)\<close>
proof (cases \<open>qregister F\<close>)
  case True
  define PA FPA where \<open>PA = polar_decomposition A\<close> and \<open>FPA = apply_qregister F PA\<close>
  have \<open>kernel (apply_qregister F (polar_decomposition A)) = kernel (apply_qregister F A)\<close>
    by (metis True apply_qregister_space_kernel polar_decomposition_initial_space)
  moreover have \<open>apply_qregister F (polar_decomposition A) o\<^sub>C\<^sub>L abs_op (apply_qregister F A) = apply_qregister F A\<close>
    by (metis apply_qregister_abs_op polar_decomposition_correct qregister_compose)
  ultimately show ?thesis
    by (rule polar_decomposition_unique)
next
  case False
  then show ?thesis 
    by (simp add: polar_decomposition_0 non_qregister)
qed

(* axiomatization lift_pure_state :: \<open>('a,'b) qregister \<Rightarrow> 'a ell2 \<Rightarrow> 'b ell2\<close> *)

(* lift_definition ccomplements :: \<open>('a,'c) cregister \<Rightarrow> ('b,'c) cregister \<Rightarrow> bool\<close> is complements. *)
lift_definition qcomplements :: \<open>('a,'c) qregister \<Rightarrow> ('b,'c) qregister \<Rightarrow> bool\<close> is complements.

lemma qcomplements_def': \<open>qcomplements F G \<longleftrightarrow> iso_qregister (qregister_pair F G)\<close>
(* TODO "qcompatible F G" can be dropped *)
  unfolding iso_qregister_def apply transfer 
  by (auto simp: complements_def Laws_Quantum.iso_register_def non_qregister_raw)

text \<open>Contains rules for the translate_to_index_registers-method.

Format of the rules: \<^term>\<open>assumptions \<Longrightarrow> lhs \<equiv> rhs\<close>.
Here lhs is of the form \<^term>\<open>op (apply_qregister F X) (apply_qregister G Y)\<close> (or similar with \<^const>\<open>apply_qregister_space\<close>, or with nothing if its not something liftable)
and rhs is of the form \<^term>\<open>apply_qregister H term3\<close> (or similar with \<^const>\<open>apply_qregister_space\<close>).

The assumptions can be used to instantiate variables in H or term3.
The assumptions are evaluated in forward order.
Only specific forms of assumptions are allowed, see the source of the ML function \<open>translate_to_index_registers_tac1\<close>.
\<close>
named_theorems translate_to_index_registers

(* TODO ensure that we descend into registers if descent-mode is on, even if there is no explicit TTIR_EQ-condition *)

definition \<open>TTIR_QREGISTER Q \<longleftrightarrow> qregister Q\<close>
definition \<open>TTIR_LUB F G FG F' G' \<longleftrightarrow> qregister FG \<and> F = qregister_chain FG F' \<and> G = qregister_chain FG G'\<close>
definition \<open>TTIR_APPLY_QREGISTER A F B \<longleftrightarrow> A = apply_qregister F B\<close>
definition \<open>TTIR_APPLY_QREGISTER_SPACE A F B \<longleftrightarrow> A = apply_qregister_space F B\<close>
definition \<open>PROP TTIR_EQ (A::'a::{}) B \<equiv> (A \<equiv> B)\<close>

lemma translate_to_index_registers_assm_lub_tac_aux: 
  assumes \<open>qregister_le F FG \<and> qregister_le G FG\<close>
  assumes \<open>qregister_conversion F FG = F'\<close>
  assumes \<open>qregister_conversion G FG = G'\<close>
  shows \<open>TTIR_LUB F G FG F' G'\<close>
  by (metis assms TTIR_LUB_def qregister_chain_conversion qregister_le_def)

lemma translate_to_index_registers_template_oo:
  assumes \<open>\<And>FG X Y. qregister FG \<Longrightarrow> 
        apply_qregister FG (f' X Y) = f (apply_qregister FG X) (apply_qregister FG Y)\<close>
  assumes \<open>TTIR_APPLY_QREGISTER A F A'\<close>
  assumes \<open>TTIR_APPLY_QREGISTER B G B'\<close>
  assumes \<open>TTIR_LUB F G FG F' G'\<close>
  shows \<open>TTIR_APPLY_QREGISTER (f A B) FG (f' (apply_qregister F' A') (apply_qregister G' B'))\<close>
  using assms by (simp add: TTIR_APPLY_QREGISTER_def TTIR_LUB_def)

lemma translate_to_index_registers_template_o:
  assumes \<open>\<And>F X. apply_qregister F (f' X) = f (apply_qregister F X)\<close>
  assumes \<open>TTIR_APPLY_QREGISTER A F A'\<close>
  shows \<open>TTIR_APPLY_QREGISTER (f A) F (f' A')\<close>
  using assms by (simp add: TTIR_APPLY_QREGISTER_def)

lemma translate_to_index_registers_template_o':
  assumes \<open>\<And>F X. f (apply_qregister F X) = f' X\<close>
  assumes \<open>TTIR_APPLY_QREGISTER A F A'\<close>
  shows \<open>PROP TTIR_EQ (f A) (f' A')\<close>
  using assms by (simp add: TTIR_APPLY_QREGISTER_def TTIR_EQ_def)

lemma translate_to_index_registers_template_o'_qr:
  assumes \<open>\<And>F X. qregister F \<Longrightarrow> f (apply_qregister F X) = f' X\<close>
  assumes \<open>TTIR_APPLY_QREGISTER A F A'\<close>
  assumes \<open>TTIR_QREGISTER F\<close>
  shows \<open>PROP TTIR_EQ (f A) (f' A')\<close>
  using assms by (simp add: TTIR_APPLY_QREGISTER_def TTIR_QREGISTER_def TTIR_EQ_def)

lemma translate_to_index_registers_template_o_s:
  assumes \<open>\<And>F X. apply_qregister_space F (f' X) = f (apply_qregister F X)\<close>
  assumes \<open>TTIR_APPLY_QREGISTER A F A'\<close>
  shows \<open>TTIR_APPLY_QREGISTER_SPACE (f A) F (f' A')\<close>
  using assms by (simp add: TTIR_APPLY_QREGISTER_def TTIR_APPLY_QREGISTER_SPACE_def)

lemma translate_to_index_registers_template_s_o:
  assumes \<open>\<And>F X. apply_qregister F (f' X) = f (apply_qregister_space F X)\<close>
  assumes \<open>TTIR_APPLY_QREGISTER_SPACE A F A'\<close>
  shows \<open>TTIR_APPLY_QREGISTER (f A) F (f' A')\<close>
  using assms by (simp add: TTIR_APPLY_QREGISTER_def TTIR_APPLY_QREGISTER_SPACE_def)

lemma translate_to_index_registers_template_o_s_qr:
  assumes \<open>\<And>F X. qregister F \<Longrightarrow> apply_qregister_space F (f' X) = f (apply_qregister F X)\<close>
  assumes \<open>TTIR_APPLY_QREGISTER A F A'\<close>
  assumes \<open>TTIR_QREGISTER F\<close>
  shows \<open>TTIR_APPLY_QREGISTER_SPACE (f A) F (f' A')\<close>
  using assms by (simp add: TTIR_APPLY_QREGISTER_def TTIR_APPLY_QREGISTER_SPACE_def TTIR_QREGISTER_def)

lemma translate_to_index_registers_template_s:
  assumes \<open>\<And>F X. apply_qregister_space F (f' X) = f (apply_qregister_space F X)\<close>
  assumes \<open>TTIR_APPLY_QREGISTER_SPACE A F A'\<close>
  shows \<open>TTIR_APPLY_QREGISTER_SPACE (f A) F (f' A')\<close>
  using assms by (simp add: TTIR_APPLY_QREGISTER_SPACE_def)

lemma translate_to_index_registers_template_s_qr:
  assumes \<open>\<And>F X. qregister F \<Longrightarrow> apply_qregister_space F (f' X) = f (apply_qregister_space F X)\<close>
  assumes \<open>TTIR_APPLY_QREGISTER_SPACE A F A'\<close>
  assumes \<open>TTIR_QREGISTER F\<close>
  shows \<open>TTIR_APPLY_QREGISTER_SPACE (f A) F (f' A')\<close>
  using assms by (simp add: TTIR_APPLY_QREGISTER_SPACE_def TTIR_QREGISTER_def)

lemma translate_to_index_registers_template_ss:
  assumes \<open>\<And>FG X Y. qregister FG \<Longrightarrow> 
        apply_qregister_space FG (f' X Y) = f (apply_qregister_space FG X) (apply_qregister_space FG Y)\<close>
  assumes \<open>TTIR_APPLY_QREGISTER_SPACE A F A'\<close>
  assumes \<open>TTIR_APPLY_QREGISTER_SPACE B G B'\<close>
  assumes \<open>TTIR_LUB F G FG F' G'\<close>
  shows \<open>TTIR_APPLY_QREGISTER_SPACE (f A B) FG (f' (apply_qregister_space F' A') (apply_qregister_space G' B'))\<close>
  using assms by (simp add: TTIR_APPLY_QREGISTER_SPACE_def TTIR_LUB_def)

lemma translate_to_index_registers_template_oo':
  assumes \<open>\<And>FG X Y. qregister FG \<Longrightarrow> 
        f (apply_qregister FG X) (apply_qregister FG Y) = f' X Y\<close>
  assumes \<open>TTIR_APPLY_QREGISTER A F A'\<close>
  assumes \<open>TTIR_APPLY_QREGISTER B G B'\<close>
  assumes \<open>TTIR_LUB F G FG F' G'\<close>
  shows \<open>PROP TTIR_EQ (f A B) (f' (apply_qregister F' A') (apply_qregister G' B'))\<close>
  using assms by (simp add: TTIR_APPLY_QREGISTER_def TTIR_EQ_def TTIR_LUB_def)

lemma translate_to_index_registers_template_ss':
  assumes \<open>\<And>FG X Y. qregister FG \<Longrightarrow> 
        f (apply_qregister_space FG X) (apply_qregister_space FG Y) = f' X Y\<close>
  assumes \<open>TTIR_APPLY_QREGISTER_SPACE A F A'\<close>
  assumes \<open>TTIR_APPLY_QREGISTER_SPACE B G B'\<close>
  assumes \<open>TTIR_LUB F G FG F' G'\<close>
  shows \<open>PROP TTIR_EQ (f A B) (f' (apply_qregister_space F' A') (apply_qregister_space G' B'))\<close>
  using assms by (simp add: TTIR_APPLY_QREGISTER_SPACE_def TTIR_EQ_def TTIR_LUB_def)

lemma translate_to_index_registers_template_os:
  assumes \<open>\<And>FG X Y. qregister FG \<Longrightarrow> 
        apply_qregister_space FG (f' X Y) = f (apply_qregister FG X) (apply_qregister_space FG Y)\<close>
  assumes \<open>TTIR_APPLY_QREGISTER A F A'\<close>
  assumes \<open>TTIR_APPLY_QREGISTER_SPACE B G B'\<close>
  assumes \<open>TTIR_LUB F G FG F' G'\<close>
  shows \<open>TTIR_APPLY_QREGISTER_SPACE (f A B) FG (f' (apply_qregister F' A') (apply_qregister_space G' B'))\<close>
  using assms by (simp add: TTIR_APPLY_QREGISTER_def TTIR_APPLY_QREGISTER_SPACE_def TTIR_LUB_def)

lemma translate_to_index_registers_template_s_empty:
  assumes \<open>\<And>FG. qregister FG \<Longrightarrow> apply_qregister_space FG f = f'\<close>
  shows \<open>TTIR_APPLY_QREGISTER_SPACE f' (empty_qregister :: (unit,_) qregister) f\<close>
  using assms by (simp add: TTIR_APPLY_QREGISTER_SPACE_def)

lemma translate_to_index_registers_template_o_empty:
  assumes \<open>\<And>FG. qregister FG \<Longrightarrow> apply_qregister FG f = f'\<close>
  shows \<open>TTIR_APPLY_QREGISTER f' (empty_qregister :: (unit,_) qregister) f\<close>
  using assms by (simp add: TTIR_APPLY_QREGISTER_def)

lemma translate_to_index_registers_apply[translate_to_index_registers]:
  assumes \<open>TTIR_APPLY_QREGISTER A G A'\<close>
  shows \<open>TTIR_APPLY_QREGISTER (apply_qregister F A) (qregister_chain F G) A'\<close>
  using assms by (auto simp: TTIR_APPLY_QREGISTER_def)

lemma translate_to_index_registers_apply_space[translate_to_index_registers]:
  assumes \<open>TTIR_APPLY_QREGISTER_SPACE A G A'\<close>
  shows \<open>TTIR_APPLY_QREGISTER_SPACE (apply_qregister_space F A) (qregister_chain F G) A'\<close>
  using assms by (auto simp: TTIR_APPLY_QREGISTER_SPACE_def)

lemmas translate_to_index_registers_compose[translate_to_index_registers] =
  translate_to_index_registers_template_oo[where f=cblinfun_compose, OF qregister_compose]

lemmas translate_to_index_registers_plus_op[translate_to_index_registers] =
  translate_to_index_registers_template_oo[where f=plus, OF apply_qregister_plus]

lemmas translate_to_index_registers_minus_op[translate_to_index_registers] =
  translate_to_index_registers_template_oo[where f=minus, OF apply_qregister_minus]

lemmas translate_to_index_registers_image[translate_to_index_registers] =
  translate_to_index_registers_template_os[where f=cblinfun_image, OF apply_qregister_space_image]

lemmas translate_to_index_registers_eq_op[translate_to_index_registers] =
  translate_to_index_registers_template_oo'[where f=HOL.eq, OF apply_qregister_inject', remove_prem]

lemmas translate_to_index_registers_inf[translate_to_index_registers] =
  translate_to_index_registers_template_ss[where f=inf, OF apply_qregister_space_inf]

lemmas translate_to_index_registers_minus_space[translate_to_index_registers] =
  translate_to_index_registers_template_ss[where f=minus, OF apply_qregister_space_minus]

lemmas translate_to_index_registers_sup[translate_to_index_registers] =
  translate_to_index_registers_template_ss[where f=sup, OF apply_qregister_space_sup]

lemmas translate_to_index_registers_plus_space[translate_to_index_registers] =
  translate_to_index_registers_template_ss[where f=plus, OF apply_qregister_space_plus]

lemmas translate_to_index_registers_eq_space[translate_to_index_registers] =
  translate_to_index_registers_template_ss'[where f=HOL.eq, OF apply_qregister_space_inject', remove_prem]

lemmas translate_to_index_registers_leq_space[translate_to_index_registers] =
  translate_to_index_registers_template_ss'[where f=less_eq, OF apply_qregister_space_mono, remove_prem]

lemmas translate_to_index_registers_leq_op[translate_to_index_registers] =
  translate_to_index_registers_template_oo'[where f=less_eq, OF apply_qregister_mono, remove_prem]

lemmas translate_to_index_registers_top[translate_to_index_registers] =
  translate_to_index_registers_template_s_empty[where f=top, OF apply_qregister_space_top, remove_prem]

lemmas translate_to_index_registers_bot[translate_to_index_registers] =
  translate_to_index_registers_template_s_empty[where f=bot, OF apply_qregister_space_bot]

lemmas translate_to_index_registers_id[translate_to_index_registers] =
  translate_to_index_registers_template_o_empty[where f=id_cblinfun, OF apply_qregister_of_id, remove_prem]

lemma translate_to_index_registers_1[translate_to_index_registers]:
  \<open>TTIR_APPLY_QREGISTER 1 (empty_qregister :: (unit,_) qregister) id_cblinfun\<close>
  using translate_to_index_registers_id by (simp flip: id_cblinfun_eq_1)

lemmas translate_to_index_registers_zero[translate_to_index_registers] =
  translate_to_index_registers_template_o_empty[where f=0, OF apply_qregister_of_0]

lemmas translate_to_index_registers_zero_space[translate_to_index_registers] =
  translate_to_index_registers_template_s_empty[where f=0, OF apply_qregister_space_of_0]

lemmas translate_to_index_registers_uminus_op[translate_to_index_registers] =
  translate_to_index_registers_template_o[where f=uminus, OF apply_qregister_uminus]

lemmas translate_to_index_registers_uminus_space[translate_to_index_registers] =
  translate_to_index_registers_template_s_qr[where f=uminus, OF apply_qregister_space_uminus, remove_prem]

lemmas translate_to_index_registers_adj[translate_to_index_registers] =
  translate_to_index_registers_template_o[where f=adj, OF apply_qregister_adj]

lemmas translate_to_index_registers_scaleC[translate_to_index_registers] =
  translate_to_index_registers_template_o[where f=\<open>scaleC _\<close>, OF apply_qregister_scaleC]

lemmas translate_to_index_registers_scaleR[translate_to_index_registers] =
  translate_to_index_registers_template_o[where f=\<open>scaleR _\<close>, OF apply_qregister_scaleR]

lemmas translate_to_index_registers_scaleC_space[translate_to_index_registers] =
  translate_to_index_registers_template_s_qr[where f=\<open>scaleC _\<close>, OF apply_qregister_space_scaleC, remove_prem]

lemmas translate_to_index_registers_scaleR_space[translate_to_index_registers] =
  translate_to_index_registers_template_s_qr[where f=\<open>scaleR _\<close>, OF apply_qregister_space_scaleR, remove_prem]

lemmas translate_to_index_registers_norm[translate_to_index_registers] =
  translate_to_index_registers_template_o'_qr[where f=norm, OF apply_qregister_norm, remove_prem]

lemmas translate_to_index_registers_Proj[translate_to_index_registers] =
  translate_to_index_registers_template_s_o[where f=Proj, OF apply_qregister_Proj]

lemmas translate_to_index_registers_is_Proj[translate_to_index_registers] =
  translate_to_index_registers_template_o'_qr[where f=is_Proj, OF apply_qregister_is_Proj, remove_prem]

lemmas translate_to_index_registers_kernel[translate_to_index_registers] =
  translate_to_index_registers_template_o_s_qr[where f=Complex_Bounded_Linear_Function.kernel, OF apply_qregister_space_kernel, remove_prem]

lemmas translate_to_index_registers_eigenspace[translate_to_index_registers] =
  translate_to_index_registers_template_o_s_qr[where f=\<open>eigenspace _\<close>, OF apply_qregister_space_eigenspace, remove_prem]

lemmas translate_to_index_registers_orthogonal_spaces[translate_to_index_registers] =
  translate_to_index_registers_template_ss'[where f=orthogonal_spaces, OF apply_qregister_space_orthogonal_spaces, remove_prem]

lemmas translate_to_index_registers_abs_op[translate_to_index_registers] =
  translate_to_index_registers_template_o[where f=abs_op, OF apply_qregister_abs_op]

lemmas translate_to_index_registers_sqrt_op[translate_to_index_registers] =
  translate_to_index_registers_template_o[where f=sqrt_op, OF apply_qregister_sqrt_op]

lemmas translate_to_index_registers_polar_decomposition[translate_to_index_registers] =
  translate_to_index_registers_template_o[where f=polar_decomposition, OF apply_qregister_polar_decomposition]

lemmas translate_to_index_registers_unitary[translate_to_index_registers] =
  translate_to_index_registers_template_o'_qr[where f=unitary, OF apply_qregister_unitary, remove_prem]

lemmas translate_to_index_registers_isometry[translate_to_index_registers] =
  translate_to_index_registers_template_o'_qr[where f=isometry, OF apply_qregister_isometry, remove_prem]

lemmas translate_to_index_registers_partial_isometry[translate_to_index_registers] =
  translate_to_index_registers_template_o'_qr[where f=partial_isometry, OF apply_qregister_partial_isometry, remove_prem]

lemma translate_to_index_registers_INF[translate_to_index_registers]:
  assumes \<open>\<And>x. TTIR_APPLY_QREGISTER_SPACE (S x) Q (T x)\<close>
  assumes \<open>TTIR_QREGISTER Q\<close>
  shows \<open>TTIR_APPLY_QREGISTER_SPACE (INF x\<in>A. S x) Q (INF x\<in>A. T x)\<close>
  using assms
  by (simp add: TTIR_APPLY_QREGISTER_SPACE_def TTIR_QREGISTER_def apply_qregister_space_INF)

lemma translate_to_index_registers_SUP[translate_to_index_registers]:
  assumes \<open>\<And>x. TTIR_APPLY_QREGISTER_SPACE (S x) Q (T x)\<close>
  shows \<open>TTIR_APPLY_QREGISTER_SPACE (SUP x\<in>A. S x) Q (SUP x\<in>A. T x)\<close>
  using assms
  by (simp add: TTIR_APPLY_QREGISTER_SPACE_def TTIR_QREGISTER_def apply_qregister_space_SUP)

lemma translate_to_index_registers_let_ss[translate_to_index_registers]:
  fixes S :: \<open>'a ell2 ccsubspace \<Rightarrow> 'b ell2 ccsubspace\<close>
  assumes \<open>TTIR_APPLY_QREGISTER_SPACE A R B\<close>
  assumes \<open>\<And>x. TTIR_APPLY_QREGISTER_SPACE (S (apply_qregister_space R x)) Q (T x)\<close>
  shows \<open>TTIR_APPLY_QREGISTER_SPACE (let x = A in S x) Q (let x = B in T x)\<close>
  using assms by (simp add: Let_def TTIR_APPLY_QREGISTER_SPACE_def)

lemma translate_to_index_registers_let_os[translate_to_index_registers]:
  fixes S :: \<open>'a qupdate \<Rightarrow> 'b ell2 ccsubspace\<close>
  assumes \<open>TTIR_APPLY_QREGISTER A R B\<close>
  assumes \<open>\<And>x. TTIR_APPLY_QREGISTER_SPACE (S (apply_qregister R x)) Q (T x)\<close>
  shows \<open>TTIR_APPLY_QREGISTER_SPACE (let x = A in S x) Q (let x = B in T x)\<close>
  using assms by (simp add: Let_def TTIR_APPLY_QREGISTER_def TTIR_APPLY_QREGISTER_SPACE_def)

lemma translate_to_index_registers_let_sx[translate_to_index_registers]:
  fixes S :: \<open>'a ell2 ccsubspace \<Rightarrow> 'b ell2 ccsubspace\<close>
  assumes \<open>TTIR_APPLY_QREGISTER_SPACE A R B\<close>
  assumes \<open>\<And>x. PROP TTIR_EQ (S (apply_qregister_space R x)) (T x)\<close>
  shows \<open>PROP TTIR_EQ (let x = A in S x) (let x = B in T x)\<close>
  using assms by (simp add: Let_def TTIR_APPLY_QREGISTER_SPACE_def)

lemma translate_to_index_registers_let_ox[translate_to_index_registers]:
  fixes S :: \<open>'a qupdate \<Rightarrow> 'b ell2 ccsubspace\<close>
  assumes \<open>TTIR_APPLY_QREGISTER A R B\<close>
  assumes \<open>\<And>x. PROP TTIR_EQ (S (apply_qregister R x)) (T x)\<close>
  shows \<open>PROP TTIR_EQ (let x = A in S x) (let x = B in T x)\<close>
  using assms by (simp add: Let_def TTIR_APPLY_QREGISTER_def)

lemma translate_to_index_registers_let_so[translate_to_index_registers]:
  fixes S :: \<open>'a ell2 ccsubspace \<Rightarrow> 'b qupdate\<close>
  assumes \<open>TTIR_APPLY_QREGISTER_SPACE A R B\<close>
  assumes \<open>\<And>x. TTIR_APPLY_QREGISTER (S (apply_qregister_space R x)) Q (T x)\<close>
  shows \<open>TTIR_APPLY_QREGISTER (let x = A in S x) Q (let x = B in T x)\<close>
  using assms by (simp add: Let_def TTIR_APPLY_QREGISTER_def TTIR_APPLY_QREGISTER_SPACE_def)

lemma translate_to_index_registers_let_oo[translate_to_index_registers]:
  fixes S :: \<open>'a qupdate \<Rightarrow> 'b qupdate\<close>
  assumes \<open>TTIR_APPLY_QREGISTER A R B\<close>
  assumes \<open>\<And>x. TTIR_APPLY_QREGISTER (S (apply_qregister R x)) Q (T x)\<close>
  shows \<open>TTIR_APPLY_QREGISTER (let x = A in S x) Q (let x = B in T x)\<close>
  using assms by (simp add: Let_def TTIR_APPLY_QREGISTER_def)

lemma translate_to_index_registers_let_s[translate_to_index_registers]:
  assumes \<open>\<And>x. TTIR_APPLY_QREGISTER_SPACE (S x) Q (T x)\<close>
  shows \<open>TTIR_APPLY_QREGISTER_SPACE (let x = y in S x) Q (let x = y in T x)\<close>
  by (simp add: assms)

lemma translate_to_index_registers_let_o[translate_to_index_registers]:
  assumes \<open>\<And>x. TTIR_APPLY_QREGISTER (S x) Q (T x)\<close>
  shows \<open>TTIR_APPLY_QREGISTER (let x = y in S x) Q (let x = y in T x)\<close>
  by (simp add: assms)

(* Could be an alternative to the more complex (but more let-duplication-avoiding) TTIR_APPLY_QREGISTER_SPACE-rules for let above *)
lemma translate_to_index_registers_let1':
  assumes \<open>TTIR_APPLY_QREGISTER_SPACE (S y) Q T\<close>
  shows \<open>TTIR_APPLY_QREGISTER_SPACE (let x = y in S x) Q T\<close>
  by (simp add: assms)
lemma translate_to_index_registers_let2':
  assumes \<open>TTIR_APPLY_QREGISTER (S y) Q T\<close>
  shows \<open>TTIR_APPLY_QREGISTER (let x = y in S x) Q T\<close>
  by (simp add: assms)

section \<open>ML code\<close>

(* TODO remove *)
lemma distinct_cvarsL: "distinct_cvars (cregister_pair Q R) \<Longrightarrow> distinct_cvars Q"
  by (rule ccompatible_register1)
lemma distinct_cvarsR: "distinct_cvars (cregister_pair Q R) \<Longrightarrow> distinct_cvars R"
  by (rule ccompatible_register2)

ML_file "prog_variables.ML"

method_setup translate_to_index_registers = \<open>
  Scan.succeed (fn ctxt => SIMPLE_METHOD (CONVERSION (Prog_Variables.translate_to_index_registers_conv ctxt Prog_Variables.translate_to_index_registers_conv_default_options) 1))
\<close>

text \<open>Invocation: \<open>debug_translate_to_index_registers term for x y z and w z\<close>.
Meaning: x y z are assumed compatible, and so are w z.\<close>
ML \<open>
  Outer_Syntax.command \<^command_keyword>\<open>debug_translate_to_index_registers\<close> "try what translate_to_index_registers does to a subterm"
    ((Parse.term -- Scan.optional (Parse.$$$ "for" |-- Parse.!!! (Parse.and_list1 (Scan.repeat Parse.name))) []) >> 
  (fn (term_str,fixes) => Toplevel.keep (fn state => let
  val ctxt = Toplevel.context_of state
  val ctxt = Config.put Syntax.ambiguity_limit 0 ctxt
  val term_parsed = Syntax.parse_term ctxt term_str
  fun mk_tuple [] = error "unexpected"
    | mk_tuple [x] = Free(x,dummyT)
    | mk_tuple (x::xs) = \<^Const>\<open>qregister_pair dummyT dummyT dummyT\<close> $ mk_tuple [x] $ mk_tuple xs
  val assms_parsed = map (fn f => \<^Const>\<open>qregister dummyT dummyT\<close> $ mk_tuple f |> HOLogic.mk_Trueprop) fixes
  (* val _ = assms_parsed |> map (Syntax.string_of_term ctxt) |> map writeln *)
  val term :: assms = Syntax.check_terms ctxt (term_parsed :: assms_parsed)
  val ctxt = fold (fn assm => Context.proof_map (Prog_Variables.declare_register_simps_from_thm (Thm.assume (Thm.cterm_of ctxt assm)))) assms ctxt
  val ct = Thm.cterm_of ctxt term
  val rhs = Prog_Variables.translate_to_index_registers_conv ctxt Prog_Variables.translate_to_index_registers_conv_default_options ct |> Thm.rhs_of
  val result = Syntax.string_of_term ctxt (Thm.term_of rhs)
  val _ = writeln result
  in () end)));
\<close>

section \<open>Syntax\<close>


nonterminal variable_list_args
nonterminal variable_nth
nonterminal variable_nth'
syntax
  "_qvariable_nth" :: "'a \<Rightarrow> 'b"
  "_cvariable_nth" :: "'a \<Rightarrow> 'b"
  "_qvariable_nth'" :: "'a \<Rightarrow> 'b"
  "_cvariable_nth'" :: "'a \<Rightarrow> 'b"
  "_empty_qregister"      :: "'a"        ("(1'[|'|])")
  "_empty_qregister"      :: "'a"        ("(1'\<lbrakk>'\<rbrakk>)")
  "_empty_qregister"      :: "'a"        ("(1'[|'|]\<^sub>q)")
  "_empty_qregister"      :: "'a"        ("(1'\<lbrakk>'\<rbrakk>\<^sub>q)")
  "_empty_cregister"      :: "'a"        ("(1'[|'|]\<^sub>c)")
  "_empty_cregister"      :: "'a"        ("(1'\<lbrakk>'\<rbrakk>\<^sub>c)")
  "_qvariables"      :: "variable_list_args \<Rightarrow> 'a"        ("(1'[|_'|])")
  "_qvariables"      :: "variable_list_args \<Rightarrow> 'a"        ("(1'[|_'|]\<^sub>q)")
  "_cvariables"      :: "variable_list_args \<Rightarrow> 'a"        ("(1'[|_'|]\<^sub>c)")
  "_qvariables"      :: "variable_list_args \<Rightarrow> 'a"        ("(1'\<lbrakk>_'\<rbrakk>)")
  "_qvariables"      :: "variable_list_args \<Rightarrow> 'a"        ("(1'\<lbrakk>_'\<rbrakk>\<^sub>q)")
  "_cvariables"      :: "variable_list_args \<Rightarrow> 'a"        ("(1'\<lbrakk>_'\<rbrakk>\<^sub>c)")
  "_variable_list_arg_nth"  :: "'a \<Rightarrow> variable_list_args"                   ("#_")  (* Instead of 'a, would like to match only natural numbers *)
  "_variable_list_arg_nth'"  :: "'a \<Rightarrow> variable_list_args"                   ("#_.")
  "_variable_list_arg"  :: "'a \<Rightarrow> variable_list_args"                   ("_")
  "_variable_list_args_nth"  :: "'a \<Rightarrow> variable_list_args \<Rightarrow> variable_list_args"                   ("#_,/ _")
  "_variable_list_args_nth'"  :: "'a \<Rightarrow> variable_list_args \<Rightarrow> variable_list_args"                   ("#_.,/ _")
  "_variable_list_args" :: "'a \<Rightarrow> variable_list_args \<Rightarrow> variable_list_args"     ("_,/ _")

  "_qvariable_conversion"      :: "variable_list_args \<Rightarrow> variable_list_args \<Rightarrow> 'a"        ("(1'\<lbrakk>_ \<mapsto> _'\<rbrakk>)")
  "_qvariable_conversion"      :: "variable_list_args \<Rightarrow> variable_list_args \<Rightarrow> 'a"        ("(1'\<lbrakk>_ \<mapsto> _'\<rbrakk>\<^sub>q)")
  "_cvariable_conversion"      :: "variable_list_args \<Rightarrow> variable_list_args \<Rightarrow> 'a"        ("(1'\<lbrakk>_ \<mapsto> _'\<rbrakk>\<^sub>c)")
  "_qvariable_le"      :: "variable_list_args \<Rightarrow> variable_list_args \<Rightarrow> 'a"        ("(1'\<lbrakk>_ \<le> _'\<rbrakk>)")
  "_qvariable_le"      :: "variable_list_args \<Rightarrow> variable_list_args \<Rightarrow> 'a"        ("(1'\<lbrakk>_ \<le> _'\<rbrakk>\<^sub>q)")
  "_cvariable_le"      :: "variable_list_args \<Rightarrow> variable_list_args \<Rightarrow> 'a"        ("(1'\<lbrakk>_ \<le> _'\<rbrakk>\<^sub>c)")

translations
  "_empty_qregister" \<rightleftharpoons> "CONST empty_qregister :: (unit, _) qregister"
  "_empty_cregister" \<rightleftharpoons> "CONST empty_cregister :: (unit, _) cregister"
  "_qvariables (_variable_list_args x y)" \<rightleftharpoons> "CONST qregister_pair x (_qvariables y)"
  "_cvariables (_variable_list_args x y)" \<rightleftharpoons> "CONST cregister_pair x (_cvariables y)"
  "_qvariables (_variable_list_args_nth x y)" \<rightleftharpoons> "CONST qregister_pair (_qvariable_nth x) (_qvariables y)"
  "_cvariables (_variable_list_args_nth x y)" \<rightleftharpoons> "CONST cregister_pair (_cvariable_nth x) (_cvariables y)"
  "_qvariables (_variable_list_args_nth' x y)" \<rightleftharpoons> "CONST qregister_pair (_qvariable_nth' x) (_qvariables y)"
  "_cvariables (_variable_list_args_nth' x y)" \<rightleftharpoons> "CONST cregister_pair (_cvariable_nth' x) (_cvariables y)"
  "_qvariables (_variable_list_arg x)" \<rightharpoonup> "x"
  "_cvariables (_variable_list_arg x)" \<rightharpoonup> "x"
  "_qvariables (_variable_list_arg_nth x)" \<rightleftharpoons> "_qvariable_nth x"
  "_cvariables (_variable_list_arg_nth x)" \<rightleftharpoons> "_cvariable_nth x"
  "_qvariables (_variable_list_arg_nth' x)" \<rightleftharpoons> "_qvariable_nth' x"
  "_cvariables (_variable_list_arg_nth' x)" \<rightleftharpoons> "_cvariable_nth' x"

  "_qvariables (_variable_list_args x y)" \<leftharpoondown> "CONST qregister_pair x y"
  "_cvariables (_variable_list_args x y)" \<leftharpoondown> "CONST cregister_pair x y"
  "_qvariables (_variable_list_args x (_variable_list_args y z))" \<leftharpoondown> "_qvariables (_variable_list_args x (_qvariables (_variable_list_args y z)))"
  "_cvariables (_variable_list_args x (_variable_list_args y z))" \<leftharpoondown> "_cvariables (_variable_list_args x (_cvariables (_variable_list_args y z)))"

  "_qvariable_conversion x y" \<rightharpoonup> "CONST qregister_conversion (_qvariables x) (_qvariables y)"
  "_qvariable_conversion x y" \<leftharpoondown> "CONST qregister_conversion x y"
  "_qvariable_conversion x y" \<leftharpoondown> "_qvariable_conversion (_qvariables x) y"
  "_qvariable_conversion x y" \<leftharpoondown> "_qvariable_conversion x (_qvariables y)"

  "_cvariable_conversion x y" \<rightharpoonup> "CONST cregister_conversion (_cvariables x) (_cvariables y)"
  "_cvariable_conversion x y" \<leftharpoondown> "CONST cregister_conversion x y"
  "_cvariable_conversion x y" \<leftharpoondown> "_cvariable_conversion (_cvariables x) y"
  "_cvariable_conversion x y" \<leftharpoondown> "_cvariable_conversion x (_cvariables y)"

  "_qvariable_le x y" \<rightharpoonup> "CONST qregister_le (_qvariables x) (_qvariables y)"
  "_qvariable_le x y" \<leftharpoondown> "CONST qregister_le x y"
  "_qvariable_le x y" \<leftharpoondown> "_qvariable_le (_qvariables x) y"
  "_qvariable_le x y" \<leftharpoondown> "_qvariable_le x (_qvariables y)"

  "_cvariable_le x y" \<rightharpoonup> "CONST cregister_le (_cvariables x) (_cvariables y)"
  "_cvariable_le x y" \<leftharpoondown> "CONST cregister_le x y"
  "_cvariable_le x y" \<leftharpoondown> "_cvariable_le (_cvariables x) y"
  "_cvariable_le x y" \<leftharpoondown> "_cvariable_le x (_cvariables y)"

parse_translation
  \<open>let open Prog_Variables in
   [(\<^syntax_const>\<open>_qvariable_nth\<close>,  fn ctxt => fn [nt] => register_n Quantum   false (Misc.dest_number_syntax nt)),
    (\<^syntax_const>\<open>_qvariable_nth'\<close>, fn ctxt => fn [nt] => register_n Quantum   true  (Misc.dest_number_syntax nt)),
    (\<^syntax_const>\<open>_cvariable_nth\<close>,  fn ctxt => fn [nt] => register_n Classical false (Misc.dest_number_syntax nt)),
    (\<^syntax_const>\<open>_cvariable_nth'\<close>, fn ctxt => fn [nt] => register_n Classical true  (Misc.dest_number_syntax nt))] end\<close>

translations
  "_qvariable_nth (CONST Suc CONST zero)" \<leftharpoondown> "CONST qFst"
  "_qvariable_nth' (CONST Suc (CONST Suc CONST zero))" \<leftharpoondown> "CONST qSnd"
(*   "_qvariable_nth (CONST Suc n)" \<leftharpoondown> "CONST qregister_chain (_qvariables (_variable_list_arg_nth' (CONST Suc (CONST Suc CONST zero)))) (_qvariables (_variable_list_arg_nth n))"
  "_qvariable_nth' (CONST Suc n)" \<leftharpoondown> "CONST qregister_chain (_qvariables (_variable_list_arg_nth' (CONST Suc (CONST Suc CONST zero)))) (_qvariables (_variable_list_arg_nth' n))" *)
  "_qvariable_nth (CONST Suc n)" \<leftharpoondown> "CONST qregister_chain (_qvariables (_variable_list_arg_nth' 2)) (_qvariables (_variable_list_arg_nth n))"
  "_qvariable_nth' (CONST Suc n)" \<leftharpoondown> "CONST qregister_chain (_qvariables (_variable_list_arg_nth' 2)) (_qvariables (_variable_list_arg_nth' n))"

  "_cvariable_nth (CONST Suc CONST zero)" \<leftharpoondown> "CONST cFst"
  "_cvariable_nth' (CONST Suc (CONST Suc CONST zero))" \<leftharpoondown> "CONST cSnd"
(*   "_cvariable_nth (CONST Suc n)" \<leftharpoondown> "CONST cregister_chain (_cvariables (_variable_list_arg_nth' (CONST Suc (CONST Suc CONST zero)))) (_cvariables (_variable_list_arg_nth n))"
  "_cvariable_nth' (CONST Suc n)" \<leftharpoondown> "CONST cregister_chain (_cvariables (_variable_list_arg_nth' (CONST Suc (CONST Suc CONST zero)))) (_cvariables (_variable_list_arg_nth' n))" *)
  "_cvariable_nth (CONST Suc n)" \<leftharpoondown> "CONST cregister_chain (_cvariables (_variable_list_arg_nth' 2)) (_cvariables (_variable_list_arg_nth n))"
  "_cvariable_nth' (CONST Suc n)" \<leftharpoondown> "CONST cregister_chain (_cvariables (_variable_list_arg_nth' 2)) (_cvariables (_variable_list_arg_nth' n))"

(* Does not work: *)
print_translation
  \<open>let
    fun count (Const(\<^const_name>\<open>zero\<close>,_)) = 0
      | count (Const(\<^const_name>\<open>Suc\<close>,_) $ t) = count t + 1
  in
  [(\<^syntax_const>\<open>_variable_list_arg_nth'\<close>, fn ctxt => fn [t] => HOLogic.mk_number dummyT (count t))]
  end\<close>

translations
  "_variable_list_arg_nth' 1" \<leftharpoondown> "_variable_list_arg_nth' (CONST Suc CONST zero)"
  "_variable_list_arg_nth' 2" \<leftharpoondown> "_variable_list_arg_nth' (CONST Suc (CONST Suc CONST zero))"
  "_variable_list_arg_nth' 3" \<leftharpoondown> "_variable_list_arg_nth' (CONST Suc (CONST Suc (CONST Suc CONST zero)))"
  "_variable_list_arg_nth' 4" \<leftharpoondown> "_variable_list_arg_nth' (CONST Suc (CONST Suc (CONST Suc (CONST Suc CONST zero))))"
  "_variable_list_arg_nth' 5" \<leftharpoondown> "_variable_list_arg_nth' (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc CONST zero)))))"
  "_variable_list_arg_nth' 6" \<leftharpoondown> "_variable_list_arg_nth' (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc CONST zero))))))"
  "_variable_list_arg_nth' 7" \<leftharpoondown> "_variable_list_arg_nth' (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc CONST zero)))))))"
  "_variable_list_arg_nth' 8" \<leftharpoondown> "_variable_list_arg_nth' (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc CONST zero))))))))"
  "_variable_list_arg_nth' 9" \<leftharpoondown> "_variable_list_arg_nth' (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc CONST zero)))))))))"

  "_variable_list_arg_nth' 3" \<leftharpoondown> "_variable_list_arg_nth' (CONST Suc 2)"
  "_variable_list_arg_nth' 4" \<leftharpoondown> "_variable_list_arg_nth' (CONST Suc (CONST Suc 2))"
  "_variable_list_arg_nth' 5" \<leftharpoondown> "_variable_list_arg_nth' (CONST Suc (CONST Suc (CONST Suc 2)))"
  "_variable_list_arg_nth' 6" \<leftharpoondown> "_variable_list_arg_nth' (CONST Suc (CONST Suc (CONST Suc (CONST Suc 2))))"
  "_variable_list_arg_nth' 7" \<leftharpoondown> "_variable_list_arg_nth' (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc 2)))))"
  "_variable_list_arg_nth' 8" \<leftharpoondown> "_variable_list_arg_nth' (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc 2))))))"
  "_variable_list_arg_nth' 9" \<leftharpoondown> "_variable_list_arg_nth' (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc 2)))))))"

  "_variable_list_arg_nth 1" \<leftharpoondown> "_variable_list_arg_nth (CONST Suc CONST zero)"
  "_variable_list_arg_nth 2" \<leftharpoondown> "_variable_list_arg_nth (CONST Suc (CONST Suc CONST zero))"
  "_variable_list_arg_nth 3" \<leftharpoondown> "_variable_list_arg_nth (CONST Suc (CONST Suc (CONST Suc CONST zero)))"
  "_variable_list_arg_nth 4" \<leftharpoondown> "_variable_list_arg_nth (CONST Suc (CONST Suc (CONST Suc (CONST Suc CONST zero))))"
  "_variable_list_arg_nth 5" \<leftharpoondown> "_variable_list_arg_nth (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc CONST zero)))))"
  "_variable_list_arg_nth 6" \<leftharpoondown> "_variable_list_arg_nth (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc CONST zero))))))"
  "_variable_list_arg_nth 7" \<leftharpoondown> "_variable_list_arg_nth (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc CONST zero)))))))"
  "_variable_list_arg_nth 8" \<leftharpoondown> "_variable_list_arg_nth (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc CONST zero))))))))"
  "_variable_list_arg_nth 9" \<leftharpoondown> "_variable_list_arg_nth (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc CONST zero)))))))))"

  "_variable_list_arg_nth 2" \<leftharpoondown> "_variable_list_arg_nth (CONST Suc 1)"
  "_variable_list_arg_nth 3" \<leftharpoondown> "_variable_list_arg_nth (CONST Suc (CONST Suc 1))"
  "_variable_list_arg_nth 4" \<leftharpoondown> "_variable_list_arg_nth (CONST Suc (CONST Suc (CONST Suc 1)))"
  "_variable_list_arg_nth 5" \<leftharpoondown> "_variable_list_arg_nth (CONST Suc (CONST Suc (CONST Suc (CONST Suc 1))))"
  "_variable_list_arg_nth 6" \<leftharpoondown> "_variable_list_arg_nth (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc 1)))))"
  "_variable_list_arg_nth 7" \<leftharpoondown> "_variable_list_arg_nth (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc 1))))))"
  "_variable_list_arg_nth 8" \<leftharpoondown> "_variable_list_arg_nth (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc 1)))))))"
  "_variable_list_arg_nth 9" \<leftharpoondown> "_variable_list_arg_nth (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc (CONST Suc 1))))))))"

term \<open>\<lbrakk>#3\<rbrakk>\<^sub>q\<close>

section \<open>Simprocs\<close>

(* A simproc that utters warnings whenever the simplifier tries to prove a distinct_qvars statement with distinct, explicitly listed variables but can't *)
(* syntax "_declared_qvars" :: "variable_list_args \<Rightarrow> bool" ("declared'_qvars \<lbrakk>_\<rbrakk>")
syntax "_declared_qvars" :: "variable_list_args \<Rightarrow> bool" ("declared'_qvars [|_|]") *)
(* LEGACY *)
abbreviation (input) \<open>declared_qvars Q \<equiv> qregister Q\<close>

(* parse_translation \<open>[("_declared_qvars", Prog_Variables.declared_qvars_parse_tr)]\<close> *)

(* simproc_setup warn_declared_qvars ("variable_name q") = Prog_Variables.warn_declared_qvars_simproc *)

(* simproc_setup index_var ("index_var lr v") = Prog_Variables.index_var_simproc *)
(* simproc_setup index_flip_var ("index_flip_var v") = Prog_Variables.index_flip_var_simproc *)

(* Simproc that rewrites a `qregister_conversion F G` into an index-register.
   (Index-registers are registers build from chain, pair, Fst, Snd.) *)
simproc_setup qregister_conversion_to_register (\<open>qregister_conversion x y\<close>) =
  \<open>fn m => fn ctxt => fn ct => SOME (Prog_Variables.qregister_conversion_to_register_conv ctxt ct) handle e => NONE\<close>

(* A hint to the simplifier with the meaning:
    - A is a term of the form x>>Q
    - Q,R are registers
    - Q \<le> R
    - The whole term should be rewritten into x'>>R for some x'
  Rewriting the term is done by the simproc TODO declared below.
*)
definition "register_conversion_hint R A = A" (* LEGACY *)
lemma register_conversion_hint_cong[cong]: "A=A' \<Longrightarrow> register_conversion_hint R A = register_conversion_hint R A'" by simp

(* Simproc that rewrites terms of the form `register_conversion_hint G (apply_qregister F a)` into
  `apply_qregister target (apply_qregister (qregister_conversion \<dots>) A)` for suitable \<dots> *)
simproc_setup register_conversion_hint (\<open>register_conversion_hint G (apply_qregister F a)\<close> | \<open>register_conversion_hint G (apply_qregister_space F S)\<close>) =
  \<open>fn m => fn ctxt => fn ct => let
    (* val _ = \<^print> ct *)
    val target = ct |> Thm.dest_arg1
    val conv = (Prog_Variables.apply_qregister_conversion_conv ctxt target |> Conv.arg_conv)
        then_conv Conv.rewr_conv @{thm register_conversion_hint_def[THEN eq_reflection]}
    in SOME (conv ct) handle e => NONE end\<close>

(* TODO: check if we keep this mechanism. *)
definition \<open>JOIN_REGISTERS F G FG \<equiv> True\<close>

(* TODO: check if we keep this mechanism. *)
definition \<open>REGISTER_SOLVE x \<equiv> x\<close>
lemma REGISTER_SOLVER_cong[cong]: \<open>REGISTER_SOLVE x = REGISTER_SOLVE x\<close>
  by (rule refl)

named_theorems join_registers

(* TODO: remove or move *)
(* Indicates to the simplifier that the (schematic) variable x should be instantiated as y *)
definition \<open>INSTANTIATE_VARIABLE x y = True\<close>
lemma INSTANTIATE_VARIABLE_cong[cong]: \<open>INSTANTIATE_VARIABLE x y = INSTANTIATE_VARIABLE x y\<close>
  by simp
lemma INSTANTIATE_VARIABLE_instantiate: \<open>INSTANTIATE_VARIABLE x x\<close>
  by (simp add: INSTANTIATE_VARIABLE_def)
setup \<open>
map_theory_simpset (fn ctxt => ctxt
    addSolver 
      Simplifier.mk_solver "INSTANTIATE_VARIABLE" (fn ctxt => 
        resolve_tac ctxt @{thms INSTANTIATE_VARIABLE_instantiate}))\<close>

(* 
(* TODO outdated doc comment *)

Simproc that proves a goal of the form \<open>JOIN_REGISTERS F G ?H ?L\<close> where
  F G are qregisters and H,L will be instantiated.
  (Strictly speaking, they will not be instantiated because simprocs cannot do that.
   Instead, the JOIN_REGISTERS term will be rewritten into (?H=\<dots> \<and> ?L=\<dots>).
   Strictly speaking, H,L do not need to be schematic therefore.)

  Both H, L will instantiated to \<open>(\<lambda>F. register_conversion_hint FG F)\<close> where FG is an upper bound (not proven!)
  for F,G (w.r.t., qregister_le).

  (We have two variables H,L because they may need different types.)
  (* TODO: Do they? Do we have cases where the types are different? Let's see in the end and possibly simplify. *)
*)
(* simproc_setup JOIN_REGISTERS (\<open>JOIN_REGISTERS F G H L\<close>) = \<open>fn _ => fn ctxt => fn ct => let
  val (((F,G),H),L) = ct |> Thm.dest_comb |> apfst Thm.dest_comb |> apfst (apfst Thm.dest_comb) |> apfst (apfst (apfst Thm.dest_arg))
  val F' = Thm.term_of F val G' = Thm.term_of G
  val index = Prog_Variables.is_index_qregister F' andalso Prog_Variables.is_index_qregister G'
  val FG_option = if index then NONE else Prog_Variables.join_registers ctxt F' G' |> Option.map (Thm.cterm_of ctxt)
  in case FG_option of
    NONE => NONE
    | SOME FG =>
        SOME \<^instantiate>\<open>FG and F and G and H and L and 'f=\<open>Thm.ctyp_of_cterm F\<close> and 'g=\<open>Thm.ctyp_of_cterm G\<close> and
              'h=\<open>Thm.ctyp_of_cterm H |> Thm.dest_funT |> fst\<close> and 'l=\<open>Thm.ctyp_of_cterm L |> Thm.dest_funT |> fst\<close> and
              'fg=\<open>Thm.ctyp_of_cterm FG\<close> in
              lemma \<open>JOIN_REGISTERS (F::'f) (G::'g) (H::'h\<Rightarrow>'h) (L::'l\<Rightarrow>'l) \<equiv>
              H = (\<lambda>F. register_conversion_hint (FG::'fg) F) \<and> L = (\<lambda>F. register_conversion_hint FG F)\<close>
              by (auto simp add: JOIN_REGISTERS_def register_conversion_hint_def id_def)\<close> (* |> \<^print> *)
end\<close> *)
simproc_setup JOIN_REGISTERS (\<open>JOIN_REGISTERS F G FG\<close>) = \<open>fn _ => fn ctxt => fn ct => let
  val ((F,G),FG) = ct |> Thm.dest_comb |> apfst Thm.dest_comb |> apfst (apfst Thm.dest_arg)
  val F' = Thm.term_of F val G' = Thm.term_of G
  val FG_option = Prog_Variables.join_registers ctxt F' G' |> Option.map (Thm.cterm_of ctxt)
  (* val _ = \<^print> ("JOIN_REGISTERS", Option.map Thm.typ_of_cterm FG_option, Thm.typ_of_cterm FG) *)
  in case FG_option of
    NONE => NONE
    | SOME FG' =>
        SOME \<^instantiate>\<open>FG and FG' and F and G and 'f=\<open>Thm.ctyp_of_cterm F\<close> and 'g=\<open>Thm.ctyp_of_cterm G\<close> and
              'fg=\<open>Thm.ctyp_of_cterm FG\<close> and 'fg'=\<open>Thm.ctyp_of_cterm FG'\<close> in
              lemma \<open>JOIN_REGISTERS (F::'f) (G::'g) (FG::'fg) \<equiv> INSTANTIATE_VARIABLE FG (FG'::'fg')\<close>
              by (auto simp add: JOIN_REGISTERS_def INSTANTIATE_VARIABLE_def)\<close> (* |> \<^print> *)
end\<close>

(* TODO move to .ML *)
ML \<open>
(* ct is of the form REGISTER_SOLVE (X :: bool) *)
fun register_solve_simproc_of_tac ctxt tac ct = let
    val goal = ct |> Thm.dest_arg |> Thm.apply \<^cterm>\<open>Trueprop\<close>
(* val _ = goal |> Thm.term_of |> \<^print> *)
    val thm = SOME (Goal.prove_internal ctxt [] goal (fn _ => tac))
           (* handle _ => NONE *)
(* val _ = \<^print> thm *)
    val lemma = @{lemma \<open>X \<Longrightarrow> REGISTER_SOLVE X \<equiv> True\<close> by (simp add: REGISTER_SOLVE_def)}
    val eq = Option.map (fn thm => lemma OF [thm]) thm
(* val _ = \<^print> eq *)
  in eq end

(* TODO: support cregisters as well *)
fun register_solve_le_simproc (_:morphism) ctxt ct =
  case Thm.term_of ct of
    \<^Const_>\<open>REGISTER_SOLVE _\<close> $ (\<^Const_>\<open>qregister_le _ _ _\<close> $ _ $ _) =>
      register_solve_simproc_of_tac ctxt (Prog_Variables.qregister_le_tac ctxt 1) ct
\<close>

(* TODO: support cregisters as well *)
simproc_setup register_solve_le (\<open>REGISTER_SOLVE (qregister_le Q R)\<close>) = register_solve_le_simproc

(* lemma register_conversion_hint_solve[simp]: 
  \<open>register_conversion_hint R (apply_qregister Q x) = apply_qregister R (apply_qregister (qregister_conversion Q R) x)\<close>
  if \<open>REGISTER_SOLVE (qregister_le Q R)\<close>
   *)

definition \<open>NOT_INDEX_REGISTER x = True\<close>
lemma NOT_INDEX_REGISTER_cong[cong]: \<open>NOT_INDEX_REGISTER x = NOT_INDEX_REGISTER x\<close>
  by simp

simproc_setup NOT_INDEX_REGISTER (\<open>NOT_INDEX_REGISTER R\<close>) = \<open>fn _ => fn ctxt => fn ct => let
  val R = Thm.dest_arg ct
  in
      if Prog_Variables.is_index_qregister (Thm.term_of R) |> \<^print>
      then NONE
      else SOME \<^instantiate>\<open>R and 'r=\<open>Thm.ctyp_of_cterm R\<close> in lemma \<open>NOT_INDEX_REGISTER (R::'r) \<equiv> True\<close> by (simp add: NOT_INDEX_REGISTER_def)\<close> |> \<^print>
  end
\<close>

section \<open>Cleanup\<close>

end
