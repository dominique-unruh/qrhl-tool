theory Prog_Variables
  imports Extended_Sorry Multi_Transfer (* Registers.Classical_Extra Registers.Quantum_Extra2 *)
    (* Complex_Bounded_Operators.Complex_L2 *)
    HOL.Map
    (* "HOL-Library.Adhoc_Overloading" *)
    (* Tensor_Product.Tensor_Product *)
    BOLegacy
    Misc_Missing
  (* keywords "variables" :: thy_decl_block *)
    Missing_Bounded_Operators
begin

unbundle cblinfun_notation

(* hide_const (open) Classical_Extra.X Classical_Extra.Y Classical_Extra.x Classical_Extra.y *)

type_synonym 'a cupdate = \<open>'a \<Rightarrow> 'a option\<close>
type_synonym 'a qupdate = \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close>

axiomatization cregister_raw :: \<open>('a cupdate \<Rightarrow> 'b cupdate) \<Rightarrow> bool\<close>
  where cregister_raw_empty: \<open>cregister_raw F \<Longrightarrow> F Map.empty = Map.empty\<close>
    and cregister_raw_1: \<open>cregister_raw F \<Longrightarrow> F Some = Some\<close>
axiomatization qregister_raw :: \<open>('a qupdate \<Rightarrow> 'b qupdate) \<Rightarrow> bool\<close>
  where qregister_raw_1: \<open>qregister_raw F \<Longrightarrow> F id_cblinfun = id_cblinfun\<close>
    and qregister_raw_bounded_clinear: \<open>qregister_raw F \<Longrightarrow> bounded_clinear F\<close>

lemma qregister_raw_0: \<open>qregister_raw F \<Longrightarrow> F 0 = 0\<close>
  by (intro complex_vector.linear_0 bounded_clinear.clinear qregister_raw_bounded_clinear)

definition non_cregister_raw :: \<open>'a cupdate \<Rightarrow> 'b cupdate\<close> where \<open>non_cregister_raw a = Map.empty\<close>
definition non_qregister_raw :: \<open>'a qupdate \<Rightarrow> 'b qupdate\<close> where \<open>non_qregister_raw a = 0\<close>

lemma cregister_raw_inj: \<open>cregister_raw F \<Longrightarrow> inj F\<close> sorry
lemma qregister_raw_inj: \<open>qregister_raw F \<Longrightarrow> inj F\<close> sorry

axiomatization where non_cregister_raw: \<open>\<not> cregister_raw non_cregister_raw\<close>
axiomatization where non_qregister_raw: \<open>\<not> qregister_raw non_qregister_raw\<close>

typedef ('a,'b) cregister = \<open>{f :: 'a cupdate \<Rightarrow> 'b cupdate. cregister_raw f} \<union> {non_cregister_raw}\<close> 
  morphisms apply_cregister Abs_cregister by auto
typedef ('a,'b) qregister = \<open>{f :: 'a qupdate \<Rightarrow> 'b qupdate. qregister_raw f} \<union> {non_qregister_raw}\<close>
  morphisms apply_qregister Abs_qregister by auto
setup_lifting type_definition_cregister
setup_lifting type_definition_qregister

axiomatization apply_cregister_total :: \<open>('a,'b) cregister \<Rightarrow> ('a\<Rightarrow>'a) \<Rightarrow> ('b\<Rightarrow>'b)\<close>

lift_definition non_cregister :: \<open>('a,'b) cregister\<close> is non_cregister_raw by auto
lift_definition non_qregister :: \<open>('a,'b) qregister\<close> is non_qregister_raw by auto

lift_definition cregister :: \<open>('a,'b) cregister \<Rightarrow> bool\<close> is cregister_raw.
lift_definition qregister :: \<open>('a,'b) qregister \<Rightarrow> bool\<close> is qregister_raw.

lemma non_cregister: \<open>\<not> cregister F \<longleftrightarrow> F = non_cregister\<close>
  apply transfer using non_cregister_raw by blast
lemma non_qregister: \<open>\<not> qregister F \<longleftrightarrow> F = non_qregister\<close>
  apply transfer using non_qregister_raw by blast

lemma apply_qregister_bounded_clinear: \<open>bounded_clinear (apply_qregister F)\<close>
  apply transfer by (auto simp add: qregister_raw_bounded_clinear non_qregister_raw_def[abs_def])

lemma apply_cregister_of_0[simp]: \<open>apply_cregister F Map.empty = Map.empty\<close>
  apply transfer apply (auto simp: non_cregister_raw_def)
  by (simp add: cregister_raw_empty)
lemma apply_qregister_of_0[simp]: \<open>apply_qregister F 0 = 0\<close>
  by (metis non_qregister non_qregister.rep_eq non_qregister_raw_def qregister.rep_eq qregister_raw_0)

lemma apply_cregister_of_id[simp]: \<open>cregister F \<Longrightarrow> apply_cregister F Some = Some\<close>
  using cregister.rep_eq cregister_raw_1 by blast
lemma apply_qregister_of_id[simp]: \<open>qregister F \<Longrightarrow> apply_qregister F id_cblinfun = id_cblinfun\<close>
  by (simp add: qregister.rep_eq qregister_raw_1)

(* Equivalence class of cregisters *)
axiomatization valid_cregister_range :: \<open>'a cupdate set \<Rightarrow> bool\<close>
  where valid_cregister_range: \<open>cregister F \<Longrightarrow> valid_cregister_range (range (apply_cregister F))\<close> for F :: \<open>('b,'a) cregister\<close>
axiomatization valid_qregister_range :: \<open>'a qupdate set \<Rightarrow> bool\<close>
  where valid_qregister_range: \<open>qregister F \<Longrightarrow> valid_qregister_range (range (apply_qregister F))\<close> for F :: \<open>('b,'a) qregister\<close>
definition \<open>empty_cregister_range = {Map.empty, Some}\<close>
axiomatization where valid_empty_cregister_range: \<open>valid_cregister_range empty_cregister_range\<close>
definition \<open>empty_qregister_range = {c *\<^sub>C (id_cblinfun) | c. True}\<close>
axiomatization where valid_empty_qregister_range: \<open>valid_qregister_range empty_qregister_range\<close>
typedef 'a CREGISTER = \<open>Collect valid_cregister_range :: 'a cupdate set set\<close>
  using valid_empty_cregister_range by blast
typedef 'a QREGISTER = \<open>Collect valid_qregister_range :: 'a qupdate set set\<close>
  using valid_empty_qregister_range by blast
setup_lifting type_definition_CREGISTER
setup_lifting type_definition_QREGISTER

lift_definition CREGISTER_of :: \<open>('a,'b) cregister \<Rightarrow> 'b CREGISTER\<close> is
  \<open>\<lambda>F::('a,'b) cregister. if cregister F then range (apply_cregister F) :: 'b cupdate set else empty_cregister_range\<close>
  by (simp add: valid_empty_cregister_range valid_cregister_range)
lift_definition QREGISTER_of :: \<open>('a,'b) qregister \<Rightarrow> 'b QREGISTER\<close> is
  \<open>\<lambda>F::('a,'b) qregister. if qregister F then range (apply_qregister F) :: 'b qupdate set else empty_qregister_range\<close>
  by (simp add: valid_empty_qregister_range valid_qregister_range)

instantiation CREGISTER :: (type) order begin
lift_definition less_eq_CREGISTER :: \<open>'a CREGISTER \<Rightarrow> 'a CREGISTER \<Rightarrow> bool\<close> is \<open>(\<subseteq>)\<close>.
lift_definition less_CREGISTER :: \<open>'a CREGISTER \<Rightarrow> 'a CREGISTER \<Rightarrow> bool\<close> is \<open>(\<subset>)\<close>.
instance
  apply (intro_classes; transfer)
  by auto
end
instantiation QREGISTER :: (type) order begin
lift_definition less_eq_QREGISTER :: \<open>'a QREGISTER \<Rightarrow> 'a QREGISTER \<Rightarrow> bool\<close> is \<open>(\<subseteq>)\<close>.
print_theorems
lift_definition less_QREGISTER :: \<open>'a QREGISTER \<Rightarrow> 'a QREGISTER \<Rightarrow> bool\<close> is \<open>(\<subset>)\<close>.
instance
  apply (intro_classes; transfer)
  by auto
end

lift_definition CREGISTER_unit :: \<open>'a CREGISTER\<close> is empty_cregister_range
  by (simp add: valid_empty_cregister_range)
lift_definition QREGISTER_unit :: \<open>'a QREGISTER\<close> is empty_qregister_range
  by (simp add: valid_empty_qregister_range)

axiomatization CREGISTER_pair :: \<open>'a CREGISTER \<Rightarrow> 'a CREGISTER \<Rightarrow> 'a CREGISTER\<close>
axiomatization QREGISTER_pair :: \<open>'a QREGISTER \<Rightarrow> 'a QREGISTER \<Rightarrow> 'a QREGISTER\<close>

definition ccommuting_raw :: \<open>('a cupdate \<Rightarrow> 'c cupdate) \<Rightarrow> ('b cupdate \<Rightarrow> 'c cupdate) \<Rightarrow> bool\<close> where
  \<open>ccommuting_raw F G \<longleftrightarrow> (\<forall>a b. F a \<circ>\<^sub>m G b = G b \<circ>\<^sub>m F a)\<close>
definition qcommuting_raw :: \<open>('a qupdate \<Rightarrow> 'c qupdate) \<Rightarrow> ('b qupdate \<Rightarrow> 'c qupdate) \<Rightarrow> bool\<close> where
  \<open>qcommuting_raw F G \<longleftrightarrow> (\<forall>a b. F a o\<^sub>C\<^sub>L G b = G b o\<^sub>C\<^sub>L F a)\<close>

definition ccompatible_raw :: \<open>('a cupdate \<Rightarrow> 'c cupdate) \<Rightarrow> ('b cupdate \<Rightarrow> 'c cupdate) \<Rightarrow> bool\<close> where
  \<open>ccompatible_raw F G \<longleftrightarrow> cregister_raw F \<and> cregister_raw G \<and> (\<forall>a b. F a \<circ>\<^sub>m G b = G b \<circ>\<^sub>m F a)\<close>
definition qcompatible_raw :: \<open>('a qupdate \<Rightarrow> 'c qupdate) \<Rightarrow> ('b qupdate \<Rightarrow> 'c qupdate) \<Rightarrow> bool\<close> where
  \<open>qcompatible_raw F G \<longleftrightarrow> qregister_raw F \<and> qregister_raw G \<and> (\<forall>a b. F a o\<^sub>C\<^sub>L G b = G b o\<^sub>C\<^sub>L F a)\<close>

lift_definition ccompatible :: \<open>('a,'c) cregister \<Rightarrow> ('b,'c) cregister \<Rightarrow> bool\<close> is ccompatible_raw.
lift_definition qcompatible :: \<open>('a,'c) qregister \<Rightarrow> ('b,'c) qregister \<Rightarrow> bool\<close> is qcompatible_raw.

axiomatization cregister_pair :: \<open>('a,'c) cregister \<Rightarrow> ('b,'c) cregister \<Rightarrow> ('a\<times>'b, 'c) cregister\<close>
  where cregister_pair_iff_compatible: \<open>cregister (cregister_pair F G) \<longleftrightarrow> ccompatible F G\<close>
axiomatization qregister_pair :: \<open>('a,'c) qregister \<Rightarrow> ('b,'c) qregister \<Rightarrow> ('a\<times>'b, 'c) qregister\<close>
  where qregister_pair_iff_compatible: \<open>qregister (qregister_pair F G) \<longleftrightarrow> qcompatible F G\<close>

definition tensor_map :: \<open>'a cupdate \<Rightarrow> 'b cupdate \<Rightarrow> ('a\<times>'b) cupdate\<close> where
  \<open>tensor_map a b m = (case a (fst m) of None \<Rightarrow> None | Some x \<Rightarrow> (case b (snd m) of None \<Rightarrow> None | Some y \<Rightarrow> Some (x,y)))\<close>

axiomatization where apply_cregister_pair: \<open>ccompatible F G \<Longrightarrow> 
  apply_cregister (cregister_pair F G) (tensor_map a b) = apply_cregister F a \<circ>\<^sub>m apply_cregister G b\<close>
axiomatization where apply_qregister_pair: \<open>qcompatible F G \<Longrightarrow> 
  apply_qregister (qregister_pair F G) (tensorOp a b) = apply_qregister F a o\<^sub>C\<^sub>L  apply_qregister G b\<close>

lift_definition CCcompatible :: \<open>'a CREGISTER \<Rightarrow> 'a CREGISTER \<Rightarrow> bool\<close> is
  \<open>\<lambda>F G. \<forall>a\<in>F. \<forall>b\<in>G. a \<circ>\<^sub>m b = b \<circ>\<^sub>m a\<close>.
lift_definition QQcompatible :: \<open>'a QREGISTER \<Rightarrow> 'a QREGISTER \<Rightarrow> bool\<close> is
  \<open>\<lambda>F G. \<forall>a\<in>F. \<forall>b\<in>G. a o\<^sub>C\<^sub>L b = b o\<^sub>C\<^sub>L a\<close>.

lift_definition Cccompatible :: \<open>'a CREGISTER \<Rightarrow> ('b,'a) cregister \<Rightarrow> bool\<close> is
  \<open>\<lambda>F G. cregister_raw G \<and> (\<forall>a\<in>F. \<forall>b. a \<circ>\<^sub>m G b = G b \<circ>\<^sub>m a)\<close>.
lift_definition Qqcompatible :: \<open>'a QREGISTER \<Rightarrow> ('b,'a) qregister \<Rightarrow> bool\<close> is
  \<open>\<lambda>F G. qregister_raw G \<and> (\<forall>a\<in>F. \<forall>b. a o\<^sub>C\<^sub>L G b = G b o\<^sub>C\<^sub>L a)\<close>.

axiomatization empty_cregister :: \<open>('a::{CARD_1,enum}, 'b) cregister\<close>
  where empty_cregister_is_register[simp]: \<open>cregister empty_cregister\<close>
axiomatization empty_qregister :: \<open>('a::{CARD_1,enum}, 'b) qregister\<close>
  where empty_qregister_is_register[simp]: \<open>qregister empty_qregister\<close>


lemma empty_cregisters_same[simp]: 
  fixes F :: \<open>('a::{CARD_1,enum},'b) cregister\<close>
  assumes [simp]: \<open>cregister F\<close>
  shows \<open>F = empty_cregister\<close>
proof (rule apply_cregister_inject[THEN iffD1], rule ext)
  fix a :: \<open>'a cupdate\<close>
  consider \<open>a = Map.empty\<close> | \<open>a = Some\<close>
  proof (atomize_elim, cases \<open>a undefined\<close>)
    case None
    then have \<open>a = Map.empty\<close>
      apply (rule_tac ext, subst everything_the_same[of _ undefined])
      by simp
    then show \<open>a = Map.empty \<or> a = Some\<close>
      by simp
  next
    case (Some x)
    then have \<open>a = Some\<close>
      apply (rule_tac ext, subst everything_the_same[of _ undefined])
      by simp
    then show \<open>a = Map.empty \<or> a = Some\<close>
      by simp
  qed
  then show \<open>apply_cregister F a = apply_cregister empty_cregister a\<close>
    apply cases apply auto
    by -
qed
lemma empty_qregisters_same[simp]:
  fixes F :: \<open>('a::{CARD_1,enum},'b) qregister\<close>
  assumes [simp]: \<open>qregister F\<close>
  shows \<open>F = empty_qregister\<close>
proof (rule apply_qregister_inject[THEN iffD1], rule ext)
  fix a :: \<open>'a qupdate\<close>
  define empty :: \<open>('a,'b) qregister\<close> where \<open>empty = empty_qregister\<close>
  have [simp]: \<open>qregister empty\<close>
    using empty_qregister_is_register empty_def by blast

  have [simp]: \<open>clinear (apply_qregister F)\<close> \<open>clinear (apply_qregister empty)\<close>
    by (auto simp add: apply_qregister_bounded_clinear bounded_clinear.clinear)
  have \<open>apply_qregister F a = apply_qregister F (one_dim_iso a *\<^sub>C id_cblinfun)\<close>
    by simp
  also have \<open>\<dots> = one_dim_iso a *\<^sub>C apply_qregister F (id_cblinfun)\<close>
    by (metis \<open>clinear (apply_qregister F)\<close> complex_vector.linear_scale)
  also have \<open>\<dots> = one_dim_iso a *\<^sub>C id_cblinfun\<close>
    by (metis apply_qregister_of_id assms(1))
  also have \<open>\<dots> = one_dim_iso a *\<^sub>C apply_qregister empty (id_cblinfun)\<close>
    by (metis \<open>qregister empty\<close> apply_qregister_of_id)
  also have \<open>\<dots> = apply_qregister empty (one_dim_iso a *\<^sub>C id_cblinfun)\<close>
    by (metis \<open>clinear (apply_qregister empty)\<close> complex_vector.linear_scale)
  also have \<open>\<dots> = apply_qregister empty a\<close>
    by simp
  finally show \<open>apply_qregister F a = apply_qregister empty a\<close>
    by -
qed

axiomatization where CCcompatible_sym: \<open>CCcompatible F G \<Longrightarrow> CCcompatible G F\<close> for F G :: \<open>'a CREGISTER\<close>
axiomatization where QQcompatible_sym: \<open>QQcompatible F G \<Longrightarrow> QQcompatible G F\<close> for F G :: \<open>'a QREGISTER\<close>

lemma ccompatible_CCcompatible: \<open>ccompatible F G \<longleftrightarrow> cregister F \<and> cregister G \<and> CCcompatible (CREGISTER_of F) (CREGISTER_of G)\<close>
  apply (transfer fixing: F G) apply auto
  by (transfer; simp add: ccompatible_raw_def)+
lemma qcompatible_QQcompatible: \<open>qcompatible F G \<longleftrightarrow> qregister F \<and> qregister G \<and> QQcompatible (QREGISTER_of F) (QREGISTER_of G)\<close>
  apply (transfer fixing: F G) apply auto
  by (transfer; simp add: qcompatible_raw_def)+

lemma CCcompatible_CREGISTER_ofI[simp]: \<open>ccompatible F G \<Longrightarrow> CCcompatible (CREGISTER_of F) (CREGISTER_of G)\<close>
  using ccompatible_CCcompatible by auto
lemma QQcompatible_QREGISTER_ofI[simp]: \<open>qcompatible F G \<Longrightarrow> QQcompatible (QREGISTER_of F) (QREGISTER_of G)\<close>
  using qcompatible_QQcompatible by auto

lemma ccompatible_sym: \<open>ccompatible F G \<Longrightarrow> ccompatible G F\<close> for F :: \<open>('a,'c) cregister\<close> and G :: \<open>('b,'c) cregister\<close>
  by (auto intro: CCcompatible_sym simp: ccompatible_CCcompatible)
lemma qcompatible_sym: \<open>qcompatible F G \<Longrightarrow> qcompatible G F\<close> for F :: \<open>('a,'c) qregister\<close> and G :: \<open>('b,'c) qregister\<close>
  by (auto intro: QQcompatible_sym simp: qcompatible_QQcompatible)

axiomatization where ccompatible3: \<open>ccompatible (cregister_pair F G) H \<longleftrightarrow> ccompatible F G \<and> ccompatible F H \<and> ccompatible G H\<close>
axiomatization where qcompatible3: \<open>qcompatible (qregister_pair F G) H \<longleftrightarrow> qcompatible F G \<and> qcompatible F H \<and> qcompatible G H\<close>

lemma ccompatible3': \<open>ccompatible H (cregister_pair F G) \<longleftrightarrow> ccompatible F G \<and> ccompatible H F \<and> ccompatible H G\<close>
  by (metis ccompatible3 ccompatible_sym)
lemma qcompatible3': \<open>qcompatible H (qregister_pair F G) \<longleftrightarrow> qcompatible F G \<and> qcompatible H F \<and> qcompatible H G\<close>
  by (metis qcompatible3 qcompatible_sym)

lemma ccompatible_empty[simp]: \<open>ccompatible Q empty_cregister \<longleftrightarrow> cregister Q\<close>
  sorry
lemma qcompatible_empty[simp]: \<open>qcompatible Q empty_qregister \<longleftrightarrow> qregister Q\<close>
  sorry
lemma ccompatible_empty'[simp]: \<open>ccompatible empty_cregister Q \<longleftrightarrow> cregister Q\<close>
  by (metis ccompatible_empty ccompatible_sym)
lemma qcompatible_empty'[simp]: \<open>qcompatible empty_qregister Q \<longleftrightarrow> qregister Q\<close>
  by (meson qcompatible_empty qcompatible_sym)

lemma ccompatible_register1: \<open>ccompatible F G \<Longrightarrow> cregister F\<close>
  apply transfer by (simp add: ccompatible_raw_def)
lemma ccompatible_register2: \<open>ccompatible F G \<Longrightarrow> cregister G\<close>
  apply transfer by (simp add: ccompatible_raw_def)
lemma qcompatible_register1: \<open>qcompatible F G \<Longrightarrow> qregister F\<close>
  apply transfer by (simp add: qcompatible_raw_def)
lemma qcompatible_register2: \<open>qcompatible F G \<Longrightarrow> qregister G\<close>
  apply transfer by (simp add: qcompatible_raw_def)

lemma ccompatible_non_cregister1[simp]: \<open>\<not> ccompatible non_cregister F\<close>
  apply transfer by (simp add: non_cregister_raw ccompatible_raw_def)
lemma ccompatible_non_cregister2[simp]: \<open>\<not> ccompatible F non_cregister\<close>
  apply transfer by (simp add: non_cregister_raw ccompatible_raw_def)
lemma qcompatible_non_qregister1[simp]: \<open>\<not> qcompatible non_qregister F\<close>
  apply transfer by (simp add: non_qregister_raw qcompatible_raw_def)
lemma qcompatible_non_qregister2[simp]: \<open>\<not> qcompatible F non_qregister\<close>
  apply transfer by (simp add: non_qregister_raw qcompatible_raw_def)

axiomatization cFst :: \<open>('a, 'a\<times>'b) cregister\<close> where
  cFst_register[simp]: \<open>cregister cFst\<close>
axiomatization qFst :: \<open>('a, 'a\<times>'b) qregister\<close> where
  qFst_register[simp]: \<open>qregister qFst\<close>
axiomatization cSnd :: \<open>('b, 'a\<times>'b) cregister\<close> where
  cSnd_register[simp]: \<open>cregister cSnd\<close>
axiomatization qSnd :: \<open>('b, 'a\<times>'b) qregister\<close> where
  qSnd_register[simp]: \<open>qregister qSnd\<close>

axiomatization where ccompatible_Fst_Snd[simp]: \<open>ccompatible cFst cSnd\<close>
axiomatization where qcompatible_Fst_Snd[simp]: \<open>qcompatible qFst qSnd\<close>

lift_definition cregister_chain :: \<open>('b,'c) cregister \<Rightarrow> ('a,'b) cregister \<Rightarrow> ('a,'c) cregister\<close>
  is \<open>\<lambda>F G. if cregister_raw F \<and> cregister_raw G then F o G else non_cregister_raw\<close>
  sorry
lift_definition qregister_chain :: \<open>('b,'c) qregister \<Rightarrow> ('a,'b) qregister \<Rightarrow> ('a,'c) qregister\<close>
  is \<open>\<lambda>F G. if qregister_raw F \<and> qregister_raw G then F o G else non_qregister_raw\<close>
  sorry

axiomatization where cregister_raw_chain: \<open>cregister_raw F \<Longrightarrow> cregister_raw G \<Longrightarrow> cregister_raw (F o G)\<close>
axiomatization where qregister_raw_chain: \<open>qregister_raw F \<Longrightarrow> qregister_raw G \<Longrightarrow> qregister_raw (F o G)\<close>

lemma cregister_chain_apply[simp]: \<open>apply_cregister (cregister_chain F G) = apply_cregister F o apply_cregister G\<close>
  apply (rule ext) apply transfer
  by (auto simp: non_cregister_raw_def cregister_raw_empty)
lemma qregister_chain_apply[simp]: \<open>apply_qregister (qregister_chain F G) = apply_qregister F o apply_qregister G\<close>
  apply (rule ext) apply transfer
  by (auto simp: non_qregister_raw_def qregister_raw_0)

lemma cregister_chain_non_register1[simp]: \<open>cregister_chain non_cregister F = non_cregister\<close>
  apply transfer by (auto simp add: non_cregister_raw)
lemma cregister_chain_non_register2[simp]: \<open>cregister_chain F non_cregister = non_cregister\<close>
  apply transfer by (auto simp add: non_cregister_raw)
lemma qregister_chain_non_register1[simp]: \<open>qregister_chain non_qregister F = non_qregister\<close>
  apply transfer by (auto simp add: non_qregister_raw)
lemma qregister_chain_non_register2[simp]: \<open>qregister_chain F non_qregister = non_qregister\<close>
  apply transfer by (auto simp add: non_qregister_raw)

lemma cregister_chain_assoc: \<open>cregister_chain (cregister_chain F G) H = cregister_chain F (cregister_chain G H)\<close>
  apply (cases \<open>cregister F\<close>; cases \<open>cregister G\<close>; cases \<open>cregister H\<close>)
  apply (simp_all add: non_cregister)
  apply transfer 
  by (auto simp add: cregister_raw_chain)
lemma qregister_chain_assoc: \<open>qregister_chain (qregister_chain F G) H = qregister_chain F (qregister_chain G H)\<close>
  apply (cases \<open>qregister F\<close>; cases \<open>qregister G\<close>; cases \<open>qregister H\<close>)
  apply (simp_all add: non_qregister)
  apply transfer 
  by (auto simp add: qregister_raw_chain)

lemma cregister_chain_is_cregister[simp]: \<open>cregister (cregister_chain F G) \<longleftrightarrow> cregister F \<and> cregister G\<close>
  apply transfer
  by (auto simp: non_cregister_raw cregister_raw_chain)
lemma qregister_chain_is_qregister[simp]: \<open>qregister (qregister_chain F G) \<longleftrightarrow> qregister F \<and> qregister G\<close>
  apply transfer
  by (auto simp: non_qregister_raw qregister_raw_chain)

axiomatization where cregister_chain_pair_Fst[simp]: \<open>ccompatible F G \<Longrightarrow> cregister_chain (cregister_pair F G) cFst = F\<close>
axiomatization where qregister_chain_pair_Fst[simp]: \<open>qcompatible F G \<Longrightarrow> qregister_chain (qregister_pair F G) qFst = F\<close>

axiomatization where cregister_chain_pair_Snd[simp]: \<open>ccompatible F G \<Longrightarrow> cregister_chain (cregister_pair F G) cSnd = G\<close>
axiomatization where qregister_chain_pair_Snd[simp]: \<open>qcompatible F G \<Longrightarrow> qregister_chain (qregister_pair F G) qSnd = G\<close>

lemma qregister_chain_empty_right[simp]: \<open>qregister F \<Longrightarrow> qregister_chain F empty_qregister = empty_qregister\<close>
  apply (rule empty_qregisters_same) by auto
lemma qregister_chain_empty_left[simp]: \<open>qregister F \<Longrightarrow> qregister_chain empty_qregister F = empty_qregister\<close>
  apply (rule empty_qregisters_same) by auto

lemma ccompatible_comp_left[simp]: "ccompatible F G \<Longrightarrow> cregister H \<Longrightarrow> ccompatible (cregister_chain F H) G" sorry
lemma qcompatible_comp_left[simp]: "qcompatible F G \<Longrightarrow> qregister H \<Longrightarrow> qcompatible (qregister_chain F H) G" sorry

lemma ccompatible_comp_right[simp]: "ccompatible F G \<Longrightarrow> cregister H \<Longrightarrow> ccompatible F (cregister_chain G H)"
  by (meson ccompatible_comp_left ccompatible_sym)
lemma qcompatible_comp_right[simp]: "qcompatible F G \<Longrightarrow> qregister H \<Longrightarrow> qcompatible F (qregister_chain G H)"
  by (meson qcompatible_comp_left qcompatible_sym)

lemma Cccompatible_comp_right[simp]: "Cccompatible F G \<Longrightarrow> cregister H \<Longrightarrow> Cccompatible F (cregister_chain G H)" sorry
lemma Qqcompatible_comp_right[simp]: "Qqcompatible F G \<Longrightarrow> qregister H \<Longrightarrow> Qqcompatible F (qregister_chain G H)" sorry

lemmas ccompatible_Snd_Fst[simp] = ccompatible_Fst_Snd[THEN ccompatible_sym]
lemmas qcompatible_Snd_Fst[simp] = qcompatible_Fst_Snd[THEN qcompatible_sym]

lemma ccompatible3I[simp]: \<open>ccompatible F G \<Longrightarrow> ccompatible G H \<Longrightarrow> ccompatible F H \<Longrightarrow> ccompatible (cregister_pair F G) H\<close>
  by (simp add: ccompatible3)
lemma qcompatible3I[simp]: \<open>qcompatible F G \<Longrightarrow> qcompatible G H \<Longrightarrow> qcompatible F H \<Longrightarrow> qcompatible (qregister_pair F G) H\<close>
  by (simp add: qcompatible3)
lemma ccompatible3I'[simp]: \<open>ccompatible F G \<Longrightarrow> ccompatible F H \<Longrightarrow> ccompatible G H \<Longrightarrow> ccompatible F (cregister_pair G H)\<close>
  by (simp add: ccompatible3')
lemma qcompatible3I'[simp]: \<open>qcompatible F G \<Longrightarrow> qcompatible F H \<Longrightarrow> qcompatible G H \<Longrightarrow> qcompatible F (qregister_pair G H)\<close>
  by (simp add: qcompatible3')

lemma Cccompatible3I[simp]: \<open>CCcompatible F G \<Longrightarrow> Cccompatible G H \<Longrightarrow> Cccompatible F H \<Longrightarrow> Cccompatible (CREGISTER_pair F G) H\<close> sorry
lemma Qqcompatible3I[simp]: \<open>QQcompatible F G \<Longrightarrow> Qqcompatible G H \<Longrightarrow> Qqcompatible F H \<Longrightarrow> Qqcompatible (QREGISTER_pair F G) H\<close> sorry
lemma Cccompatible3I'[simp]: \<open>Cccompatible F G \<Longrightarrow> Cccompatible F H \<Longrightarrow> ccompatible G H \<Longrightarrow> Cccompatible F (cregister_pair G H)\<close> sorry
lemma Qqcompatible3I'[simp]: \<open>Qqcompatible F G \<Longrightarrow> Qqcompatible F H \<Longrightarrow> qcompatible G H \<Longrightarrow> Qqcompatible F (qregister_pair G H)\<close> sorry

(* TODO: (and also for quantum, also for COMPATIBLE)
lemma ccompatible_register_tensor[simp]: \<open>ccompatible F F' \<Longrightarrow> ccompatible G G' \<Longrightarrow> ccompatible (cregister_tensor F G) (cregister_tensor F' G')\<close> *)

lemma cregister_cregister_pairI[simp]: \<open>ccompatible x y \<Longrightarrow> cregister (cregister_pair x y)\<close>
  by (simp add: cregister_pair_iff_compatible)
lemma qregister_qregister_pairI[simp]: \<open>qcompatible x y \<Longrightarrow> qregister (qregister_pair x y)\<close>
  by (simp add: qregister_pair_iff_compatible)

definition \<open>cswap = cregister_pair cSnd cFst\<close>
definition \<open>qswap = qregister_pair qSnd qFst\<close>

lemma cregister_cswap[simp]: \<open>cregister cswap\<close>
  by (simp add: ccompatible_Fst_Snd ccompatible_sym cregister_pair_iff_compatible cswap_def)
lemma qregister_qswap[simp]: \<open>qregister qswap\<close>
  by (simp add: qcompatible_Fst_Snd qcompatible_sym qregister_pair_iff_compatible qswap_def)

(* TODO: compatibility condition can be omitted *)
lemma cregister_chain_pair:
  assumes \<open>ccompatible G H\<close>
  shows \<open>cregister_chain F (cregister_pair G H) = cregister_pair (cregister_chain F G) (cregister_chain F H)\<close>
  sorry
lemma qregister_chain_pair:
  assumes \<open>qcompatible G H\<close>
  shows \<open>qregister_chain F (qregister_pair G H) = qregister_pair (qregister_chain F G) (qregister_chain F H)\<close>
  sorry

lemma not_ccompatible_pair: \<open>\<not> ccompatible F G \<Longrightarrow> cregister_pair F G = non_cregister\<close>
  apply (subst (asm) cregister_pair_iff_compatible[symmetric])
  by (simp add: non_cregister)
lemma not_qcompatible_pair: \<open>\<not> qcompatible F G \<Longrightarrow> qregister_pair F G = non_qregister\<close>
  apply (subst (asm) qregister_pair_iff_compatible[symmetric])
  using non_qregister by auto

axiomatization where cregister_raw_id[simp]: \<open>cregister_raw id\<close>
axiomatization where qregister_raw_id[simp]: \<open>qregister_raw id\<close>

lift_definition cregister_id :: \<open>('a,'a) cregister\<close> is id by simp
lift_definition qregister_id :: \<open>('a,'a) qregister\<close> is id by simp

lemma cregister_id_chain[simp]: \<open>cregister_chain cregister_id F = F\<close>
  apply transfer by auto
lemma qregister_id_chain[simp]: \<open>qregister_chain qregister_id F = F\<close>
  apply transfer by auto
lemma cregister_chain_id[simp]: \<open>cregister_chain F cregister_id = F\<close>
  apply transfer by auto
lemma qregister_chain_id[simp]: \<open>qregister_chain F qregister_id = F\<close>
  apply transfer by auto

lemma apply_cregister_id[simp]: \<open>apply_cregister cregister_id = id\<close>
  by (rule cregister_id.rep_eq)
lemma apply_qregister_id[simp]: \<open>apply_qregister qregister_id = id\<close>
  by (rule qregister_id.rep_eq)

axiomatization where cregister_id[simp]: \<open>cregister cregister_id\<close>
axiomatization where qregister_id[simp]: \<open>qregister qregister_id\<close>

definition \<open>iso_cregister I \<longleftrightarrow> cregister I \<and> (\<exists>J. cregister J \<and> cregister_chain I J = cregister_id \<and> cregister_chain J I = cregister_id)\<close>
definition \<open>iso_qregister I \<longleftrightarrow> qregister I \<and> (\<exists>J. qregister J \<and> qregister_chain I J = qregister_id \<and> qregister_chain J I = qregister_id)\<close>

lift_definition cregister_inv :: \<open>('a,'b) cregister \<Rightarrow> ('b,'a) cregister\<close> is
  \<open>\<lambda>F. if cregister_raw (inv F) then inv F else non_cregister_raw\<close> by auto
lift_definition qregister_inv :: \<open>('a,'b) qregister \<Rightarrow> ('b,'a) qregister\<close> is
  \<open>\<lambda>F. if qregister_raw (inv F) then inv F else non_qregister_raw\<close> by auto

lemma iso_cregister_inv_iso: \<open>iso_cregister I \<Longrightarrow> iso_cregister (cregister_inv I)\<close>
  unfolding iso_cregister_def apply transfer apply auto
  using non_cregister_raw apply fastforce
  using inv_unique_comp apply blast
  apply (simp add: inv_unique_comp)
  using inv_unique_comp by blast
lemma iso_qregister_inv_iso: \<open>iso_qregister I \<Longrightarrow> iso_qregister (qregister_inv I)\<close>
  unfolding iso_qregister_def apply transfer apply auto
  using non_qregister_raw apply fastforce
  using inv_unique_comp apply blast
  apply (simp add: inv_unique_comp)
  using inv_unique_comp by blast

lemma iso_cregister_inv_iso_apply: \<open>iso_cregister I \<Longrightarrow> apply_cregister (cregister_inv I) = inv (apply_cregister I)\<close>
  unfolding iso_cregister_def apply transfer using non_cregister_raw inv_unique_comp apply auto by blast
lemma iso_qregister_inv_iso_apply: \<open>iso_qregister I \<Longrightarrow> apply_qregister (qregister_inv I) = inv (apply_qregister I)\<close>
  unfolding iso_qregister_def apply transfer using non_qregister_raw inv_unique_comp apply auto by blast

lemma iso_cregister_inv_chain: \<open>iso_cregister I \<Longrightarrow> cregister_chain (cregister_inv I) I = cregister_id\<close>
  apply (rule apply_cregister_inject[THEN iffD1], rule ext)
  apply simp
  by (smt (verit, del_insts) apply_cregister_id inv_unique_comp iso_cregister_def iso_cregister_inv_iso_apply pointfree_idE cregister_chain_apply)
lemma iso_qregister_inv_chain: \<open>iso_qregister I \<Longrightarrow> qregister_chain (qregister_inv I) I = qregister_id\<close>
  apply (rule apply_qregister_inject[THEN iffD1], rule ext)
  apply simp
  by (smt (verit, del_insts) apply_qregister_id inv_unique_comp iso_qregister_def iso_qregister_inv_iso_apply pointfree_idE qregister_chain_apply)

lemma iso_cregister_chain_inv: \<open>iso_cregister I \<Longrightarrow> cregister_chain I (cregister_inv I) = cregister_id\<close>
  apply (rule apply_cregister_inject[THEN iffD1], rule ext)
  apply simp
  by (smt (verit, best) apply_cregister_id iso_cregister_def iso_cregister_inv_chain left_right_inverse_eq pointfree_idE cregister_chain_apply)
lemma iso_qregister_chain_inv: \<open>iso_qregister I \<Longrightarrow> qregister_chain I (qregister_inv I) = qregister_id\<close>
  apply (rule apply_qregister_inject[THEN iffD1], rule ext)
  apply simp
  by (smt (verit, best) apply_qregister_id iso_qregister_def iso_qregister_inv_chain left_right_inverse_eq pointfree_idE qregister_chain_apply)

axiomatization where cswap_iso[simp]: \<open>iso_cregister cswap\<close>
axiomatization where qswap_iso[simp]: \<open>iso_qregister qswap\<close>

axiomatization where ccompatible_chain[simp]: \<open>cregister F \<Longrightarrow> ccompatible G H \<Longrightarrow> ccompatible (cregister_chain F G) (cregister_chain F H)\<close>
axiomatization where qcompatible_chain[simp]: \<open>qregister F \<Longrightarrow> qcompatible G H \<Longrightarrow> qcompatible (qregister_chain F G) (qregister_chain F H)\<close>

lemma ccompatible_chain_iso: \<open>iso_cregister I \<Longrightarrow> ccompatible (cregister_chain I F) (cregister_chain I G) \<longleftrightarrow> ccompatible F G\<close>
  apply (cases \<open>cregister F\<close>; cases \<open>cregister G\<close>)
     apply (simp_all add: non_cregister)
  apply (rule iffI)
   apply (subst asm_rl[of \<open>F = cregister_chain (cregister_inv I) (cregister_chain I F)\<close>])
    apply (simp add: cregister_chain_assoc[symmetric] iso_cregister_inv_chain)
   apply (subst asm_rl[of \<open>G = cregister_chain (cregister_inv I) (cregister_chain I G)\<close>])
    apply (simp add: cregister_chain_assoc[symmetric] iso_cregister_inv_chain)
   apply (rule ccompatible_chain)
  using iso_cregister_def iso_cregister_inv_iso apply auto
  by (simp add: iso_cregister_def ccompatible_chain)
lemma qcompatible_chain_iso: \<open>iso_qregister I \<Longrightarrow> qcompatible (qregister_chain I F) (qregister_chain I G) \<longleftrightarrow> qcompatible F G\<close>
  apply (cases \<open>qregister F\<close>; cases \<open>qregister G\<close>)
     apply (simp_all add: non_qregister)
  apply (rule iffI)
   apply (subst asm_rl[of \<open>F = qregister_chain (qregister_inv I) (qregister_chain I F)\<close>])
    apply (simp add: qregister_chain_assoc[symmetric] iso_qregister_inv_chain)
   apply (subst asm_rl[of \<open>G = qregister_chain (qregister_inv I) (qregister_chain I G)\<close>])
    apply (simp add: qregister_chain_assoc[symmetric] iso_qregister_inv_chain)
   apply (rule qcompatible_chain)
  using iso_qregister_def iso_qregister_inv_iso apply auto
  by (simp add: iso_qregister_def qcompatible_chain)

axiomatization getter :: \<open>('a,'b) cregister \<Rightarrow> 'b \<Rightarrow> 'a\<close>
axiomatization setter :: \<open>('a,'b) cregister \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b\<close>

axiomatization where getter_non_cregister[simp]: \<open>getter non_cregister m = undefined\<close>
axiomatization where setter_non_cregister[simp]: \<open>setter non_cregister a = id\<close>

axiomatization where getter_setter_same[simp]: \<open>cregister x \<Longrightarrow> getter x (setter x a m) = a\<close>
axiomatization where setter_setter_same[simp]: \<open>setter x b (setter x a m) = setter x b m\<close>
axiomatization where getter_setter_compat[simp]: \<open>ccompatible x y \<Longrightarrow> getter x (setter y a m) = getter x m\<close>
axiomatization where setter_setter_compat: \<open>ccompatible x y \<Longrightarrow> setter x a (setter y b m) = setter y b (setter x a m)\<close>
axiomatization where setter_getter_same[simp]: \<open>setter x (getter x m) m = m\<close>

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

axiomatization CCOMPLEMENT :: \<open>'a CREGISTER \<Rightarrow> 'a CREGISTER\<close>
axiomatization QCOMPLEMENT :: \<open>'a QREGISTER \<Rightarrow> 'a QREGISTER\<close>

axiomatization where cregister_pair_chain_swap[simp]:
  "cregister_chain (cregister_pair A B) cswap = (cregister_pair B A)"
axiomatization where qregister_pair_chain_swap[simp]:
  "qregister_chain (qregister_pair A B) qswap = (qregister_pair B A)"

lemma Cccompatible_antimono_left: \<open>A \<le> B \<Longrightarrow> Cccompatible B C \<Longrightarrow> Cccompatible A C\<close>
  apply transfer by auto
lemma Qqcompatible_antimono_left: \<open>A \<le> B \<Longrightarrow> Qqcompatible B C \<Longrightarrow> Qqcompatible A C\<close>
  apply transfer by auto

lemma setter_chain: 
  assumes \<open>cregister F\<close> \<open>cregister G\<close>
  shows \<open>setter (cregister_chain F G) a m = setter F (setter G a (getter F m)) m\<close>
  sorry

lemma setter_Fst: \<open>setter cFst = (\<lambda>x (_,y). (x,y))\<close>
  sorry
lemma setter_Snd: \<open>setter cSnd = (\<lambda>y (x,_). (x,y))\<close>
  sorry

lemma getter_Fst[simp]: \<open>getter cFst = fst\<close>
  sorry
lemma getter_Snd[simp]: \<open>getter cSnd = snd\<close>
  sorry


(* TODO move to misc *)
lemma Some_map_comp[simp]: \<open>Some \<circ>\<^sub>m f = f\<close>
  apply (rule ext, case_tac \<open>f x\<close>)
  by (auto simp: map_comp_def)

(* TODO move to misc *)
lemma map_comp_Some[simp]: \<open>f \<circ>\<^sub>m Some = f\<close>
  apply (rule ext, case_tac \<open>f x\<close>)
  by (auto simp: map_comp_def)

lemma Cccompatible_CREGISTER_of: \<open>Cccompatible (CREGISTER_of A) B \<longleftrightarrow> ccompatible A B \<or> (cregister B \<and> A = non_cregister)\<close>
  unfolding CREGISTER_of.rep_eq Cccompatible.rep_eq
  apply transfer
  by (auto simp add: non_cregister_raw empty_cregister_range_def ccompatible_raw_def)
lemma Qqcompatible_QREGISTER_of: \<open>Qqcompatible (QREGISTER_of A) B \<longleftrightarrow> qcompatible A B \<or> (qregister B \<and> A = non_qregister)\<close>
  unfolding QREGISTER_of.rep_eq Qqcompatible.rep_eq
  apply transfer
  by (auto simp add: non_qregister_raw empty_qregister_range_def qcompatible_raw_def)

lemma Cccompatible_CREGISTER_ofI[simp]: \<open>ccompatible F G \<Longrightarrow> Cccompatible (CREGISTER_of F) G\<close>
  by (simp add: Cccompatible_CREGISTER_of)
lemma Qqcompatible_QREGISTER_ofI[simp]: \<open>qcompatible F G \<Longrightarrow> Qqcompatible (QREGISTER_of F) G\<close>
  by (simp add: Qqcompatible_QREGISTER_of)

lemma cregister_conversion_raw_register: \<open>cregister_raw F \<Longrightarrow> cregister_raw G \<Longrightarrow> range F \<subseteq> range G \<Longrightarrow> cregister_raw (inv G \<circ> F)\<close>
  sorry
lemma qregister_conversion_raw_register: \<open>qregister_raw F \<Longrightarrow> qregister_raw G \<Longrightarrow> range F \<subseteq> range G \<Longrightarrow> qregister_raw (inv G \<circ> F)\<close>
  sorry

lift_definition cregister_conversion :: \<open>('a,'c) cregister \<Rightarrow> ('b,'c) cregister \<Rightarrow> ('a,'b) cregister\<close> is
  \<open>\<lambda>F G. if cregister_raw F \<and> cregister_raw G \<and> range F \<subseteq> range G then inv G o F else non_cregister_raw\<close>
  by (auto intro: cregister_conversion_raw_register)

lift_definition qregister_conversion :: \<open>('a,'c) qregister \<Rightarrow> ('b,'c) qregister \<Rightarrow> ('a,'b) qregister\<close> is
  \<open>\<lambda>F G. if qregister_raw F \<and> qregister_raw G \<and> range F \<subseteq> range G then inv G o F else non_qregister_raw\<close>
  by (auto intro: qregister_conversion_raw_register)

definition \<open>cregister_le F G = (cregister F \<and> cregister G \<and> CREGISTER_of F \<le> CREGISTER_of G)\<close>
definition \<open>qregister_le F G = (qregister F \<and> qregister G \<and> QREGISTER_of F \<le> QREGISTER_of G)\<close>

lemma cregister_chain_conversion: \<open>cregister_le F G \<Longrightarrow> cregister_chain G (cregister_conversion F G) = F\<close>
  unfolding cregister_le_def
  apply (transfer fixing: F G)
  apply transfer
  by (auto simp: non_cregister_raw cregister_conversion_raw_register f_inv_into_f in_mono intro!: ext)

lemma qregister_chain_conversion: \<open>qregister_le F G  \<Longrightarrow> qregister_chain G (qregister_conversion F G) = F\<close>
  unfolding qregister_le_def
  apply (transfer fixing: F G)
  apply transfer
  by (auto simp: non_qregister_raw qregister_conversion_raw_register f_inv_into_f in_mono intro!: ext)

lemma cregister_conversion_id[simp]: \<open>cregister_conversion F cregister_id = F\<close>
  apply transfer by auto
lemma qregister_conversion_id[simp]: \<open>qregister_conversion F qregister_id = F\<close>
  apply transfer by auto

lemma cregister_conversion_non_reg_right[simp]: \<open>cregister_conversion F non_cregister = non_cregister\<close>
  apply transfer by (auto simp add: non_cregister_raw)
lemma qregister_conversion_non_reg_right[simp]: \<open>qregister_conversion F non_qregister = non_qregister\<close>
  apply transfer by (auto simp add: non_qregister_raw)

lemma cregister_conversion_non_reg_left[simp]: \<open>cregister_conversion non_cregister F = non_cregister\<close>
  apply transfer by (auto simp add: non_cregister_raw)
lemma qregister_conversion_non_reg_left[simp]: \<open>qregister_conversion non_qregister F = non_qregister\<close>
  apply transfer by (auto simp add: non_qregister_raw)

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
    apply (simp add: \<open>G = qregister_chain H G'\<close>)
    by -
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
    apply (rule inv_comp_eqI)
    using qregister_raw_inj[OF \<open>qregister_raw H\<close>] qregister_raw_inj[OF \<open>qregister_raw G'\<close>]
    using inj_compose that by (auto simp add: ext f_inv_into_f subset_iff)
  assume [simp]: \<open>qregister F'\<close> \<open>qregister G'\<close>
  then show ?thesis
    using assms apply transfer
    using range_le_preserve H_cancel by (auto simp: qregister_raw_chain)
qed


lemma cregister_conversion_as_register: 
  fixes F :: \<open>('a,'c) cregister\<close> and F' G'
  assumes \<open>cregister G\<close>
  assumes \<open>F = cregister_chain G F'\<close>
  shows \<open>cregister_conversion F G = F'\<close>
  apply (subst cregister_conversion_rename[where H=G and G'=cregister_id and F'=F'])
  using assms by auto
lemma qregister_conversion_as_register: 
  fixes F :: \<open>('a,'c) qregister\<close> and F' G'
  assumes \<open>qregister G\<close>
  assumes \<open>F = qregister_chain G F'\<close>
  shows \<open>qregister_conversion F G = F'\<close>
  apply (subst qregister_conversion_rename[where H=G and G'=qregister_id and F'=F'])
  using assms by auto

(* lift_definition qregister_of_cregister :: \<open>('a,'b) cregister \<Rightarrow> ('a,'b) qregister\<close> is
  \<open>\<lambda>F a. if cregister F then 
      explicit_cblinfun (\<lambda>i j. if same_outside_cregister F i j then Rep_ell2 (a *\<^sub>V ket (getter F j)) (getter F i) else 0)
    else 0\<close>
  sorry *)

lift_definition qregister_of_cregister :: \<open>('a,'b) cregister \<Rightarrow> ('a,'b) qregister\<close> is
  \<open>\<lambda>F a. if cregister F then permute_and_tensor1_cblinfun (getter F) (same_outside_cregister F) a else 0\<close>
  sorry

lemma qregister_of_cregister_Fst: \<open>qregister_of_cregister cFst = qFst\<close>
  sorry
lemma qregister_of_cregister_Snd: \<open>qregister_of_cregister cSnd = qSnd\<close>
  sorry

lemma qregister_qregister_of_cregister[simp]: \<open>qregister (qregister_of_cregister F) \<longleftrightarrow> cregister F\<close>
  sorry

lemma qcompatible_qregister_of_cregister[simp]: 
  \<open>qcompatible (qregister_of_cregister F) (qregister_of_cregister G) \<longleftrightarrow> ccompatible F G\<close>
  sorry

lemmas qcompatible_FS_qregister_of_cregister[simp] = 
  qcompatible_Fst_Snd[unfolded qregister_of_cregister_Fst[symmetric]]
  qcompatible_Fst_Snd[unfolded qregister_of_cregister_Snd[symmetric]]
  qcompatible_Fst_Snd[unfolded qregister_of_cregister_Fst[symmetric] qregister_of_cregister_Snd[symmetric]]
  qcompatible_Snd_Fst[unfolded qregister_of_cregister_Fst[symmetric]]
  qcompatible_Snd_Fst[unfolded qregister_of_cregister_Snd[symmetric]]
  qcompatible_Snd_Fst[unfolded qregister_of_cregister_Fst[symmetric] qregister_of_cregister_Snd[symmetric]]




typedecl cl
typedecl qu
instance qu :: default sorry

type_synonym 'a cvariable = \<open>('a,cl) cregister\<close>
type_synonym 'a qvariable = \<open>('a,qu) qregister\<close>

type_synonym QVARIABLE = \<open>qu QREGISTER\<close>
type_synonym CVARIABLE = \<open>cl CREGISTER\<close>
(* typedecl QVARIABLE
typedef QVARIABLE = \<open>UNIV :: qu Axioms_Quantum.update set set\<close>..
setup_lifting type_definition_QVARIABLE
(* TODO: Is this truely an equivalence class of classical variables? *)
typedef CVARIABLE = \<open>UNIV :: cl Axioms_Classical.update set set\<close>..
setup_lifting type_definition_CVARIABLE *)

(* lift_definition QVARIABLE_of :: \<open>'a::finite qvariable \<Rightarrow> QVARIABLE\<close> is
  \<open>\<lambda>x::'a::finite qvariable. range x\<close>.
axiomatization CVARIABLE_of :: \<open>'a cvariable \<Rightarrow> CVARIABLE\<close> *)

(* lift_definition QVARIABLE_unit :: \<open>QVARIABLE\<close> is
  \<open>{c *\<^sub>C (id_cblinfun) | c. True} :: 'qu Axioms_Quantum.update set\<close>.
axiomatization CVARIABLE_unit :: \<open>CVARIABLE\<close> *)

(* axiomatization QVARIABLE_pair :: \<open>QVARIABLE \<Rightarrow> QVARIABLE \<Rightarrow> QVARIABLE\<close>
axiomatization CVARIABLE_pair :: \<open>CVARIABLE \<Rightarrow> CVARIABLE \<Rightarrow> CVARIABLE\<close> *)

(* axiomatization compatible_CC :: \<open>CVARIABLE \<Rightarrow> CVARIABLE \<Rightarrow> bool\<close>
axiomatization compatible_Cc :: \<open>CVARIABLE \<Rightarrow> 'a cvariable \<Rightarrow> bool\<close> *)

datatype 'a vtree = VTree_Singleton 'a | VTree_Concat "'a vtree" "'a vtree" | VTree_Unit

consts variable_concat :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c\<close>
adhoc_overloading variable_concat qregister_pair cregister_pair
consts register_conversion :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c\<close>
adhoc_overloading register_conversion qregister_conversion cregister_conversion
consts register_le :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c\<close>
adhoc_overloading register_le qregister_le cregister_le
consts register_id :: \<open>'a\<close>
adhoc_overloading register_id qregister_id cregister_id
consts register_chain :: \<open>'a\<close>
adhoc_overloading register_chain qregister_chain cregister_chain
consts Fst :: \<open>'a\<close>
adhoc_overloading Fst qFst cFst
consts Snd :: \<open>'a\<close>
adhoc_overloading Snd qSnd cSnd


(* We need those definition (not abbreviations!) with slightly more restrictive type, otherwise the overloaded variable_unit below will expand to \<open>('a,'b) empty_qregister\<close> etc *)
definition [simp]: \<open>qvariable_unit \<equiv> empty_qregister :: (unit,_) qregister\<close>
definition [simp]: \<open>cvariable_unit \<equiv> empty_cregister :: (unit,_) cregister\<close>

consts variable_unit :: \<open>'a\<close>
adhoc_overloading variable_unit 
  qvariable_unit cvariable_unit

(* LEGACY *)
abbreviation (input) "variable_singleton x \<equiv> x"

section \<open>Distinct variables\<close>

abbreviation (input) "distinct_qvars Q == qregister Q"
abbreviation (input) "distinct_cvars Q == cregister Q"

(* lemma register_pair_is_register_iff: \<open>qregister (Q;R) \<longleftrightarrow> compatible Q R\<close>
  apply auto
  by (smt (verit, best) Axioms_Quantum.register_pair_def Laws_Quantum.compatibleI zero_not_register) *)

lemma distinct_qvars_split1: 
  "distinct_qvars (variable_concat (variable_concat Q R) S) = (distinct_qvars (variable_concat Q R) \<and> distinct_qvars (variable_concat Q S) \<and> distinct_qvars (variable_concat R S))"
  unfolding qregister_pair_iff_compatible
  using qcompatible3 by blast
lemma distinct_qvars_swap: "distinct_qvars (variable_concat Q R) \<Longrightarrow> distinct_qvars (variable_concat R Q)" 
  unfolding qregister_pair_iff_compatible
  using qcompatible_sym by auto
lemma distinct_qvars_split2: "distinct_qvars (variable_concat S (variable_concat Q R)) = (distinct_qvars (variable_concat Q R) \<and> distinct_qvars (variable_concat Q S) \<and> distinct_qvars (variable_concat R S))"
  unfolding qregister_pair_iff_compatible
  by (metis qcompatible3 qcompatible_sym)
lemma distinct_qvars_concat_unit1[simp]: "distinct_qvars (variable_concat Q qvariable_unit) = distinct_qvars Q" for Q::"'a qvariable" 
  unfolding qregister_pair_iff_compatible qvariable_unit_def
  using qcompatible_QQcompatible qcompatible_empty by auto
lemma distinct_qvars_concat_unit2[simp]: "distinct_qvars (variable_concat qvariable_unit Q) = distinct_qvars Q" for Q::"'a::finite qvariable" 
  unfolding qregister_pair_iff_compatible qvariable_unit_def
  using qcompatible_QQcompatible qcompatible_empty qcompatible_sym by blast
lemma distinct_qvars_unit[simp]: "distinct_qvars qvariable_unit"
  by (simp add: qvariable_unit_def)
(* lemma distinct_qvars_single[simp]: "distinct_qvars \<lbrakk>q\<rbrakk>" for q::"'a::finite qvariable"
  unfolding distinct_qvars_def apply transfer by auto *)

lemma distinct_qvarsL: "distinct_qvars (variable_concat Q R) \<Longrightarrow> distinct_qvars Q"
  unfolding qregister_pair_iff_compatible
  by (simp add: qcompatible_QQcompatible)
lemma distinct_qvarsR: "distinct_qvars (variable_concat Q R) \<Longrightarrow> distinct_qvars R"
  unfolding qregister_pair_iff_compatible
  by (simp add: qcompatible_register2)

lemma distinct_cvars_split1: 
  "distinct_cvars (variable_concat (variable_concat Q R) S) = (distinct_cvars (variable_concat Q R) \<and> distinct_cvars (variable_concat Q S) \<and> distinct_cvars (variable_concat R S))"
  unfolding cregister_pair_iff_compatible
  by (simp add: ccompatible3)
lemma distinct_cvars_swap: "distinct_cvars (variable_concat Q R) \<Longrightarrow> distinct_cvars (variable_concat R Q)" 
  unfolding cregister_pair_iff_compatible
  using ccompatible_sym by blast
lemma distinct_cvars_split2: "distinct_cvars (variable_concat S (variable_concat Q R)) = (distinct_cvars (variable_concat Q R) \<and> distinct_cvars (variable_concat Q S) \<and> distinct_cvars (variable_concat R S))"
  by (metis distinct_cvars_split1 distinct_cvars_swap)
lemma distinct_cvars_concat_unit1[simp]: "distinct_cvars (variable_concat Q cvariable_unit) = distinct_cvars Q" for Q::"'a::finite cvariable" 
  unfolding cregister_pair_iff_compatible cvariable_unit_def
  using ccompatible_CCcompatible ccompatible_empty by blast
lemma distinct_cvars_concat_unit2[simp]: "distinct_cvars (variable_concat cvariable_unit Q) = distinct_cvars Q" for Q::"'a::finite cvariable"
  by (metis distinct_cvars_concat_unit1 distinct_cvars_swap) 
lemma distinct_cvars_unit[simp]: "distinct_cvars cvariable_unit" 
  by (simp add: cvariable_unit_def)
(* lemma distinct_cvars_single[simp]: "distinct_cvars \<lbrakk>q\<rbrakk>" for q::"'a::finite cvariable"
  unfolding distinct_cvars_def apply transfer by auto *)

lemma distinct_cvarsL: "distinct_cvars (variable_concat Q R) \<Longrightarrow> distinct_cvars Q"
  using ccompatible.rep_eq cregister.rep_eq cregister_pair_iff_compatible ccompatible_raw_def by blast
lemma distinct_cvarsR: "distinct_cvars (variable_concat Q R) \<Longrightarrow> distinct_cvars R"
  using ccompatible.rep_eq cregister.rep_eq cregister_pair_iff_compatible ccompatible_raw_def by blast

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
  apply (simp add: qregister_chain_pair)
  apply (subst not_qcompatible_pair, simp)
  apply (subst not_qcompatible_pair)
    apply auto
  using qcompatible_chain_iso qswap_iso by blast

lemma index_flip_qvar_chain[simp]: \<open>index_flip_qvar (qregister_chain Q R) = qregister_chain (index_flip_qvar Q) R\<close>
  unfolding index_flip_qvar_def
  by (simp add: qregister_chain_assoc)

lemma index_flip_qvar_Fst[simp]: \<open>index_flip_qvar qFst = qSnd\<close>
  unfolding index_flip_qvar_def
  by (simp add: qcompatible_Fst_Snd qcompatible_sym qregister_chain_pair_Fst qswap_def)

lemma index_flip_qvar_Snd[simp]: \<open>index_flip_qvar qSnd = qFst\<close>
  by (simp add: index_flip_qvar_def qcompatible_Fst_Snd qcompatible_sym qregister_chain_pair_Snd qswap_def)

definition index_flip_mem2 :: "qu2 \<Rightarrow> qu2" where \<open>index_flip_mem2 = (\<lambda>(x,y). (y,x))\<close>
(*  "\<lambda>(f::_\<Rightarrow>universe) v. f (index_flip_var_raw v)"
  using variable_raw_domain_index_flip_var_raw by blast *)

definition swap_cvariables_mem2 :: "'a c2variable \<Rightarrow> 'a c2variable \<Rightarrow> (cl2 \<Rightarrow> cl2)" where
  \<open>swap_cvariables_mem2 x y m = apply_cregister_total (cregister_pair x y) (\<lambda>(a,b). (b,a)) m\<close>

axiomatization swap_variables_qvars :: \<open>'a q2variable \<Rightarrow> 'a q2variable \<Rightarrow> 'b q2variable \<Rightarrow> 'b q2variable\<close>

section \<open>Unsorted\<close>

lemma getter_Snd_chain_swap[simp]: \<open>getter (cregister_chain cSnd G) (prod.swap m) = getter (cregister_chain cFst G) m\<close>
  sorry

lemma getter_Fst_chain_swap[simp]: \<open>getter (cregister_chain cFst G) (prod.swap m) = getter (cregister_chain cSnd G) m\<close>
  sorry

section \<open>ML code\<close>

(* 
lemma index_var_conv1_aux: \<comment> \<open>Helper for ML function index_var_conv\<close>
  assumes "variable_name v \<equiv> vname"
  assumes "variable_name v1 \<equiv> v1name"
  assumes "vname @ ''1'' \<equiv> v1name"
  shows "index_var True v \<equiv> v1"
  using assms index_var1I by smt

lemma index_var_conv2_aux: \<comment> \<open>Helper for ML function index_var_conv\<close>
  assumes "variable_name v \<equiv> vname"
  assumes "variable_name v2 \<equiv> v2name"
  assumes "vname @ ''2'' \<equiv> v2name"
  shows "index_var False v \<equiv> v2"
  using assms index_var2I by smt

lemma index_flip_var_conv_aux1: "index_flip_var (index_var True v) \<equiv> index_var False v"
  by simp
lemma index_flip_var_conv_aux2: "index_flip_var (index_var False v) \<equiv> index_var True v"
  by simp *)

ML_file "prog_variables.ML"


section \<open>Syntax\<close>


nonterminal variable_list_args 
nonterminal variable_nth
nonterminal variable_nth'
syntax
  "_variable_nth" :: "'a \<Rightarrow> 'b"
  "_variable_nth'" :: "'a \<Rightarrow> 'b"
  "variable_unit"      :: "variable_list_args \<Rightarrow> 'a"        ("(1'[|'|])")
  "variable_unit"      :: "variable_list_args \<Rightarrow> 'a"        ("(1'\<lbrakk>'\<rbrakk>)")
  "_variables"      :: "variable_list_args \<Rightarrow> 'a"        ("(1'[|_'|])")
  "_variables"      :: "variable_list_args \<Rightarrow> 'a"        ("(1'\<lbrakk>_'\<rbrakk>)")
  "_variable_list_arg_nth"  :: "'a \<Rightarrow> variable_list_args"                   ("#_")  (* Instead of 'a, would like to match only natural numbers *)
  "_variable_list_arg_nth'"  :: "'a \<Rightarrow> variable_list_args"                   ("#_.")
  "_variable_list_arg"  :: "'a \<Rightarrow> variable_list_args"                   ("_")
  "_variable_list_args_nth"  :: "'a \<Rightarrow> variable_list_args \<Rightarrow> variable_list_args"                   ("#_,/ _")
  "_variable_list_args_nth'"  :: "'a \<Rightarrow> variable_list_args \<Rightarrow> variable_list_args"                   ("#_.,/ _")
  "_variable_list_args" :: "'a \<Rightarrow> variable_list_args \<Rightarrow> variable_list_args"     ("_,/ _")

  "_variable_conversion"      :: "variable_list_args \<Rightarrow> variable_list_args \<Rightarrow> 'a"        ("(1'\<lbrakk>_ \<mapsto> _'\<rbrakk>)")
  "_variable_le"      :: "variable_list_args \<Rightarrow> variable_list_args \<Rightarrow> 'a"        ("(1'\<lbrakk>_ \<le> _'\<rbrakk>)")

translations
  "_variables (_variable_list_args x y)" \<rightleftharpoons> "CONST variable_concat x (_variables y)"
  "_variables (_variable_list_args_nth x y)" \<rightleftharpoons> "CONST variable_concat (_variable_nth x) (_variables y)"
  "_variables (_variable_list_args_nth' x y)" \<rightleftharpoons> "CONST variable_concat (_variable_nth' x) (_variables y)"
  "_variables (_variable_list_arg x)" \<rightharpoonup> "x"
  "_variables (_variable_list_arg_nth x)" \<rightharpoonup> "_variable_nth x"
  "_variables (_variable_list_arg_nth' x)" \<rightharpoonup> "_variable_nth' x"
  "_variables (_variable_list_args x y)" \<leftharpoondown> "CONST variable_concat (_variables (_variable_list_arg x)) (_variables y)"

  "_variable_conversion x y" \<rightleftharpoons> "CONST register_conversion (_variables x) (_variables y)"
  "_variable_le x y" \<rightleftharpoons> "CONST register_le (_variables x) (_variables y)"

parse_translation
  \<open>[(\<^syntax_const>\<open>_variable_nth\<close>, fn ctxt => fn [nt] => Prog_Variables.register_n false (Misc.dest_number_syntax nt)),
    (\<^syntax_const>\<open>_variable_nth'\<close>, fn ctxt => fn [nt] => Prog_Variables.register_n true (Misc.dest_number_syntax nt))]\<close>

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

simproc_setup qregister_conversion_to_register (\<open>qregister_conversion x y\<close>) =
  \<open>fn m => fn ctxt => fn ct => SOME (Prog_Variables.qregister_conversion_to_register_conv ctxt ct) handle e => NONE\<close>

(* A hint to the simplifier with the meaning:
    - A is a term of the form x>>Q
    - Q,R are registers
    - Q \<le> R
    - The whole term should be rewritten into x'>>R for some x'
  Rewriting the term is done by the simproc TODO declared below.
*)
definition "register_conversion_hint A R = A"
lemma register_conversion_hint_cong[cong]: "A=A' \<Longrightarrow> register_conversion_hint A R = register_conversion_hint A' R" by simp

section \<open>Cleanup\<close>

hide_type (open) vtree

end
