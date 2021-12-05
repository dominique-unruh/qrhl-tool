theory Scratch
  imports QRHL_Operations
begin

ML \<open>open Prog_Variables\<close>



lemma rew1: \<open>qregister_le F G \<Longrightarrow> apply_qregister F x = apply_qregister G (apply_qregister (qregister_conversion F G) x)\<close>
  apply (subst qregister_chain_conversion[where F=F and G=G, symmetric])
  by auto

lemma lepairI: \<open>qregister_le F H \<Longrightarrow> qregister_le G H \<Longrightarrow> qcompatible F G \<Longrightarrow> qregister_le (qregister_pair F G) H\<close>
  sorry

lemma lepairI1: \<open>qregister_le F G \<Longrightarrow> qcompatible G H \<Longrightarrow> qregister_le F (qregister_pair G H)\<close>
  sorry
lemma lepairI2: \<open>qregister_le F H \<Longrightarrow> qcompatible G H \<Longrightarrow> qregister_le F (qregister_pair G H)\<close>
  sorry
lemma lerefl: \<open>qregister F \<Longrightarrow> qregister_le F F\<close>
  sorry

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

lemma tensor_ext2: 
  assumes \<open>\<And>x y. apply_qregister F (x\<otimes>y) = apply_qregister G (x\<otimes>y)\<close>
  shows \<open>F = G\<close>
  sorry

lemma tensor_ext3: 
  assumes \<open>\<And>x y z. apply_qregister F (x\<otimes>y\<otimes>z) = apply_qregister G (x\<otimes>y\<otimes>z)\<close>
  shows \<open>F = G\<close>
  sorry

lemma qcompatible_Abs_qregister:
  assumes \<open>qregister_raw F\<close> \<open>qregister_raw G\<close>
  assumes \<open>(\<forall>a b. F a o\<^sub>C\<^sub>L G b = G b o\<^sub>C\<^sub>L F a)\<close>
  shows \<open>qcompatible (Abs_qregister F) (Abs_qregister G)\<close>
  by (simp add: assms(1) assms(2) assms(3) eq_onp_same_args qcompatible.abs_eq)

lemma qregister_raw_tensor_left[intro!]:
  assumes \<open>qregister_raw F\<close>
  shows \<open>qregister_raw (\<lambda>x. id_cblinfun \<otimes> F x)\<close>
  sorry

lemma qregister_raw_tensor_right[intro!]:
  assumes \<open>qregister_raw F\<close>
  shows \<open>qregister_raw (\<lambda>x. F x \<otimes> id_cblinfun)\<close>
  sorry

lemma qregister_raw_id[simp]: \<open>qregister_raw (\<lambda>x. x)\<close>
  sorry

experiment fixes a b c
  assumes xxx: \<open>qregister \<lbrakk>a,b,c\<rbrakk>\<close> begin

thm cregister_pair_iff_compatible[THEN iffD1]
thm ccompatible3'[THEN iffD1, THEN conjunct1]
 ccompatible3'[THEN iffD1, THEN conjunct2, THEN conjunct1]
 ccompatible3'[THEN iffD1, THEN conjunct2, THEN conjunct2]

ML Thm.declaration_attribute

ML \<open>
;;
register_thms_of @{thm xxx} []
;;
register_compats_of @{thm xxx} []
\<close>
lemma Test
proof -
  fix a b c

  define R1 R2 R3 :: \<open>(bit,bit*bit*bit) qregister\<close> 
    where \<open>R1 = Abs_qregister (\<lambda>x. x\<otimes>id_cblinfun\<otimes>id_cblinfun)\<close> 
      and \<open>R2 = Abs_qregister (\<lambda>x. id_cblinfun\<otimes>x\<otimes>id_cblinfun)\<close> 
      and \<open>R3 = Abs_qregister (\<lambda>x. id_cblinfun\<otimes>id_cblinfun\<otimes>x)\<close> 

  have t[variable]: \<open>qregister (\<lbrakk>a,b,c\<rbrakk> :: (bit*bit*bit) qvariable)\<close> sorry

  have le: \<open>\<lbrakk>a,c \<le> a,b,c\<rbrakk>\<close>
    by (auto intro!: lepairI lerefl simp: lepairI1 lepairI2 lepairI lerefl)

  define CNOT' where \<open>CNOT' = apply_qregister \<lbrakk>a,c \<mapsto> a,b,c\<rbrakk> CNOT\<close>

  have \<open>apply_qregister \<lbrakk>a,c\<rbrakk> CNOT = apply_qregister \<lbrakk>a,b,c\<rbrakk> CNOT'\<close>
    apply (subst rew1[where G=\<open>\<lbrakk>a,b,c\<rbrakk>\<close>])
     apply (fact le)
    by (simp add: CNOT'_def)

  have rename: \<open>\<lbrakk>a,c \<mapsto> a,b,c\<rbrakk> = \<lbrakk>R1,R3 \<mapsto> R1,R2,R3\<rbrakk>\<close>
    term \<open>\<lbrakk>a,c\<rbrakk> :: (_,_)qregister\<close>
    apply (rule qregister_conversion_rename[where H=\<open>\<lbrakk>a,b,c\<rbrakk>\<close>])
      apply auto
     apply (rule tensor_ext2)
     apply (auto simp: R1_def R2_def R3_def)
    apply (subst apply_qregister_pair)
      apply simp
    apply (subst apply_qregister_pair)
      apply simp
      apply (rule qcompatible_Abs_qregister)
        apply (rule qregister_raw_tensor_right)
        apply simp
       apply (rule qregister_raw_tensor_left)
       apply (rule qregister_raw_tensor_left)
       apply simp
      apply simp
     apply (subst Abs_qregister_inverse)
      apply (auto intro!: qregister_raw_tensor_left)[1]
     apply (subst Abs_qregister_inverse)
      apply (auto intro!: qregister_raw_tensor_left)[1]
     apply simp
     apply (subst apply_qregister_pair)
      apply simp
     apply (subst apply_qregister_pair)
      apply simp
     apply (subst apply_qregister_of_id)
      apply simp
     apply simp

    apply (rule tensor_ext3)
    apply (subst apply_qregister_pair)
     apply simp
    apply (subst apply_qregister_pair)
     apply simp
    apply (subst qregister_chain_apply)
    unfolding o_def
    apply (subst apply_qregister_pair)
     apply simp
     apply (rule qcompatible3I')
       apply (rule qcompatible_Abs_qregister)
         apply (rule qregister_raw_tensor_right)
         apply simp
        apply (rule qregister_raw_tensor_left)
        apply (rule qregister_raw_tensor_right)
        apply simp
       apply simp
       apply (rule qcompatible_Abs_qregister)
        apply (rule qregister_raw_tensor_right)
        apply simp
       apply (rule qregister_raw_tensor_left)
       apply (rule qregister_raw_tensor_left)
       apply simp
      apply simp
     apply (rule qcompatible_Abs_qregister)
       apply (rule qregister_raw_tensor_left)
       apply (rule qregister_raw_tensor_right)
       apply simp
      apply (rule qregister_raw_tensor_left)
      apply (rule qregister_raw_tensor_left)
      apply simp
     apply simp
     apply (subst Abs_qregister_inverse)
     apply (auto intro!: qregister_raw_tensor_left)[1]
    apply (subst apply_qregister_pair)
     apply (rule qcompatible_Abs_qregister)
       apply (rule qregister_raw_tensor_left)
       apply (rule qregister_raw_tensor_right)
       apply simp
      apply (rule qregister_raw_tensor_left)
      apply (rule qregister_raw_tensor_left)
      apply simp
     apply simp
    apply (subst Abs_qregister_inverse)
      apply (auto intro!: qregister_raw_tensor_left)[1]
    apply (subst Abs_qregister_inverse)
      apply (auto intro!: qregister_raw_tensor_left)[1]
    apply simp
    apply (subst apply_qregister_pair)
     apply simp
    apply (subst apply_qregister_pair)
     apply simp
    apply simp
    by -

  have \<open>CNOT' = apply_qregister \<lbrakk>R1,R2 \<mapsto> R1,R2,R3\<rbrakk> CNOT\<close>

  have \<open>qregister a\<close>
    by simp

  have \<open>qregister \<lbrakk>a,b\<rbrakk>\<close>
    by simp

  oops


term \<open>declared_qvars \<lbrakk>x,y\<rbrakk>\<close>


term \<open>mutually ccompatible (X,Y)\<close>

ML \<open>
local
val ctxt = \<^context>
val ctxt = Prog_Variables.declare_variable ctxt \<^binding>\<open>z\<close> \<^typ>\<open>int\<close> Classical []
val ctxt = Prog_Variables.declare_variable ctxt \<^binding>\<open>b\<close> \<^typ>\<open>int\<close> Classical [("z", \<^typ>\<open>int\<close>)]
val ctxt = Prog_Variables.declare_variable ctxt \<^binding>\<open>count\<close> \<^typ>\<open>int\<close> Classical [("z", \<^typ>\<open>int\<close>),("b", \<^typ>\<open>int\<close>)]
val ctxt = Prog_Variables.declare_variable ctxt \<^binding>\<open>Find\<close> \<^typ>\<open>int\<close> Classical [("z", \<^typ>\<open>int\<close>),("b", \<^typ>\<open>int\<close>),("count", \<^typ>\<open>int\<close>)]
val ctxt = Prog_Variables.declare_variable ctxt \<^binding>\<open>G\<close> \<^typ>\<open>int\<close> Classical [("z", \<^typ>\<open>int\<close>),("b", \<^typ>\<open>int\<close>),("count", \<^typ>\<open>int\<close>),("Find", \<^typ>\<open>int\<close>)]
val ctxt = Prog_Variables.declare_variable ctxt \<^binding>\<open>H\<close> \<^typ>\<open>int\<close> Classical [("z", \<^typ>\<open>int\<close>),("b", \<^typ>\<open>int\<close>),("count", \<^typ>\<open>int\<close>),("Find", \<^typ>\<open>int\<close>),("G", \<^typ>\<open>int\<close>)]
val ctxt = Prog_Variables.declare_variable ctxt \<^binding>\<open>hit\<close> \<^typ>\<open>int\<close> Classical [("z", \<^typ>\<open>int\<close>),("b", \<^typ>\<open>int\<close>),("count", \<^typ>\<open>int\<close>),("Find", \<^typ>\<open>int\<close>),("G", \<^typ>\<open>int\<close>),("H", \<^typ>\<open>int\<close>)]
val ctxt = Prog_Variables.declare_variable ctxt \<^binding>\<open>S\<close> \<^typ>\<open>int\<close> Classical [("z", \<^typ>\<open>int\<close>),("b", \<^typ>\<open>int\<close>),("count", \<^typ>\<open>int\<close>),("Find", \<^typ>\<open>int\<close>),("G", \<^typ>\<open>int\<close>),("H", \<^typ>\<open>int\<close>),("hit", \<^typ>\<open>int\<close>)]

val ctxt = Prog_Variables.declare_variable ctxt \<^binding>\<open>q\<close> \<^typ>\<open>int\<close> Quantum []
val ctxt = Prog_Variables.declare_variable ctxt \<^binding>\<open>r\<close> \<^typ>\<open>int\<close> Quantum [("q",\<^typ>\<open>int\<close>)]
val ctxt = Prog_Variables.declare_variable ctxt \<^binding>\<open>s\<close> \<^typ>\<open>int\<close> Quantum [("q",\<^typ>\<open>int\<close>),("r",\<^typ>\<open>int\<close>)]
(* val t = Syntax.read_term ctxt "qregister (qregister_pair q r)" *)
(* val t = Syntax.read_term ctxt "qcompatible r q" *)
(* val t = Syntax.read_term ctxt "cregister (variable_concat x (variable_concat z y))" *)
(* val t = Syntax.read_term ctxt "ccompatible z y" *)
val str = "Cccompatible (CREGISTER_pair (CREGISTER_of z) (CREGISTER_of b)) (variable_concat count (variable_concat Find (variable_concat G (variable_concat H (variable_concat S hit))))) "
val t = Syntax.read_term ctxt str
in
val ctxt = ctxt
val t2 = Simplifier.rewrite ctxt (Thm.cterm_of ctxt t) |> Thm.cprop_of 
end
\<close>

(* lemma xxx: \<open>getter x (fst m) == getter (cregister_chain cFst x) m\<close>
  apply (rule eq_reflection)
  by (metis cFst_register cregister_chain_non_register2 getter_Fst getter_non_cregister getter_setter_same non_cregister setter_chain setter_getter_same) *)

ML \<open>
local
val t = Syntax.read_term ctxt "\<lambda>m::cl. getter x m = 1"
val t2 = add_index_to_expression ctxt true t
(* val t3 = Raw_Simplifier.rewrite_term (Proof_Context.theory_of ctxt) @{thms xxx} [] t2 *)
in
val ct2 = Thm.cterm_of ctxt t2
end
\<close>


ML \<open>
  expression_to_term ctxt (Syntax.read_term ctxt "\<lambda>m::cl2. qregister_chain qSnd q")
\<close>

lemma [program_fv]: True
  by simp

ML \<open>
val l = [("x", \<^typ>\<open>int\<close>)]
val ctxt = declare_abstract_program (ctxt, "A", l, l, [], 0)
val t = Syntax.read_term ctxt "x"
\<close>

thm program_fv

end
