theory RandomOracle
  imports QRHL.QRHL
begin

section \<open>Specification\<close>

text \<open>We declare three types x,y,r. All three types are finite, and on y, + is the XOR operation.\<close>

declare_variable_type x :: finite
declare_variable_type y :: "{finite,xor_group}"
declare_variable_type r :: finite

text \<open>\<pi> is an arbitrary bijection from r to y\<close>

axiomatization \<pi> :: "r \<Rightarrow> y"
  where bij_pi: "bij \<pi>"

section \<open>Lemmas\<close>


text \<open>Three auxiliary lemmas\<close>

lemma l1: "isometry (A*) \<Longrightarrow> A o\<^sub>C\<^sub>L (A* o\<^sub>C\<^sub>L B) = B" for B :: "(_,_) l2bounded"
  by (metis isometryD double_adj cblinfun_compose_assoc cblinfun_compose_id_left)
lemma l2: "(A \<otimes>\<^sub>o B) o\<^sub>C\<^sub>L ((A' \<otimes>\<^sub>o B') o\<^sub>C\<^sub>L C) = ((A o\<^sub>C\<^sub>L A') \<otimes>\<^sub>o (B o\<^sub>C\<^sub>L B')) o\<^sub>C\<^sub>L C"
  apply (subst cblinfun_compose_assoc[symmetric])
  by (auto simp: comp_tensor_op)
lemma l3: "isometry A \<Longrightarrow> A* o\<^sub>C\<^sub>L (A o\<^sub>C\<^sub>L B) = B"
  by (metis isometryD cblinfun_compose_assoc cblinfun_compose_id_left)

lemma Uora_twice: 
  \<comment> \<open>This lemma is needed in the proof for simplifying a quantum equality with two Uoracle's applied to it\<close>

  assumes [simp]: "declared_qvars \<lbrakk>x1,y1,x2,y2,qglobA1,qglobA2\<rbrakk>"
  assumes heq: "h1=h2"
  shows "Uoracle h2\<guillemotright>\<lbrakk>x2, y2\<rbrakk> *\<^sub>S Uoracle h1\<guillemotright>\<lbrakk>x1, y1\<rbrakk> *\<^sub>S \<lbrakk>qglobA1, x1, y1\<rbrakk> \<equiv>\<qq> \<lbrakk>qglobA2, x2, y2\<rbrakk>
      =  \<lbrakk>qglobA1, x1, y1\<rbrakk> \<equiv>\<qq> \<lbrakk>qglobA2, x2, y2\<rbrakk>"
  apply (rewrite at "Uoracle _ \<guillemotright> \<lbrakk>x1,y1\<rbrakk>" reorder_variables_hint_def[symmetric, where R="\<lbrakk>qglobA1,x1,y1\<rbrakk>"])
  apply (rewrite at "Uoracle _ \<guillemotright> \<lbrakk>x2,y2\<rbrakk>" reorder_variables_hint_def[symmetric, where R="\<lbrakk>qglobA2,x2,y2\<rbrakk>"])
  by (simp add: l1 l2 l3 heq cblinfun_compose_assoc)

end
