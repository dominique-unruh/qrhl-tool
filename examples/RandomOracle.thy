theory RandomOracle
  imports QRHL
begin

typedecl x
typedecl y
typedecl r
instance x :: finite sorry
instance y :: finite sorry
instance r :: finite sorry

axiomatization Uoracle :: "('x\<Rightarrow>'y) \<Rightarrow> ('x*'y,'x*'y) bounded"
  where unitary_Uoracle[simp]: "unitary (Uoracle f)"
  for f :: "'x \<Rightarrow> 'y"

axiomatization \<pi> :: "r \<Rightarrow> y"
  where bij_pi: "bij \<pi>"

lemma l1 [simp]: "isometry (A*) \<Longrightarrow> A \<cdot> (A* \<cdot> B) = B" for B :: "(_,_) bounded"
  by (metis adjUU adjoint_twice timesOp_assoc times_idOp2)
lemma l2 [simp]: "(A \<otimes> B) \<cdot> ((A' \<otimes> B') \<cdot> C) = ((A\<cdot>A') \<otimes> (B\<cdot>B')) \<cdot> C" for A A' B B' C :: "(_,_) bounded"
  apply (subst timesOp_assoc[symmetric])
  by auto
lemma l3 [simp]: "isometry A \<Longrightarrow> A* \<cdot> (A \<cdot> B) = B" for B :: "(_,_) bounded"
  by (metis adjUU timesOp_assoc times_idOp2)

lemma Uora_twice:
  assumes [simp]: "declared_qvars \<lbrakk>x1,y1,x2,y2,qglobA1,qglobA2\<rbrakk>"
  assumes heq: "h1=h2"
  shows "(Uoracle h2*\<guillemotright>\<lbrakk>x2, y2\<rbrakk> \<cdot> (Uoracle h1*\<guillemotright>\<lbrakk>x1, y1\<rbrakk> \<cdot> \<lbrakk>qglobA1, x1, y1\<rbrakk> \<equiv>\<qq> \<lbrakk>qglobA2, x2, y2\<rbrakk>)) =
         \<lbrakk>qglobA1, x1, y1\<rbrakk> \<equiv>\<qq> \<lbrakk>qglobA2, x2, y2\<rbrakk>"
  apply (rewrite at "_* \<guillemotright> \<lbrakk>x1,y1\<rbrakk>" reorder_variables_hint_def[symmetric, where R="\<lbrakk>qglobA1,x1,y1\<rbrakk>"], simp)
  apply (rewrite at "_* \<guillemotright> \<lbrakk>x2,y2\<rbrakk>" reorder_variables_hint_def[symmetric, where R="\<lbrakk>qglobA2,x2,y2\<rbrakk>"], simp)
  by (simp add: heq timesOp_assoc)

lemma bij_comp[simp]: "bij (op\<circ> f) = bij f" sorry (* TODO: move to QRHL *)

end
