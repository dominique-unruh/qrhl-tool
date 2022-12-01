theory Test_Squash_Sampling
  imports QRHL.Squash_Sampling UnitTest
begin

experiment
  fixes q r s t :: \<open>int qvariable\<close>
    and x y z :: \<open>int cvariable\<close>
  assumes [variable]: \<open>qregister \<lbrakk>q,r,s,t\<rbrakk>\<close>
  assumes [variable]: \<open>cregister \<lbrakk>x,y,z\<rbrakk>\<^sub>c\<close>
begin

(* TODO remove/move *)
lemma [simp]: \<open>qregister_conversion Q Q = qregister_id\<close> if \<open>qregister Q\<close>
  using that apply transfer
  apply auto
  sorry


lemma 
  assumes  \<open>qrhl A [qinit \<lbrakk>q\<rbrakk> Expr[U *\<^sub>V \<psi>]] [] B\<close>
  shows \<open>qrhl A [qinit \<lbrakk>q\<rbrakk> Expr[\<psi>], qapply \<lbrakk>q\<rbrakk> Expr[U]] [] B\<close>
  apply (tactic \<open>Squash_Sampling.squash_sampling_tac true \<^context> 1\<close>)
  using assms
  by simp

lemma \<open>qrhl A [qinit \<lbrakk>q,s,r\<rbrakk> Expr[ket (x,y,z)], qapply \<lbrakk>q,r\<rbrakk> Expr[U x \<otimes>\<^sub>o id_cblinfun]] [] B\<close>
  apply (tactic \<open>Squash_Sampling.squash_sampling_tac true \<^context> 1\<close>)
  oops


lemma 
  assumes  \<open>qrhl A [qapply \<lbrakk>q\<rbrakk> Expr[U o\<^sub>C\<^sub>L V]] [] B\<close>
  shows \<open>qrhl A [qapply \<lbrakk>q\<rbrakk> Expr[V], qapply \<lbrakk>q\<rbrakk> Expr[U]] [] B\<close>
  apply (tactic \<open>Squash_Sampling.squash_sampling_tac true \<^context> 1\<close>)
  using assms by simp

(* TODO move *)
lemma apply_qFst: \<open>apply_qregister qFst U = U \<otimes>\<^sub>o id_cblinfun\<close>
  sorry
(* TODO move *)
lemma apply_qSnd: \<open>apply_qregister qSnd U = id_cblinfun \<otimes>\<^sub>o U\<close>
  sorry

lemma 
  assumes \<open>qrhl A [qapply \<lbrakk>q, s\<rbrakk> Expr[U \<otimes>\<^sub>o id_cblinfun o\<^sub>C\<^sub>L V]] [] B\<close>
  shows \<open>qrhl A [qapply \<lbrakk>q, s\<rbrakk> Expr[V], qapply \<lbrakk>q\<rbrakk> Expr[U]] [] B\<close>
  apply (tactic \<open>Squash_Sampling.squash_sampling_tac true \<^context> 1\<close>)
  using assms by (simp add: apply_qFst)

lemma
  assumes \<open>qrhl A [qapply \<lbrakk>r, s, q\<rbrakk> Expr[id_cblinfun \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o U o\<^sub>C\<^sub>L V]] [] B\<close>
  shows \<open>qrhl A [qapply \<lbrakk>r, s, q\<rbrakk> Expr[V], qapply \<lbrakk>q\<rbrakk> Expr[U]] [] B\<close>
  apply (tactic \<open>Squash_Sampling.squash_sampling_tac true \<^context> 1\<close>)
  using assms by (simp add: apply_qFst apply_qSnd qregister_chain_apply)

lemma
  assumes \<open>qrhl A [qapply \<lbrakk>r, q\<rbrakk> Expr[U o\<^sub>C\<^sub>L id_cblinfun \<otimes>\<^sub>o V]] [] B\<close>
  shows \<open>qrhl A [qapply \<lbrakk>q\<rbrakk> Expr[V], qapply \<lbrakk>r,q\<rbrakk> Expr[U]] [] B\<close>
  apply (tactic \<open>Squash_Sampling.squash_sampling_tac true \<^context> 1\<close>)
  using assms by (simp add: apply_qSnd)

lemma
  shows \<open>qrhl A [qapply \<lbrakk>q,s\<rbrakk> Expr[V], qapply \<lbrakk>q,r\<rbrakk> Expr[U]] [] B\<close>
  apply (tactic \<open>Squash_Sampling.squash_sampling_tac true \<^context> 1\<close>)
  apply simp
  oops

end

end