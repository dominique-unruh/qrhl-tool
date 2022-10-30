theory Test_Squash_Sampling
  imports QRHL.Squash_Sampling UnitTest
begin

variables
quantum q :: int and
quantum r :: int and
quantum s :: int and
classical x :: int and
classical y :: int and
classical z :: int
begin

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

lemma 
  assumes \<open>qrhl A [qapply \<lbrakk>q, s\<rbrakk> Expr[U \<otimes>\<^sub>o id_cblinfun o\<^sub>C\<^sub>L V]] [] B\<close>
  shows \<open>qrhl A [qapply \<lbrakk>q, s\<rbrakk> Expr[V], qapply \<lbrakk>q\<rbrakk> Expr[U]] [] B\<close>
  apply (tactic \<open>Squash_Sampling.squash_sampling_tac true \<^context> 1\<close>)
  using assms by simp

lemma 
  assumes \<open>qrhl A [qapply \<lbrakk>r, s, q\<rbrakk> Expr[id_cblinfun \<otimes>\<^sub>o id_cblinfun \<otimes>\<^sub>o U o\<^sub>C\<^sub>L V]] [] B\<close>
  shows \<open>qrhl A [qapply \<lbrakk>r, s, q\<rbrakk> Expr[V], qapply \<lbrakk>q\<rbrakk> Expr[U]] [] B\<close>
  apply (tactic \<open>Squash_Sampling.squash_sampling_tac true \<^context> 1\<close>)
  using assms by simp

lemma 
  assumes \<open>qrhl A [qapply \<lbrakk>r, q\<rbrakk> Expr[U o\<^sub>C\<^sub>L id_cblinfun \<otimes>\<^sub>o V]] [] B\<close>
  shows \<open>qrhl A [qapply \<lbrakk>q\<rbrakk> Expr[V], qapply \<lbrakk>r,q\<rbrakk> Expr[U]] [] B\<close>
  apply (tactic \<open>Squash_Sampling.squash_sampling_tac true \<^context> 1\<close>)
  using assms by simp

lemma 
  shows \<open>qrhl A [qapply \<lbrakk>q,s\<rbrakk> Expr[V], qapply \<lbrakk>q,r\<rbrakk> Expr[U]] [] B\<close>
  apply (tactic \<open>Squash_Sampling.squash_sampling_tac true \<^context> 1\<close>)
  oops

end

end