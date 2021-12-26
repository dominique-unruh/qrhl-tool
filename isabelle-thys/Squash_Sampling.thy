theory Squash_Sampling
  imports Programs Relational_Hoare
begin

(* TODO move *)
lemma assign_sample:
  shows "denotation (assign Q e) = denotation (sample Q (\<lambda>m. point_distr (e m)))"
  by (cheat assign_sample)

lemma squash_sampling: 
  fixes Q R d e
  assumes \<open>ccompatible Q R\<close>
  defines "\<And>z. e' z \<equiv> (\<lambda>m. e (setter Q z m))"
  defines "de \<equiv> (\<lambda>m. bind_distr (d m) (\<lambda>z. map_distr (\<lambda>y. (z,y)) (e' z m)))"
  shows "denotation (block [sample Q d, sample R e]) =
         denotation (sample \<lbrakk>Q,R\<rbrakk>\<^sub>c de)"
  by (cheat squash_sampling)

lemma squash_sampling_assign: 
  fixes Q R d e
  assumes \<open>ccompatible Q R\<close>
  defines "\<And>z. e' z \<equiv> (\<lambda>m. e (setter Q z m))"
  defines "de \<equiv> (\<lambda>m. map_distr (\<lambda>d. (d,e' d m)) (d m))"
  shows "denotation (block [sample Q d, assign R e]) =
         denotation (sample \<lbrakk>Q,R\<rbrakk>\<^sub>c de)"
proof -
  have \<open>denotation (block [sample Q d, assign R e])
      = denotation (block [sample Q d, sample R (\<lambda>m. point_distr (e m))])\<close>
    by (auto simp: denotation_block assign_sample)
  also have \<open>\<dots> = denotation (sample \<lbrakk>Q,R\<rbrakk>\<^sub>c de)\<close>
    by (simp add: squash_sampling assms)
  finally show ?thesis
    by -
qed

lemma squash_assign_sampling: 
  fixes Q R d e
  assumes \<open>ccompatible Q R\<close>
  defines "\<And>z. e' z \<equiv> (\<lambda>m. e (setter Q z m))"
  defines "de \<equiv> (\<lambda>m. let z = d m in map_distr (\<lambda>y. (z,y)) (e' z m))"
  shows "denotation (block [assign Q d, sample R e]) =
         denotation (sample \<lbrakk>Q,R\<rbrakk>\<^sub>c de)"
proof -
  have \<open>denotation (block [assign Q d, sample R e])
      = denotation (block [sample Q (\<lambda>m. point_distr (d m)), sample R e])\<close>
    by (auto simp: denotation_block assign_sample)
  also have \<open>\<dots> = denotation (sample \<lbrakk>Q,R\<rbrakk>\<^sub>c de)\<close>
    by (simp add: squash_sampling assms Let_def)
  finally show ?thesis
    by -
qed

lemma squash_assign: 
  fixes Q R d e
  assumes \<open>ccompatible Q R\<close>
  defines "\<And>z. e' z \<equiv> (\<lambda>m. e (setter Q z m))"
  defines "de \<equiv> (\<lambda>m. (d m, e' (d m) m))"
  shows "denotation (block [assign Q d, assign R e]) =
         denotation (assign \<lbrakk>Q,R\<rbrakk>\<^sub>c de)"
proof -
  have \<open>denotation (block [assign Q d, assign R e])
      = denotation (block [sample Q (\<lambda>m. point_distr (d m)), sample R (\<lambda>m. point_distr (e m))])\<close>
    by (auto simp: denotation_block assign_sample)
  also have \<open>\<dots> = denotation (assign \<lbrakk>Q,R\<rbrakk>\<^sub>c de)\<close>
    by (simp add: squash_sampling assms assign_sample Let_def)
  finally show ?thesis
    by -
qed

lemma squash_sampling_left_ss_tac:
  assumes left0: "left0 @ [sample Q d, sample R e] = left"
  defines "\<And>z. e' z \<equiv> (\<lambda>m. e (setter Q z m))"
  defines "de \<equiv> (\<lambda>m. bind_distr (d m) (\<lambda>z. map_distr (\<lambda>y. (z,y)) (e' z m)))"
  assumes left': "left' = left0 @ [sample \<lbrakk>Q,R\<rbrakk>\<^sub>c de]"
  assumes \<open>ccompatible Q R\<close>
  assumes qrhl: "qrhl A left' right B"
  shows "qrhl A left right B"
proof -
  have "denotation (block [sample Q d, sample R e]) = denotation (sample \<lbrakk>Q,R\<rbrakk>\<^sub>c de)"
    unfolding de_def e'_def using \<open>ccompatible Q R\<close> by (rule squash_sampling)
  then have "denotation (block left) = denotation (block left')"
    unfolding left' left0[symmetric] denotation_block by auto
  with qrhl show ?thesis
    using qrhl_denotation_replace by blast 
qed


lemma squash_sampling_left_as_tac:
  assumes left0: "left0 @ [assign Q d, sample R e] = left"
  defines "\<And>z. e' z \<equiv> (\<lambda>m. e (setter Q z m))"
  defines "de \<equiv> (\<lambda>m. let z = d m in map_distr (\<lambda>y. (z,y)) (e' z m))"
  assumes left': "left' = left0 @ [sample \<lbrakk>Q,R\<rbrakk>\<^sub>c de]"
  assumes \<open>ccompatible Q R\<close>
  assumes qrhl: "qrhl A left' right B"
  shows "qrhl A left right B"
proof -
  have "denotation (block [assign Q d, sample R e]) = denotation (sample \<lbrakk>Q,R\<rbrakk>\<^sub>c de)"
    unfolding de_def e'_def using \<open>ccompatible Q R\<close> by (rule squash_assign_sampling)
  then have "denotation (block left) = denotation (block left')"
    unfolding left' left0[symmetric] denotation_block by auto
  with qrhl show ?thesis
    using qrhl_denotation_replace by blast 
qed

lemma squash_sampling_left_sa_tac:
  assumes left0: "left0 @ [sample Q d, assign R e] = left"
  defines "\<And>z. e' z \<equiv> (\<lambda>m. e (setter Q z m))"
  defines "de \<equiv> (\<lambda>m. map_distr (\<lambda>d. (d,e' d m)) (d m))"
  assumes left': "left' = left0 @ [sample \<lbrakk>Q,R\<rbrakk>\<^sub>c de]"
  assumes \<open>ccompatible Q R\<close>
  assumes qrhl: "qrhl A left' right B"
  shows "qrhl A left right B"
proof -
  have "denotation (block [sample Q d, assign R e]) = denotation (sample \<lbrakk>Q,R\<rbrakk>\<^sub>c de)"
    unfolding de_def e'_def using \<open>ccompatible Q R\<close> by (rule squash_sampling_assign)
  then have "denotation (block left) = denotation (block left')"
    unfolding left' left0[symmetric] denotation_block by auto
  with qrhl show ?thesis
    using qrhl_denotation_replace by blast 
qed
  
lemma squash_sampling_left_aa_tac:
  assumes left0: "left0 @ [assign Q d, assign R e] = left"
  defines "\<And>z. e' z \<equiv> (\<lambda>m. e (setter Q z m))"
  defines "de \<equiv> (\<lambda>m. (d m, e' (d m) m))"
  assumes left': "left' = left0 @ [assign \<lbrakk>Q,R\<rbrakk>\<^sub>c de]"
  assumes \<open>ccompatible Q R\<close>
  assumes qrhl: "qrhl A left' right B"
  shows "qrhl A left right B"
proof -
  have "denotation (block [assign Q d, assign R e]) = denotation (assign \<lbrakk>Q,R\<rbrakk>\<^sub>c de)"
    unfolding de_def e'_def using \<open>ccompatible Q R\<close> by (rule squash_assign)
  then have "denotation (block left) = denotation (block left')"
    unfolding left' left0[symmetric] denotation_block by auto
  with qrhl show ?thesis
    using qrhl_denotation_replace by blast
qed

lemma squash_sampling_right_ss_tac:
  assumes right0: "right0 @ [sample Q d, sample R e] = right"
  defines "\<And>z. e' z \<equiv> (\<lambda>m. e (setter Q z m))"
  defines "de \<equiv> (\<lambda>m. bind_distr (d m) (\<lambda>z. map_distr (\<lambda>y. (z,y)) (e' z m)))"
  assumes right': "right' = right0 @ [sample \<lbrakk>Q,R\<rbrakk>\<^sub>c de]"
  assumes \<open>ccompatible Q R\<close>
  assumes qrhl: "qrhl A left right' B"
  shows "qrhl A left right B"
proof -
  have "denotation (block [sample Q d, sample R e]) = denotation (sample \<lbrakk>Q,R\<rbrakk>\<^sub>c de)"
    unfolding de_def e'_def using \<open>ccompatible Q R\<close> by (rule squash_sampling)
  then have "denotation (block right) = denotation (block right')"
    unfolding right' right0[symmetric] denotation_block by auto
  with qrhl show ?thesis
    using qrhl_denotation_replace by blast 
qed

lemma squash_sampling_right_as_tac:
  assumes right0: "right0 @ [assign Q d, sample R e] = right"
  defines "\<And>z. e' z \<equiv> (\<lambda>m. e (setter Q z m))"
  defines "de \<equiv> (\<lambda>m. let z = d m in map_distr (\<lambda>y. (z,y)) (e' z m))"
  assumes right': "right' = right0 @ [sample \<lbrakk>Q,R\<rbrakk>\<^sub>c de]"
  assumes \<open>ccompatible Q R\<close>
  assumes qrhl: "qrhl A left right' B"
  shows "qrhl A left right B"
proof -
  have "denotation (block [assign Q d, sample R e]) = denotation (sample \<lbrakk>Q,R\<rbrakk>\<^sub>c de)"
    unfolding de_def e'_def using \<open>ccompatible Q R\<close> by (rule squash_assign_sampling)
  then have "denotation (block right) = denotation (block right')"
    unfolding right' right0[symmetric] denotation_block by auto
  with qrhl show ?thesis
    using qrhl_denotation_replace by blast 
qed

lemma squash_sampling_right_sa_tac:
  assumes right0: "right0 @ [sample Q d, assign R e] = right"
  defines "\<And>z. e' z \<equiv> (\<lambda>m. e (setter Q z m))"
  defines "de \<equiv> (\<lambda>m. map_distr (\<lambda>d. (d,e' d m)) (d m))"
  assumes right': "right' = right0 @ [sample \<lbrakk>Q,R\<rbrakk>\<^sub>c de]"
  assumes \<open>ccompatible Q R\<close>
  assumes qrhl: "qrhl A left right' B"
  shows "qrhl A left right B"
proof -
  have "denotation (block [sample Q d, assign R e]) = denotation (sample \<lbrakk>Q,R\<rbrakk>\<^sub>c de)"
    unfolding de_def e'_def using \<open>ccompatible Q R\<close> by (rule squash_sampling_assign)
  then have "denotation (block right) = denotation (block right')"
    unfolding right' right0[symmetric] denotation_block by auto
  with qrhl show ?thesis
    using qrhl_denotation_replace by blast 
qed

lemma squash_sampling_right_aa_tac:
  assumes right0: "right0 @ [assign Q d, assign R e] = right"
  defines "\<And>z. e' z \<equiv> (\<lambda>m. e (setter Q z m))"
  defines "de \<equiv> (\<lambda>m. (d m, e' (d m) m))"
  assumes right': "right' = right0 @ [assign \<lbrakk>Q,R\<rbrakk>\<^sub>c de]"
  assumes \<open>ccompatible Q R\<close>
  assumes qrhl: "qrhl A left right' B"
  shows "qrhl A left right B"
proof -
  have "denotation (block [assign Q d, assign R e]) = denotation (assign \<lbrakk>Q,R\<rbrakk>\<^sub>c de)"
    unfolding de_def e'_def using \<open>ccompatible Q R\<close> by (rule squash_assign)
  then have "denotation (block right) = denotation (block right')"
    unfolding right' right0[symmetric] denotation_block by auto
  with qrhl show ?thesis
    using qrhl_denotation_replace by blast 
qed


ML \<open>
structure Squash_Sampling = struct

fun squash_sampling_tac left ctxt =
  resolve_tac ctxt (if left then 
      @{thms squash_sampling_left_ss_tac squash_sampling_left_sa_tac squash_sampling_left_as_tac squash_sampling_left_aa_tac} 
    else 
      @{thms squash_sampling_right_ss_tac squash_sampling_right_sa_tac squash_sampling_right_as_tac squash_sampling_right_aa_tac})
  THEN' Misc.match_list_tac ctxt
  (* THEN' Expressions.subst_expression_tac ctxt *)
  (* THEN' Expressions.map_expression_tac ctxt *)
  THEN' Misc.append_list_tac ctxt
  THEN' Prog_Variables.distinct_vars_tac ctxt
end\<close>

experiment
  fixes x :: \<open>bit cvariable\<close> and y :: \<open>bit cvariable\<close> and z :: \<open>bit cvariable\<close> and w :: \<open>bit cvariable\<close>
  assumes [variable,simp]: \<open>cregister x\<close> \<open>cregister y\<close> \<open>cregister z\<close> \<open>cregister w\<close>
  assumes [simp]: \<open>mutually ccompatible (x,y,z,w)\<close>
begin

schematic_goal xxx: "qrhl A
 [sample z Expr[uniform UNIV], sample \<lbrakk>x\<rbrakk> Expr[uniform {1,z}], sample \<lbrakk>y\<rbrakk> Expr[uniform {x,z}]]
 [assign \<lbrakk>\<rbrakk>\<^sub>c Expr[()]] Expr[Cla[x1=y2]]"
  apply (tactic \<open>Squash_Sampling.squash_sampling_tac true \<^context> 1\<close>)
  apply (tactic \<open>Squash_Sampling.squash_sampling_tac true \<^context> 1\<close>)
  apply simp
  oops

schematic_goal xxx: "qrhl A
 [assign \<lbrakk>w\<rbrakk> Expr[3], sample \<lbrakk>z\<rbrakk> Expr[uniform UNIV], assign \<lbrakk>x\<rbrakk> Expr[1], assign \<lbrakk>y\<rbrakk> Expr[x]]
 [assign \<lbrakk>\<rbrakk>\<^sub>c Expr[()]] Expr[Cla[x1=y2]]"
  apply (tactic \<open>Squash_Sampling.squash_sampling_tac true \<^context> 1\<close>)
  apply simp
  apply (tactic \<open>Squash_Sampling.squash_sampling_tac true \<^context> 1\<close>)
  (* apply simp *)
  apply (tactic \<open>Squash_Sampling.squash_sampling_tac true \<^context> 1\<close>)
  apply simp
  oops

schematic_goal xxx: "qrhl A
     [assign \<lbrakk>\<rbrakk>\<^sub>c Expr[()]] 
     [assign \<lbrakk>w\<rbrakk> Expr[0], sample \<lbrakk>z\<rbrakk> Expr[uniform UNIV], assign \<lbrakk>x\<rbrakk> Expr[1], assign \<lbrakk>y\<rbrakk> Expr[x]]
     Expr[Cla[x1=y2]]"
  apply (tactic \<open>Squash_Sampling.squash_sampling_tac false \<^context> 1\<close>)
  apply simp
  apply (tactic \<open>Squash_Sampling.squash_sampling_tac false \<^context> 1\<close>)
  (* apply simp *)
  apply (tactic \<open>Squash_Sampling.squash_sampling_tac false \<^context> 1\<close>)
  apply simp
  oops

end

end
