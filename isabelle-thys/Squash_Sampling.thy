theory Squash_Sampling
  imports Programs Relational_Hoare
begin

lemma squash_sampling:
  fixes Q R d e
  assumes "\<And>z. e' z = subst_expression (substitute_vars Q (const_expression z)) e"
  assumes "de = map_expression2' (\<lambda>d e. bind_distr d (\<lambda>z. map_distr (\<lambda>y. (z,y)) (e z))) d e'"
  shows "denotation (block [sample Q d, sample R e]) =
         denotation (sample (variable_concat Q R) de)"
  by (cheat squash_sampling)

lemma squash_sampling_assign: 
  fixes Q R d e
  assumes "\<And>z. e' z = subst_expression (substitute_vars Q (const_expression z)) e"
  assumes "de = map_expression2' (\<lambda>d e. map_distr (\<lambda>d. (d,e d)) d) d e'"
  shows "denotation (block [sample Q d, assign R e]) =
         denotation (sample (variable_concat Q R) de)"
    by (cheat squash_sampling_assign)

lemma squash_assign_sampling: 
  fixes Q R d e
  assumes "\<And>z. e' z = subst_expression (substitute_vars Q (const_expression z)) e"
  assumes "de = map_expression2' (\<lambda>d e. bind_distr (point_distr d) (\<lambda>z. map_distr (\<lambda>y. (z,y)) (e z))) d e'"
  shows "denotation (block [assign Q d, sample R e]) =
         denotation (sample (variable_concat Q R) de)"
  by (cheat squash_sampling_assign)

lemma squash_assign: 
  fixes Q R d e
  assumes "\<And>z. e' z = subst_expression (substitute_vars Q (const_expression z)) e"
  assumes "de = map_expression2' (\<lambda>d e. (d,e d)) d e'"
  shows "denotation (block [assign Q d, assign R e]) =
         denotation (assign (variable_concat Q R) de)"
  by (cheat squash_assign)

lemma squash_qinit_qapply:
  assumes \<open>distinct_qvars Q\<close>
  assumes \<open>distinct_qvars R\<close>
  assumes \<open>\<And>U::_ \<Rightarrow>\<^sub>C\<^sub>L _. liftOp (trafo U) Q = liftOp U R\<close>
  assumes \<open>U'\<psi> = map_expression2 (\<lambda>U \<psi>. trafo U *\<^sub>V \<psi>) U \<psi>\<close>
  shows \<open>denotation (block [qinit Q \<psi>, qapply R U])
       = denotation (qinit Q U'\<psi>)\<close>
  by (cheat squash_qinit_qapply)

lemma squash_qapply_qapply:
  assumes \<open>distinct_qvars Q\<close>
  assumes \<open>distinct_qvars R\<close>
  assumes \<open>\<And>U V::_ \<Rightarrow>\<^sub>C\<^sub>L _. liftOp (trafoU U) QR = liftOp U Q \<and> liftOp (trafoV V) QR = liftOp V R\<close>
  assumes \<open>UV = map_expression2 (\<lambda>U V. trafoV V o\<^sub>C\<^sub>L trafoU U) U V\<close>
  shows \<open>denotation (block [qapply Q U, qapply R V])
       = denotation (qapply QR UV)\<close>
  by (cheat squash_qapply_qapply)

(* lemma assign_sample:
  shows "denotation (assign Q e) = denotation (sample Q (map_expression (\<lambda>x. uniform {x}) e))"
  by (cheat assign_sample) *)

lemma squash_left_qrhl:
  assumes left0: "left0 @ [c1, c2] = left"
  assumes deneq: "denotation (block [c1, c2]) = denotation c12"
  assumes left': "left' = left0 @ [c12]"
  assumes qrhl: "qrhl A left' right B"
  shows "qrhl A left right B"
proof -
   have "denotation (block left) = denotation (block left')"
     using deneq unfolding left' left0[symmetric] denotation_block by auto
  with qrhl show ?thesis
    using qrhl_denotation_replace by blast 
qed

lemma squash_left_deneq:
  assumes left0: "left0 @ [c1, c2] = left"
  assumes deneq: "denotation (block [c1, c2]) = denotation c12"
  assumes left': "left' = left0 @ [c12]"
  assumes newgoal: "denotation (block left') = denotation (block right)"
  shows "denotation (block left) = denotation (block right)"
proof -
   have "denotation (block left) = denotation (block left')"
     using deneq unfolding left' left0[symmetric] denotation_block by auto
   with newgoal show ?thesis
     by simp
qed


lemma squash_right_qrhl:
  assumes right0: "right0 @ [c1, c2] = right"
  assumes deneq: "denotation (block [c1, c2]) = denotation c12"
  assumes right': "right' = right0 @ [c12]"
  assumes qrhl: "qrhl A left right' B"
  shows "qrhl A left right B"
proof -
   have "denotation (block right) = denotation (block right')"
     using deneq unfolding right' right0[symmetric] denotation_block by auto
  with qrhl show ?thesis
    using qrhl_denotation_replace by blast 
qed

lemma squash_right_deneq:
  assumes right0: "right0 @ [c1, c2] = right"
  assumes deneq: "denotation (block [c1, c2]) = denotation c12"
  assumes right': "right' = right0 @ [c12]"
  assumes newgoal: "denotation (block left) = denotation (block right')"
  shows "denotation (block left) = denotation (block right)"
proof -
   have "denotation (block right) = denotation (block right')"
     using deneq unfolding right' right0[symmetric] denotation_block by auto
   with newgoal show ?thesis
     by simp
qed

(* lemma squash_sampling_left_ss_tac:
  assumes left0: "left0 @ [sample Q d, sample R e] = left"
  assumes e': "\<And>z. e' z = subst_expression (substitute_vars Q (const_expression z)) e"
  assumes de: "de = map_expression2' (\<lambda>d e. bind_distr d (\<lambda>z. map_distr (\<lambda>y. (z,y)) (e z))) d e'"
  assumes left': "left' = left0 @ [sample (variable_concat Q R) de]"
  assumes qrhl: "qrhl A left' right B"
  shows "qrhl A left right B"
proof -
  have "denotation (block [sample Q d, sample R e]) = denotation (sample (variable_concat Q R) de)"
    unfolding de e' by (rule squash_sampling)
  then have "denotation (block left) = denotation (block left')"
    unfolding left' left0[symmetric] denotation_block by auto
  with qrhl show ?thesis
    using qrhl_denotation_replace by blast 
qed


lemma squash_sampling_left_as_tac:
  assumes left0: "left0 @ [assign Q d, sample R e] = left"
  assumes e': "\<And>z. e' z = subst_expression (substitute_vars Q (const_expression z)) e"
  assumes de: "de = map_expression2' (\<lambda>d e. bind_distr (point_distr d) (\<lambda>z. map_distr (\<lambda>y. (z,y)) (e z))) d e'"
  assumes left': "left' = left0 @ [sample (variable_concat Q R) de]"
  assumes qrhl: "qrhl A left' right B"
  shows "qrhl A left right B"
proof -
  have "denotation (block [assign Q d, sample R e]) = denotation (sample (variable_concat Q R) de)"
    unfolding de e' by (rule squash_assign_sampling)
  then have "denotation (block left) = denotation (block left')"
    unfolding left' left0[symmetric] denotation_block by auto
  with qrhl show ?thesis
    using qrhl_denotation_replace by blast 
qed

lemma squash_sampling_left_sa_tac:
  assumes left0: "left0 @ [sample Q d, assign R e] = left"
  assumes e': "\<And>z. e' z = subst_expression (substitute_vars Q (const_expression z)) e"
  assumes de: "de = map_expression2' (\<lambda>d e. map_distr (\<lambda>d. (d,e d)) d) d e'"
  assumes left': "left' = left0 @ [sample (variable_concat Q R) de]"
  assumes qrhl: "qrhl A left' right B"
  shows "qrhl A left right B"
proof -
  have "denotation (block [sample Q d, assign R e]) = denotation (sample (variable_concat Q R) de)"
    unfolding de e' by (rule squash_sampling_assign)
  then have "denotation (block left) = denotation (block left')"
    unfolding left' left0[symmetric] denotation_block by auto
  with qrhl show ?thesis
    using qrhl_denotation_replace by blast 
qed
  
lemma squash_sampling_left_aa_tac:
  assumes left0: "left0 @ [assign Q d, assign R e] = left"
  assumes e': "\<And>z. e' z = subst_expression (substitute_vars Q (const_expression z)) e"
  assumes de: "de = map_expression2' (\<lambda>d e. (d,e d)) d e'"
  assumes left': "left' = left0 @ [assign (variable_concat Q R) de]"
  assumes qrhl: "qrhl A left' right B"
  shows "qrhl A left right B"
proof -
  have "denotation (block [assign Q d, assign R e]) = denotation (assign (variable_concat Q R) de)"
    unfolding de e' by (rule squash_assign)
  then have "denotation (block left) = denotation (block left')"
    unfolding left' left0[symmetric] denotation_block by auto
  with qrhl show ?thesis
    using qrhl_denotation_replace by blast 
qed

lemma squash_sampling_right_ss_tac:
  assumes right0: "right0 @ [sample Q d, sample R e] = right"
  assumes e': "\<And>z. e' z = subst_expression (substitute_vars Q (const_expression z)) e"
  assumes de: "de = map_expression2' (\<lambda>d e. bind_distr d (\<lambda>z. map_distr (\<lambda>y. (z,y)) (e z))) d e'"
  assumes right': "right' = right0 @ [sample (variable_concat Q R) de]"
  assumes qrhl: "qrhl A left right' B"
  shows "qrhl A left right B"
proof -
  have "denotation (block [sample Q d, sample R e]) = denotation (sample (variable_concat Q R) de)"
    unfolding de e' by (rule squash_sampling)
  then have "denotation (block right) = denotation (block right')"
    unfolding right' right0[symmetric] denotation_block by auto
  with qrhl show ?thesis
    using qrhl_denotation_replace by blast 
qed

lemma squash_sampling_right_as_tac:
  assumes right0: "right0 @ [assign Q d, sample R e] = right"
  assumes e': "\<And>z. e' z = subst_expression (substitute_vars Q (const_expression z)) e"
  assumes de: "de = map_expression2' (\<lambda>d e. bind_distr (point_distr d) (\<lambda>z. map_distr (\<lambda>y. (z,y)) (e z))) d e'"
  assumes right': "right' = right0 @ [sample (variable_concat Q R) de]"
  assumes qrhl: "qrhl A left right' B"
  shows "qrhl A left right B"
proof -
  have "denotation (block [assign Q d, sample R e]) = denotation (sample (variable_concat Q R) de)"
    unfolding de e' by (rule squash_assign_sampling)
  then have "denotation (block right) = denotation (block right')"
    unfolding right' right0[symmetric] denotation_block by auto
  with qrhl show ?thesis
    using qrhl_denotation_replace by blast 
qed

lemma squash_sampling_right_sa_tac:
  assumes right0: "right0 @ [sample Q d, assign R e] = right"
  assumes e': "\<And>z. e' z = subst_expression (substitute_vars Q (const_expression z)) e"
  assumes de: "de = map_expression2' (\<lambda>d e. map_distr (\<lambda>d. (d,e d)) d) d e'"
  assumes right': "right' = right0 @ [sample (variable_concat Q R) de]"
  assumes qrhl: "qrhl A left right' B"
  shows "qrhl A left right B"
proof -
  have "denotation (block [sample Q d, assign R e]) = denotation (sample (variable_concat Q R) de)"
    unfolding de e' by (rule squash_sampling_assign)
  then have "denotation (block right) = denotation (block right')"
    unfolding right' right0[symmetric] denotation_block by auto
  with qrhl show ?thesis
    using qrhl_denotation_replace by blast 
qed

lemma squash_sampling_right_aa_tac:
  assumes right0: "right0 @ [assign Q d, assign R e] = right"
  assumes e': "\<And>z. e' z = subst_expression (substitute_vars Q (const_expression z)) e"
  assumes de: "de = map_expression2' (\<lambda>d e. (d,e d)) d e'"
  assumes right': "right' = right0 @ [assign (variable_concat Q R) de]"
  assumes qrhl: "qrhl A left right' B"
  shows "qrhl A left right B"
proof -
  have "denotation (block [assign Q d, assign R e]) = denotation (assign (variable_concat Q R) de)"
    unfolding de e' by (rule squash_assign)
  then have "denotation (block right) = denotation (block right')"
    unfolding right' right0[symmetric] denotation_block by auto
  with qrhl show ?thesis
    using qrhl_denotation_replace by blast 
qed *)

thm squash_sampling squash_sampling_assign squash_assign_sampling squash_assign

ML \<open>
structure Squash_Sampling = struct

fun squash_sampling_focused_tac ctxt = 
    (resolve_tac ctxt @{thms squash_sampling squash_sampling_assign squash_assign_sampling squash_assign}
     THEN' Expressions.subst_expression_tac ctxt
     THEN' Expressions.map_expression_tac ctxt)
  ORELSE'
    (resolve_tac ctxt @{thms squash_qinit_qapply}
     THEN' QRHL.distinct_qvars_tac ctxt
     THEN' QRHL.distinct_qvars_tac ctxt
     THEN' QRHL.extend_op_vars_tac ctxt
     THEN' Expressions.map_expression_tac ctxt)

fun squash_sampling_tac left ctxt =
  resolve_tac ctxt (if left then @{thms squash_left_qrhl squash_left_deneq}
                            else @{thms squash_right_qrhl squash_right_deneq})
  THEN' Misc.match_list_tac ctxt
  THEN' squash_sampling_focused_tac ctxt
  THEN' Misc.append_list_tac ctxt

(*   resolve_tac ctxt (if left then 
      @{thms squash_sampling_left_ss_tac squash_sampling_left_sa_tac squash_sampling_left_as_tac squash_sampling_left_aa_tac} 
    else 
      @{thms squash_sampling_right_ss_tac squash_sampling_right_sa_tac squash_sampling_right_as_tac squash_sampling_right_aa_tac})
  THEN' Misc.match_list_tac ctxt
  THEN' Expressions.subst_expression_tac ctxt
  THEN' Expressions.map_expression_tac ctxt
  THEN' Misc.append_list_tac ctxt *)
end\<close>


end
