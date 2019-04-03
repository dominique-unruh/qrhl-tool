theory Squash_Sampling
  imports Programs Relational_Hoare
begin

(* TODO move *)
axiomatization denotation :: "program \<Rightarrow> program_state \<Rightarrow> program_state"

(* TODO move *)
lemma denotation_block: "denotation (block ps) = fold denotation ps"
  by (cheat denotation_block)

(* TODO move *)
lemma qrhl_denotation_replace:
  assumes "denotation (block c) = denotation (block c')"
    and "denotation (block d) = denotation (block d')"
  shows "qrhl A c d B = qrhl A c' d' B"
  by (cheat qrhl_denotation_replace)

(* TODO move *)
lift_definition "bind_distr" :: "'a distr \<Rightarrow> ('a \<Rightarrow> 'b distr) \<Rightarrow> 'b distr" 
  is "\<lambda>(\<mu>::'a\<Rightarrow>real) (f::'a\<Rightarrow>'b\<Rightarrow>real) x. \<Sum>\<^sub>a y\<in>UNIV. \<mu> y * f y x"
  by (cheat bind_distr)

lemma squash_sampling: 
  fixes Q R d e
  defines "\<And>z. e' z \<equiv> subst_expression (substitute_vars Q (const_expression z)) e"
  defines "de \<equiv> map_expression2' (\<lambda>d e. bind_distr d (\<lambda>z. map_distr (\<lambda>y. (z,y)) (e z))) d e'"
  shows "denotation (block [sample Q d, sample R e]) =
         denotation (sample (variable_concat Q R) de)"
  by (cheat squash_sampling)

lemma squash_sampling_left_tac:
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

lemma squash_sampling_right_tac:
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

ML \<open>
structure Squash_Sampling = struct

fun squash_sampling_tac left ctxt =
  resolve_tac ctxt (if left then @{thms squash_sampling_left_tac} else @{thms squash_sampling_right_tac})
  THEN' Misc.match_list_tac ctxt
  THEN' Expressions.subst_expression_tac ctxt
  THEN' Expressions.map_expression_tac ctxt
  THEN' Misc.append_list_tac ctxt
end\<close>

(* TODO remove *)
variables classical x :: bit and classical y :: bit and classical z ::bit begin
schematic_goal xxx: "qrhl A
 [sample \<lbrakk>var_z\<rbrakk> Expr[uniform UNIV], sample \<lbrakk>var_x\<rbrakk> Expr[uniform {1,z}], sample \<lbrakk>var_y\<rbrakk> Expr[uniform {x,z}]]
 [assign \<lbrakk>\<rbrakk> Expr[()]] Expr[Cla[x1=y2]]"
  apply (tactic \<open>Squash_Sampling.squash_sampling_tac true \<^context> 1\<close>)
  apply (tactic \<open>Squash_Sampling.squash_sampling_tac true \<^context> 1\<close>)
  apply simp
  oops
end

end