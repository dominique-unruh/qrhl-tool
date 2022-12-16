theory Expressions
  imports Prog_Variables
begin

type_synonym 'a expression = \<open>cl \<Rightarrow> 'a\<close>
type_synonym 'a expression2 = \<open>cl2 \<Rightarrow> 'a\<close>
abbreviation (input) \<open>expression_eval e \<equiv> e\<close> (* LEGACY *)
abbreviation (input) \<open>map_expression2 f e1 e2 \<equiv> (\<lambda>m. f (e1 m) (e2 m))\<close> (* LEGACY *)
abbreviation (input) \<open>const_expression x \<equiv> (\<lambda>m. x)\<close> (* LEGACY *)
abbreviation (input) \<open>expression R f \<equiv> (\<lambda>m. f (getter R m))\<close>

(* TODO: not a sound concept, probably. The choice of fv for a given expression might not be unique. Or is it? *)
axiomatization fv_expression :: \<open>'a expression \<Rightarrow> CVARIABLE\<close>

lemma add_index_to_expression_aux1: \<open>getter x (fst m) \<equiv> getter (cregister_chain cFst x) m\<close>
  apply (rule eq_reflection)
  by (metis cFst_register cregister_chain_non_register2 getter_Fst getter_non_cregister getter_setter_same non_cregister setter_chain setter_getter_same)

lemma add_index_to_expression_aux2: \<open>getter x (snd m) \<equiv> getter (cregister_chain cSnd x) m\<close>
  apply (rule eq_reflection)
  by (metis add_index_to_expression_aux1 fst_swap getter_Fst_chain_swap)

ML_file \<open>expressions.ML\<close>

consts "expression_syntax" :: "'a \<Rightarrow> 'a expression" ("Expr[_]")
parse_translation \<open>[(\<^const_syntax>\<open>expression_syntax\<close>, fn ctx => fn [e] => Expressions.term_to_expression ctx dummyT e)]\<close>
hide_const expression_syntax

end
