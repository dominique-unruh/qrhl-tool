theory Tactics
  imports Encoding
begin

lemma seq:
  assumes "c = c1@c2" and "d = d1@d2"
  assumes "qrhl A c1 d1 B"
  and "qrhl B c2 d2 C"
  shows "qrhl A c d C"
  sorry

lemma wp_skip:
  shows "qrhl B [] [] B"
  sorry

lemma wp1_assign:
  fixes A B x e
  defines "A \<equiv> subst_expression (substitute1 (index_var True x) (index_expression True e)) B"
  shows "qrhl A [assign x e] [] B"
  sorry

lemma wp2_assign:
  fixes A B x e
  defines "A \<equiv> subst_expression (substitute1 (index_var False x) (index_expression False e)) B"
  shows "qrhl A [] [assign x e] B"
  sorry

lemma wp1_sample:
  fixes A B x e
  defines "e' \<equiv> index_expression True e"
  defines "B' z \<equiv> subst_expression (substitute1 (index_var True x) (const_expression z)) B"
  defines "A \<equiv> map_expression2' (\<lambda>e' B'. Cla[weight e' = 1] \<sqinter> (INF z:supp e'. B' z)) e' B'"
  shows "qrhl A [sample x e] [] B"
  sorry

lemma wp2_sample:
  fixes A B x e
  defines "e' \<equiv> index_expression False e"
  defines "B' z \<equiv> subst_expression (substitute1 (index_var False x) (const_expression z)) B"
  defines "A \<equiv> map_expression2' (\<lambda>e' B'. Cla[weight e' = 1] \<sqinter> (INF z:supp e'. B' z)) e' B'"
  shows "qrhl A [] [sample x e] B"
  sorry

lemma wp1_block:
  assumes "qrhl A p [] B"
  shows "qrhl A [block p] [] B"
  sorry

lemma wp2_block:
  assumes "qrhl A [] p B"
  shows "qrhl A [] [block p] B"
  sorry

ML_file "tactics.ML"

method_setup seq = {*
  Scan.lift Parse.nat -- Scan.lift Parse.nat -- Scan.lift Parse.term >> (fn ((i,j),B) => fn ctx =>
    SIMPLE_METHOD (Tactics.seq_tac i j (Encoding.read_predicate ctx B) ctx 1))
*}

(* ML {* val t = Unsynchronized.ref @{thm refl} *} *)


(*   apply (tactic \<open>Tactics.seq_tac ~2 ~1 (Var(("xxx",0),@{typ "predicate expression"})) @{context} 2\<close>)
  apply (tactic \<open>Tactics.seq_tac 0 0 (Var(("xxx",0),@{typ "predicate expression"})) @{context} 2\<close>)
  apply (tactic \<open>resolve_tac @{context} [Tactics.get_wp1 @{term "assign x e"} @{term B} @{context} |> #2] 3\<close>) *)

end
