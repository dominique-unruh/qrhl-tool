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

lemma wp1_qapply:
  fixes A B Q e
  defines "Q\<^sub>1 \<equiv> index_vars True Q"
  defines "A \<equiv> map_expression2 (\<lambda>e\<^sub>1 B. Cla[isometry e\<^sub>1] \<sqinter> (adjoint (e\<^sub>1\<guillemotright>Q\<^sub>1) \<cdot> (B \<sqinter> (e\<^sub>1\<guillemotright>Q\<^sub>1 \<cdot> top)))) (index_expression True e) B"
  shows "qrhl A [qapply Q e] [] B"
  sorry

lemma wp2_qapply:
  fixes A B Q e
  defines "Q\<^sub>2 \<equiv> index_vars False Q"
  defines "A \<equiv> map_expression2 (\<lambda>e\<^sub>2 B. Cla[isometry e\<^sub>2] \<sqinter> (adjoint (e\<^sub>2\<guillemotright>Q\<^sub>2) \<cdot> (B \<sqinter> (e\<^sub>2\<guillemotright>Q\<^sub>2 \<cdot> top)))) (index_expression False e) B"
  shows "qrhl A [] [qapply Q e] B"
  sorry

lemma wp1_measure:
  fixes A B x Q e
  defines "e\<^sub>1 \<equiv> index_expression True e"
  defines "B' z \<equiv> subst_expression (substitute1 (index_var True x) (const_expression z)) B"
  defines "\<And>e\<^sub>1 z. ebar e\<^sub>1 z \<equiv> ((mproj e\<^sub>1 z)\<guillemotright>(index_vars True Q)) \<cdot> top"
  defines "A \<equiv> map_expression2' (\<lambda>e\<^sub>1 B'. Cla[mtotal e\<^sub>1] \<sqinter> 
           (INF z. ((B' z \<sqinter> ebar e\<^sub>1 z) + ortho (ebar e\<^sub>1 z)))) e\<^sub>1 B'"
  shows "qrhl A [measurement x Q e] [] B"
  sorry

lemma wp2_measure:
  fixes A B x Q e
  defines "e\<^sub>2 \<equiv> index_expression False e"
  defines "B' z \<equiv> subst_expression (substitute1 (index_var False x) (const_expression z)) B"
  defines "\<And>e\<^sub>2 z. ebar e\<^sub>2 z \<equiv> ((mproj e\<^sub>2 z)\<guillemotright>(index_vars False Q)) \<cdot> top"
  defines "A \<equiv> map_expression2' (\<lambda>e\<^sub>2 B'. Cla[mtotal e\<^sub>2] \<sqinter> 
           (INF z. ((B' z \<sqinter> ebar e\<^sub>2 z) + ortho (ebar e\<^sub>2 z)))) e\<^sub>2 B'"
  shows "qrhl A [] [measurement x Q e] B"
  sorry

lemma wp1_qinit:
  fixes B e Q
  defines "A \<equiv> map_expression2 (\<lambda>e\<^sub>1 B. Cla[norm e\<^sub>1 = 1] \<sqinter> (B \<div> e\<^sub>1 \<guillemotright> (index_vars True Q)))
           (index_expression True e) B"
  shows "qrhl A [qinit Q e] [] B"
  sorry

lemma wp2_qinit:
  fixes B e Q
  defines "A \<equiv> map_expression2 (\<lambda>e\<^sub>2 B. Cla[norm e\<^sub>2 = 1] \<sqinter> (B \<div> e\<^sub>2 \<guillemotright> (index_vars False Q)))
           (index_expression False e) B"
  shows "qrhl A [] [qinit Q e] B"
  sorry

lemma wp1_if:
  fixes e p1 p2 B
  assumes "qrhl wp_true p1 [] B"
  assumes "qrhl wp_false p2 [] B"
  defines "A \<equiv> map_expression3 (\<lambda>e\<^sub>1 wp_true wp_false. (Cla[\<not>e\<^sub>1] + wp_true) \<sqinter> (Cla[e\<^sub>1] + wp_false))
           (index_expression True e) wp_true wp_false"
  shows "qrhl A [ifthenelse e p1 p2] [] B"
  sorry

lemma wp2_if:
  fixes e p1 p2 B
  assumes "qrhl wp_true [] p1 B"
  assumes "qrhl wp_false [] p2 B"
  defines "A \<equiv> map_expression3 (\<lambda>e\<^sub>2 wp_true wp_false. (Cla[\<not>e\<^sub>2] + wp_true) \<sqinter> (Cla[e\<^sub>2] + wp_false))
           (index_expression False e) wp_true wp_false"
  shows "qrhl A [] [ifthenelse e p1 p2] B"
  sorry

lemma wp1_block:
  assumes "qrhl A p [] B"
  shows "qrhl A [block p] [] B"
  sorry

lemma wp2_block:
  assumes "qrhl A [] p B"
  shows "qrhl A [] [block p] B"
  sorry

lemma wp1_cons:
  assumes "qrhl A [p] [] B'"
    and "qrhl B' ps [] B"
  shows "qrhl A (p#ps) [] B"
  sorry

lemma wp2_cons:
  assumes "qrhl A [] [p] B'"
    and "qrhl B' [] ps B"
  shows "qrhl A [] (p#ps) B"
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

variables classical x :: nat begin

schematic_goal "qrhl ?pre [block [assign var_x Expr[x+2], assign var_x Expr[0], assign var_x Expr[x+1] ] ] [] Expr[ Cla[x1=1] ]"
  apply (tactic \<open>Tactics.wp_tac @{context} true 1\<close>)
  apply simp
  oops

end

end
