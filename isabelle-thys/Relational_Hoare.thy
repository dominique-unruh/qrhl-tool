theory Relational_Hoare
  imports Programs
begin

consts left_marginal :: \<open>('a\<times>'b, 'c\<times>'d) cq_operator \<Rightarrow> ('a, 'c) cq_operator\<close>
consts right_marginal :: \<open>('a\<times>'b, 'c\<times>'d) cq_operator \<Rightarrow> ('b, 'd) cq_operator\<close>
consts satisfies :: \<open>('cl,'qu) cq_operator \<Rightarrow> ('cl \<Rightarrow> 'qu ell2 ccsubspace) \<Rightarrow> bool\<close>

lemma satisfies_mono: \<open>(\<And>m. A m \<le> B m) \<Longrightarrow> satisfies \<rho> A \<Longrightarrow> satisfies \<rho> B\<close>
  sorry

definition qrhl :: "predicate expression2 \<Rightarrow> program list \<Rightarrow> program list \<Rightarrow> predicate expression2 \<Rightarrow> bool" where
  \<open>qrhl A c d B \<longleftrightarrow> (\<forall>\<rho>. satisfies \<rho> A \<longrightarrow>(\<exists>\<rho>'. satisfies \<rho>' B 
          \<and> left_marginal  \<rho>' = denotation (block c) (left_marginal  \<rho>)
          \<and> right_marginal \<rho>' = denotation (block d) (right_marginal \<rho>)))\<close>

consts "qrhl_syntax" :: "bool expression \<Rightarrow> program list \<Rightarrow> program list \<Rightarrow> bool expression \<Rightarrow> bool" ("QRHL {_} _ _ {_}")
translations "CONST qrhl_syntax a b c d" \<rightleftharpoons> "CONST qrhl (Expr[a]) b c (Expr[d])"
hide_const qrhl_syntax

consts "rhl_syntax" :: "bool \<Rightarrow> program list \<Rightarrow> program list \<Rightarrow> bool \<Rightarrow> bool" ("RHL {_} _ _ {_}")
translations "CONST rhl_syntax a b c d" \<rightleftharpoons> "QRHL {classical_subspace a} b c {classical_subspace d}"
hide_const rhl_syntax

ML_file "relational_hoare.ML"

lemma qrhl_denotation_replace:
  assumes "denotation (block c) = denotation (block c')"
    and "denotation (block d) = denotation (block d')"
  shows "qrhl A c d B = qrhl A c' d' B"
  using assms by (simp add: qrhl_def)

end
