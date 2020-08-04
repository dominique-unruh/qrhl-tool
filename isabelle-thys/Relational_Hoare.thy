theory Relational_Hoare
  imports Programs
begin

consts qrhl :: "predicate expression \<Rightarrow> program list \<Rightarrow> program list \<Rightarrow> predicate expression \<Rightarrow> bool"

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
  by (cheat qrhl_denotation_replace)

end