theory Programs
  imports Expressions QRHL_Core
begin



typedecl program
typedecl oracle_program
consts
  block :: "program list \<Rightarrow> program"
  assign :: "'a::universe variable \<Rightarrow> 'a expression \<Rightarrow> program"
  sample :: "'a variables \<Rightarrow> 'a distr expression \<Rightarrow> program"
  ifthenelse :: "bool expression \<Rightarrow> program list \<Rightarrow> program list \<Rightarrow> program"
  while :: "bool expression \<Rightarrow> program list \<Rightarrow> program"
  qinit :: "'a variables \<Rightarrow> 'a vector expression \<Rightarrow> program"
  qapply :: "'a variables \<Rightarrow> ('a,'a) bounded expression \<Rightarrow> program"
  measurement :: "'a variable \<Rightarrow> 'b variables \<Rightarrow> ('a,'b) measurement expression \<Rightarrow> program"
  instantiateOracles :: "oracle_program \<Rightarrow> program list \<Rightarrow> program"

consts fv_program :: "program \<Rightarrow> string set"
lemma fv_program_sequence: "fv_program (block b) = (\<Union>s\<in>set b. fv_program s)"
  by (cheat TODO7)
lemma fv_program_assign: "fv_program (assign x e) = {variable_name x} \<union> fv_expression e"
  by (cheat TODO7)
lemma fv_program_sample: "fv_program (sample xs e2) = set (variable_names xs) \<union> fv_expression e2"
  by (cheat TODO7)
lemma fv_program_ifthenelse: "fv_program (ifthenelse c p1 p2) =
  fv_expression c \<union> (\<Union>s\<in>set p1. fv_program s) \<union> (\<Union>s\<in>set p2. fv_program s)"
  by (cheat TODO7)
lemma fv_program_while: "fv_program (while c b) = fv_expression c \<union> (\<Union>s\<in>set b. fv_program s)"
  by (cheat TODO7)
lemma fv_program_qinit: "fv_program (qinit Q e3) = set (variable_names Q) \<union> fv_expression e3"
  by (cheat TODO7)
lemma fv_program_qapply: "fv_program (qapply Q e4) = set (variable_names Q) \<union> fv_expression e4"
  by (cheat TODO7)
lemma fv_program_measurement: "fv_program (measurement x R e5) = {variable_name x} \<union> set (variable_names R) \<union> fv_expression e5"
  by (cheat TODO7)

typedecl program_state

consts probability :: "bool expression \<Rightarrow> program \<Rightarrow> program_state \<Rightarrow> real"

consts "probability_syntax" :: "bool \<Rightarrow> program \<Rightarrow> program_state \<Rightarrow> real" ("Pr[_:(_'(_'))]")
translations "CONST probability_syntax a b c" \<rightleftharpoons> "CONST probability (Expr[a]) b c"
hide_const probability_syntax

ML_file "programs.ML"

end