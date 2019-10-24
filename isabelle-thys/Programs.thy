theory Programs
  imports Expressions QRHL_Core
begin

typedecl program
typedecl oracle_program
consts
  block :: "program list \<Rightarrow> program"
  assign :: "'a::universe variables \<Rightarrow> 'a expression \<Rightarrow> program"
  sample :: "'a variables \<Rightarrow> 'a distr expression \<Rightarrow> program"
  ifthenelse :: "bool expression \<Rightarrow> program list \<Rightarrow> program list \<Rightarrow> program"
  while :: "bool expression \<Rightarrow> program list \<Rightarrow> program"
  qinit :: "'a variables \<Rightarrow> 'a ell2 expression \<Rightarrow> program"
  qapply :: "'a variables \<Rightarrow> ('a,'a) l2bounded expression \<Rightarrow> program"
  measurement :: "'a variables \<Rightarrow> 'b variables \<Rightarrow> ('a,'b) measurement expression \<Rightarrow> program"
  instantiateOracles :: "oracle_program \<Rightarrow> program list \<Rightarrow> program"
  localvars :: "'a variables \<Rightarrow> 'b variables \<Rightarrow> program list \<Rightarrow> program"

consts fvq_oracle_program :: "oracle_program \<Rightarrow> string set"
consts fvc_oracle_program :: "oracle_program \<Rightarrow> string set"
consts fvcw_oracle_program :: "oracle_program \<Rightarrow> string set"

consts fvq_program :: "program \<Rightarrow> string set"
lemma fvq_program_sequence: "fvq_program (block b) = (\<Union>s\<in>set b. fvq_program s)"
  by (cheat TODO7)
lemma fvq_program_assign: "fvq_program (assign x e) = {}"
  by (cheat TODO7)
lemma fvq_program_sample: "fvq_program (sample xs e2) = {}"
  by (cheat TODO7)
lemma fvq_program_ifthenelse: "fvq_program (ifthenelse c p1 p2) =
  (\<Union>s\<in>set p1. fvq_program s) \<union> (\<Union>s\<in>set p2. fvq_program s)"
  by (cheat TODO7)
lemma fvq_program_while: "fvq_program (while c b) = (\<Union>s\<in>set b. fvq_program s)"
  by (cheat TODO7)
lemma fvq_program_qinit: "fvq_program (qinit Q e3) = set (variable_names Q)"
  by (cheat TODO7)
lemma fvq_program_qapply: "fvq_program (qapply Q e4) = set (variable_names Q)"
  by (cheat TODO7)
lemma fvq_program_measurement: "fvq_program (measurement x R e5) = set (variable_names R)"
  by (cheat TODO7)

consts fvc_program :: "program \<Rightarrow> string set"
lemma fvc_program_sequence: "fvc_program (block b) = (\<Union>s\<in>set b. fvc_program s)"
  by (cheat TODO7)
lemma fvc_program_assign: "fvc_program (assign x e) = set (variable_names x) \<union> fv_expression e"
  by (cheat TODO7)
lemma fvc_program_sample: "fvc_program (sample xs e2) = set (variable_names xs) \<union> fv_expression e2"
  by (cheat TODO7)
lemma fvc_program_ifthenelse: "fvc_program (ifthenelse c p1 p2) =
  fv_expression c \<union> (\<Union>s\<in>set p1. fvc_program s) \<union> (\<Union>s\<in>set p2. fvc_program s)"
  by (cheat TODO7)
lemma fvc_program_while: "fvc_program (while c b) = fv_expression c \<union> (\<Union>s\<in>set b. fvc_program s)"
  by (cheat TODO7)
lemma fvc_program_qinit: "fvc_program (qinit Q e3) = fv_expression e3"
  by (cheat TODO7)
lemma fvc_program_qapply: "fvc_program (qapply Q e4) = fv_expression e4"
  by (cheat TODO7)
lemma fvc_program_measurement: "fvc_program (measurement x R e5) = set (variable_names x) \<union> fv_expression e5"
  by (cheat TODO7)

consts fvcw_program :: "program \<Rightarrow> string set"
lemma fvcw_program_sequence: "fvcw_program (block b) = (\<Union>s\<in>set b. fvcw_program s)"
  by (cheat TODO7)
lemma fvcw_program_assign: "fvcw_program (assign x e) = set (variable_names x)"
  by (cheat TODO7)
lemma fvcw_program_sample: "fvcw_program (sample xs e2) = set (variable_names xs)"
  by (cheat TODO7)
lemma fvcw_program_ifthenelse: "fvcw_program (ifthenelse c p1 p2) =
  (\<Union>s\<in>set p1. fvcw_program s) \<union> (\<Union>s\<in>set p2. fvcw_program s)"
  by (cheat TODO7)
lemma fvcw_program_while: "fvcw_program (while c b) = (\<Union>s\<in>set b. fvcw_program s)"
  by (cheat TODO7)
lemma fvcw_program_qinit: "fvcw_program (qinit Q e3) = {}"
  by (cheat TODO7)
lemma fvcw_program_qapply: "fvcw_program (qapply Q e4) = {}"
  by (cheat TODO7)
lemma fvcw_program_measurement: "fvcw_program (measurement x R e5) = set (variable_names x)"
  by (cheat TODO7)

typedecl program_state

axiomatization
  denotation :: "program \<Rightarrow> program_state \<Rightarrow> program_state" and
  program_state_distrib :: "program_state \<Rightarrow> mem2 distr"

definition probability :: "bool expression \<Rightarrow> program \<Rightarrow> program_state \<Rightarrow> real" where
  "probability e p \<rho> = Prob (program_state_distrib (denotation p \<rho>)) {m. expression_eval e m}"

consts "probability_syntax" :: "bool \<Rightarrow> program \<Rightarrow> program_state \<Rightarrow> real" ("Pr[_:(_'(_'))]")
translations "CONST probability_syntax a b c" \<rightleftharpoons> "CONST probability (Expr[a]) b c"
hide_const probability_syntax

named_theorems program_bodies
named_theorems program_fv

ML_file "programs.ML"

end