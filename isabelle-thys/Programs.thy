theory Programs
  imports QRHL_Core Prog_Variables
begin

(* typedef 'a expression = \<open>UNIV :: (CVARIABLE \<times> ('cl \<Rightarrow> 'a)) set\<close>..
setup_lifting type_definition_expression
lift_definition fv_expression :: \<open>'a expression \<Rightarrow> CVARIABLE\<close> is
  \<open>\<lambda>(fv :: CVARIABLE,_). fv\<close>.
lift_definition expression_eval :: \<open>'a expression \<Rightarrow> ('cl \<Rightarrow> 'a)\<close> is
  \<open>\<lambda>(_, e). e\<close>.
lift_definition expression :: \<open>'a cvariable \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> ('b,'cl) expression\<close> is
  \<open>\<lambda>(v::'a cvariable) (f::'a\<Rightarrow>'b). (CVARIABLE_of v, f o getter v)\<close>.
definition \<open>const_expression x = expression (Classical_Extra.empty_var :: (unit,_) cvariable) (\<lambda>_. x)\<close> *)

type_synonym 'a expression = \<open>cl \<Rightarrow> 'a\<close>
type_synonym 'a expression2 = \<open>cl2 \<Rightarrow> 'a\<close>
abbreviation (input) \<open>expression_eval e \<equiv> e\<close>
abbreviation (input) \<open>map_expression2 f e1 e2 \<equiv> (\<lambda>m. f (e1 m) (e2 m))\<close>

typedecl program
typedecl oracle_program
consts
  block :: "program list \<Rightarrow> program"
  assign :: "'a cvariable \<Rightarrow> 'a expression \<Rightarrow> program"
  sample :: "'a cvariable \<Rightarrow> 'a distr expression \<Rightarrow> program"
  ifthenelse :: "bool expression \<Rightarrow> program list \<Rightarrow> program list \<Rightarrow> program"
  while :: "bool expression \<Rightarrow> program list \<Rightarrow> program"
  qinit :: "'a qvariable \<Rightarrow> 'a ell2 expression \<Rightarrow> program"
  qapply :: "'a qvariable \<Rightarrow> ('a,'a) l2bounded expression \<Rightarrow> program"
  measurement :: "'a cvariable \<Rightarrow> 'b qvariable \<Rightarrow> ('a,'b) measurement expression \<Rightarrow> program"
  instantiateOracles :: "oracle_program \<Rightarrow> program list \<Rightarrow> program"
  localvars :: "'a cvariable \<Rightarrow> 'b qvariable \<Rightarrow> program list \<Rightarrow> program"

consts fvq_program :: "program \<Rightarrow> QVARIABLE"
consts fvc_program :: "program \<Rightarrow> CVARIABLE"
consts fvcw_program :: "program \<Rightarrow> CVARIABLE"
consts fvq_oracle_program :: "oracle_program \<Rightarrow> QVARIABLE"
consts fvc_oracle_program :: "oracle_program \<Rightarrow> CVARIABLE"
consts fvcw_oracle_program :: "oracle_program \<Rightarrow> CVARIABLE"

(* TODO: not a sound concept, probably. The choice of fv for a given expression might not be unique. Or is it? *)
axiomatization fv_expression :: \<open>'a expression \<Rightarrow> CVARIABLE\<close>

(* consts fvq_program :: "program \<Rightarrow> string set" *)
lemma fvq_program_sequence: "fvq_program (block b) = fold (\<lambda>p v. QVARIABLE_pair (fvq_program p) v) b QVARIABLE_unit"
  by (cheat TODO7)
lemma fvq_program_assign: "fvq_program (assign x e) = QVARIABLE_unit"
  by (cheat TODO7)
lemma fvq_program_sample: "fvq_program (sample xs e2) = QVARIABLE_unit"
  by (cheat TODO7)
lemma fvq_program_ifthenelse: "fvq_program (ifthenelse c p1 p2) =
  QVARIABLE_pair (fvq_program (block p1)) (fvq_program (block p2))"
  by (cheat TODO7)
lemma fvq_program_while: "fvq_program (while c b) = (fvq_program (block b))"
  by (cheat TODO7)
lemma fvq_program_qinit: "fvq_program (qinit Q e3) = QVARIABLE_of Q"
  by (cheat TODO7)
lemma fvq_program_qapply: "fvq_program (qapply Q e4) = QVARIABLE_of Q"
  by (cheat TODO7)
lemma fvq_program_measurement: "fvq_program (measurement x R e5) = QVARIABLE_of R"
  by (cheat TODO7)

lemma fvc_program_sequence: "fvc_program (block b) = fold (\<lambda>p v. CVARIABLE_pair (fvc_program p) v) b CVARIABLE_unit"
  by (cheat TODO7)
lemma fvc_program_assign: "fvc_program (assign x e) = CVARIABLE_pair (CVARIABLE_of x) (fv_expression e)"
  by (cheat TODO7)
lemma fvc_program_sample: "fvc_program (sample x e) = CVARIABLE_pair (CVARIABLE_of x) (fv_expression e)"
  by (cheat TODO7)
lemma fvc_program_ifthenelse: "fvc_program (ifthenelse c p1 p2) =
  CVARIABLE_pair (fv_expression c) (CVARIABLE_pair (fvc_program (block p1)) (fvc_program (block p2)))"
  by (cheat TODO7)
lemma fvc_program_while: "fvc_program (while c b) = 
  CVARIABLE_pair (fv_expression c) (fvc_program (block b))"
  by (cheat TODO7)
lemma fvc_program_qinit: "fvc_program (qinit Q e3) = fv_expression e3"
  by (cheat TODO7)
lemma fvc_program_qapply: "fvc_program (qapply Q e4) = fv_expression e4"
  by (cheat TODO7)
lemma fvc_program_measurement: "fvc_program (measurement x R e) = CVARIABLE_pair (CVARIABLE_of x) (fv_expression e)"
  by (cheat TODO7)

lemma fvcw_program_sequence: "fvcw_program (block b) = fold (\<lambda>p v. CVARIABLE_pair (fvcw_program p) v) b CVARIABLE_unit"
  by (cheat TODO7)
lemma fvcw_program_assign: "fvcw_program (assign x e) = CVARIABLE_of x"
  by (cheat TODO7)
lemma fvcw_program_sample: "fvcw_program (sample x e2) = CVARIABLE_of x"
  by (cheat TODO7)
lemma fvcw_program_ifthenelse: "fvcw_program (ifthenelse c p1 p2) =
  CVARIABLE_pair (fvc_program (block p1)) (fvc_program (block p2))"
  by (cheat TODO7)
lemma fvcw_program_while: "fvcw_program (while c b) = fvcw_program (block b)"
  by (cheat TODO7)
lemma fvcw_program_qinit: "fvcw_program (qinit Q e3) = CVARIABLE_unit"
  by (cheat TODO7)
lemma fvcw_program_qapply: "fvcw_program (qapply Q e4) = CVARIABLE_unit"
  by (cheat TODO7)
lemma fvcw_program_measurement: "fvcw_program (measurement x R e5) = CVARIABLE_of x"
  by (cheat TODO7)

lemma localvars_empty: "localvars empty_cregister empty_qregister P = block P"
  by (cheat localvars_empty)

lemma singleton_block: "block [P] = P"
  by (cheat singleton_block)

typedecl program_state

axiomatization
  denotation :: "program \<Rightarrow> program_state \<Rightarrow> program_state" and
  program_state_distrib :: "program_state \<Rightarrow> cl distr"

lemma denotation_block: "denotation (block ps) = fold denotation ps"
  by (cheat denotation_block)

definition probability :: "bool expression \<Rightarrow> program \<Rightarrow> program_state \<Rightarrow> real" where
  "probability e p \<rho> = Prob (program_state_distrib (denotation p \<rho>)) (Collect e)"

lemma probability_sample: 
  "probability (expression m f) (block [sample m (const_expression D)]) rho
  = Prob D (Collect f)"
  by (cheat probability_sample)


lemma equal_until_bad: 
  assumes "probability (map_expression2 (|) e b) g3 rho \<ge> probability b g4 rho"
  assumes "probability (map_expression2 (\<lambda>e b. \<not>e&b) e b) g3 rho \<le> probability b g4 rho"
  shows "abs (probability b g3 rho - probability b g4 rho) \<le> probability e g3 rho"
proof -
  define d3 d4 B E where "d3 = program_state_distrib (Programs.denotation g3 rho)"
    and "d4 = program_state_distrib (Programs.denotation g4 rho)"
    and "B = Collect (expression_eval b)"
    and "E = Collect (expression_eval e)"
  note defs = this

  have EorB: "B\<union>E = Collect (expression_eval (map_expression2 (|) e b))"
    unfolding defs by auto
  have EandB: "B-E = Collect (expression_eval (map_expression2 (\<lambda>e b. \<not>e&b) e b))"
    unfolding defs by auto

  from assms(1) have a1: "Prob d4 B \<le> Prob d3 (B\<union>E)"
    unfolding EorB unfolding defs probability_def by auto
  from assms(2) have a2: "Prob d3 (B-E) \<le> Prob d4 B"
    unfolding EandB unfolding defs probability_def by auto

  have "Prob d3 B \<le> Prob d3 (B-E) + Prob d3 E"
    apply (subst Prob_setdiff) by simp
  also have "\<dots> \<le> Prob d4 B + Prob d3 E"
    using a2 by linarith
  finally have bound1: "Prob d3 B - Prob d4 B \<le> Prob d3 E"
    by linarith

  have "Prob d4 B \<le> Prob d3 (B\<union>E)"
    using a1 by assumption
  also have "\<dots> \<le> Prob d3 B + Prob d3 E"
    unfolding Prob_union by simp
  finally have bound2: "Prob d4 B - Prob d3 B \<le> Prob d3 E"
    by linarith

  from bound1 bound2 have "\<bar>Prob d3 B - Prob d4 B\<bar> \<le> Prob d3 E"
    by linarith

  then show ?thesis
    unfolding probability_def defs by simp
qed

named_theorems program_bodies
named_theorems program_fv


lemma add_index_to_expression_aux1: \<open>getter x (fst m) \<equiv> getter (cregister_chain cFst x) m\<close>
  apply (rule eq_reflection)
  by (metis cFst_register cregister_chain_non_register2 getter_Fst getter_non_cregister getter_setter_same non_cregister setter_chain setter_getter_same)

lemma add_index_to_expression_aux2: \<open>getter x (snd m) \<equiv> getter (cregister_chain cSnd x) m\<close>
  apply (rule eq_reflection)
  by (metis add_index_to_expression_aux1 fst_swap getter_Fst_chain_swap)

ML_file "programs.ML"

consts "expression_syntax" :: "'a \<Rightarrow> 'a expression" ("Expr[_]")
parse_translation \<open>[(\<^const_syntax>\<open>expression_syntax\<close>, fn ctx => fn [e] => Programs.term_to_expression ctx dummyT e)]\<close>
hide_const expression_syntax

consts "probability_syntax" :: "bool expression \<Rightarrow> program \<Rightarrow> program_state \<Rightarrow> real" ("Pr[_:(_'(_'))]")
translations "CONST probability_syntax a b c" \<rightleftharpoons> "CONST probability (Expr[a]) b c"
(* translations "CONST probability_syntax a b c" \<rightleftharpoons> "CONST probability a b c" *)
hide_const probability_syntax

experiment
  fixes x :: \<open>nat cvariable\<close>
  assumes [variable]: \<open>cregister x\<close>
begin
(* local_setup \<open>Prog_Variables.declare_variable_lthy (\<^term>\<open>x\<close> |> dest_Free |> fst) Prog_Variables.Classical \<^typ>\<open>nat\<close>\<close> *)
term \<open>Expr[x1+1]\<close>
term \<open>Pr[b=1 : left(rho)]\<close>
end

end
