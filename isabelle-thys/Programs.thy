theory Programs
  imports QRHL_Core Expressions Wlog.Wlog Kraus_Maps CQ_Operators
begin



datatype raw_program =
  Seq \<open>raw_program\<close> \<open>raw_program\<close>
  | Skip
  | Sample \<open>cl distr expression\<close>
  | IfThenElse \<open>bool expression\<close> \<open>raw_program\<close> \<open>raw_program\<close>
  | While \<open>bool expression\<close> \<open>raw_program\<close>
  | QuantumOp \<open>(qu ell2, qu ell2) kraus_map expression\<close>
  | Measurement \<open>(cl, qu) measurement expression\<close>
  | InstantiateOracles \<open>raw_program\<close> \<open>raw_program list\<close>
  | LocalQ \<open>qu QREGISTER\<close> \<open>(qu ell2, qu ell2) trace_class\<close> \<open>raw_program\<close>
  | LocalC \<open>cl CREGISTER\<close> \<open>cl \<Rightarrow> cl\<close> \<open>raw_program\<close>
  | OracleCall nat

fun oracle_number :: \<open>raw_program \<Rightarrow> nat\<close> where
  \<open>oracle_number (Seq c d) = max (oracle_number c) (oracle_number d)\<close>
| \<open>oracle_number Skip = 0\<close>
| \<open>oracle_number (Sample _) = 0\<close>
| \<open>oracle_number (QuantumOp _) = 0\<close>
| \<open>oracle_number (Measurement _) = 0\<close>
| \<open>oracle_number (IfThenElse e c d) = max (oracle_number c) (oracle_number d)\<close>
| \<open>oracle_number (While e c) = oracle_number c\<close>
| \<open>oracle_number (InstantiateOracles _ _) = 0\<close>
| \<open>oracle_number (LocalQ _ _ c) = oracle_number c\<close>
| \<open>oracle_number (LocalC _ _ c) = oracle_number c\<close>
| \<open>oracle_number (OracleCall i) = Suc i\<close>


inductive valid_oracle_program :: \<open>raw_program \<Rightarrow> bool\<close> and valid_program :: \<open>raw_program \<Rightarrow> bool\<close> where
  \<open>valid_oracle_program c \<Longrightarrow> valid_oracle_program d \<Longrightarrow> valid_oracle_program (Seq c d)\<close>
| \<open>valid_oracle_program Skip\<close>
| \<open>(\<And>m. weight (e m) \<le> 1) \<Longrightarrow> valid_oracle_program (Sample e)\<close>
| \<open>valid_oracle_program c \<Longrightarrow> valid_oracle_program d \<Longrightarrow> valid_oracle_program (IfThenElse e c d)\<close>
| \<open>valid_oracle_program c \<Longrightarrow> valid_oracle_program (While e c)\<close>
| \<open>(\<And>m. kraus_map_norm (e m) \<le> 1) \<Longrightarrow> valid_oracle_program (QuantumOp e)\<close>
| \<open>valid_oracle_program (Measurement e)\<close>
| \<open>(\<And>d. d \<in> set ds \<Longrightarrow> valid_program d) \<Longrightarrow> valid_oracle_program c \<Longrightarrow> 
  oracle_number c \<le> length ds \<Longrightarrow> valid_oracle_program (InstantiateOracles c ds)\<close>
| \<open>valid_oracle_program c \<Longrightarrow> ACTUAL_QREGISTER q \<Longrightarrow> norm \<rho> = 1 \<Longrightarrow> from_trace_class \<rho> \<in> Rep_QREGISTER q \<Longrightarrow> valid_oracle_program (LocalQ q \<rho> c)\<close>
| \<open>valid_oracle_program c \<Longrightarrow> Some o f \<in> Rep_CREGISTER x \<Longrightarrow> 
    (\<And>g. Some o g \<in> Rep_CREGISTER x \<Longrightarrow> f o g = f) \<Longrightarrow> valid_oracle_program (LocalC x f c)\<close>
| \<open>valid_oracle_program c \<Longrightarrow> oracle_number c = 0 \<Longrightarrow> valid_program c\<close>


typedef program = \<open>Collect valid_program\<close>
  apply (rule exI[of _ Skip])
  by (simp add: valid_oracle_program_valid_program.intros)
setup_lifting type_definition_program

typedef oracle_program = \<open>Collect valid_oracle_program\<close>
  apply (rule exI[of _ Skip])
  by (simp add: valid_oracle_program_valid_program.intros)
setup_lifting type_definition_oracle_program

lift_definition oracle_program_from_program :: \<open>program \<Rightarrow> oracle_program\<close> is id
  by (simp add: valid_program.simps)

lift_definition block :: \<open>program list \<Rightarrow> program\<close> is
  \<open>\<lambda>ps. fold Seq ps Skip\<close>
proof -
  fix ps
  assume \<open>list_all (\<lambda>x. x \<in> Collect valid_program) ps\<close>
  then have \<open>list_all valid_program ps\<close>
    by simp
  then have \<open>valid_oracle_program (fold Seq ps Skip)\<close> and \<open>oracle_number (fold Seq ps Skip) = 0\<close>
  proof (induction ps rule:rev_induct)
    case Nil
    show \<open>valid_oracle_program (fold Seq [] Skip)\<close>
      by (auto intro!: valid_oracle_program_valid_program.intros)
    show \<open>oracle_number (fold Seq [] Skip) = 0\<close>
      by simp
  next
    case (snoc p ps)
    then show \<open>valid_oracle_program (fold Seq (ps @ [p]) Skip)\<close>
      if \<open>list_all valid_program (ps @ [p])\<close>
      using that apply (auto intro!: valid_oracle_program_valid_program.intros)
      using valid_program.simps by blast
    show \<open>oracle_number (fold Seq (ps @ [p]) Skip) = 0\<close>
      if \<open>list_all valid_program (ps @ [p])\<close>
      using that snoc apply simp
      using valid_program.simps by blast
  qed
  then show \<open>fold Seq ps Skip \<in> Collect valid_program\<close>
    by (simp add: valid_program.simps)
qed

lift_definition sample :: \<open>'a cvariable \<Rightarrow> 'a distr expression \<Rightarrow> program\<close> is
  \<open>\<lambda>X e. Sample (\<lambda>m::cl. map_distr (\<lambda>x. setter X x m) (e m))\<close>
  by (simp add: valid_oracle_program_valid_program.intros(3) valid_program.simps)

definition assign :: \<open>'a cvariable \<Rightarrow> 'a expression \<Rightarrow> program\<close> where
  \<open>assign x e = sample x (point_distr o e)\<close>

lift_definition qapply :: \<open>'a qvariable \<Rightarrow> ('a,'a) l2bounded expression \<Rightarrow> program\<close> is
  \<open>\<lambda>Q e. if qregister Q then
      QuantumOp (\<lambda>m. kraus_map_of_op (apply_qregister Q (if norm (e m) \<le> 1 then e m else 0))) else Skip\<close>
  apply (auto intro!: valid_oracle_program_valid_program.intros)
  by (simp add: power_le_one)

consts
  ifthenelse :: "bool expression \<Rightarrow> program list \<Rightarrow> program list \<Rightarrow> program"
  while :: "bool expression \<Rightarrow> program list \<Rightarrow> program"
  qinit :: "'a qvariable \<Rightarrow> 'a ell2 expression \<Rightarrow> program"
  measurement :: "'a cvariable \<Rightarrow> 'b qvariable \<Rightarrow> ('a,'b) measurement expression \<Rightarrow> program"
  instantiateOracles :: "oracle_program \<Rightarrow> program list \<Rightarrow> program"
  localvars :: "'a cvariable \<Rightarrow> 'b qvariable \<Rightarrow> program list \<Rightarrow> program"

consts fvq_program :: "program \<Rightarrow> QVARIABLE"
consts fvc_program :: "program \<Rightarrow> CVARIABLE"
consts fvcw_program :: "program \<Rightarrow> CVARIABLE"
consts fvq_oracle_program :: "oracle_program \<Rightarrow> QVARIABLE"
consts fvc_oracle_program :: "oracle_program \<Rightarrow> CVARIABLE"
consts fvcw_oracle_program :: "oracle_program \<Rightarrow> CVARIABLE"

(* consts fvq_program :: "program \<Rightarrow> string set" *)
lemma fvq_program_sequence: "fvq_program (block b) = fold (\<lambda>p v. QREGISTER_pair (fvq_program p) v) b QREGISTER_unit"
  sorry
lemma fvq_program_assign: "fvq_program (assign x e) = QREGISTER_unit"
  sorry
lemma fvq_program_sample: "fvq_program (sample xs e2) = QREGISTER_unit"
  sorry
lemma fvq_program_ifthenelse: "fvq_program (ifthenelse c p1 p2) =
  QREGISTER_pair (fvq_program (block p1)) (fvq_program (block p2))"
  sorry
lemma fvq_program_while: "fvq_program (while c b) = (fvq_program (block b))"
  sorry
lemma fvq_program_qinit: "fvq_program (qinit Q e3) = QREGISTER_of Q"
  sorry
lemma fvq_program_qapply: "fvq_program (qapply Q e4) = QREGISTER_of Q"
  sorry
lemma fvq_program_measurement: "fvq_program (measurement x R e5) = QREGISTER_of R"
  sorry

lemma fvc_program_sequence: "fvc_program (block b) = fold (\<lambda>p v. CREGISTER_pair (fvc_program p) v) b CREGISTER_unit"
  sorry
lemma fvc_program_assign: "fvc_program (assign x e) = CREGISTER_pair (CREGISTER_of x) (fv_expression e)"
  sorry
lemma fvc_program_sample: "fvc_program (sample x e) = CREGISTER_pair (CREGISTER_of x) (fv_expression e)"
  sorry
lemma fvc_program_ifthenelse: "fvc_program (ifthenelse c p1 p2) =
  CREGISTER_pair (fv_expression c) (CREGISTER_pair (fvc_program (block p1)) (fvc_program (block p2)))"
  sorry
lemma fvc_program_while: "fvc_program (while c b) = 
  CREGISTER_pair (fv_expression c) (fvc_program (block b))"
  sorry
lemma fvc_program_qinit: "fvc_program (qinit Q e3) = fv_expression e3"
  sorry
lemma fvc_program_qapply: "fvc_program (qapply Q e4) = fv_expression e4"
  sorry
lemma fvc_program_measurement: "fvc_program (measurement x R e) = CREGISTER_pair (CREGISTER_of x) (fv_expression e)"
  sorry

lemma fvcw_program_sequence: "fvcw_program (block b) = fold (\<lambda>p v. CREGISTER_pair (fvcw_program p) v) b CREGISTER_unit"
  sorry
lemma fvcw_program_assign: "fvcw_program (assign x e) = CREGISTER_of x"
  sorry
lemma fvcw_program_sample: "fvcw_program (sample x e2) = CREGISTER_of x"
  sorry
lemma fvcw_program_ifthenelse: "fvcw_program (ifthenelse c p1 p2) =
  CREGISTER_pair (fvc_program (block p1)) (fvc_program (block p2))"
  sorry
lemma fvcw_program_while: "fvcw_program (while c b) = fvcw_program (block b)"
  sorry
lemma fvcw_program_qinit: "fvcw_program (qinit Q e3) = CREGISTER_unit"
  sorry
lemma fvcw_program_qapply: "fvcw_program (qapply Q e4) = CREGISTER_unit"
  sorry
lemma fvcw_program_measurement: "fvcw_program (measurement x R e5) = CREGISTER_of x"
  sorry

lemma localvars_empty: "localvars empty_cregister empty_qregister P = block P"
  sorry

lemma singleton_block: "block [P] = P"
  sorry

type_synonym program_state = \<open>(cl,qu) cq_operator\<close>

fun denotation_raw :: "raw_program \<Rightarrow> program_state \<Rightarrow> program_state" where
  denotation_raw_Skip: \<open>denotation_raw Skip \<rho> = \<rho>\<close>
| denotation_raw_Seq: \<open>denotation_raw (Seq c d) \<rho> = denotation_raw d (denotation_raw c \<rho>)\<close>
(* TODO missing cases *)

lift_definition denotation :: "program \<Rightarrow> program_state \<Rightarrow> program_state" is denotation_raw.

lift_definition program_state_distrib :: "program_state \<Rightarrow> cl distr" is
  \<open>\<lambda>\<rho> m. if \<rho> \<ge> 0 \<and> norm \<rho> \<le> 1 then norm (cq_operator_at \<rho> m) else 0\<close>
proof -
  fix \<rho> :: \<open>(cl, qu) cq_operator\<close>
  show \<open>is_distribution
        (\<lambda>m. if 0 \<le> \<rho> \<and> norm \<rho> \<le> 1 then norm (cq_operator_at \<rho> m) else 0)\<close>
  proof (cases \<open>0 \<le> \<rho> \<and> norm \<rho> \<le> 1\<close>)
    case True
    then show ?thesis
      apply (subst if_P)
      using cq_operator_at
      by (auto simp add: is_distribution_def norm_cq_operator.rep_eq)
  next
    case False
    then show ?thesis
      apply (subst if_not_P)
      by (auto simp add: is_distribution_def)
  qed
qed

lemma denotation_block: "denotation (block ps) = foldr denotation ps"
  apply transfer
  subgoal for ps
    apply (induction ps rule:rev_induct)
    by (auto intro!: ext)
  done

definition probability :: "bool expression \<Rightarrow> program \<Rightarrow> program_state \<Rightarrow> real" where
  "probability e p \<rho> = Prob (program_state_distrib (denotation p \<rho>)) (Collect e)"

(* consts "probability_syntax" :: "bool \<Rightarrow> program \<Rightarrow> program_state \<Rightarrow> real" ("Pr[_ : (_'(_'))]")
translations "CONST probability_syntax a b c" \<rightleftharpoons> "CONST probability (Expr[a]) b c"
hide_const probability_syntax *)

lemma probability_sample: 
  "probability (expression m f) (block [sample m (const_expression D)]) rho
  = Prob D (Collect f)"
  sorry

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


ML_file "programs.ML"

consts "probability_syntax" :: "bool expression \<Rightarrow> program \<Rightarrow> program_state \<Rightarrow> real" ("Pr[_:(_'(_'))]")
translations "CONST probability_syntax a b c" \<rightleftharpoons> "CONST probability (Expr[a]) b c"
(* translations "CONST probability_syntax a b c" \<rightleftharpoons> "CONST probability a b c" *)
hide_const probability_syntax

end
