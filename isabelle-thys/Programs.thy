theory Programs
  imports QRHL_Core Expressions Wlog.Wlog Kraus_Maps (* CQ_Operators2 *)
begin

no_notation Lattice.join (infixl "\<squnion>\<index>" 65)
no_notation Order.bottom ("\<bottom>\<index>")



(* definition \<open>cregister_with_init_rel = (\<lambda>(F,m) (G,n). F=G \<and> (\<exists>f\<in>Rep_CREGISTER (- F). f m = Some n))\<close>

lemma Some_in_valid_cregister_range:
  assumes \<open>valid_cregister_range X\<close>
  shows \<open>Some \<in> X\<close>
try0
sledgehammer [dont_slice]
by -

lemma cregister_with_init_rel_refl[iff]: \<open>reflp cregister_with_init_rel\<close>
  using Rep_CREGISTER Some_in_valid_cregister_range
  by (auto intro!: reflpI bexI[of _ Some] simp: cregister_with_init_rel_def)

lemma cregister_with_init_rel_transp[iff]: \<open>transp cregister_with_init_rel\<close>
proof (rule transpI)
  fix Fm Gn Hk assume assms: \<open>cregister_with_init_rel Fm Gn\<close> \<open>cregister_with_init_rel Gn Hk\<close>
  obtain F m G n H k where defs: \<open>Fm = (F,m)\<close> \<open>Gn = (G,n)\<close> \<open>Hk = (H,k)\<close>
    by force
  from assms have [simp]: \<open>F = G\<close> \<open>G = H\<close>
    by (simp_all add: cregister_with_init_rel_def defs)
  from assms obtain f where f: \<open>f \<in> Rep_CREGISTER (-F)\<close> and fm: \<open>f m = Some n\<close>
    apply atomize_elim
    by (auto simp: cregister_with_init_rel_def defs)
  from assms obtain g where g: \<open>g \<in> Rep_CREGISTER (-G)\<close> and gn: \<open>g n = Some k\<close>
    apply atomize_elim
    by (auto simp: cregister_with_init_rel_def defs)
  show \<open>cregister_with_init_rel Fm Hk\<close>
    using Rep_CREGISTER f g fm gn
    by (auto intro!: bexI[of _ \<open>g \<circ>\<^sub>m f\<close>] valid_cregister_range_mult Rep_CREGISTER 
        simp: cregister_with_init_rel_def defs)
qed

lemma cregister_with_init_rel_sym[iff]: \<open>symp cregister_with_init_rel\<close>
proof (rule sympI)
  fix Fm Gn assume assm: \<open>cregister_with_init_rel Fm Gn\<close>
  obtain F m G n where defs: \<open>Fm = (F,m)\<close> \<open>Gn = (G,n)\<close>
    by force
  from assm have [simp]: \<open>F = G\<close>
    by (simp add: cregister_with_init_rel_def defs)
  from assm obtain f where f: \<open>f \<in> Rep_CREGISTER (-F)\<close> and fm: \<open>f m = Some n\<close>
    apply atomize_elim
    by (auto simp: cregister_with_init_rel_def defs)
  define g where \<open>g n' = (if n' then \<close>
  show \<open>cregister_with_init_rel Gn Fm\<close>
    apply (simp add: cregister_with_init_rel_def defs)

quotient_type 'a cregister_with_init = \<open>'a CREGISTER \<times> 'a\<close> / cregister_with_init_rel
apply (auto intro!: equivpI simp: )
proof (rule )
*)

datatype raw_program =
  Seq \<open>raw_program\<close> \<open>raw_program\<close>
  | Skip
  | Sample \<open>cl distr expression\<close>
  | IfThenElse \<open>bool expression\<close> \<open>raw_program\<close> \<open>raw_program\<close>
  | While \<open>bool expression\<close> \<open>raw_program\<close>
  | QuantumOp \<open>(qu ell2, qu ell2, unit) kraus_family expression\<close>
  | Measurement \<open>(cl, qu) measurement expression\<close>
  | InstantiateOracles \<open>raw_program\<close> \<open>raw_program list\<close>
  | LocalQ \<open>qu QREGISTER\<close> \<open>(qu ell2, qu ell2) trace_class\<close> \<open>raw_program\<close>
  | LocalC \<open>cl CREGISTER\<close> \<open>cl\<close> \<open>raw_program\<close>
      \<comment> \<open>Interpretation: \<^term>\<open>LocalC F init P\<close> temporarily back up the content of reference F,
      updated the classical memory using the content of F in init, and then runs P\<close>
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
| \<open>(\<And>m. kraus_family_norm (e m) \<le> 1) \<Longrightarrow> valid_oracle_program (QuantumOp e)\<close>
| \<open>valid_oracle_program (Measurement e)\<close>
| \<open>(\<And>d. d \<in> set ds \<Longrightarrow> valid_program d) \<Longrightarrow> valid_oracle_program c \<Longrightarrow> 
  oracle_number c \<le> length ds \<Longrightarrow> valid_oracle_program (InstantiateOracles c ds)\<close>
| \<open>valid_oracle_program c \<Longrightarrow> ACTUAL_QREGISTER q \<Longrightarrow> norm \<rho> = 1 \<Longrightarrow> valid_oracle_program (LocalQ q \<rho> c)\<close>
| \<open>valid_oracle_program c \<Longrightarrow> ACTUAL_CREGISTER x \<Longrightarrow> valid_oracle_program (LocalC x init c)\<close>
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

lift_definition seq :: \<open>program \<Rightarrow> program \<Rightarrow> program\<close> is Seq
proof -
  fix p q
  assume assms: \<open>p \<in> Collect valid_program\<close> \<open>q \<in> Collect valid_program\<close>
  have \<open>valid_oracle_program (Seq p q)\<close>
    using assms by (auto intro!: valid_oracle_program_valid_program.intros simp: valid_program.simps)
  moreover have \<open>oracle_number (Seq p q) = 0\<close>
    using assms by (auto intro!: valid_oracle_program_valid_program.intros simp: valid_program.simps)
  ultimately show \<open>Seq p q \<in> Collect valid_program\<close>
    by (simp add: valid_oracle_program_valid_program.intros)
qed

lift_definition skip :: program is Skip
  by (auto intro!: valid_oracle_program_valid_program.intros)

fun block :: \<open>program list \<Rightarrow> program\<close> where
  block_empty[simp del]: \<open>block [] = skip\<close>
| block_single[simp del]: \<open>block [p] = p\<close>
| block_cons[simp del]: \<open>block (p#ps) = seq p (block ps)\<close>

(* lift_definition block :: \<open>program list \<Rightarrow> program\<close> is
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
qed *)

lift_definition sample :: \<open>'a cvariable \<Rightarrow> 'a distr expression \<Rightarrow> program\<close> is
  \<open>\<lambda>X e. Sample (\<lambda>m::cl. map_distr (\<lambda>x. setter X x m) (e m))\<close>
  by (simp add: valid_oracle_program_valid_program.intros(3) valid_program.simps)

definition assign :: \<open>'a cvariable \<Rightarrow> 'a expression \<Rightarrow> program\<close> where
  \<open>assign x e = sample x (point_distr o e)\<close>

lift_definition qapply :: \<open>'a qvariable \<Rightarrow> ('a,'a) l2bounded expression \<Rightarrow> program\<close> is
  \<open>\<lambda>Q e. if qregister Q then
      QuantumOp (\<lambda>m. kraus_family_of_op (apply_qregister Q (if norm (e m) \<le> 1 then e m else 0))) else Skip\<close>
  apply (auto intro!: valid_oracle_program_valid_program.intros)
  by (simp add: power_le_one)

consts
  ifthenelse :: "bool expression \<Rightarrow> program list \<Rightarrow> program list \<Rightarrow> program"
  while :: "bool expression \<Rightarrow> program list \<Rightarrow> program"
  qinit :: "'a qvariable \<Rightarrow> 'a ell2 expression \<Rightarrow> program"
  measurement :: "'a cvariable \<Rightarrow> 'b qvariable \<Rightarrow> ('a,'b) measurement expression \<Rightarrow> program"
  instantiateOracles :: "oracle_program \<Rightarrow> program list \<Rightarrow> program"
  localvars :: "'a cvariable \<Rightarrow> 'b qvariable \<Rightarrow> program list \<Rightarrow> program"

fun fvq_raw_program :: \<open>raw_program \<Rightarrow> QVARIABLE\<close> where
  \<open>fvq_raw_program (Seq p q) = fvq_raw_program p \<squnion> fvq_raw_program q\<close>
| \<open>fvq_raw_program Skip = \<bottom>\<close>
| \<open>fvq_raw_program (Sample _) = \<bottom>\<close>
| \<open>fvq_raw_program (IfThenElse c p q) = fvq_raw_program p \<squnion> fvq_raw_program q\<close>
| \<open>fvq_raw_program (While c p) = fvq_raw_program p\<close>
| \<open>fvq_raw_program (QuantumOp e) = undefined\<close> (* TODO *)
| \<open>fvq_raw_program (Measurement e) = undefined\<close> (* TODO *)
| \<open>fvq_raw_program (InstantiateOracles p qs) = fvq_raw_program p \<squnion> (\<Squnion>q\<in>set qs. fvq_raw_program q)\<close>
| \<open>fvq_raw_program (LocalQ Q _ p) = undefined\<close> (* TODO *)
| \<open>fvq_raw_program (LocalC _ _ p) = fvq_raw_program p\<close>
| \<open>fvq_raw_program (OracleCall _) = \<bottom>\<close>

lift_definition fvq_program :: "program \<Rightarrow> QVARIABLE" is fvq_raw_program.
lift_definition fvq_oracle_program :: "oracle_program \<Rightarrow> QVARIABLE" is fvq_raw_program.

consts fvc_program :: "program \<Rightarrow> CVARIABLE"
consts fvcw_program :: "program \<Rightarrow> CVARIABLE"
consts fvc_oracle_program :: "oracle_program \<Rightarrow> CVARIABLE"
consts fvcw_oracle_program :: "oracle_program \<Rightarrow> CVARIABLE"

lemma fvq_program_skip[simp]: \<open>fvq_program skip = \<bottom>\<close>
  apply transfer' by simp

lemma fvq_program_seq: \<open>fvq_program (seq a b) = fvq_program a \<squnion> fvq_program b\<close>
  apply transfer by simp

lemma fvq_program_sequence: "fvq_program (block b) 
      = fold (\<lambda>p v. QREGISTER_pair (fvq_program p) v) b QREGISTER_unit"
proof (induction b rule:induct_list012)
  case 1
  show ?case
    by (simp add: block_empty)
next
  case (2 x)
  show ?case
    by (simp add: block_single)
next
  case (3 x y zs)
  define yzs where \<open>yzs = y # zs\<close>
  have \<open>fvq_program (block (x # yzs)) = fvq_program x \<squnion> fvq_program (block yzs)\<close>
    by (simp add: block_cons fvq_program_seq yzs_def)
  also have \<open>\<dots> = fvq_program x \<squnion> fold (\<lambda>p v. fvq_program p \<squnion> v) yzs \<bottom>\<close>
    by (simp add: 3 yzs_def)
  also have \<open>fvq_program x \<squnion> fold (\<lambda>p v. fvq_program p \<squnion> v) yzs w = fold (\<lambda>p v. fvq_program p \<squnion> v) (x # yzs) w\<close> for w
    apply (induction yzs arbitrary: w)
    by (simp_all add: sup_aci)
  finally show ?case
    by (simp add: yzs_def)
qed

lemma fvq_program_sample: "fvq_program (sample xs e2) = QREGISTER_unit"
  apply transfer' by simp
lemma fvq_program_assign: "fvq_program (assign x e) = QREGISTER_unit"
  by (simp add: assign_def fvq_program_sample)
lemma fvq_program_ifthenelse: "fvq_program (ifthenelse c p1 p2) =
  QREGISTER_pair (fvq_program (block p1)) (fvq_program (block p2))"
  apply transfer
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

definition \<open>program_semantics_rel \<EE> \<FF> \<longleftrightarrow> (\<forall>x. kraus_family_norm (\<EE> x) \<le> 1 \<and> kraus_equivalent' (\<EE> x) (\<FF> x))\<close>
  for \<EE> \<FF> :: \<open>cl \<Rightarrow> (qu ell2, qu ell2, cl) kraus_family\<close>

(* TODO move *)
typedef program_state = \<open>{\<rho> :: cl \<Rightarrow> (qu ell2, qu ell2) trace_class. (\<forall>c. \<rho> c \<ge> 0) \<and> 
                          (\<lambda>c. trace_tc (\<rho> c)) summable_on UNIV \<and> (\<Sum>\<^sub>\<infinity>c. trace_tc (\<rho> c)) \<le> 1}\<close>
  apply (rule exI[of _ \<open>\<lambda>_. 0\<close>])
  by auto
setup_lifting type_definition_program_state

lift_definition fixed_cl_program_state :: \<open>cl \<Rightarrow> (qu ell2, qu ell2) trace_class \<Rightarrow> program_state\<close> is
  \<open>\<lambda>c (\<rho>::(qu ell2, qu ell2) trace_class) d. if \<rho> \<ge> 0 \<and> trace_tc \<rho> \<le> 1 then of_bool (c=d) *\<^sub>R \<rho> else 0\<close>
proof (rename_tac c \<rho>, intro conjI allI)
  fix c d :: cl and \<rho> :: \<open>(qu ell2, qu ell2) trace_class\<close>
  show \<open>0 \<le> (if \<rho> \<ge> 0 \<and> trace_tc \<rho> \<le> 1 then of_bool (c = d) *\<^sub>R \<rho> else 0)\<close>
    by simp
  show \<open>(\<lambda>d. trace_tc (if \<rho> \<ge> 0 \<and> trace_tc \<rho> \<le> 1 then of_bool (c = d) *\<^sub>R \<rho> else 0)) summable_on UNIV\<close>
  proof (cases \<open>\<rho> \<ge> 0 \<and> trace_tc \<rho> \<le> 1\<close>)
    case True
    have \<open>(\<lambda>d. trace_tc (of_bool (c = d) *\<^sub>R \<rho>)) summable_on UNIV\<close>
      apply (rule finite_nonzero_values_imp_summable_on)
      by auto
    with True show ?thesis
      by simp
  next
    case False
    then show ?thesis
      by auto
  qed
  show \<open>(\<Sum>\<^sub>\<infinity>d. trace_tc (if \<rho> \<ge> 0 \<and> trace_tc \<rho> \<le> 1 then of_bool (c = d) *\<^sub>R \<rho> else 0)) \<le> 1\<close>
  proof (cases \<open>\<rho> \<ge> 0 \<and> trace_tc \<rho> \<le> 1\<close>)
    case True
    have \<open>(\<Sum>\<^sub>\<infinity>d. trace_tc (of_bool (c = d) *\<^sub>R \<rho>)) = trace_tc \<rho>\<close>
      apply (subst infsum_single[where i=c])
      by auto
    also have \<open>trace_tc \<rho> \<le> 1\<close>
      using True by blast
    finally show ?thesis
      by (simp add: True)
  next
    case False
    then show ?thesis
      by auto
  qed
qed



(* type_synonym program_state = \<open>(cl,qu) cq_operator\<close> *)
quotient_type program_semantics = \<open>cl \<Rightarrow> (qu ell2, qu ell2, cl) kraus_family\<close> /
  partial: program_semantics_rel
proof (rule part_equivpI)
  show \<open>\<exists>x. program_semantics_rel x x\<close>
    apply (rule exI[of _ \<open>\<lambda>_. 0\<close>])
    by (simp add: program_semantics_rel_def)
  show \<open>symp program_semantics_rel\<close>
  proof (rule sympI)
    fix \<EE> \<FF> assume asm: \<open>program_semantics_rel \<EE> \<FF>\<close>
    then have eq1: \<open>kraus_equivalent' (\<EE> x) (\<FF> x)\<close> for x
      using program_semantics_rel_def by blast
    then have eq2: \<open>kraus_equivalent' (\<FF> x) (\<EE> x)\<close> for x
      using kraus_equivalent'_sym by blast
    from eq1 have eq3: \<open>kraus_equivalent (\<EE> x) (\<FF> x)\<close> for x
      by (rule kraus_equivalent'_imp_equivalent)
    have \<open>kraus_family_norm (\<EE> x) \<le> 1\<close> for x
      using asm program_semantics_rel_def by blast
    with eq3
    have norm: \<open>kraus_family_norm (\<FF> x) \<le> 1\<close> for x
      by (metis kraus_family_norm_welldefined)
    with eq2 show \<open>program_semantics_rel \<FF> \<EE>\<close>
      by (simp add: program_semantics_rel_def)
  qed
  show \<open>transp program_semantics_rel\<close>
    apply (auto intro!: transpI simp: program_semantics_rel_def)
    using kraus_equivalent'_trans by blast
qed
(* setup_lifting type_definition_program_semantics *)

lift_definition program_semantics_id :: program_semantics is 
  \<open>\<lambda>c. kraus_family_map_outcome (\<lambda>(). c) kraus_family_id\<close>
  by (simp add: program_semantics_rel_def)

lift_definition program_semantics_apply :: \<open>program_semantics \<Rightarrow> program_state \<Rightarrow> program_state\<close> is
  \<open>\<lambda>\<EE> \<rho> c. (\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (\<EE> d) (\<rho> d))\<close>
proof (rename_tac \<EE> \<EE>' \<rho>, intro conjI allI ext)
  fix \<EE> \<EE>' assume rel: \<open>program_semantics_rel \<EE> \<EE>'\<close>
  then have norm_\<EE>: \<open>kraus_family_norm (\<EE> x) \<le> 1\<close> for x
    using program_semantics_rel_def by blast
  fix \<rho> :: \<open>cl \<Rightarrow> (qu ell2, qu ell2) trace_class\<close> and c
  assume \<open>(\<forall>c. 0 \<le> \<rho> c) \<and> (\<lambda>c. trace_tc (\<rho> c)) summable_on UNIV \<and> (\<Sum>\<^sub>\<infinity>c. trace_tc (\<rho> c)) \<le> 1\<close>
  then have \<rho>_pos: \<open>0 \<le> \<rho> c\<close> and \<rho>_sum: \<open>(\<lambda>c. trace_tc (\<rho> c)) summable_on UNIV\<close> and \<rho>_leq1: \<open>(\<Sum>\<^sub>\<infinity>c. trace_tc (\<rho> c)) \<le> 1\<close> for c
    by auto
  from \<rho>_pos
  show \<open>0 \<le> (\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (\<EE> d) (\<rho> d))\<close>
    by (auto intro!: infsum_nonneg_traceclass kraus_family_map'_pos)


  from \<rho>_pos
  have 9: \<open>trace_tc (kraus_family_map (\<EE> d) (\<rho> d)) \<le> kraus_family_norm (\<EE> d) * trace_tc (\<rho> d)\<close> for d
    by (smt (verit) Extra_Ordered_Fields.complex_of_real_cmod cmod_mono complex_of_real_nn_iff 
        kraus_family_map_bounded_pos kraus_family_map_pos nn_comparable norm_tc_pos of_real_hom.hom_mult 
        of_real_hom.injectivity trace_tc_0 trace_tc_mono) 
  from \<rho>_pos have 10: \<open>\<dots>d \<le> trace_tc (\<rho> d)\<close> for d
    by (smt (verit) Extra_Ordered_Fields.complex_of_real_cmod Extra_Ordered_Fields.mult_sign_intros(1) cmod_mono complex_of_real_leq_1_iff complex_of_real_nn_iff kraus_family_norm_geq0 mult_left_le_one_le nn_comparable norm_\<EE> norm_mult trace_tc_0 trace_tc_mono) 
  have 0: \<open>0 \<le> Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))\<close> for c d
    by (metis Re_complex_of_real \<rho>_pos kraus_family_map'_pos norm_cblinfun_mono_trace_class norm_tc_pos norm_zero order_eq_refl)
  have 3: \<open>(\<Sum>\<^sub>\<infinity>c. kraus_family_map' {c} (\<EE> d) (\<rho> d)) = kraus_family_map (\<EE> d) (\<rho> d)\<close> for d
  proof -
    have \<open>(\<Sum>\<^sub>\<infinity>c. kraus_family_map' {c} (\<EE> d) (\<rho> d)) = (\<Sum>\<^sub>\<infinity>X\<in>range (\<lambda>c. {c}). kraus_family_map' X (\<EE> d) (\<rho> d))\<close>
      by (simp add: infsum_reindex o_def)
    also have \<open>\<dots> = kraus_family_map' (\<Union>(range (\<lambda>c. {c}))) (\<EE> d) (\<rho> d)\<close>
      apply (rule kraus_family_map'_union_infsum)
      by auto
    also have \<open>\<dots> = kraus_family_map (\<EE> d) (\<rho> d)\<close>
      by simp
    finally show ?thesis
      by -
  qed
  have 4: \<open>(\<lambda>c. kraus_family_map' {c} (\<EE> d) (\<rho> d)) summable_on UNIV\<close> for d
  proof -
    have \<open>(\<lambda>X. kraus_family_map' X (\<EE> d) (\<rho> d)) summable_on range (\<lambda>c. {c})\<close> for d
      apply (rule kraus_family_map'_union_summable_on)
      by auto
    then show ?thesis
      apply (rule summable_on_reindex[THEN iffD1, unfolded o_def, rotated])
      by simp
  qed
  have 16: \<open>bounded_linear (\<lambda>x. Re (trace_tc x))\<close> for x :: \<open>(qu ell2,qu ell2) trace_class\<close>
    by (intro bounded_linear_compose[OF bounded_linear_Re] bounded_linear_intros)
  from 3 4 have 5: \<open>(\<Sum>\<^sub>\<infinity>c. Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))) = Re (trace_tc (kraus_family_map (\<EE> d) (\<rho> d)))\<close> for d
    apply (subst infsum_bounded_linear[where f=\<open>Re o trace_tc\<close>, unfolded o_def])
    using 16 by auto
  have 13: \<open>0 \<le> Re (trace_tc (kraus_family_map (\<EE> d) (\<rho> d)))\<close> for d
    by (metis Re_complex_of_real \<rho>_pos kraus_family_map_pos norm_cblinfun_mono_trace_class norm_tc_pos norm_zero order_eq_refl)
  from \<rho>_sum   have 12:  \<open>(\<lambda>d. Re (trace_tc (\<rho> d))) summable_on UNIV\<close>
    using summable_on_Re by blast
  from 9 10 have 14: \<open>Re (trace_tc (kraus_family_map (\<EE> d) (\<rho> d))) \<le> Re (trace_tc (\<rho> d))\<close> for d
    apply (auto intro!: Re_mono)
    using basic_trans_rules(23) by blast
  have 6: \<open>(\<lambda>d. Re (trace_tc (kraus_family_map (\<EE> d) (\<rho> d)))) summable_on UNIV\<close>
    apply (rule summable_on_comparison_test[where f=\<open>\<lambda>d. Re (trace_tc (\<rho> d))\<close>])
    using 12 13 14 by auto
  from 6 have 11: \<open>(\<Sum>\<^sub>\<infinity>d. Re (trace_tc (kraus_family_map (\<EE> d) (\<rho> d)))) \<le> (\<Sum>\<^sub>\<infinity>d. Re (trace_tc (\<rho> d)))\<close>
    apply (rule infsum_mono)
    using 12 14 by auto
  have 28: \<open>norm (\<rho> d) = Re (trace_tc (\<rho> d))\<close> for d
    by (metis Re_complex_of_real \<rho>_pos norm_tc_pos)
  have 27: \<open>\<rho> summable_on UNIV\<close>
    apply (rule abs_summable_summable)
    using 12 28 by auto
  have 15: \<open>(\<Sum>\<^sub>\<infinity>d. Re (trace_tc (\<rho> d))) \<le> 1\<close>
    apply (subst infsum_bounded_linear[where f=\<open>Re o trace_tc\<close>, unfolded o_def])
    using 16 27 28 \<rho>_sum \<rho>_leq1 \<rho>_pos
      apply auto
    by (smt (verit) Infinite_Sum.infsum_nonneg_complex abs_summable_on_comparison_test cmod_mono complex_Re_le_cmod infsum_Re infsum_cong norm_infsum_bound norm_one summable_on_iff_abs_summable_on_complex trace_tc_norm trace_tc_pos)
  from 5 6 have 2: \<open>(\<lambda>d. \<Sum>\<^sub>\<infinity>c. Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))) summable_on UNIV\<close>
    by simp
  have 17: \<open>(\<Sum>\<^sub>\<infinity>d. \<Sum>\<^sub>\<infinity>c. Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))) \<le> 1\<close>
    using 5 15 11
    by auto
  have 29: \<open>(\<lambda>c. Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))) summable_on UNIV\<close> for d
    apply (rule summable_on_bounded_linear[where h=\<open>\<lambda>x. Re (trace_tc x)\<close>])
    using 16 4 by auto
  have 18: \<open>(\<lambda>(d,c). Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))) summable_on (UNIV \<times> UNIV)\<close>
    apply (rule summable_on_SigmaI[where g=\<open>\<lambda>d. \<Sum>\<^sub>\<infinity>c. Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))\<close>])
    using 0 5 6 29 by (auto intro!: has_sumI)
  have 21: \<open>(\<lambda>d. Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))) summable_on UNIV\<close> for c
    using summable_on_SigmaD1[OF summable_on_swap[THEN iffD1, OF 18]]
    by auto
  have 22: \<open>(\<lambda>c. \<Sum>\<^sub>\<infinity>d. Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))) summable_on UNIV\<close>
    apply (rule summable_on_Sigma_banach)
    apply (rule summable_on_swap[THEN iffD2])
    using 18 by simp
  have 20: \<open>(\<lambda>(c, d). Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))) summable_on UNIV\<close>
    apply (subst asm_rl[of \<open>UNIV = UNIV \<times> UNIV\<close>], simp)
    apply (rule summable_on_SigmaI[where g=\<open>\<lambda>c. \<Sum>\<^sub>\<infinity>d. Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))\<close>])
    using 21 22 0 by (auto intro!: has_sum_infsum)
  from 17 18 20 have 19: \<open>(\<Sum>\<^sub>\<infinity>c. \<Sum>\<^sub>\<infinity>d. Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))) \<le> 1\<close>
    apply (subst infsum_swap_banach)
    by auto
  have 36: \<open>norm (kraus_family_map' {c} (\<EE> d) (\<rho> d)) = Re (trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d)))\<close> for c d
    apply (rule norm_tc_pos_Re)
    by (simp add: \<rho>_pos kraus_family_map'_pos)
  from 36 have 35: \<open>(\<lambda>d. kraus_family_map' {c} (\<EE> d) (\<rho> d)) abs_summable_on UNIV\<close> for c
    by (simp add: 36 21)
  from 35 have 34: \<open>(\<lambda>d. kraus_family_map' {c} (\<EE> d) (\<rho> d)) summable_on UNIV\<close> for c
    by (rule abs_summable_summable)
  from 22 have 23: \<open>(\<lambda>c. Re (trace_tc (\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (\<EE> d) (\<rho> d)))) summable_on UNIV\<close>
    apply (rule summable_on_cong[THEN iffD1, rotated])
    using 16 34 by (rule infsum_bounded_linear[unfolded o_def])
  have 25: \<open>(\<Sum>\<^sub>\<infinity>c. \<Sum>\<^sub>\<infinity>d. trace_tc (kraus_family_map' {c} (\<EE> d) (\<rho> d))) \<ge> 0\<close>
    by (auto intro!: infsum_nonneg_complex trace_tc_pos kraus_family_map'_pos \<rho>_pos)
  from 23 show \<open>(\<lambda>c. trace_tc (\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (\<EE> d) (\<rho> d))) summable_on UNIV\<close>
    apply (rewrite at \<open>trace_tc _\<close> of_real_Re[symmetric])
    by (auto intro!: nonnegative_complex_is_real summable_on_bounded_linear[where h=of_real]
        bounded_linear_of_real trace_tc_pos  infsum_nonneg_traceclass kraus_family_map'_pos \<rho>_pos)
  have 26: \<open>(\<Sum>\<^sub>\<infinity>c. Re (trace_tc (\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (\<EE> d) (\<rho> d)))) \<le> 1\<close>
    apply (subst infsum_bounded_linear[OF 16, symmetric, unfolded o_def])
    using 19 34 by auto
  from 26 show \<open>(\<Sum>\<^sub>\<infinity>c. trace_tc (\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (\<EE> d) (\<rho> d))) \<le> 1\<close>
    apply (rewrite at \<open>trace_tc _\<close> of_real_Re[symmetric])
    by (auto intro!: nonnegative_complex_is_real summable_on_bounded_linear[where h=of_real]
        bounded_linear_of_real trace_tc_pos  infsum_nonneg_traceclass kraus_family_map'_pos \<rho>_pos
        simp: infsum_of_real )
  from rel
  show \<open>(\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (\<EE> d) (\<rho> d)) = (\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (\<EE>' d) (\<rho> d))\<close>
    by (auto intro!: kraus_family_map'_eqI infsum_cong simp: program_semantics_rel_def)
qed

lift_definition program_semantics_seq :: \<open>program_semantics \<Rightarrow> program_semantics \<Rightarrow> program_semantics\<close>
  is \<open>\<lambda>\<EE> \<FF> c. kraus_family_map_outcome snd (kraus_family_comp_dependent \<FF> (\<EE> c))\<close>
proof -
  fix \<EE> \<FF> \<EE>' \<FF>' assume asms: \<open>program_semantics_rel \<EE> \<EE>'\<close>  \<open>program_semantics_rel \<FF> \<FF>'\<close>
  have F1: \<open>kraus_family_norm (\<FF>' x) \<le> 1\<close> for x
    by (metis asms(2) kraus_equivalent'_imp_equivalent kraus_family_norm_welldefined program_semantics_rel_def)
  have \<open>kraus_family_norm (kraus_family_comp_dependent \<FF> (\<EE> x)) \<le> 1 * kraus_family_norm (\<EE> x)\<close> for x
    apply (rule kraus_family_comp_dependent_norm)
    using asms(2) program_semantics_rel_def by blast
  also have \<open>\<dots>x \<le> 1 * 1\<close> for x
    using asms(1) program_semantics_rel_def by force
  finally have 1: \<open>kraus_family_norm (kraus_family_comp_dependent \<FF> (\<EE> x)) \<le> 1\<close> for x
    by simp
  have 2: \<open>kraus_equivalent' (kraus_family_map_outcome snd (kraus_family_comp_dependent \<FF> (\<EE> x)))
                 (kraus_family_map_outcome snd (kraus_family_comp_dependent \<FF>' (\<EE>' x)))\<close> for x
    using asms
    by (auto intro!: F1 bdd_aboveI kraus_equivalent'_map_cong kraus_family_comp_dependent_cong'
        simp: program_semantics_rel_def)
  from 1 2
  show \<open>program_semantics_rel (\<lambda>c. kraus_family_map_outcome snd (kraus_family_comp_dependent \<FF> (\<EE> c)))
        (\<lambda>c. kraus_family_map_outcome snd (kraus_family_comp_dependent \<FF>' (\<EE>' c)))\<close>
    by (simp add: program_semantics_rel_def)
qed

(* TODO move *)
lemma kraus_family_map'_0_right[simp]: \<open>kraus_family_map' X \<EE> 0 = 0\<close>
  by (simp add: kraus_family_map'_def)

lemma program_semantics_eqI:
  assumes \<open>\<And>\<rho>. program_semantics_apply s \<rho> = program_semantics_apply t \<rho>\<close>
  shows \<open>s = t\<close>
proof -
  from assms[THEN Rep_program_state_inject[THEN iffD2]]
  have *: \<open>(\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (rep_program_semantics s d) (Rep_program_state \<rho> d))
      = (\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (rep_program_semantics t d) (Rep_program_state \<rho> d))\<close> for c \<rho>
    apply (simp add: program_semantics_apply.rep_eq)
    by meson
  have \<open>kraus_family_map' {c} (rep_program_semantics s d) \<rho> = kraus_family_map' {c} (rep_program_semantics t d) \<rho>\<close>
    if \<open>\<rho> \<ge> 0\<close> and \<open>trace_tc \<rho> \<le> 1\<close> for c d \<rho>
    using *[of c \<open>fixed_cl_program_state d \<rho>\<close>]
    unfolding fixed_cl_program_state.rep_eq
    apply (subst (asm) infsum_single[where i=d])
     apply auto[1]
    apply (subst (asm) infsum_single[where i=d])
    using that by auto
  then have \<open>kraus_family_map' {c} (rep_program_semantics s d) = kraus_family_map' {c} (rep_program_semantics t d)\<close> for c d
    apply (rule eq_from_separatingI[OF separating_density_ops[where B=1], rotated -1])
        apply (auto intro!: kraus_family_map'_bounded_clinear bounded_clinear.clinear)
    using complex_of_real_mono norm_tc_pos by fastforce
  from fun_cong[OF this] have \<open>kraus_equivalent' (rep_program_semantics s c) (rep_program_semantics t c)\<close> for c
    by (rule kraus_equivalent'I)
  then show ?thesis
    apply (rule_tac Quotient3_rel_rep[OF Quotient3_program_semantics, THEN iffD1])
    using Quotient3_rep_reflp[OF Quotient3_program_semantics, of s]
    using Quotient3_rep_reflp[OF Quotient3_program_semantics, of t]
    by (simp add: program_semantics_rel_def)
qed

lemma program_semantics_apply_id[simp]: \<open>program_semantics_apply program_semantics_id \<rho> = \<rho>\<close>
proof transfer'
  fix \<rho> :: \<open>cl \<Rightarrow> (qu ell2, qu ell2) trace_class\<close>
  have inj: \<open>inj_on (\<lambda>(). x) X\<close> for x :: cl and X
    by (simp add: inj_onI)

  show \<open>(\<lambda>c. \<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (kraus_family_map_outcome (\<lambda>(). d) kraus_family_id) (\<rho> d)) = \<rho>\<close>
  proof (rule ext)
    fix c
    have 1: \<open>Set.filter (\<lambda>(E, x). x = c) {(id_cblinfun, j)} = {}\<close> if \<open>j \<noteq> c\<close> for j :: cl
      using that by auto

    have \<open>(\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (kraus_family_map_outcome (\<lambda>(). d) kraus_family_id) (\<rho> d))
      = (\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (kraus_family_map_outcome_inj (\<lambda>(). d) kraus_family_id) (\<rho> d))\<close>
      by (auto intro!: infsum_cong kraus_family_map'_eqI kraus_equivalent'_map_outcome_inj[symmetric] inj)
    also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>d. \<Sum>E\<in>Set.filter (\<lambda>(E, x). x = c) {(id_cblinfun, d)}. sandwich_tc (fst E) (\<rho> d))\<close>
      by (simp add: kraus_family_map'_def kraus_family_map.rep_eq kraus_family_filter.rep_eq
          kraus_family_map_outcome_inj.rep_eq kraus_family_id_def kraus_family_of_op.rep_eq Nitpick.case_unit_unfold)
    also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>E\<in>Set.filter (\<lambda>(E::qu ell2 \<Rightarrow>\<^sub>C\<^sub>L qu ell2, x). x = c) {(id_cblinfun, c)}. \<rho> c)\<close>
      apply (subst infsum_single[where i=c])
      by (auto simp: 1)
    also have \<open>\<dots> = \<rho> c\<close>
      apply (subst infsum_single[where i=\<open>(id_cblinfun,c)\<close>])
      by auto
    finally show \<open>(\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (kraus_family_map_outcome (\<lambda>(). d) kraus_family_id) (\<rho> d)) = \<rho> c\<close>
      by -
  qed
qed

lemma program_semantics_apply_seq: \<open>program_semantics_apply (program_semantics_seq s t) \<rho> = program_semantics_apply t (program_semantics_apply s \<rho>)\<close>
proof (transfer, intro ext)
  fix s t :: \<open>cl \<Rightarrow> (qu ell2, qu ell2, cl) kraus_family\<close> and \<rho> :: \<open>cl \<Rightarrow> (qu ell2, qu ell2) trace_class\<close> and c :: cl
  assume assms: \<open>(\<forall>c. 0 \<le> \<rho> c) \<and> (\<lambda>c. trace_tc (\<rho> c)) summable_on UNIV \<and> (\<Sum>\<^sub>\<infinity>c. trace_tc (\<rho> c)) \<le> 1\<close>
  assume \<open>program_semantics_rel s s\<close>
  assume \<open>program_semantics_rel t t\<close>
  then have bdd_t: \<open>bdd_above (range (kraus_family_norm \<circ> t))\<close>
    by (auto simp: program_semantics_rel_def)
  have inj: \<open>inj_on fst (Set.filter (\<lambda>(E, x). x = f) X)\<close> for X f
    by (auto intro!: inj_onI)
  from bdd_t have bdd': \<open>bdd_above (range (kraus_family_norm \<circ> (\<lambda>e. kraus_family_filter (\<lambda>f. f = c) (t e))))\<close>
    apply (rule bdd_above_mono2)
    by (auto simp: kraus_family_norm_filter)
  have \<rho>_abs: \<open>\<rho> abs_summable_on UNIV\<close>
    by (smt (verit) assms complex_Re_le_cmod norm_tc_pos_Re summable_on_cong summable_on_iff_abs_summable_on_complex trace_tc_norm)

  have summ2: \<open>(\<lambda>d. kraus_family_map' {f} (s d) (\<rho> d)) summable_on UNIV\<close> for f
  proof (rule abs_summable_summable, rule abs_summable_on_comparison_test)
    from \<rho>_abs show \<open>\<rho> abs_summable_on UNIV\<close>
      by -
    fix d
    have \<open>norm (kraus_family_map' {f} (s d) (\<rho> d)) \<le> kraus_family_norm (kraus_family_filter (\<lambda>x. x = f) (s d)) * norm (\<rho> d)\<close>
      using assms by (auto intro!: kraus_family_map_bounded_pos simp add: kraus_family_map'_def)
    also have \<open>\<dots> \<le> 1 * norm (\<rho> d)\<close>
      apply (rule mult_right_mono)
      using \<open>program_semantics_rel s s\<close>
        kraus_family_norm_filter[of \<open>\<lambda>x. x = f\<close> \<open>s d\<close>]
       apply (auto intro!: simp: program_semantics_rel_def)
      by (smt (verit, del_insts))
    also have \<open>\<dots> \<le> norm (\<rho> d)\<close>
      by simp
    finally show \<open>norm (kraus_family_map' {f} (s d) (\<rho> d)) \<le> norm (\<rho> d)\<close>
      by -
  qed
  have summ3: \<open>(\<lambda>F. sandwich_tc F (\<rho> c)) summable_on {F. (F, f) \<in> Rep_kraus_family (s c)}\<close> for c f
  proof -
    have *: \<open>(\<lambda>x. fst x) ` Set.filter (\<lambda>Ff. snd Ff = f) (Rep_kraus_family (s c))
        = {F. (F, f) \<in> Rep_kraus_family (s c)}\<close>
      by (auto intro!: simp: image_iff Bex_def)
    from kraus_family_map_summable[of _ \<open>s c\<close>]
    have \<open>(\<lambda>Ff. sandwich_tc (fst Ff) (\<rho> c)) summable_on Rep_kraus_family (s c)\<close>
      by (simp add: case_prod_unfold)
    then have \<open>(\<lambda>Ff. sandwich_tc (fst Ff) (\<rho> c)) summable_on Set.filter (\<lambda>Ff. snd Ff = f) (Rep_kraus_family (s c))\<close>
      apply (rule summable_on_subset_banach)
      by auto
    then show ?thesis
      apply (subst (asm) summable_on_reindex[unfolded o_def, symmetric, where h=fst])
      by (auto intro!: inj_onI simp: * )
  qed
(*   have summ: \<open>(\<lambda>F. kraus_family_map' {c} (t f) (sandwich_tc F (\<rho> d))) summable_on
       {F. (F, f) \<in> Rep_kraus_family (s d)}\<close> for f d c
    by x *)
  have summ4: \<open>(\<lambda>y. kraus_family_map' {c} (t y) (kraus_family_map' {y} (s d) (\<rho> d))) summable_on UNIV\<close> for d
  proof -
    have 1: \<open>(\<lambda>f. kraus_family_map' {f} (s d) (\<rho> d)) abs_summable_on UNIV\<close>
    proof -
      have \<open>(\<lambda>X. kraus_family_map' X (s d) (\<rho> d)) summable_on range (\<lambda>f. {f})\<close>
        apply (rule kraus_family_map'_union_summable_on)
        by auto
      then have \<open>(\<lambda>f. kraus_family_map' {f} (s d) (\<rho> d)) summable_on UNIV\<close>
        apply (subst (asm) summable_on_reindex)
        by (simp_all add: o_def)
      then show ?thesis
        apply (rule summable_abs_summable_tc)
        using assms by (auto intro!: kraus_family_map'_pos simp: )
    qed
    have 2: \<open>norm (kraus_family_map' {c} (t f) (kraus_family_map' {f} (s d) (\<rho> d)))
         \<le> norm (kraus_family_map' {f} (s d) (\<rho> d))\<close> for f
    proof -
      have \<open>norm (kraus_family_map' {c} (t f) (kraus_family_map' {f} (s d) (\<rho> d)))
        \<le> kraus_family_norm (kraus_family_filter (\<lambda>x. x\<in>{c}) (t f)) * norm (kraus_family_map' {f} (s d) (\<rho> d))\<close>
        using assms
        by (auto intro!: kraus_family_map_bounded_pos
            simp: kraus_family_map'_def kraus_family_map_pos)
      also have \<open>\<dots> \<le> 1 * norm (kraus_family_map' {f} (s d) (\<rho> d))\<close>
        apply (rule mult_right_mono)
         apply (smt (verit, best) \<open>program_semantics_rel t t\<close> kraus_family_norm_filter program_semantics_rel_def)
        by simp
      finally show ?thesis
        by simp
    qed
    show ?thesis
      apply (rule abs_summable_summable)
      using 1 2 by (rule abs_summable_on_comparison_test)
  qed

  have \<open>(\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (kraus_family_map_outcome snd (kraus_family_comp_dependent t (s d))) (\<rho> d))
     = (\<Sum>\<^sub>\<infinity>d. kraus_family_map (kraus_family_filter (\<lambda>(e, f). f=c \<and> True) (kraus_family_comp_dependent t (s d))) (\<rho> d))\<close>
    by (simp add: kraus_family_map'_def kraus_family_filter_map_outcome case_prod_unfold)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>d. kraus_family_map (kraus_family_comp_dependent (\<lambda>e. kraus_family_filter (\<lambda>f. f = c) (t e)) (s d)) (\<rho> d))\<close>
    apply (subst kraus_family_filter_comp_dependent)
    using bdd_t by simp_all
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>d. \<Sum>\<^sub>\<infinity>(F, f)\<in>Rep_kraus_family (s d). kraus_family_map' {c} (t f) (sandwich_tc F (\<rho> d)))\<close>
    using bdd'
    by (simp add: kraus_family_comp_dependent_apply kraus_family_map'_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>d. \<Sum>\<^sub>\<infinity>(f, F)\<in>prod.swap ` Rep_kraus_family (s d). kraus_family_map' {c} (t f) (sandwich_tc F (\<rho> d)))\<close>
    apply (subst infsum_reindex)
    by (auto intro!: inj_onI simp: o_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>d. \<Sum>\<^sub>\<infinity>(f, F)\<in>(SIGMA f:UNIV. {F. (F, f) \<in> Rep_kraus_family (s d)}). kraus_family_map' {c} (t f) (sandwich_tc F (\<rho> d)))\<close>
    apply (rule infsum_cong)
    apply (rule arg_cong[where f=\<open>infsum _\<close>])
    by fastforce
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>d. \<Sum>\<^sub>\<infinity>f. \<Sum>\<^sub>\<infinity>F\<in>{F. (F,f) \<in> Rep_kraus_family (s d)}. kraus_family_map' {c} (t f) (sandwich_tc F (\<rho> d)))\<close>
    apply (rule infsum_cong)
    apply (subst infsum_Sigma_positive_tc)
    using assms by (auto intro!: summ3 kraus_family_map'_pos sandwich_tc_pos
        summable_on_bounded_linear[where h=\<open>kraus_family_map' _ _\<close>]
        bounded_clinear.bounded_linear kraus_family_map'_bounded_clinear)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>d. \<Sum>\<^sub>\<infinity>f. kraus_family_map' {c} (t f) (\<Sum>\<^sub>\<infinity>F\<in>{F. (F,f) \<in> Rep_kraus_family (s d)}. sandwich_tc F (\<rho> d)))\<close>
    apply (intro infsum_cong)
    apply (rule infsum_bounded_linear[unfolded o_def])
    by (auto intro!: bounded_clinear.bounded_linear kraus_family_map'_bounded_clinear summ3)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>d. \<Sum>\<^sub>\<infinity>f. kraus_family_map' {c} (t f) (kraus_family_map' {f} (s d) (\<rho> d)))\<close>
    apply (auto intro!: infsum_cong arg_cong[where f=\<open>kraus_family_map' _ _\<close>]
        simp: kraus_family_map'_def kraus_family_map.rep_eq kraus_family_filter.rep_eq)
    apply (subst infsum_reindex[OF inj, symmetric, unfolded o_def])
    by (auto intro!: arg_cong[where f=\<open>sandwich_tc _\<close>] arg_cong[where f=\<open>infsum _\<close>]
        simp: image_iff Bex_def)
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>f. \<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (t f) (kraus_family_map' {f} (s d) (\<rho> d)))\<close>
    apply (rule infsum_swap_positive_tc)
    using assms
    by (auto intro!: summ4 summ2 summable_on_bounded_linear[where h=\<open>kraus_family_map' _ _\<close>]
        bounded_clinear.bounded_linear kraus_family_map'_bounded_clinear kraus_family_map'_pos simp: )
  also have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>f. kraus_family_map' {c} (t f) (\<Sum>\<^sub>\<infinity>d. kraus_family_map' {f} (s d) (\<rho> d)))\<close>
    apply (intro infsum_cong)
    apply (rule infsum_bounded_linear[unfolded o_def])
    by (auto intro!: bounded_clinear.bounded_linear kraus_family_map'_bounded_clinear summ2)
  finally  show \<open>(\<Sum>\<^sub>\<infinity>d. kraus_family_map' {c} (kraus_family_map_outcome snd (kraus_family_comp_dependent t (s d))) (\<rho> d)) =
       (\<Sum>\<^sub>\<infinity>f. kraus_family_map' {c} (t f) (\<Sum>\<^sub>\<infinity>d. kraus_family_map' {f} (s d) (\<rho> d)))\<close>
    by -
qed


lemma program_semantics_seq_id_right[simp]: \<open>program_semantics_seq s program_semantics_id = s\<close>
  apply (rule program_semantics_eqI)
  by (simp add: program_semantics_apply_seq)

lemma program_semantics_seq_id_left[simp]: \<open>program_semantics_seq program_semantics_id s = s\<close>
  apply (rule program_semantics_eqI)
  by (simp add: program_semantics_apply_seq)


lift_definition program_semantics_sample :: \<open>cl distr expression \<Rightarrow> program_semantics\<close> is
  \<open>\<lambda>e c. kraus_map_sample (prob (e c))\<close>
  by (simp add: program_semantics_rel_def kraus_map_sample_norm prob_summable )

lift_definition program_semantics_if :: \<open>bool expression \<Rightarrow> program_semantics \<Rightarrow> program_semantics \<Rightarrow> program_semantics\<close> is
  \<open>\<lambda>e p q c. if e c then p c else q c\<close>
  by (simp add: program_semantics_rel_def)

lift_definition program_semantics_quantum_op :: \<open>(qu ell2, qu ell2, unit) kraus_family expression \<Rightarrow> program_semantics\<close> is
  \<open>\<lambda>(\<EE>::(qu ell2, qu ell2, unit) kraus_family expression) c. 
      kraus_family_map_outcome (\<lambda>_. c) (if kraus_family_norm (\<EE> c) \<le> 1 then \<EE> c else 0)\<close>
  by (simp add: program_semantics_rel_def)

text \<open>\<^term>\<open>copy_CREGISTER_from F m n\<close> takes the content of \<^term>\<open>F\<close> from m and everything outside of \<^term>\<open>F\<close> from n
  and returns the combination. See \<^term>\<open>copy_CREGISTER_from_CREGISTER_of\<close> below.\<close>
lift_definition copy_CREGISTER_from :: \<open>'a CREGISTER \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> is
  \<open>\<lambda>F m0 m1. SOME m. \<exists>a\<in>F. \<exists>b\<in>map_commutant F. Some m = a m1 \<and> Some m = b m0\<close>.

lemma copy_CREGISTER_from_bot[simp]:
  \<open>copy_CREGISTER_from \<bottom> m0 m1 = m1\<close>
proof -
  have [simp]: \<open>Some \<in> empty_cregister_range\<close>
    by (simp add: empty_cregister_range_def)
  have \<open>\<exists>a\<in>empty_cregister_range. \<exists>b\<in>map_commutant empty_cregister_range. Some m1 = a m1 \<and> Some m1 = b m0\<close>
    apply (rule bexI[of _ Some], rule bexI[of _ \<open>\<lambda>_. Some m1\<close>])
    by auto
  moreover have \<open>m = m1\<close> 
    if \<open>\<exists>a\<in>empty_cregister_range. \<exists>b\<in>map_commutant empty_cregister_range. Some m = a m1 \<and> Some m = b m0\<close> for m
    using that by (simp add: empty_cregister_range_def)
  ultimately have \<open>(SOME m. \<exists>a\<in>empty_cregister_range. \<exists>b\<in>map_commutant empty_cregister_range. Some m = a m1 \<and> Some m = b m0) = m1\<close>
    by (rule some_equality)
  then show ?thesis
    apply (transfer' fixing: m0 m1)
    by simp
qed

lemma CREGISTER_of_non_cregister[simp]: \<open>CREGISTER_of non_cregister = \<bottom>\<close>
  by (simp add: CREGISTER_of.abs_eq bot_CREGISTER_def)

lemma apply_cregister_getter_setter:
  assumes \<open>cregister F\<close>
  shows \<open>apply_cregister F a m = (case a (getter F m) of None \<Rightarrow> None | Some x \<Rightarrow> Some (setter F x m))\<close>
  using assms
  apply (transfer' fixing: a)
  apply (subst register_from_getter_setter_of_getter_setter[symmetric])
  by (auto intro!: simp: register_from_getter_setter_def[abs_def])

lemma map_commutant_range_apply_cregister:
  \<open>map_commutant (range (apply_cregister F)) 
    = range (\<lambda>f m. case f (setter F m0 m) of None \<Rightarrow> None | Some m' \<Rightarrow> Some (setter F (getter F m) m'))\<close>
proof (cases \<open>cregister F\<close>)
  case True
  note [simp] = True
  define g s where \<open>g = getter F\<close> and \<open>s = setter F\<close>
  have [simp]: \<open>g (s x m) = x\<close> for x m
    by (simp add: g_def s_def)
  have [simp]: \<open>s x (s y m) = s x m\<close> for x y m
    by (simp add: s_def)
  have [simp]: \<open>s (g m) m = m\<close> for m
    by (simp add: g_def s_def)
  have F_Some_x: \<open>apply_cregister F (\<lambda>_. Some x) = Some o s x\<close> for x
    apply (subst apply_cregister_getter_setter[OF True, abs_def])
    by (simp add: s_def o_def)
  show ?thesis
  proof (intro Set.set_eqI iffI range_eqI ext)
    fix h
    assume \<open>h \<in> range
              (\<lambda>f m. case f (Classical_Registers.setter F m0 m) of None \<Rightarrow> None
                      | Some m' \<Rightarrow> Some (Classical_Registers.setter F (Classical_Registers.getter F m) m'))\<close>
    then obtain f where h_f: \<open>h m = (case f (Classical_Registers.setter F m0 m) of None \<Rightarrow> None
                      | Some m' \<Rightarrow> Some (Classical_Registers.setter F (Classical_Registers.getter F m) m'))\<close> for m
      by auto
    have \<open>(h \<circ>\<^sub>m apply_cregister F a) m = (apply_cregister F a \<circ>\<^sub>m h) m\<close>
      for m a 
      unfolding map_comp_def h_f apply_cregister_getter_setter[OF True, folded g_def s_def, abs_def] 
        g_def[symmetric] s_def[symmetric]
      apply (cases \<open>a (g m)\<close>; cases \<open>f (s m0 m)\<close>)
      by (auto intro!: ext)
    then show \<open>h \<in> map_commutant (range (apply_cregister F))\<close>
      by (auto intro!: ext simp: map_commutant_def)
  next
    fix h m assume \<open>h \<in> map_commutant (range (apply_cregister F))\<close>
    then have comm: \<open>(h \<circ>\<^sub>m apply_cregister F a) m = (apply_cregister F a \<circ>\<^sub>m h) m\<close> for a m
      by (simp add: map_commutant_def)
    have \<open>(case h (s m0 m) of None \<Rightarrow> None | Some m' \<Rightarrow> Some (s (g m) m'))
        = ((Some o s (g m)) \<circ>\<^sub>m h) (s m0 m)\<close>
      by (simp add: map_comp_def o_def)
    also have \<open>\<dots> = (apply_cregister F (\<lambda>_. Some (g m)) \<circ>\<^sub>m h) (s m0 m)\<close>
      by (simp add: F_Some_x)
    also have \<open>\<dots> = (h \<circ>\<^sub>m apply_cregister F (\<lambda>_. Some (g m))) (s m0 m)\<close>
      by (simp add: comm)
    also have \<open>\<dots> = h m\<close>
      by (simp add: F_Some_x)
    finally show \<open>h m =
           (case h (setter F m0 m) of None \<Rightarrow> None
            | Some m' \<Rightarrow> Some (setter F (getter F m) m'))\<close>
      by (simp add: g_def s_def cong: option.case_cong)
  qed
next
  case False
  then have [simp]: \<open>F = non_cregister\<close>
    using non_cregister by blast
  show ?thesis
    by (simp add: non_cregister.rep_eq non_cregister_raw_def redundant_option_case cong: option.case_cong)
qed

lemma copy_CREGISTER_from_CREGISTER_of:
  fixes F :: \<open>('a,'b) cregister\<close>
  assumes [simp]: \<open>cregister F\<close>
  shows \<open>copy_CREGISTER_from (CREGISTER_of F) m0 m1 = setter F (getter F m0) m1\<close>
proof -
  define g s where \<open>g = getter F\<close> and \<open>s = setter F\<close>
  have [simp]: \<open>g (s x m) = x\<close> for x m
    by (simp add: g_def s_def)
  have [simp]: \<open>s x (s y m) = s x m\<close> for x y m
    by (simp add: s_def)
  have [simp]: \<open>s (g m) m = m\<close> for m
    by (simp add: g_def s_def)
  define F' where \<open>F' = range (apply_cregister F)\<close>
  define m where \<open>m = s (g m0) m1\<close>
  have \<open>\<exists>a\<in>F'. \<exists>b\<in>map_commutant F'. Some m = a m1 \<and> Some m = b m0\<close>
  proof (rule bexI[of _ \<open>\<lambda>m'. Some (s (g m) m')\<close>],
      rule bexI[of _ \<open>\<lambda>m'. Some (s (g m') m1)\<close>], rule conjI)
    show \<open>Some m = Some (s (g m) m1)\<close>
      by (simp add: m_def)
    show \<open>Some m = Some (s (g m0) m1)\<close>
      by (simp add: m_def)
    show \<open>(\<lambda>m'. Some (s (g m') m1)) \<in> map_commutant F'\<close>
    proof -
      have \<open>((\<lambda>m'. Some (s (g m') m1)) \<circ>\<^sub>m apply_cregister F a) x =
           apply_cregister F a (s (g x) m1)\<close> for a x
        apply (cases \<open>a (g x)\<close>)
        by (auto intro!: ext simp add: apply_cregister_getter_setter s_def g_def)
      then show ?thesis
        by (auto intro!: ext simp add: F'_def map_commutant_def)
    qed
    show \<open>(\<lambda>m'. Some (s (g m) m')) \<in> F'\<close>
      by (auto intro!: ext exI[of _ \<open>\<lambda>_. Some (g m)\<close>] simp add: F'_def image_iff apply_cregister_getter_setter s_def g_def)
  qed
  moreover have \<open>\<exists>a\<in>F'. \<exists>b\<in>map_commutant F'. Some m' = a m1 \<and> Some m' = b m0 \<Longrightarrow> m' = m\<close> for m'
  proof (erule bexE, erule bexE)
    fix a b assume a: \<open>a \<in> F'\<close> and \<open>b \<in> map_commutant F'\<close> and m'_ab: \<open>Some m' = a m1 \<and> Some m' = b m0\<close>
    from \<open>a \<in> F'\<close> obtain a' where \<open>a = apply_cregister F a'\<close>
      by (auto simp: F'_def)
    then have a': \<open>a m = (case a' (g m) of None \<Rightarrow> None | Some x \<Rightarrow> Some (s x m))\<close> for m
      by (simp add: apply_cregister_getter_setter g_def option.case_eq_if s_def)
    from \<open>b \<in> map_commutant F'\<close>
    obtain b' where b': \<open>b m = (case b' (s m_fix m) of None \<Rightarrow> None
         | Some m' \<Rightarrow> Some (s (g m) m'))\<close> for m
      apply atomize_elim
      by (auto simp: map_commutant_range_apply_cregister[of F m_fix, folded F'_def s_def g_def])
    have gmm': \<open>g m' = g m\<close>
    proof -
      from m'_ab have \<open>Some m' = b m0\<close>
        by auto
      then obtain x where \<open>m' = s (g m0) x\<close>
        apply atomize_elim
        apply (cases \<open>b' (s m_fix m0)\<close>)
        by (auto intro!: simp: b')
      then show ?thesis
        by (simp add: m_def)
    qed
    have \<open>s x m = s x m'\<close> for x
    proof -
      from m'_ab have \<open>Some m' = a m1\<close>
        by simp
      then show ?thesis
        apply (cases \<open>a' (g m1)\<close>)
        by (auto simp add: a' m_def)
    qed
    with gmm' have \<open>s (g m) m = s (g m') m'\<close>
      by metis
    then show \<open>m' = m\<close>
      by simp
  qed
  ultimately have \<open>(SOME m. \<exists>a\<in>F'. \<exists>b\<in>map_commutant F'. Some m = a m1 \<and> Some m = b m0) = m\<close>
    by (rule some_equality)
  with assms show ?thesis
    apply (simp only: m_def F'_def s_def g_def)
    apply (transfer' fixing: m0 m1)
    by auto
qed


lift_definition program_semantics_local_c :: \<open>cl CREGISTER \<Rightarrow> cl \<Rightarrow> program_semantics \<Rightarrow> program_semantics\<close> is
  \<open>\<lambda>F init \<EE> c. kraus_family_map_outcome (\<lambda>d. copy_CREGISTER_from F c d) (\<EE> (copy_CREGISTER_from F init c))\<close>
  by (simp add: program_semantics_rel_def kraus_equivalent'_map_cong)

axiomatization program_semantics_local_q :: \<open>qu QREGISTER \<Rightarrow> (qu ell2, qu ell2) trace_class \<Rightarrow> program_semantics \<Rightarrow> program_semantics\<close>

axiomatization program_semantics_while :: \<open>bool expression \<Rightarrow> program_semantics \<Rightarrow> program_semantics\<close>



(* lemma kraus_map_from_measurement_norm: 
  assumes \<open>M \<noteq> 0\<close>
  shows \<open>kraus_family_norm (kraus_map_from_measurement M) = 1\<close> *)

(* lemma kraus_map_from_measurement_0: \<open>kraus_equivalent' (kraus_map_from_measurement 0) 0\<close> *)

lift_definition program_semantics_measurement :: \<open>(cl, qu) measurement expression \<Rightarrow> program_semantics\<close> is
  \<open>\<lambda>m c. kraus_map_from_measurement (m c)\<close>
  by (auto intro!: kraus_map_from_measurement_norm_leq1 simp: program_semantics_rel_def)

fun denotation_raw :: \<open>raw_program \<Rightarrow> program_semantics\<close> where
  denotation_raw_Skip: \<open>denotation_raw Skip = program_semantics_id\<close>
| denotation_raw_Seq:  \<open>denotation_raw (Seq c d) = program_semantics_seq (denotation_raw c) (denotation_raw d)\<close>
| denotation_raw_Sample: \<open>denotation_raw (Sample e) = program_semantics_sample e\<close>
| denotation_raw_IfThenElse: \<open>denotation_raw (IfThenElse e c d) = program_semantics_if e (denotation_raw c) (denotation_raw d)\<close>
| denotation_raw_While: \<open>denotation_raw (While e c) = program_semantics_while e (denotation_raw c)\<close>
| denotation_raw_QuantumOp: \<open>denotation_raw (QuantumOp \<EE>) = program_semantics_quantum_op \<EE>\<close>
| denotation_raw_Measurement: \<open>denotation_raw (Measurement m) = program_semantics_measurement m\<close>
| denotation_raw_OracleCall: \<open>denotation_raw (OracleCall _) = undefined\<close>
  \<comment> \<open>\<^const>\<open>OracleCall\<close> should not occur in valid programs\<close>
| denotation_raw_InstantiateOracles: \<open>denotation_raw (InstantiateOracles _ _) = undefined\<close>
  \<comment> \<open>\<^const>\<open>InstantiateOracles\<close> should not occur in valid programs\<close>
| denotation_raw_LocalC: \<open>denotation_raw (LocalC F init c) = program_semantics_local_c F init (denotation_raw c)\<close>
| denotation_raw_LocalQ: \<open>denotation_raw (LocalQ F init c) = program_semantics_local_q F init (denotation_raw c)\<close>



(* fun denotation_raw :: "raw_program \<Rightarrow> program_semantics" where
  denotation_raw_Skip: \<open>denotation_raw Skip = cq_kraus_family_id\<close>
| denotation_raw_Seq: \<open>denotation_raw (Seq c d) = cq_kraus_family_comp (denotation_raw d) (denotation_raw c)\<close>
| denotation_raw_Sample: \<open>denotation_raw (Sample e) = 
      cq_operator_cases (\<lambda>c \<rho>. cq_diagonal_operator (prob (e c)) \<rho>) \<rho>\<close>

fun denotation_raw :: "raw_program \<Rightarrow> program_state \<Rightarrow> program_state" where
  denotation_raw_Skip: \<open>denotation_raw Skip \<rho> = \<rho>\<close>
| denotation_raw_Seq: \<open>denotation_raw (Seq c d) \<rho> = denotation_raw d (denotation_raw c \<rho>)\<close>
| denotation_raw_Sample: \<open>denotation_raw (Sample e) \<rho> = cq_operator_cases (\<lambda>c \<rho>. cq_from_distrib (e c) \<rho>) \<rho>\<close>
(* TODO missing cases *)
 *)

lift_definition denotation :: "program \<Rightarrow> program_semantics" is denotation_raw.

lift_definition program_state_distrib :: "program_state \<Rightarrow> cl distr" is
  \<open>\<lambda>\<rho> c. norm (\<rho> c)\<close>
proof -
  fix \<rho> :: \<open>cl \<Rightarrow> (qu ell2, qu ell2) trace_class\<close>
  assume asm: \<open>(\<forall>c. 0 \<le> \<rho> c) \<and> (\<lambda>c. trace_tc (\<rho> c)) summable_on UNIV \<and> (\<Sum>\<^sub>\<infinity>c. trace_tc (\<rho> c)) \<le> 1\<close>
  have \<open>(\<lambda>c. trace_tc (\<rho> c)) summable_on UNIV\<close>
    by (metis asm)
  then have Re_sum: \<open>(\<lambda>c. Re (trace_tc (\<rho> c))) summable_on UNIV\<close>
    using summable_on_Re by blast
  then have abs_sum: \<open>(\<lambda>c. \<rho> c) abs_summable_on UNIV\<close>
    by (meson asm norm_tc_pos_Re summable_on_cong)
  have \<open>(\<Sum>\<^sub>\<infinity>c. Re (trace_tc (\<rho> c))) \<le> Re 1\<close>
    by (metis Re_mono asm infsum_Re)
  then have \<open>(\<Sum>\<^sub>\<infinity>c. norm (\<rho> c)) \<le> 1\<close>
    by (smt (verit, ccfv_SIG) Re_sum asm abs_sum infsum_mono norm_tc_pos_Re one_complex.simps(1))
  with abs_sum show \<open>is_distribution (\<lambda>c. norm (\<rho> c))\<close>
    by (simp add: is_distribution_def)
qed

lemma denotation_sample: \<open>denotation (sample x e) = program_semantics_sample (\<lambda>m. map_distr (\<lambda>xa. Classical_Registers.setter x xa m) (e m))\<close>
  apply (transfer' fixing: x e)
  by simp

(* TODO nicer one *)
lemma denotation_assign: \<open>denotation (assign x e) = program_semantics_sample (\<lambda>m. point_distr (Classical_Registers.setter x (e m) m))\<close>
  by (simp add: assign_def denotation_sample)

lemma denotation_skip: \<open>denotation skip = program_semantics_id\<close>
  apply transfer' 
  by simp

lemma denotation_seq: \<open>denotation (seq p q) = program_semantics_seq (denotation p) (denotation q)\<close>
  apply transfer' by (auto intro!: ext)

lemma denotation_block: "denotation (block ps) = foldr (\<lambda>p s. program_semantics_seq (denotation p) s) ps program_semantics_id"
proof (induction ps rule:block.induct)
  case 1
  show ?case
    by (simp add: block_empty denotation_skip)
next
  case (2 p)
  show ?case
    by (simp add: block_single denotation_skip)
next
  case (3 p v va)
  then show ?case
    by (simp add: block_cons denotation_seq)
qed

definition probability :: "bool expression \<Rightarrow> program \<Rightarrow> program_state \<Rightarrow> real" where
  "probability e p \<rho> = Prob (program_state_distrib (program_semantics_apply (denotation p) \<rho>)) (Collect e)"

(* consts "probability_syntax" :: "bool \<Rightarrow> program \<Rightarrow> program_state \<Rightarrow> real" ("Pr[_ : (_'(_'))]")
translations "CONST probability_syntax a b c" \<rightleftharpoons> "CONST probability (Expr[a]) b c"
hide_const probability_syntax *)

lemma probability_sample: 
  "probability (expression m f) (block [sample m (const_expression D)]) rho
  = Prob D (Collect f)"
  apply (simp add: probability_def denotation_block denotation_sample)
  sorry

lemma equal_until_bad: 
  assumes "probability (map_expression2 (|) e b) g3 rho \<ge> probability b g4 rho"
  assumes "probability (map_expression2 (\<lambda>e b. \<not>e&b) e b) g3 rho \<le> probability b g4 rho"
  shows "abs (probability b g3 rho - probability b g4 rho) \<le> probability e g3 rho"
proof -
  define d3 d4 where \<open>d3 = program_state_distrib (program_semantics_apply (denotation g3) rho)\<close>
    and \<open>d4 = program_state_distrib (program_semantics_apply (denotation g4) rho)\<close>
  from assms have assm1: \<open>Prob d4 (Collect b) \<le> Prob d3 {m. e m \<or> b m}\<close>
    and assm2: \<open>Prob d3 {m. \<not> e m \<and> b m} \<le> Prob d4 (Collect b)\<close>
    by (simp_all add: probability_def d3_def d4_def)

  have EorB: "Collect b \<union> Collect e = {m. e m \<or> b m}"
    by auto
  have EandB: "Collect b - Collect e = {m. \<not> e m \<and> b m}"
    by auto

  from assm1 have a1: "Prob d4 (Collect b) \<le> Prob d3 (Collect b \<union> Collect e)"
    unfolding EorB unfolding defs probability_def by auto
  from assm2 have a2: "Prob d3 (Collect b - Collect e) \<le> Prob d4 (Collect b)"
    unfolding EandB unfolding defs probability_def by auto

  have "Prob d3 (Collect b) \<le> Prob d3 (Collect b - Collect e) + Prob d3 (Collect e)"
    apply (subst Prob_setdiff) by simp
  also have "\<dots> \<le> Prob d4 (Collect b) + Prob d3 (Collect e)"
    using a2 by simp
  finally have bound1: "Prob d3 (Collect b) - Prob d4 (Collect b) \<le> Prob d3 (Collect e)"
    by linarith

  have "Prob d4 (Collect b) \<le> Prob d3 (Collect b \<union> Collect e)"
    using a1 by assumption
  also have "\<dots> \<le> Prob d3 (Collect b) + Prob d3 (Collect e)"
    unfolding Prob_union by simp
  finally have bound2: "Prob d4 (Collect b) - Prob d3 (Collect b) \<le> Prob d3 (Collect e)"
    by linarith

  from bound1 bound2 have "\<bar>Prob d3 (Collect b) - Prob d4 (Collect b)\<bar> \<le> Prob d3 (Collect e)"
    by linarith

  then show ?thesis
    by (simp add: probability_def d3_def d4_def)
qed


named_theorems program_bodies
named_theorems program_fv


ML_file "programs.ML"

consts "probability_syntax" :: "bool expression \<Rightarrow> program \<Rightarrow> program_state \<Rightarrow> real" ("Pr[_:(_'(_'))]")
translations "CONST probability_syntax a b c" \<rightleftharpoons> "CONST probability (Expr[a]) b c"
(* translations "CONST probability_syntax a b c" \<rightleftharpoons> "CONST probability a b c" *)
hide_const probability_syntax

end
