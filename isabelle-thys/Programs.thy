theory Programs
  imports QRHL_Core Expressions Wlog.Wlog Kraus_Maps CQ_Operators
begin

no_notation Lattice.join (infixl "\<squnion>\<index>" 65)
no_notation Order.bottom ("\<bottom>\<index>")

lift_definition program_semantics_sample :: \<open>('cl \<Rightarrow> 'cl distr) \<Rightarrow> ('cl,'qu) program_semantics\<close> is
  \<open>\<lambda>e c. kraus_map_sample (prob (e c))\<close>
  by (simp add: program_semantics_rel_def kraus_map_sample_norm prob_summable )

lift_definition program_state_distrib :: "('cl,'qu) program_state \<Rightarrow> 'cl distr" is
  \<open>\<lambda>\<rho> c. norm (\<rho> c)\<close>
proof -
  fix \<rho> :: \<open>'cl \<Rightarrow> ('qu ell2, 'qu ell2) trace_class\<close>
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


lift_definition program_semantics_local_c :: \<open>cl CREGISTER \<Rightarrow> cl \<Rightarrow> (cl,qu) program_semantics \<Rightarrow> (cl,qu) program_semantics\<close> is
  \<open>\<lambda>F init \<EE> c. kraus_family_map_outcome (\<lambda>d. copy_CREGISTER_from F c d) (\<EE> (copy_CREGISTER_from F init c))\<close>
  by (simp add: program_semantics_rel_def kraus_equivalent'_map_cong)

axiomatization program_semantics_local_q :: \<open>qu QREGISTER \<Rightarrow> (qu ell2, qu ell2) trace_class \<Rightarrow> (cl,qu) program_semantics \<Rightarrow> (cl,qu) program_semantics\<close>

axiomatization program_semantics_while :: \<open>bool expression \<Rightarrow> (cl,qu) program_semantics \<Rightarrow> (cl,qu) program_semantics\<close>



(* lemma kraus_map_from_measurement_norm: 
  assumes \<open>M \<noteq> 0\<close>
  shows \<open>kraus_family_norm (kraus_map_from_measurement M) = 1\<close> *)

(* lemma kraus_map_from_measurement_0: \<open>kraus_equivalent' (kraus_map_from_measurement 0) 0\<close> *)

lift_definition program_semantics_measurement :: \<open>(cl, qu) measurement expression \<Rightarrow> (cl,qu) program_semantics\<close> is
  \<open>\<lambda>m c. kraus_map_from_measurement (m c)\<close>
  by (auto intro!: kraus_map_from_measurement_norm_leq1 simp: program_semantics_rel_def)

fun denotation_raw :: \<open>raw_program \<Rightarrow> (cl,qu) program_semantics\<close> where
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

lift_definition denotation :: "program \<Rightarrow> (cl,qu) program_semantics" is denotation_raw.

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

definition probability :: "bool expression \<Rightarrow> program \<Rightarrow> (cl,qu) program_state \<Rightarrow> real" where
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

consts "probability_syntax" :: "bool expression \<Rightarrow> program \<Rightarrow> (cl,qu) program_state \<Rightarrow> real" ("Pr[_:(_'(_'))]")
translations "CONST probability_syntax a b c" \<rightleftharpoons> "CONST probability (Expr[a]) b c"
(* translations "CONST probability_syntax a b c" \<rightleftharpoons> "CONST probability a b c" *)
hide_const probability_syntax

end
