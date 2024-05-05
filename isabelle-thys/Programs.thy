theory Programs
  imports QRHL_Core Expressions Wlog.Wlog Kraus_Maps CQ_Operators
begin

no_notation Lattice.join (infixl "\<squnion>\<index>" 65)
no_notation Order.bottom ("\<bottom>\<index>")

lift_definition cq_map_sample :: \<open>('cl1 \<Rightarrow> 'cl2 distr) \<Rightarrow> ('cl1,'qu,'cl2,'qu) cq_map\<close> is
  \<open>\<lambda>e c. kraus_map_sample (prob (e c))\<close>
  by (simp add: cq_map_rel_def kraus_map_sample_norm prob_summable )

lift_definition cq_operator_distrib :: "('cl,'qu) cq_operator \<Rightarrow> 'cl distr" is
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

fun no_oracles :: \<open>raw_program \<Rightarrow> bool\<close> where
\<open>no_oracles (Seq c d) \<longleftrightarrow> no_oracles c \<and> no_oracles d\<close>
| \<open>no_oracles (IfThenElse e c d) \<longleftrightarrow> no_oracles c \<and> no_oracles d\<close>
| \<open>no_oracles (While e c) \<longleftrightarrow> no_oracles c\<close>
| \<open>no_oracles (LocalQ _ _ c) \<longleftrightarrow> no_oracles c\<close>
| \<open>no_oracles (LocalC _ _ c) \<longleftrightarrow> no_oracles c\<close>
| \<open>no_oracles (OracleCall _) \<longleftrightarrow> False\<close>
| \<open>no_oracles (InstantiateOracles _ _) \<longleftrightarrow> False\<close>
| \<open>no_oracles p \<longleftrightarrow> True\<close>


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
| \<open>valid_oracle_program c \<Longrightarrow> no_oracles c \<Longrightarrow> valid_program c\<close>


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
  moreover have \<open>no_oracles (Seq p q)\<close>
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

lift_definition ifthenelse1 :: \<open>bool expression \<Rightarrow> program \<Rightarrow> program \<Rightarrow> program\<close> is IfThenElse
  by (auto intro!: valid_oracle_program_valid_program.intros simp: valid_program.simps)

definition ifthenelse :: \<open>bool expression \<Rightarrow> program list \<Rightarrow> program list \<Rightarrow> program\<close> where
  \<open>ifthenelse c p q = ifthenelse1 c (block p) (block q)\<close>

lift_definition while1 :: \<open>bool expression \<Rightarrow> program \<Rightarrow> program\<close> is While
  by (auto intro!: valid_oracle_program_valid_program.intros simp: valid_program.simps)

definition while :: \<open>bool expression \<Rightarrow> program list \<Rightarrow> program\<close> where
  \<open>while c p = while1 c (block p)\<close>

(* lift_definition qinit :: \<open>'a qvariable \<Rightarrow> 'a ell2 expression \<Rightarrow> program\<close> is
\<open>\<lambda>... QuantumOp\<close> *)

consts
  qinit :: "'a qvariable \<Rightarrow> 'a ell2 expression \<Rightarrow> program"
  measurement :: "'a cvariable \<Rightarrow> 'b qvariable \<Rightarrow> ('a,'b) measurement expression \<Rightarrow> program"
  instantiateOracles :: "oracle_program \<Rightarrow> program list \<Rightarrow> program"
  localvars :: "'a cvariable \<Rightarrow> 'b qvariable \<Rightarrow> program list \<Rightarrow> program"

(* fun fvq_raw_program :: \<open>raw_program \<Rightarrow> QVARIABLE\<close> where
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
| \<open>fvq_raw_program (OracleCall _) = \<bottom>\<close> *)


lemma localvars_empty: "localvars empty_cregister empty_qregister P = block P"
  sorry


(* definition \<open>swap_QREGISTER' = (\<lambda>(f,U,L,R).
  sandwich (U \<otimes>\<^sub>o U) (classical_operator (Some o map_prod (inv f) (inv f) o (\<lambda>((x,y),(z,w)). ((z,y),(x,w))) o map_prod f f))
)\<close> *)

lift_definition cq_map_local_c :: \<open>'cl CREGISTER \<Rightarrow> 'cl \<Rightarrow> ('cl, 'qu1, 'cl, 'qu2) cq_map \<Rightarrow> ('cl, 'qu1, 'cl, 'qu2) cq_map\<close> is
  \<open>\<lambda>F init \<EE> c. kraus_family_map_outcome (\<lambda>d. copy_CREGISTER_from F c d) (\<EE> (copy_CREGISTER_from F init c))\<close>
  by (simp add: cq_map_rel_def kraus_equivalent'_map_cong)



(* 
lemma von_neumann_factor_tensor:
  assumes \<open>von_neumann_factor A\<close>
  assumes \<open>von_neumann_factor B\<close>
  shows \<open>von_neumann_factor (A \<otimes>\<^sub>v\<^sub>N B)\<close>

https://math.stackexchange.com/questions/4794773/tensor-product-of-factors-is-a-factor

 *)



(* definition swap_QREGISTER :: \<open>'a QREGISTER \<Rightarrow> ('a\<times>'a) qupdate\<close> where
  \<open>swap_QREGISTER Q = the_default 0 (swap_QREGISTER' ` {(f :: 'a \<Rightarrow> 'a\<times>'a, U, L, R). unitary U \<and> 
    inj f \<and> range f = L \<times> R \<and>
    Rep_QREGISTER Q = {sandwich U a | a. actual_qregister_range_aux f a}})\<close> *)



(* TODO: generalize (not only "type", rep/abs args) *)
lemma with_type_conj:
  assumes \<open>\<forall>\<^sub>\<tau> 'a::type = A. P\<close>
    and \<open>\<forall>\<^sub>\<tau> 'b::type = B. Q\<close>
  shows \<open>\<forall>\<^sub>\<tau> 'a::type = A. \<forall>\<^sub>\<tau> 'b::type = B. P \<and> Q\<close>
  apply (auto intro!: simp: with_type_def)
  by (smt (verit, ccfv_threshold) assms(1) assms(2) prod.case_eq_if prod.simps(2) with_type_def)

lemma with_type_mp2:
  assumes \<open>with_type CR (S,p) (\<lambda>Rep Abs. with_type CR' (S',p') (P Rep Abs))\<close>
  assumes \<open>(\<And>Rep Abs Rep' Abs'. type_definition Rep Abs S \<Longrightarrow> fst CR S p \<Longrightarrow> type_definition Rep' Abs' S' \<Longrightarrow> fst CR' S' p' \<Longrightarrow>
               P Rep Abs Rep' Abs' \<Longrightarrow> Q Rep Abs Rep' Abs')\<close>
  shows \<open>with_type CR (S,p) (\<lambda>Rep Abs. with_type CR' (S',p') (Q Rep Abs))\<close>
  using assms by (auto simp add: with_type_def case_prod_beta)


(* TODO: Run inner cq_map with a \<rho>-initialized second part. *)
definition cq_map_auxiliary_state ::
  \<open>('aux ell2, 'aux ell2) trace_class \<Rightarrow> ('cl1, 'qu1\<times>'aux, 'cl2, 'qu2\<times>'aux) cq_map \<Rightarrow> ('cl1,'qu1,'cl2,'qu2) cq_map\<close> where
  \<open>cq_map_auxiliary_state \<rho> \<EE> = undefined\<close>

lift_definition cq_map_tensor_id_right :: \<open>('cl1, 'qu1, 'cl2, 'qu2) cq_map \<Rightarrow> ('cl1, 'qu1\<times>'extra, 'cl2, 'qu2\<times>'extra) cq_map\<close> is
  \<open>\<lambda>\<EE> c. kraus_family_map_outcome fst (kraus_family_tensor (\<EE> c) kraus_family_id)\<close>
  apply (auto intro!: kraus_equivalent'_map_cong kraus_family_tensor_cong'
      simp: cq_map_rel_def )
  by (smt (verit) kraus_family_norm_tensor kraus_map_norm_id mult_cancel_left2)

definition cq_map_local_q :: 
  \<open>'qu QREGISTER \<Rightarrow> ('qu ell2, 'qu ell2) trace_class \<Rightarrow> ('cl1,'qu,'cl2,'qu) cq_map \<Rightarrow> ('cl1,'qu,'cl2,'qu) cq_map\<close> where
  \<open>cq_map_local_q Q \<rho> \<EE> = cq_map_auxiliary_state \<rho> (
    cq_map_seq  (cq_map_of_op (swap_QREGISTER Q))
    (cq_map_seq (cq_map_tensor_id_right \<EE>)
                (cq_map_of_op (swap_QREGISTER Q))))\<close>

axiomatization cq_map_while :: \<open>bool expression \<Rightarrow> ('cl,'qu,'cl','qu) cq_map \<Rightarrow> ('cl,'qu,'cl','qu) cq_map\<close>



(* lemma kraus_map_from_measurement_norm: 
  assumes \<open>M \<noteq> 0\<close>
  shows \<open>kraus_family_norm (kraus_map_from_measurement M) = 1\<close> *)

(* lemma kraus_map_from_measurement_0: \<open>kraus_equivalent' (kraus_map_from_measurement 0) 0\<close> *)

lift_definition cq_map_measurement :: \<open>('cl1 \<Rightarrow> ('cl2, 'qu) measurement) \<Rightarrow> ('cl1,'qu,'cl2,'qu) cq_map\<close> is
  \<open>\<lambda>m c. kraus_map_from_measurement (m c)\<close>
  by (auto intro!: kraus_map_from_measurement_norm_leq1 simp: cq_map_rel_def)

fun denotation_raw :: \<open>raw_program \<Rightarrow> (cl,qu,cl,qu) cq_map\<close> where
  denotation_raw_Skip: \<open>denotation_raw Skip = cq_map_id\<close>
| denotation_raw_Seq:  \<open>denotation_raw (Seq c d) = cq_map_seq (denotation_raw c) (denotation_raw d)\<close>
| denotation_raw_Sample: \<open>denotation_raw (Sample e) = cq_map_sample e\<close>
| denotation_raw_IfThenElse: \<open>denotation_raw (IfThenElse e c d) = cq_map_if e (denotation_raw c) (denotation_raw d)\<close>
| denotation_raw_While: \<open>denotation_raw (While e c) = cq_map_while e (denotation_raw c)\<close>
| denotation_raw_QuantumOp: \<open>denotation_raw (QuantumOp \<EE>) = cq_map_quantum_op \<EE>\<close>
| denotation_raw_Measurement: \<open>denotation_raw (Measurement m) = cq_map_measurement m\<close>
| denotation_raw_OracleCall: \<open>denotation_raw (OracleCall _) = undefined\<close>
  \<comment> \<open>\<^const>\<open>OracleCall\<close> should not occur in valid programs\<close>
| denotation_raw_InstantiateOracles: \<open>denotation_raw (InstantiateOracles _ _) = undefined\<close>
  \<comment> \<open>\<^const>\<open>InstantiateOracles\<close> should not occur in valid programs\<close>
| denotation_raw_LocalC: \<open>denotation_raw (LocalC F init c) = cq_map_local_c F init (denotation_raw c)\<close>
| denotation_raw_LocalQ: \<open>denotation_raw (LocalQ F init c) = cq_map_local_q F init (denotation_raw c)\<close>



(* fun denotation_raw :: "raw_program \<Rightarrow> cq_map" where
  denotation_raw_Skip: \<open>denotation_raw Skip = cq_kraus_family_id\<close>
| denotation_raw_Seq: \<open>denotation_raw (Seq c d) = cq_kraus_family_comp (denotation_raw d) (denotation_raw c)\<close>
| denotation_raw_Sample: \<open>denotation_raw (Sample e) = 
      cq_operator_cases (\<lambda>c \<rho>. cq_diagonal_operator (prob (e c)) \<rho>) \<rho>\<close>

fun denotation_raw :: "raw_program \<Rightarrow> cq_operator \<Rightarrow> cq_operator" where
  denotation_raw_Skip: \<open>denotation_raw Skip \<rho> = \<rho>\<close>
| denotation_raw_Seq: \<open>denotation_raw (Seq c d) \<rho> = denotation_raw d (denotation_raw c \<rho>)\<close>
| denotation_raw_Sample: \<open>denotation_raw (Sample e) \<rho> = cq_operator_cases (\<lambda>c \<rho>. cq_from_distrib (e c) \<rho>) \<rho>\<close>
(* TODO missing cases *)
 *)

lift_definition denotation :: "program \<Rightarrow> (cl,qu,cl,qu) cq_map" is denotation_raw.

lemma denotation_sample: \<open>denotation (sample x e) = cq_map_sample (\<lambda>m. map_distr (\<lambda>xa. Classical_Registers.setter x xa m) (e m))\<close>
  apply (transfer' fixing: x e)
  by simp

(* TODO nicer one *)
lemma denotation_assign: \<open>denotation (assign x e) = cq_map_sample (\<lambda>m. point_distr (Classical_Registers.setter x (e m) m))\<close>
  by (simp add: assign_def denotation_sample)

lemma denotation_skip: \<open>denotation skip = cq_map_id\<close>
  apply transfer' 
  by simp

lemma denotation_seq: \<open>denotation (seq p q) = cq_map_seq (denotation p) (denotation q)\<close>
  apply transfer' by (auto intro!: ext)

lemma denotation_block: "denotation (block ps) = foldr (\<lambda>p s. cq_map_seq (denotation p) s) ps cq_map_id"
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

lift_definition kraus_family_in_qref_strict :: \<open>('qu ell2,'qu ell2,'cl) kraus_family \<Rightarrow> 'qu QREGISTER \<Rightarrow> bool\<close> is
  \<open>\<lambda>\<EE> Q. \<forall>(E,x)\<in>\<EE>. E \<in> Rep_QREGISTER Q\<close>.
definition kraus_family_in_qref :: \<open>('qu ell2,'qu ell2,'cl) kraus_family \<Rightarrow> 'qu QREGISTER \<Rightarrow> bool\<close> where
  \<open>kraus_family_in_qref \<EE> Q \<longleftrightarrow> (\<exists>\<FF>. kraus_equivalent' \<EE> \<FF> \<and> kraus_family_in_qref_strict \<FF> Q)\<close>

lift_definition qc_map_in_qref :: \<open>('cl1,'qu,'cl2,'qu) cq_map \<Rightarrow> 'qu QREGISTER \<Rightarrow> bool\<close> is
  \<open>\<lambda>\<EE> Q. \<forall>x. kraus_family_in_qref (\<EE> x) Q\<close>
  apply (auto intro!: simp: cq_map_rel_def kraus_family_in_qref_def)
  using kraus_equivalent'_trans kraus_equivalent'_sym
  by meson

definition fvq_of_cq_map :: \<open>(cl, qu, cl, qu) cq_map \<Rightarrow> QVARIABLE\<close> where
  \<open>fvq_of_cq_map \<EE> = Inf {Q. qc_map_in_qref \<EE> Q}\<close>

definition fvq_program :: \<open>program \<Rightarrow> QVARIABLE\<close> where
  \<open>fvq_program p = fvq_of_cq_map (denotation p)\<close>

function fvq_raw_program :: \<open>raw_program \<Rightarrow> QVARIABLE\<close> where
 \<open>no_oracles p \<Longrightarrow> fvq_raw_program p = fvq_of_cq_map (denotation_raw p)\<close>
| \<open>\<not> no_oracles (Seq p q) \<Longrightarrow> fvq_raw_program (Seq p q) = fvq_raw_program p \<squnion> fvq_raw_program q\<close>
| \<open>\<not> no_oracles (IfThenElse c p q) \<Longrightarrow> fvq_raw_program (IfThenElse c p q) = fvq_raw_program p \<squnion> fvq_raw_program q\<close>
| \<open>\<not> no_oracles (While c p) \<Longrightarrow> fvq_raw_program (While c p) = fvq_raw_program p\<close>
| \<open>fvq_raw_program (InstantiateOracles p qs) = fvq_raw_program p \<squnion> (\<Squnion>q\<in>set qs. fvq_raw_program q)\<close>
| \<open>\<not> no_oracles (LocalQ Q \<rho> p) \<Longrightarrow> fvq_raw_program (LocalQ Q \<rho> p) = undefined\<close> (* TODO *)
| \<open>\<not> no_oracles (LocalC C c p) \<Longrightarrow> fvq_raw_program (LocalC C c p) = fvq_raw_program p\<close>
| \<open>fvq_raw_program (OracleCall _) = \<bottom>\<close>
                      apply atomize_elim
  by (auto elim: no_oracles.elims)
termination by lexicographic_order

consts fvc_program :: "program \<Rightarrow> CVARIABLE"
consts fvcw_program :: "program \<Rightarrow> CVARIABLE"
consts fvc_oracle_program :: "oracle_program \<Rightarrow> CVARIABLE"
consts fvcw_oracle_program :: "oracle_program \<Rightarrow> CVARIABLE"

lemma fvq_program_skip[simp]: \<open>fvq_program skip = \<bottom>\<close>
  sorry

(* TODO Truth is \<le> *)
lemma fvq_program_seq: \<open>fvq_program (seq a b) = fvq_program a \<squnion> fvq_program b\<close>
  sorry

(* TODO Truth is \<le> *)
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
  sorry
lemma fvq_program_assign: "fvq_program (assign x e) = QREGISTER_unit"
  sorry
(* TODO Truth is \<le> *)
lemma fvq_program_ifthenelse: "fvq_program (ifthenelse c p1 p2) =
  QREGISTER_pair (fvq_program (block p1)) (fvq_program (block p2))"
  sorry
(* TODO Truth is \<le> *)
lemma fvq_program_while: "fvq_program (while c b) = (fvq_program (block b))"
  sorry
(* TODO Truth is \<le>. Or is = correct? *)
lemma fvq_program_qinit: "fvq_program (qinit Q e3) = QREGISTER_of Q"
  sorry
(* TODO Truth is \<le> *)
lemma fvq_program_qapply: "fvq_program (qapply Q e4) = QREGISTER_of Q"
  sorry
(* TODO Truth is \<le> *)
lemma fvq_program_measurement: "fvq_program (measurement x R e5) = QREGISTER_of R"
  sorry

(* TODO Truth is \<le> *)
lemma fvc_program_sequence: "fvc_program (block b) = fold (\<lambda>p v. CREGISTER_pair (fvc_program p) v) b CREGISTER_unit"
  sorry
(* TODO Truth is \<le> *)
lemma fvc_program_assign: "fvc_program (assign x e) = CREGISTER_pair (CREGISTER_of x) (fv_expression e)"
  sorry
(* TODO Truth is \<le> *)
lemma fvc_program_sample: "fvc_program (sample x e) = CREGISTER_pair (CREGISTER_of x) (fv_expression e)"
  sorry
(* TODO Truth is \<le> *)
lemma fvc_program_ifthenelse: "fvc_program (ifthenelse c p1 p2) =
  CREGISTER_pair (fv_expression c) (CREGISTER_pair (fvc_program (block p1)) (fvc_program (block p2)))"
  sorry
(* TODO Truth is \<le> *)
lemma fvc_program_while: "fvc_program (while c b) = 
  CREGISTER_pair (fv_expression c) (fvc_program (block b))"
  sorry
(* TODO Truth is \<le> *)
lemma fvc_program_qinit: "fvc_program (qinit Q e3) = fv_expression e3"
  sorry
(* TODO Truth is \<le> *)
lemma fvc_program_qapply: "fvc_program (qapply Q e4) = fv_expression e4"
  sorry
(* TODO Truth is \<le> *)
lemma fvc_program_measurement: "fvc_program (measurement x R e) = CREGISTER_pair (CREGISTER_of x) (fv_expression e)"
  sorry

(* TODO Truth is \<le> *)
lemma fvcw_program_sequence: "fvcw_program (block b) = fold (\<lambda>p v. CREGISTER_pair (fvcw_program p) v) b CREGISTER_unit"
  sorry
(* TODO Truth is \<le> *)
lemma fvcw_program_assign: "fvcw_program (assign x e) = CREGISTER_of x"
  sorry
(* TODO Truth is \<le> *)
lemma fvcw_program_sample: "fvcw_program (sample x e2) = CREGISTER_of x"
  sorry
(* TODO Truth is \<le> *)
lemma fvcw_program_ifthenelse: "fvcw_program (ifthenelse c p1 p2) =
  CREGISTER_pair (fvc_program (block p1)) (fvc_program (block p2))"
  sorry
(* TODO Truth is \<le> *)
lemma fvcw_program_while: "fvcw_program (while c b) = fvcw_program (block b)"
  sorry
lemma fvcw_program_qinit: "fvcw_program (qinit Q e3) = CREGISTER_unit"
  sorry
lemma fvcw_program_qapply: "fvcw_program (qapply Q e4) = CREGISTER_unit"
  sorry
(* TODO Truth is \<le> *)
lemma fvcw_program_measurement: "fvcw_program (measurement x R e5) = CREGISTER_of x"
  sorry

definition probability :: "bool expression \<Rightarrow> program \<Rightarrow> (cl,qu) cq_operator \<Rightarrow> real" where
  "probability e p \<rho> = Prob (cq_operator_distrib (cq_map_apply (denotation p) \<rho>)) (Collect e)"

(* consts "probability_syntax" :: "bool \<Rightarrow> program \<Rightarrow> cq_operator \<Rightarrow> real" ("Pr[_ : (_'(_'))]")
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
  define d3 d4 where \<open>d3 = cq_operator_distrib (cq_map_apply (denotation g3) rho)\<close>
    and \<open>d4 = cq_operator_distrib (cq_map_apply (denotation g4) rho)\<close>
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

consts "probability_syntax" :: "bool expression \<Rightarrow> program \<Rightarrow> (cl,qu) cq_operator \<Rightarrow> real" ("Pr[_:(_'(_'))]")
translations "CONST probability_syntax a b c" \<rightleftharpoons> "CONST probability (Expr[a]) b c"
(* translations "CONST probability_syntax a b c" \<rightleftharpoons> "CONST probability a b c" *)
hide_const probability_syntax

end
