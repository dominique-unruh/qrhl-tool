theory Programs
  imports QRHL_Core Expressions Wlog.Wlog Kraus_Maps CQ_Operators
begin

no_notation Lattice.join (infixl "\<squnion>\<index>" 65)
no_notation Order.bottom ("\<bottom>\<index>")

lift_definition cq_map_sample :: \<open>('cl \<Rightarrow> 'cl distr) \<Rightarrow> ('cl,'qu) cq_map\<close> is
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

term QuantumOp

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


lift_definition cq_map_local_c :: \<open>cl CREGISTER \<Rightarrow> cl \<Rightarrow> (cl,qu) cq_map \<Rightarrow> (cl,qu) cq_map\<close> is
  \<open>\<lambda>F init \<EE> c. kraus_family_map_outcome (\<lambda>d. copy_CREGISTER_from F c d) (\<EE> (copy_CREGISTER_from F init c))\<close>
  by (simp add: cq_map_rel_def kraus_equivalent'_map_cong)

(* definition \<open>swap_QREGISTER' = (\<lambda>(f,U,L,R).
  sandwich (U \<otimes>\<^sub>o U) (classical_operator (Some o map_prod (inv f) (inv f) o (\<lambda>((x,y),(z,w)). ((z,y),(x,w))) o map_prod f f))
)\<close> *)

definition minimal_projection_in :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a) set \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow> bool\<close> where
  \<open>minimal_projection_in A P \<longleftrightarrow> P \<in> A \<and> is_Proj P \<and> P \<noteq> 0 \<and> (\<forall>P'\<in>A. is_Proj P' \<longrightarrow> P' \<le> P \<longrightarrow> P' \<noteq> 0 \<longrightarrow> P' = P)\<close>

definition is_swap_on_qupdate_set :: \<open>'a qupdate set \<Rightarrow> ('a\<times>'a) qupdate \<Rightarrow> bool\<close> where
  \<open>is_swap_on_qupdate_set Q U \<longleftrightarrow> U \<in> Q \<otimes>\<^sub>v\<^sub>N Q \<and> unitary U \<and> (\<forall>a\<in>Q. \<forall>b\<in>Q. sandwich U (a \<otimes>\<^sub>o b) = b \<otimes>\<^sub>o a)
       \<and> (\<forall>a. minimal_projection_in Q a \<longrightarrow> U o\<^sub>C\<^sub>L (a \<otimes>\<^sub>o a) = a \<otimes>\<^sub>o a)\<close>

lift_definition swap_QREGISTER :: \<open>'a QREGISTER \<Rightarrow> ('a\<times>'a) qupdate\<close> is
  \<open>\<lambda>Q. the_default 0 (Collect (is_swap_on_qupdate_set Q))\<close>.

lemma range_apply_qregister_factor[iff]:
  fixes F :: \<open>('a, 'b) qregister\<close>
  assumes \<open>qregister F\<close>
  shows \<open>von_neumann_factor (range (apply_qregister F))\<close>
proof -
  from qcomplement_exists[OF assms]
  have \<open>\<forall>\<^sub>\<tau> 'c::type = qregister_decomposition_basis F. von_neumann_factor (range (apply_qregister F))\<close>
  proof (rule with_type_mp)
    assume \<open>\<exists>G::('c, 'b) qregister. qcomplements F G\<close>
    then obtain G :: \<open>('c, 'b) qregister\<close> where \<open>qcomplements F G\<close>
      by blast
    define F' G' FG FG' where \<open>F' = apply_qregister F\<close> and \<open>G' = apply_qregister G\<close> and \<open>FG = qregister_pair F G\<close> and \<open>FG' = apply_qregister FG\<close>
    have \<open>iso_qregister FG\<close>
      using FG_def \<open>qcomplements F G\<close> qcomplements_def' by blast
    then have [iff]: \<open>inj FG'\<close>
      using FG'_def inj_qregister iso_qregister_def by blast
    have vN: \<open>von_neumann_algebra (range F')\<close>
      by (metis assms valid_qregister_range valid_qregister_range_def F'_def)
    have \<open>range F' \<inter> commutant (range F') = range F' \<inter> range G'\<close>
      using F'_def G'_def \<open>qcomplements F G\<close>
      by (metis qcomplements.rep_eq register_range_complement_commutant)
    also have \<open>\<dots> = range (apply_qregister (qregister_chain FG qFst)) \<inter> range (apply_qregister (qregister_chain FG qSnd))\<close>
      apply (simp add: F'_def G'_def FG_def)
      by (metis (no_types, lifting) FG_def \<open>iso_qregister FG\<close> apply_qregister_fst
          apply_qregister_snd image_cong iso_qregister_def lift_extendL lift_extendR qcompatible_sym)
    also have \<open>\<dots> = FG' ` (range (apply_qregister qFst) \<inter> range (apply_qregister qSnd))\<close>
      by (simp flip: FG'_def add: image_image image_Int)
    also have \<open>\<dots> = FG' ` (range (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) \<inter> range (\<lambda>b. id_cblinfun \<otimes>\<^sub>o b))\<close>
      by (metis (no_types, lifting) apply_qregister_fst apply_qregister_snd image_cong)
    also have \<open>\<dots> = FG' ` one_algebra\<close>
    proof (intro arg_cong[where f=\<open>image FG'\<close>] Set.set_eqI iffI)
      fix x :: \<open>('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'c) ell2\<close> assume \<open>x \<in> one_algebra\<close>
      then obtain c where c_def: \<open>x = c *\<^sub>C id_cblinfun\<close>
        by (metis imageE one_algebra_def)
      then show \<open>x \<in> range (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) \<inter> range (\<lambda>b. id_cblinfun \<otimes>\<^sub>o b)\<close>
        by (auto intro!: exI[of _ \<open>c *\<^sub>C id_cblinfun\<close>]
            simp: image_iff tensor_op_cbilinear.scaleC_left tensor_op_cbilinear.scaleC_right)
    next
      fix x :: \<open>('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L ('a \<times> 'c) ell2\<close>
      assume asm: \<open>x \<in> range (\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) \<inter> range (\<lambda>b. id_cblinfun \<otimes>\<^sub>o b)\<close>
      show \<open>x \<in> one_algebra\<close>
      proof (cases \<open>x = 0\<close>)
        case True
        then show ?thesis 
          by (auto intro!: exI[of _ 0] simp: one_algebra_def)
      next
        case False
        from asm obtain a b where x_a: \<open>x = a \<otimes>\<^sub>o id_cblinfun\<close> and x_b: \<open>x = id_cblinfun \<otimes>\<^sub>o b\<close>
          by fast
        then obtain c where \<open>b = c *\<^sub>C id_cblinfun\<close>
          apply atomize_elim
          apply (rule tensor_op_almost_injective)
          by (auto intro!: simp: )
        then show \<open>x \<in> one_algebra\<close>
          by (auto simp add: x_b one_algebra_def image_iff tensor_op_cbilinear.scaleC_right)
      qed
    qed
    also have \<open>\<dots> = one_algebra\<close>
      using FG'_def \<open>iso_qregister FG\<close> apply_qregister_one_algebra iso_qregister_def by blast
    finally have \<open>range F' \<inter> commutant (range F') = one_algebra\<close>
      by -
    with vN show \<open>von_neumann_factor (range F')\<close>
      by (simp add: von_neumann_factor_def)
  qed
  from this[cancel_with_type]
  show ?thesis
    by -
qed


(* 
lemma von_neumann_factor_tensor:
  assumes \<open>von_neumann_factor A\<close>
  assumes \<open>von_neumann_factor B\<close>
  shows \<open>von_neumann_factor (A \<otimes>\<^sub>v\<^sub>N B)\<close>

https://math.stackexchange.com/questions/4794773/tensor-product-of-factors-is-a-factor

 *)

lemma is_swap_on_qupdate_set_unique:
  assumes vN: \<open>von_neumann_algebra Q\<close>
  assumes factor: \<open>von_neumann_factor (Q \<otimes>\<^sub>v\<^sub>N Q)\<close>
  assumes min_proj: \<open>Ex (minimal_projection_in Q)\<close>
  assumes U: \<open>is_swap_on_qupdate_set Q U\<close>
  assumes V: \<open>is_swap_on_qupdate_set Q V\<close>
  shows \<open>U = V\<close>
proof -
  define W where \<open>W = V* o\<^sub>C\<^sub>L U\<close>
  from U have [iff]: \<open>unitary U\<close>
    using is_swap_on_qupdate_set_def by blast
  from V have [iff]: \<open>unitary V\<close>
    using is_swap_on_qupdate_set_def by blast

  have commute_Wab: \<open>W o\<^sub>C\<^sub>L (a \<otimes>\<^sub>o b) = (a \<otimes>\<^sub>o b) o\<^sub>C\<^sub>L W\<close> if \<open>a \<in> Q\<close> and \<open>b \<in> Q\<close> for a b
  proof -
    have \<open>W o\<^sub>C\<^sub>L (a \<otimes>\<^sub>o b) = V* o\<^sub>C\<^sub>L sandwich U (a \<otimes>\<^sub>o b) o\<^sub>C\<^sub>L U\<close>
      by (simp add: W_def sandwich_apply cblinfun_compose_assoc)
    also from that have \<open>\<dots> = V* o\<^sub>C\<^sub>L sandwich V (a \<otimes>\<^sub>o b) o\<^sub>C\<^sub>L U\<close>
      using U V
      by (simp add: is_swap_on_qupdate_set_def)
    also have \<open>\<dots> = (a \<otimes>\<^sub>o b) o\<^sub>C\<^sub>L W\<close>
      by (simp add: W_def sandwich_apply flip: cblinfun_compose_assoc)
    finally show ?thesis
      by -
  qed
  have W_commutant: \<open>W \<in> commutant (Q \<otimes>\<^sub>v\<^sub>N Q)\<close>
  proof -
    from vN
    have \<open>id_cblinfun \<in> Q\<close>
      by (simp add: von_neumann_algebra_id von_neumann_factor_def)
    with commute_Wab have \<open>W \<in> commutant ((\<lambda>a. a \<otimes>\<^sub>o id_cblinfun) ` Q \<union> (\<lambda>a. id_cblinfun \<otimes>\<^sub>o a) ` Q)\<close>    
      by (auto intro!: commutant_memberI)
    also have \<open>\<dots> = commutant (Q \<otimes>\<^sub>v\<^sub>N Q)\<close>
      by (simp add: tensor_vn_def)
    finally show ?thesis
      by -
  qed
  have \<open>W \<in> Q \<otimes>\<^sub>v\<^sub>N Q\<close>
  proof -
    have \<open>U \<in> Q \<otimes>\<^sub>v\<^sub>N Q\<close>
      using U is_swap_on_qupdate_set_def by blast
    moreover have \<open>V \<in> Q \<otimes>\<^sub>v\<^sub>N Q\<close>
      using V is_swap_on_qupdate_set_def by blast
    ultimately show ?thesis
      using vN
      by (metis W_def rev_image_eqI von_neumann_algebra_adj_image von_neumann_algebra_compose von_neumann_algebra_tensor_vn von_neumann_factor_def)
  qed
  with W_commutant factor have \<open>W \<in> one_algebra\<close>
    using von_neumann_factor_def by fastforce
  then obtain c where W_cI: \<open>W = c *\<^sub>C id_cblinfun\<close>
    by (metis imageE one_algebra_def)
  have \<open>W = id_cblinfun\<close>
  proof -
    from min_proj obtain a where min_a: \<open>minimal_projection_in Q a\<close>
      by blast
    have aa_neq0: \<open>a \<otimes>\<^sub>o a \<noteq> 0\<close>
      by (metis min_a minimal_projection_in_def tensor_op_nonzero)
    from U min_a have \<open>U o\<^sub>C\<^sub>L (a \<otimes>\<^sub>o a) = a \<otimes>\<^sub>o a\<close>
      by (simp add: is_swap_on_qupdate_set_def)
    moreover    from V min_a have \<open>V o\<^sub>C\<^sub>L (a \<otimes>\<^sub>o a) = a \<otimes>\<^sub>o a\<close>
      by (simp add: is_swap_on_qupdate_set_def)
    ultimately have \<open>W o\<^sub>C\<^sub>L (a \<otimes>\<^sub>o a) = a \<otimes>\<^sub>o a\<close>
      by (metis W_def \<open>unitary V\<close> cblinfun_assoc_right(1) cblinfun_compose_id_left unitaryD1)
    with W_cI have \<open>c = 1\<close>
      using aa_neq0 apply (auto intro!: simp: )
      by (simp add: complex_vector.scale_right_imp_eq)
    with W_cI show \<open>W = id_cblinfun\<close>
      by fastforce
  qed
  then show \<open>U = V\<close>
    by (metis W_def \<open>unitary V\<close> adj_cblinfun_compose cblinfun_compose_assoc cblinfun_compose_id_right double_adj unitaryD2)
qed

lemma range_qregister_pair:
  assumes \<open>qcompatible F G\<close>
  shows \<open>range (apply_qregister (qregister_pair F G)) = commutant (commutant (range (apply_qregister F) \<union> range (apply_qregister G)))\<close>
proof -
  have \<open>range (apply_qregister (qregister_pair F G)) = Rep_QREGISTER (QREGISTER_of (qregister_pair F G))\<close>
    by (simp add: QREGISTER_of.rep_eq assms)
  also have \<open>\<dots> = Rep_QREGISTER (QREGISTER_of F \<squnion> QREGISTER_of G)\<close>
    by (simp add: QREGISTER_of_qregister_pair assms)
  also have \<open>\<dots> = commutant (commutant (Rep_QREGISTER (QREGISTER_of F) \<union> Rep_QREGISTER (QREGISTER_of G)))\<close>
    by (simp add: sup_QREGISTER.rep_eq)
  also have \<open>\<dots> = commutant (commutant (range (apply_qregister F) \<union> range (apply_qregister G)))\<close>
    using assms apply (simp add: QREGISTER_of.rep_eq)
    using distinct_qvarsL distinct_qvarsR by blast
  finally show ?thesis
    by -
qed

lemma qregister_tensor_pair:
  \<open>qregister_tensor Q R = \<lbrakk>qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q Q, qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q R\<rbrakk>\<^sub>q\<close>
proof (cases \<open>qregister Q \<and> qregister R\<close>)
  case True
  then show ?thesis
    apply transfer
    by (simp add: register_tensor_def Laws_Quantum.Fst_def Laws_Quantum.Snd_def o_def)
next
  case False
  then have \<open>Q = non_qregister \<or> R = non_qregister\<close>
    by (simp add: non_qregister)
  then show ?thesis
    by auto
qed

lemma range_qregister_tensor:
  assumes \<open>qregister F\<close> and \<open>qregister G\<close>
  shows \<open>range (apply_qregister (qregister_tensor F G)) = range (apply_qregister F) \<otimes>\<^sub>v\<^sub>N range (apply_qregister G)\<close>
  using assms 
  by (simp add: range_qregister_pair qregister_tensor_pair tensor_vn_def image_image
      qregister_chain_apply apply_qregister_fst apply_qregister_snd)

lemma qregister_qregister_tensor:
  assumes \<open>qregister F\<close>
  assumes \<open>qregister G\<close>
  shows \<open>qregister (qregister_tensor F G)\<close>
  using assms
  apply transfer
  using Laws_Quantum.register_tensor_is_register by auto

lemma minimal_projection_in_apply_qregister_preimage:
  assumes \<open>minimal_projection_in (apply_qregister Q ` A) b\<close>
  shows \<open>\<exists>a. minimal_projection_in A a \<and> b = a \<guillemotright> Q\<close>
proof (cases \<open>qregister Q\<close>)
  case True
  note [iff] = True
  from assms obtain a where baQ: \<open>b = a \<guillemotright> Q\<close> and \<open>a \<in> A\<close>
    by (auto simp: minimal_projection_in_def)
  from assms have \<open>is_Proj b\<close>
    using minimal_projection_in_def by blast
  with baQ have \<open>is_Proj a\<close>
    by simp
  from assms have \<open>b \<noteq> 0\<close>
    using minimal_projection_in_def by blast
  with baQ have \<open>a \<noteq> 0\<close>
    by force
  have \<open>a' = a\<close> if \<open>a' \<noteq> 0\<close> and \<open>is_Proj a'\<close> and \<open>a' \<in> A\<close> and \<open>a' \<le> a\<close> for a'
  proof -
    from assms have \<open>a' \<guillemotright> Q \<noteq> 0\<close>
      using lift_eqOp that(1) by fastforce
    moreover from assms have \<open>is_Proj (a' \<guillemotright> Q)\<close>
      by (simp add: that(2))
    moreover from assms have \<open>a' \<guillemotright> Q \<in> apply_qregister Q ` A\<close>
      using that(3) by blast
    moreover from assms have \<open>a' \<guillemotright> Q \<le> b\<close>
      using apply_qregister_mono baQ that(4) by blast
    ultimately have \<open>a' \<guillemotright> Q = b\<close>
      by (metis assms minimal_projection_in_def)
    then show \<open>a' = a\<close>
      by (simp add: baQ)
  qed
  with \<open>a \<in> A\<close> \<open>is_Proj a\<close> \<open>a \<noteq> 0\<close> baQ
  show ?thesis
    by (auto intro!: exI[of _ a] simp: minimal_projection_in_def)
next
  case False
  from assms obtain a where baQ: \<open>b = a \<guillemotright> Q\<close>
    by (auto simp: minimal_projection_in_def)
  from assms have \<open>b \<noteq> 0\<close>
    using minimal_projection_in_def by blast
  from False baQ have \<open>b = 0\<close>
    by (simp add: non_qregister)
  with \<open>b \<noteq> 0\<close>
  have False
    by simp
  then show ?thesis
    by simp
qed

lemma minimal_projection_in_UNIV_rank1:
  assumes \<open>minimal_projection_in UNIV a\<close>
  shows \<open>rank1 a\<close>
proof (rule ccontr)
  assume \<open>\<not> rank1 a\<close>
  then have \<open>a \<noteq> 0\<close>
    by fastforce
  then obtain \<psi> where \<open>norm \<psi> = 1\<close> and \<open>\<psi> \<in> space_as_set (a *\<^sub>S \<top>)\<close>
    by (metis Complex_Bounded_Linear_Function.zero_cblinfun_image Proj_compose_cancelI Proj_on_own_range cblinfun_assoc_left(2) cblinfun_image_bot_zero ccsubspace_leI_unit is_Proj_0)
  have \<open>is_Proj (proj \<psi>)\<close>
    by (simp add: \<open>norm \<psi> = 1\<close> butterfly_is_Proj)
  have \<open>proj \<psi> \<noteq> 0\<close>
    by (smt (verit, ccfv_threshold) Proj_0_compl Proj_idempotent Proj_ortho_compl Proj_range Proj_top UNIV_I \<open>norm \<psi> = 1\<close> basic_trans_rules(31) cblinfun_fixes_range ccspan_superset diff_zero norm_eq_zero singletonI top_ccsubspace.rep_eq)
  have \<open>space_as_set (proj \<psi> *\<^sub>S \<top>) \<le> space_as_set (a *\<^sub>S \<top>)\<close>
    by (metis Proj_fixes_image \<open>\<psi> \<in> space_as_set (a *\<^sub>S \<top>)\<close> \<open>norm \<psi> = 1\<close> butterfly_eq_proj cblinfun_comp_butterfly cblinfun_fixes_range space_as_setI_via_Proj subsetI)
  then have \<open>proj \<psi> \<le> a\<close>
    by (metis Proj_mono Proj_on_own_range Proj_range assms ccsubspace_leI minimal_projection_in_def)
  from assms \<open>is_Proj (proj \<psi>)\<close> \<open>proj \<psi> \<le> a\<close> \<open>proj \<psi> \<noteq> 0\<close>
  have \<open>a = proj \<psi>\<close>
    using minimal_projection_in_def by blast
  then have \<open>rank1 a\<close>
    by simp
  with \<open>\<not> rank1 a\<close> show False
    by simp
qed


lemma is_swap_on_qupdate_set_swap_ell2: 
  assumes [iff]: \<open>qregister Q\<close>
  shows \<open>is_swap_on_qupdate_set (range (apply_qregister Q)) (swap_ell2 \<guillemotright> qregister_tensor Q Q)\<close>
proof (unfold is_swap_on_qupdate_set_def, intro conjI ballI allI impI)
  show \<open>swap_ell2 \<guillemotright> qregister_tensor Q Q \<in> range (apply_qregister Q) \<otimes>\<^sub>v\<^sub>N range (apply_qregister Q)\<close>
    using range_qregister_tensor[OF assms assms]
    by auto
  show \<open>unitary (swap_ell2 \<guillemotright> qregister_tensor Q Q)\<close>
    by (auto intro!: qregister_unitary qregister_qregister_tensor)
  show \<open>sandwich (swap_ell2 \<guillemotright> qregister_tensor Q Q) *\<^sub>V a \<otimes>\<^sub>o b = b \<otimes>\<^sub>o a\<close>
    if \<open>a \<in> range (apply_qregister Q)\<close> and \<open>b \<in> range (apply_qregister Q)\<close> for a b
    by (smt (verit, del_insts) adjoint_lift adjoint_swap_ell2 imageE qregister_compose qregister_tensor_apply sandwich_apply swap_tensor_op that(1) that(2))
  show \<open>(swap_ell2 \<guillemotright> qregister_tensor Q Q) o\<^sub>C\<^sub>L a \<otimes>\<^sub>o a = a \<otimes>\<^sub>o a\<close>
    if \<open>minimal_projection_in (range (apply_qregister Q)) a\<close> for a
  proof -
    from minimal_projection_in_apply_qregister_preimage[OF that]
    obtain b where \<open>minimal_projection_in UNIV b\<close> and \<open>a = b \<guillemotright> Q\<close>
      by auto
    from \<open>minimal_projection_in UNIV b\<close> have \<open>rank1 b\<close>
      by (rule minimal_projection_in_UNIV_rank1)
    then obtain \<psi> \<phi> where \<open>b = butterfly \<psi> \<phi>\<close>
      by (auto intro!: simp: rank1_iff_butterfly)
    then have \<open>swap_ell2 o\<^sub>C\<^sub>L (b \<otimes>\<^sub>o b) = b \<otimes>\<^sub>o b\<close>
      by (auto intro!: tensor_ell2_extensionality simp: cblinfun.scaleC_right)
    then have \<open>(swap_ell2 \<guillemotright> qregister_tensor Q Q) o\<^sub>C\<^sub>L ((b \<otimes>\<^sub>o b) \<guillemotright> qregister_tensor Q Q) = (b \<otimes>\<^sub>o b) \<guillemotright> qregister_tensor Q Q\<close>
      by simp
    moreover have \<open>(b \<otimes>\<^sub>o b) \<guillemotright> qregister_tensor Q Q = a \<otimes>\<^sub>o a\<close>
      by (simp add: \<open>a = b \<guillemotright> Q\<close> qregister_tensor_apply)
    ultimately show \<open>apply_qregister (qregister_tensor Q Q) swap_ell2 o\<^sub>C\<^sub>L a \<otimes>\<^sub>o a = a \<otimes>\<^sub>o a\<close>
      by simp
  qed
qed

lemma card1I:
  assumes "a \<in> A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> x = a"
  shows \<open>card A = 1\<close>
  by (metis One_nat_def assms(1) assms(2) card_eq_Suc_0_ex1)

lemma the_default_CollectI:
  assumes "P a"
    and "\<And>x. P x \<Longrightarrow> x = a"
  shows "P (the_default d (Collect P))"
proof -
  have card: \<open>card (Collect P) = 1\<close>
    apply (rule card1I)
    using assms by auto
  from assms have \<open>P (THE x. P x)\<close>
    by (rule theI)
  then show ?thesis
    by (simp add: the_default_def card)
qed

lemma apply_qregister_minimal_projection_in:
  assumes \<open>qregister Q\<close>
  assumes \<open>minimal_projection_in A a\<close>
  shows \<open>minimal_projection_in (apply_qregister Q ` A) (a \<guillemotright> Q)\<close>
proof (unfold minimal_projection_in_def, intro conjI ballI impI)
  show \<open>apply_qregister Q a \<in> apply_qregister Q ` A\<close>
  by (meson assms(2) image_eqI minimal_projection_in_def)
  show \<open>is_Proj (apply_qregister Q a)\<close>
  using apply_qregister_is_Proj' assms(2) minimal_projection_in_def by blast
  show \<open>apply_qregister Q a \<noteq> 0\<close>
  by (metis apply_qregister_of_0 assms(1) assms(2) lift_eqOp minimal_projection_in_def)
  show \<open>b = apply_qregister Q a\<close>
    if \<open>b \<in> apply_qregister Q ` A\<close> and \<open>is_Proj b\<close> and \<open>b \<le> apply_qregister Q a\<close> and \<open>b \<noteq> 0\<close> for b
  proof -
    from that(1) obtain c where bcQ: \<open>b = c \<guillemotright> Q\<close> and \<open>c \<in> A\<close>
      by blast
    then have \<open>c = a\<close>
      using apply_qregister_mono assms assms minimal_projection_in_def that by fastforce
    then show \<open>b = apply_qregister Q a\<close>
      using bcQ by blast
  qed
qed


lemma minimal_projection_in_proj:
  assumes \<open>\<psi> \<noteq> 0\<close> and \<open>proj \<psi> \<in> A\<close>
  shows \<open>minimal_projection_in A (proj \<psi>)\<close>
proof (unfold minimal_projection_in_def, intro conjI impI ballI)
  from assms show \<open>proj \<psi> \<in> A\<close>
    by simp
  show \<open>is_Proj (proj \<psi>)\<close>
    by simp
  from assms show \<open>proj \<psi> \<noteq> 0\<close>
    by (metis Proj_bot Proj_inj bot_ccsubspace.rep_eq ccspan_superset empty_not_insert singleton_insert_inj_eq' subset_singleton_iff)
  show \<open>a = proj \<psi>\<close>
    if \<open>a \<in> A\<close> and \<open>is_Proj a\<close> and \<open>a \<le> proj \<psi>\<close> and \<open>a \<noteq> 0\<close> for a
    by (metis Proj_mono Proj_on_own_range cblinfun_image_bot_zero ccspan_of_empty ccspan_some_onb_of some_onb_of_0 subspace_of_1dim_ccspan that(2) that(3) that(4))
qed

lemma is_swap_on_qupdate_set_swap_QREGISTER_of:
  assumes [iff]: \<open>qregister Q\<close>
  shows \<open>is_swap_on_qupdate_set (range (apply_qregister Q)) (swap_QREGISTER (QREGISTER_of Q))\<close>
proof -
  have vN_Q: \<open>von_neumann_algebra (range (apply_qregister Q))\<close>
    using valid_qregister_range valid_qregister_range_def by blast
  have vN_QQ: \<open>von_neumann_factor (range (apply_qregister Q) \<otimes>\<^sub>v\<^sub>N range (apply_qregister Q))\<close>
    by (auto intro!: range_apply_qregister_factor qregister_qregister_tensor simp flip: range_qregister_tensor)
  have min_proj: \<open>Ex (minimal_projection_in (range (apply_qregister Q)))\<close>
    using minimal_projection_in_proj[where A=UNIV and \<psi>=\<open>ket undefined\<close>] apply_qregister_minimal_projection_in[where Q=Q and A=UNIV]
    by auto
  have 1: \<open>is_swap_on_qupdate_set (range (apply_qregister Q)) (apply_qregister (qregister_tensor Q Q) swap_ell2)\<close>
    by (simp add: is_swap_on_qupdate_set_swap_ell2) 
  have 2: \<open>U = apply_qregister (qregister_tensor Q Q) swap_ell2\<close>
    if \<open>is_swap_on_qupdate_set (range (\<lambda>a. apply_qregister Q a)) U\<close> for U
    using vN_Q vN_QQ min_proj that 1 by (rule is_swap_on_qupdate_set_unique)
  have \<open>is_swap_on_qupdate_set (range (apply_qregister Q))
     (the_default 0 (Collect (is_swap_on_qupdate_set (range (apply_qregister Q)))))\<close>
    using 1 2 by (rule the_default_CollectI[where a=\<open>swap_ell2 \<guillemotright> qregister_tensor Q Q\<close>])
  then show ?thesis
    by (simp add: swap_QREGISTER.rep_eq QREGISTER_of.rep_eq) 
qed

lemma swap_QREGISTER_QREGISTER_of: 
  assumes [simp]: \<open>qregister Q\<close>
  shows \<open>swap_QREGISTER (QREGISTER_of Q) = (swap_ell2 \<guillemotright> qregister_tensor Q Q)\<close>
proof (rule is_swap_on_qupdate_set_unique[where Q=\<open>range (apply_qregister Q)\<close>])
  show \<open>von_neumann_algebra (range (apply_qregister Q))\<close>
    using assms valid_qregister_range valid_qregister_range_def by blast
  show \<open>von_neumann_factor (range (apply_qregister Q) \<otimes>\<^sub>v\<^sub>N range (apply_qregister Q))\<close>
    by (auto intro!: range_apply_qregister_factor qregister_qregister_tensor simp flip: range_qregister_tensor)
  show \<open>Ex (minimal_projection_in (range (apply_qregister Q)))\<close>
    using minimal_projection_in_proj[where A=UNIV and \<psi>=\<open>ket undefined\<close>] apply_qregister_minimal_projection_in[where Q=Q and A=UNIV]
    by auto
  show \<open>is_swap_on_qupdate_set (range (apply_qregister Q)) (swap_QREGISTER (QREGISTER_of Q))\<close>
    using assms by (rule is_swap_on_qupdate_set_swap_QREGISTER_of)
  show \<open>is_swap_on_qupdate_set (range (apply_qregister Q))(swap_ell2 \<guillemotright> qregister_tensor Q Q)\<close>
    by (rule is_swap_on_qupdate_set_swap_ell2, simp)
qed

lemma is_swap_on_qupdate_set_swap_QREGISTER:
  assumes \<open>ACTUAL_QREGISTER Q\<close>
  shows \<open>is_swap_on_qupdate_set (Rep_QREGISTER Q) (swap_QREGISTER Q)\<close>
proof -
  from ACTUAL_QREGISTER_ex_register[OF assms]
  have \<open>\<forall>\<^sub>\<tau> 'c::type = ACTUAL_QREGISTER_content Q. is_swap_on_qupdate_set (Rep_QREGISTER Q) (swap_QREGISTER Q)\<close>
  proof (rule with_type_mp)
    assume \<open>\<exists>F::('c, 'a) qregister. qregister F \<and> QREGISTER_of F = Q\<close>
    then obtain F :: \<open>('c, 'a) qregister\<close> where [iff]: \<open>qregister F\<close> and Q_def: \<open>Q = QREGISTER_of F\<close>
      by blast
    then have \<open>swap_QREGISTER (QREGISTER_of F) = (swap_ell2 \<guillemotright> qregister_tensor F F)\<close>
      using swap_QREGISTER_QREGISTER_of by blast
    moreover have \<open>is_swap_on_qupdate_set (range (apply_qregister F)) (apply_qregister (qregister_tensor F F) swap_ell2)\<close>
      by (simp add: is_swap_on_qupdate_set_swap_ell2)
    ultimately show \<open>is_swap_on_qupdate_set (Rep_QREGISTER Q) (swap_QREGISTER Q)\<close>
      by (simp add: Q_def QREGISTER_of.rep_eq)
  qed
  from this[cancel_with_type]
  show ?thesis
    by -
qed


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

(* lemma swap_QREGISTER_welldefined_aux1:
  fixes f :: \<open>'a \<Rightarrow> 'b\<times>'c\<close> and U :: \<open>'a update\<close> and L R
    and f' :: \<open>'a \<Rightarrow> 'd\<times>'e\<close> and U' :: \<open>'a update\<close> and L' R'
  assumes \<open>unitary U\<close> and \<open>inj f\<close> and \<open>range f = L \<times> R\<close>
  assumes \<open>unitary U'\<close> and \<open>inj f'\<close> and \<open>range f' = L' \<times> R'\<close>
  assumes eq: \<open>{sandwich U a | a. actual_qregister_range_aux f a} = {sandwich U' a | a. actual_qregister_range_aux f' a}\<close>
  shows \<open>swap_QREGISTER' (f,U,L,R) = swap_QREGISTER' (f',U',L',R')\<close> (is ?goal)
proof -
  define Q :: \<open>'a update set\<close> where \<open>Q = {sandwich U a | a. actual_qregister_range_aux f a}\<close>
  then have Q_def2: \<open>Q = {sandwich U' a | a. actual_qregister_range_aux f' a}\<close>
    using eq by simp
  have ex_F: \<open>\<forall>\<^sub>\<tau> 'l1::type = L. \<forall>\<^sub>\<tau> 'r1::type = R. \<exists>F :: ('l1, 'a) qregister. qregister F \<and> range (apply_qregister F) = Q
          \<and> F = qregister_chain (transform_qregister (U o\<^sub>C\<^sub>L (classical_operator (Some o map_prod abs_l1 abs_r1 o f))* )) qFst\<close>
    apply (rule actual_qregister_range_ex_register_aux[of U f L R])
    using assms(1-3)
    by (auto simp: Q_def)
  then have \<open>\<forall>\<^sub>\<tau> 'l1::type = L. \<forall>\<^sub>\<tau> 'r1::type = R. ?goal\<close>
  proof (rule with_type_mp2)
    fix abs_l1 :: \<open>'b \<Rightarrow> 'l1\<close> and abs_r1 :: \<open>'c \<Rightarrow> 'r1\<close>
    assume \<open>\<exists>F :: ('l1, 'a) qregister. qregister F \<and> range (apply_qregister F) = Q
          \<and> F = qregister_chain (transform_qregister (U o\<^sub>C\<^sub>L (classical_operator (Some o map_prod abs_l1 abs_r1 o f))* )) qFst\<close>
    then obtain F :: \<open>('l1, 'a) qregister\<close> where \<open>qregister F\<close> and \<open>range (apply_qregister F) = Q\<close>
      and \<open>F = qregister_chain (transform_qregister (U o\<^sub>C\<^sub>L (classical_operator (Some o map_prod abs_l1 abs_r1 o f))* )) qFst\<close>
      by auto
    have ex_F': \<open>\<forall>\<^sub>\<tau> 'l2::type = L'. \<forall>\<^sub>\<tau> 'r2::type = R'. \<exists>F' :: ('l2, 'a) qregister. qregister F' \<and> range (apply_qregister F') = Q
          \<and> F' = qregister_chain (transform_qregister (U' o\<^sub>C\<^sub>L (classical_operator (Some o map_prod abs_l2 abs_r2 o f'))* )) qFst\<close>
      apply (rule actual_qregister_range_ex_register_aux[of U' f' L' R'])
      using assms(4-6)
      by (auto simp: Q_def2)
    then have \<open>\<forall>\<^sub>\<tau> 'l2::type = L'. \<forall>\<^sub>\<tau> 'r2::type = R'. ?goal\<close>
    proof (rule with_type_mp2)
      fix abs_l2 :: \<open>'d \<Rightarrow> 'l2\<close> and abs_r2 :: \<open>'e \<Rightarrow> 'r2\<close>
      assume \<open>\<exists>F' :: ('l2, 'a) qregister. qregister F' \<and> range (apply_qregister F') = Q
          \<and> F' = qregister_chain (transform_qregister (U' o\<^sub>C\<^sub>L (classical_operator (Some o map_prod abs_l2 abs_r2 o f'))* )) qFst\<close>
      then obtain F' :: \<open>('l2, 'a) qregister\<close> where \<open>qregister F'\<close> and \<open>range (apply_qregister F') = Q\<close>
        and \<open>F' = qregister_chain (transform_qregister (U' o\<^sub>C\<^sub>L (classical_operator (Some o map_prod abs_l2 abs_r2 o f'))* )) qFst\<close>
        by auto
      have \<open>equivalent_qregisters F' F\<close>
        by -
      then obtain I where \<open>iso_qregister I\<close> and FI: \<open>F' = qregister_chain F I\<close>
        by -
      have 1: \<open>swap_QREGISTER' (f, U, L, R) = apply_qregister \<lbrakk>qregister_chain qFst F, qregister_chain qSnd F\<rbrakk> swap_ell2\<close>
        by x
      have \<open>swap_QREGISTER' (f', U', L', R') = apply_qregister \<lbrakk>qregister_chain qFst F', qregister_chain qSnd F'\<rbrakk> swap_ell2\<close>
        by x
      also have \<open>\<dots> = apply_qregister \<lbrakk>qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q F, qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q F\<rbrakk> (apply_qregister (qregister_tensor I I) swap_ell2)\<close>
        apply (simp add: FI)
        by -
      also have \<open>\<dots> = apply_qregister \<lbrakk>qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q F, qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q F\<rbrakk> swap_ell2\<close>
        by -
      also have \<open>\<dots> = swap_QREGISTER' (f, U, L, R)\<close>
        by (simp flip : 1)
      finally show ?goal
        by simp
    qed
    from this[cancel_with_type, cancel_with_type]
    show ?goal
      by -
  qed
  from this[cancel_with_type, cancel_with_type]
  show ?goal
    by -
qed *)

(* lemma swap_QREGISTER_welldefined_aux2:
  fixes f :: \<open>'a \<Rightarrow> 'b\<times>'c\<close> and U :: \<open>'a update\<close> and L R
  assumes \<open>unitary U\<close> and \<open>inj f\<close> and \<open>range f = L \<times> R\<close>
  assumes \<open>Rep_QREGISTER Q = {sandwich U a | a. actual_qregister_range_aux f a}\<close>
  shows \<open>swap_QREGISTER Q = swap_QREGISTER' (f,U,L,R)\<close>
proof -
  have aux: \<open>A = {x}\<close> if \<open>x \<in> A\<close> and \<open>\<And>y. y\<in>A \<Longrightarrow> x = y\<close> for A x
    using that 
  by blast
by -


  have *: \<open>swap_QREGISTER' ` {(f :: 'a \<Rightarrow> 'a\<times>'a, U, L, R). unitary U \<and> 
    inj f \<and> range f = L \<times> R \<and>
    Rep_QREGISTER Q = {sandwich U a | a. actual_qregister_range_aux f a}} = {swap_QREGISTER' (f,U,L,R)}\<close>
  proof (rule aux)
    using assms apply (auto intro!: exI swap_QREGISTER_welldefined_aux1 simp: image_iff)
try0
sledgehammer [dont_slice]
by -

    by x
  show ?thesis
    by (simp only: swap_QREGISTER_def * the_default_singleton)
qed *)

lemma qregister_decomposition:
  fixes F :: \<open>('a,'b) qregister\<close>
  assumes \<open>qregister F\<close>
  shows \<open>\<forall>\<^sub>\<tau> 'c::type = qregister_decomposition_basis F.
         (\<exists>U :: ('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2. unitary U \<and> 
            F = qregister_chain (transform_qregister U) qFst)\<close>
proof -
  have [simp]: \<open>qregister_raw (apply_qregister F)\<close>
    using assms qregister.rep_eq by blast
  then have *: \<open>F = qregister_chain (transform_qregister U) \<lbrakk>#1\<rbrakk>\<^sub>q
      = (\<forall>\<theta>. apply_qregister F \<theta> = sandwich U *\<^sub>V \<theta> \<otimes>\<^sub>o id_cblinfun)\<close> if \<open>unitary U\<close> for U
    apply (transfer' fixing: U)
    by (auto intro!: unitary_sandwich_register that
        simp: Laws_Quantum.Fst_def sandwich_apply non_qregister_raw)
  show ?thesis
    using register_decomposition[where \<Phi>=\<open>apply_qregister F\<close>] assms * \<open>qregister_raw (apply_qregister F)\<close>
    by (smt (verit, ccfv_threshold) with_type_mp)
qed

(* lemma swap_QREGISTER_welldefined:
  fixes F :: \<open>('a,'b) qregister\<close>
  assumes \<open>qregister F\<close>
  shows \<open>swap_QREGISTER (QREGISTER_of F) = apply_qregister \<lbrakk>qregister_chain qFst F, qregister_chain qSnd F\<rbrakk> swap_ell2\<close> (is ?goal)
proof -
  from qregister_decomposition[OF assms]  
  have \<open>\<forall>\<^sub>\<tau> 'c::type = qregister_decomposition_basis F. ?goal\<close>
  proof (rule with_type_mp)
    assume \<open>\<exists>U. unitary U \<and> F = qregister_chain (transform_qregister U) qFst\<close>
    define f where \<open>\<close>
    show ?goal


  from \<open>ACTUAL_QREGISTER Q\<close>
  obtain f' :: \<open>'a \<Rightarrow> 'a\<times>'a\<close> and U' :: \<open>'a update\<close> and L' R'
    where \<open>unitary U'\<close> and \<open>inj f'\<close> and \<open>range f' = L' \<times> R'\<close>
      and \<open>Rep_QREGISTER Q = {sandwich U' a | a. actual_qregister_range_aux f' a}\<close>
    by (auto simp add: ACTUAL_QREGISTER.rep_eq actual_qregister_range_def) *)

definition cq_map_auxiliary_state ::
  \<open>('aux ell2, 'aux ell2) trace_class \<Rightarrow> ('cl, 'qu\<times>'aux) cq_map \<Rightarrow> ('cl,'qu) cq_map\<close> where
  \<open>cq_map_auxiliary_state \<rho> \<EE> = undefined\<close>


(* axiomatization cq_map_local_q :: 
  \<open>qu QREGISTER \<Rightarrow> (qu ell2, qu ell2) trace_class \<Rightarrow> (cl,qu) cq_map \<Rightarrow> (cl,qu) cq_map\<close> *)
definition cq_map_local_q :: 
  \<open>qu QREGISTER \<Rightarrow> (qu ell2, qu ell2) trace_class \<Rightarrow> (cl,qu) cq_map \<Rightarrow> (cl,qu) cq_map\<close> where
  \<open>cq_map_local_q Q \<rho> \<EE> = cq_map_auxiliary_state \<rho> (
    cq_map_seq  (cq_map_of_op (swap_QREGISTER Q))
    (cq_map_seq (undefined ''TENSOR identity'' \<EE>)
                (cq_map_of_op (swap_QREGISTER Q))))\<close>

axiomatization cq_map_while :: \<open>bool expression \<Rightarrow> (cl,qu) cq_map \<Rightarrow> (cl,qu) cq_map\<close>



(* lemma kraus_map_from_measurement_norm: 
  assumes \<open>M \<noteq> 0\<close>
  shows \<open>kraus_family_norm (kraus_map_from_measurement M) = 1\<close> *)

(* lemma kraus_map_from_measurement_0: \<open>kraus_equivalent' (kraus_map_from_measurement 0) 0\<close> *)

lift_definition cq_map_measurement :: \<open>(cl, qu) measurement expression \<Rightarrow> (cl,qu) cq_map\<close> is
  \<open>\<lambda>m c. kraus_map_from_measurement (m c)\<close>
  by (auto intro!: kraus_map_from_measurement_norm_leq1 simp: cq_map_rel_def)

fun denotation_raw :: \<open>raw_program \<Rightarrow> (cl,qu) cq_map\<close> where
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

lift_definition denotation :: "program \<Rightarrow> (cl,qu) cq_map" is denotation_raw.

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

lift_definition qc_map_in_qref :: \<open>('cl,'qu) cq_map \<Rightarrow> 'qu QREGISTER \<Rightarrow> bool\<close> is
  \<open>\<lambda>\<EE> Q. \<forall>x. kraus_family_in_qref (\<EE> x) Q\<close>
  apply (auto intro!: simp: cq_map_rel_def kraus_family_in_qref_def)
  using kraus_equivalent'_trans kraus_equivalent'_sym
  by meson

definition fvq_of_cq_map :: \<open>(cl, qu) cq_map \<Rightarrow> QVARIABLE\<close> where
  \<open>fvq_of_cq_map \<EE> = Inf {Q. qc_map_in_qref \<EE> Q}\<close>

definition fvq_program :: \<open>program \<Rightarrow> QVARIABLE\<close> where
  \<open>fvq_program p = fvq_of_cq_map (denotation p)\<close>

function fvq_raw_program :: \<open>raw_program \<Rightarrow> QVARIABLE\<close> where
 \<open>no_oracles p \<Longrightarrow> fvq_raw_program p = fvq_of_cq_map (undefined denotation_raw p)\<close>
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
