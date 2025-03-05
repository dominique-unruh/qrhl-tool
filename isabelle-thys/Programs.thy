theory Programs
  imports QRHL_Core Expressions Wlog.Wlog Kraus_Maps.Kraus_Maps
    CQ_Operators
begin

no_notation Lattice.join (infixl "\<squnion>\<index>" 65)
no_notation Order.bottom ("\<bottom>\<index>")

(* lift_definition cq_map_sample :: \<open>('cl1 \<Rightarrow> 'cl2 distr) \<Rightarrow> ('cl1\<times>'qu,'cl2\<times>'qu,unit) kraus_family\<close> is
  \<open>\<lambda>e c. kraus_map_sample (prob (e c))\<close>
  by (auto intro!: bdd_aboveI simp: kraus_map_sample_norm prob_summable) *)

type_synonym program_state = \<open>((cl\<times>qu) ell2, (cl\<times>qu) ell2) trace_class\<close>

typedef denotation = \<open>{\<EE> :: program_state \<Rightarrow> program_state. is_cq_map qFst \<EE> \<and> km_norm \<EE> \<le> 1}\<close>
  by (auto intro!: exI[of _ 0])
setup_lifting type_definition_denotation

definition cq_operator_distrib :: "program_state \<Rightarrow> cl distr" where
  \<open>cq_operator_distrib \<rho> = (if is_distribution (cq_prob qFst \<rho>) then Abs_distr (cq_prob qFst \<rho>) else 0)\<close>

datatype raw_program =
  Seq \<open>raw_program\<close> \<open>raw_program\<close>
  | Skip
  | Sample \<open>cl distr expression\<close>
  | IfThenElse \<open>bool expression\<close> \<open>raw_program\<close> \<open>raw_program\<close>
  | While \<open>bool expression\<close> \<open>raw_program\<close>
  | QuantumOp \<open>cl \<Rightarrow> (qu ell2, qu ell2) trace_class \<Rightarrow> (qu ell2, qu ell2) trace_class\<close>
  | Measurement \<open>(cl, qu) measurement expression\<close>
  | InstantiateOracles \<open>raw_program\<close> \<open>raw_program list\<close>
     \<comment> \<open>\<^term>\<open>InstantiateOracles p q\<close> replace the first oracles in p by q, and decrease the index of all other oracle calls by len q.\<close>
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
| \<open>oracle_number (InstantiateOracles p qs) = max (oracle_number p - length qs) (\<Squnion>q\<in>set qs. oracle_number q)\<close>
| \<open>oracle_number (LocalQ _ _ c) = oracle_number c\<close>
| \<open>oracle_number (LocalC _ _ c) = oracle_number c\<close>
| \<open>oracle_number (OracleCall i) = Suc i\<close>

inductive no_oracles :: \<open>raw_program \<Rightarrow> bool\<close> where
\<open>no_oracles c \<Longrightarrow> no_oracles d \<Longrightarrow> no_oracles (Seq c d)\<close>
| \<open>no_oracles c \<Longrightarrow> no_oracles d \<Longrightarrow> no_oracles (IfThenElse e c d)\<close>
| \<open>no_oracles c \<Longrightarrow> no_oracles d \<Longrightarrow> no_oracles (While e c)\<close>
| \<open>no_oracles c \<Longrightarrow> no_oracles d \<Longrightarrow> no_oracles (LocalC C m c)\<close>
| \<open>no_oracles c \<Longrightarrow> no_oracles d \<Longrightarrow> no_oracles (LocalQ Q t c)\<close>
| \<open>no_oracles Skip\<close>
| \<open>no_oracles (Sample d)\<close>
| \<open>no_oracles (QuantumOp E)\<close>
| \<open>no_oracles (Measurement M)\<close>

(* fun no_oracles :: \<open>raw_program \<Rightarrow> bool\<close> where
\<open>no_oracles (Seq c d) \<longleftrightarrow> no_oracles c \<and> no_oracles d\<close>
| \<open>no_oracles (IfThenElse e c d) \<longleftrightarrow> no_oracles c \<and> no_oracles d\<close>
| \<open>no_oracles (While e c) \<longleftrightarrow> no_oracles c\<close>
| \<open>no_oracles (LocalQ _ _ c) \<longleftrightarrow> no_oracles c\<close>
| \<open>no_oracles (LocalC _ _ c) \<longleftrightarrow> no_oracles c\<close>
| \<open>no_oracles (OracleCall _) \<longleftrightarrow> False\<close>
| \<open>no_oracles (InstantiateOracles _ _) \<longleftrightarrow> False\<close>
| \<open>no_oracles p \<longleftrightarrow> True\<close> *)

fun substitute_oracles_raw :: \<open>raw_program list \<Rightarrow> raw_program \<Rightarrow> raw_program\<close> where
\<open>substitute_oracles_raw os (Seq c d) = Seq (substitute_oracles_raw os c) (substitute_oracles_raw os d)\<close>
| \<open>substitute_oracles_raw os (IfThenElse e c d) = IfThenElse e (substitute_oracles_raw os c) (substitute_oracles_raw os d)\<close>
| \<open>substitute_oracles_raw os (While e c) = While e (substitute_oracles_raw os c)\<close>
| \<open>substitute_oracles_raw os (LocalQ Q \<rho> c) = LocalQ Q \<rho> (substitute_oracles_raw os c)\<close>
| \<open>substitute_oracles_raw os (LocalC C m c) = LocalC C m (substitute_oracles_raw os c)\<close>
| \<open>substitute_oracles_raw os (OracleCall i) = (if i < length os then os!i else OracleCall (i - length os))\<close>
| \<open>substitute_oracles_raw os (InstantiateOracles c ds) = substitute_oracles_raw (map (substitute_oracles_raw os) ds @ os) c\<close>
| \<open>substitute_oracles_raw os p = p\<close>

(* lemma cSUP_mono_simple: "bdd_above (g ` A) \<Longrightarrow> (\<And>n. n \<in> A \<Longrightarrow> f n \<le> g n) \<Longrightarrow> \<Squnion>(f ` A) \<le> \<Squnion>(g ` A)"
  for f g :: \<open>_ \<Rightarrow> _::conditionally_complete_lattice\<close>
  apply (cases \<open>A = {}\<close>)
apply (simp add: )
try0
sledgehammer [dont_slice]
by -
 *)




lemma oracle_number_substitute_oracles_raw[simp]:
  \<open>oracle_number (substitute_oracles_raw os p) \<le> max (oracle_number p - length os) (\<Squnion>q\<in>set os. oracle_number q)\<close>
proof (induction p arbitrary: os)
  case (Seq p1 p2)
  then show ?case
    apply (simp add: max_diff_distrib_left_nat)
    by (meson pre_arith_simps(3))
next
  case Skip
  then show ?case
    by simp
next
  case (Sample x)
  then show ?case
    by simp
next
  case (IfThenElse x1 p1 p2)
  then show ?case 
    apply (simp add: max_diff_distrib_left_nat)
    by (meson pre_arith_simps(3))
next
  case (While x1 p)
  then show ?case 
    by simp
next
  case (QuantumOp x)
  then show ?case
    by simp
next
  case (Measurement x)
  then show ?case 
    by simp
next
  case (InstantiateOracles p x2)
  show ?case
  proof (cases \<open>x2 = []\<close>)
    case True
    then show ?thesis 
      by (simp add: InstantiateOracles)
  next
    case False
    have aux: \<open>max a (max b c) \<le> max (max d e - l) c\<close> 
      if \<open>a \<le> d - l\<close> and \<open>b \<le> max (e - l) c\<close>
      for a b c d e f l :: nat
      using that by force
    have \<open>oracle_number (substitute_oracles_raw os (InstantiateOracles p x2)) \<le> 
      max (oracle_number p - length (map (substitute_oracles_raw os) x2 @ os))
        (\<Squnion>a\<in>set (map (substitute_oracles_raw os) x2 @ os). oracle_number a)\<close>
      using InstantiateOracles.IH(1)[where os=\<open>map (substitute_oracles_raw os) x2 @ os\<close>]
      by simp
    also have \<open>\<dots> = max (oracle_number p - length (map (substitute_oracles_raw os) x2 @ os)) 
               (max (\<Squnion>a\<in>set x2. oracle_number (substitute_oracles_raw os a)) (\<Squnion>a\<in>set os. oracle_number a))\<close>
      apply (cases \<open>x2 = []\<close>; cases \<open>os = []\<close>)
      by (auto simp: image_image cSUP_union sup_max)
    also have \<open>\<dots> \<le> max (max (oracle_number p - length x2) (\<Squnion>x\<in>set x2. oracle_number x) - length os) (\<Squnion>a\<in>set os. oracle_number a)\<close>
    proof (rule aux)
      show \<open>oracle_number p - length (map (substitute_oracles_raw os) x2 @ os) \<le> oracle_number p - length x2 - length os\<close>
        by simp
      have \<open>(\<Squnion>a\<in>set x2. oracle_number (substitute_oracles_raw os a)) 
              \<le> (\<Squnion>a\<in>set x2. max (oracle_number a - length os) (\<Squnion>a\<in>set os. oracle_number a))\<close>
        apply (cases \<open>x2 = []\<close>)
        using InstantiateOracles(2)
        by (auto intro!: cSUP_mono)
      also have \<open>\<dots> = max (\<Squnion>a\<in>set x2. oracle_number a - length os) (\<Squnion>a\<in>set x2. \<Squnion>a\<in>set os. oracle_number a)\<close>
        apply (cases \<open>x2 = []\<close>)
         apply simp
        apply (simp only: flip: sup_max)
        apply (subst SUP_sup_distrib)
        by auto
      also have \<open>\<dots> \<le> max ((\<Squnion>x\<in>set x2. oracle_number x) - length os) (\<Squnion>a\<in>set os. oracle_number a)\<close>
        apply (cases \<open>x2 = []\<close>, simp)
        by (auto intro!: simp: SUP_diff_nat)
      finally show \<open>(\<Squnion>a\<in>set x2. oracle_number (substitute_oracles_raw os a)) \<le> max ((\<Squnion>x\<in>set x2. oracle_number x) - length os) (\<Squnion>a\<in>set os. oracle_number a)\<close>
        by -
    qed
    also have \<open>\<dots> = max (oracle_number (InstantiateOracles p x2) - length os) (\<Squnion>a\<in>set os. oracle_number a)\<close>
      by simp
    finally show \<open>oracle_number (substitute_oracles_raw os (InstantiateOracles p x2))
        \<le> max (oracle_number (InstantiateOracles p x2) - length os) (\<Squnion>a\<in>set os. oracle_number a)\<close>
      by -
  qed
next
  case (LocalQ x1 x2 p)
  then show ?case 
    by simp
next
  case (LocalC x1 x2 p)
  then show ?case 
    by simp
next
  case (OracleCall x)
  show ?case 
    by (auto intro!: le_cSup_finite)
qed

lemma no_oracles_substitute_oracles_raw:
  assumes \<open>oracle_number p \<le> length os\<close>
  assumes \<open>\<And>q. q \<in> set os \<Longrightarrow> no_oracles q\<close>
  shows \<open>no_oracles (substitute_oracles_raw os p)\<close>
proof (insert assms, induction p arbitrary: os)
  case (Seq p1 p2)
  then show ?case
    by (auto intro!: no_oracles.intros)
next
  case Skip
  then show ?case
    by (auto intro!: no_oracles.intros)
next
  case (Sample x)
  then show ?case
    by (auto intro!: no_oracles.intros)
next
  case (IfThenElse x1 p1 p2)
  then show ?case
    by (auto intro!: no_oracles.intros)
next
  case (While x1 p)
  then show ?case
    by (auto intro!: no_oracles.intros)
next
  case (QuantumOp x)
  then show ?case
    by (auto intro!: no_oracles.intros)
next
  case (Measurement x)
  then show ?case
    by (auto intro!: no_oracles.intros)
next
  case (InstantiateOracles p x2)
  from InstantiateOracles.prems
  have 1: \<open>oracle_number p \<le> length (map (substitute_oracles_raw os) x2 @ os)\<close>
    by auto
  have 3: \<open>q \<in> set os \<Longrightarrow> no_oracles q\<close> for q
    using InstantiateOracles.prems by blast
  have 2: \<open>no_oracles (substitute_oracles_raw os x)\<close> if \<open>x \<in> set x2\<close> for x
  proof -
    have \<open>(\<Squnion>x\<in>set x2. oracle_number x) \<le> length os\<close>
      using InstantiateOracles.prems(1)
      by simp
    then have \<open>oracle_number x \<le> length os\<close>
      apply (subst (asm) cSUP_le_iff)
      using that by auto
    from that this 3 show ?thesis
      by (rule InstantiateOracles.IH)
  qed
  show ?case
    apply simp
    using 1 apply (rule InstantiateOracles.IH)
    using 2 3 by auto
next
  case (LocalQ x1 x2 p)
  then show ?case
    by (auto intro!: no_oracles.intros)
next
  case (LocalC x1 x2 p)
  then show ?case
    by (auto intro!: no_oracles.intros)
next
  case (OracleCall x)
  then show ?case
    by (auto intro!: no_oracles.intros)
qed

lemma substitute_oracles_raw_no_oracles:
  assumes \<open>no_oracles p\<close>
  shows \<open>substitute_oracles_raw os p = p\<close>
  using assms apply induction by auto


inductive valid_oracle_program :: \<open>raw_program \<Rightarrow> bool\<close> (* and valid_program :: \<open>raw_program \<Rightarrow> bool\<close> *) where
valid_oracle_program_Seq:  \<open>valid_oracle_program c \<Longrightarrow> valid_oracle_program d \<Longrightarrow> valid_oracle_program (Seq c d)\<close>
| valid_oracle_program_Skip: \<open>valid_oracle_program Skip\<close>
| valid_oracle_program_Sample: \<open>(\<And>m. weight (e m) \<le> 1) \<Longrightarrow> valid_oracle_program (Sample e)\<close>
| valid_oracle_program_IfThenElse: \<open>valid_oracle_program c \<Longrightarrow> valid_oracle_program d \<Longrightarrow> valid_oracle_program (IfThenElse e c d)\<close>
| valid_oracle_program_While: \<open>valid_oracle_program c \<Longrightarrow> valid_oracle_program (While e c)\<close>
| valid_oracle_program_QuantumOp: \<open>(\<And>m. km_norm (e m) \<le> 1) \<Longrightarrow> valid_oracle_program (QuantumOp e)\<close>
| valid_oracle_program_Measurement: \<open>valid_oracle_program (Measurement e)\<close>
| valid_oracle_program_InstantiateOracles: \<open>(\<And>d. d \<in> set ds \<Longrightarrow> valid_oracle_program d \<and> no_oracles d) \<Longrightarrow> valid_oracle_program c \<Longrightarrow> 
  oracle_number c \<le> length ds \<Longrightarrow> valid_oracle_program (InstantiateOracles c ds)\<close>
| valid_oracle_program_LocalQ: \<open>valid_oracle_program c \<Longrightarrow> ACTUAL_QREGISTER q \<Longrightarrow> norm \<rho> = 1 \<Longrightarrow> valid_oracle_program (LocalQ q \<rho> c)\<close>
| valid_oracle_program_LocalC: \<open>valid_oracle_program c \<Longrightarrow> ACTUAL_CREGISTER x \<Longrightarrow> valid_oracle_program (LocalC x init c)\<close>

definition \<open>valid_program p \<longleftrightarrow> valid_oracle_program p \<and> no_oracles p\<close>

(* | valid_program_no_oracles: \<open>valid_oracle_program c \<Longrightarrow> no_oracles c \<Longrightarrow> valid_program c\<close> *)

lemma substitute_oracles_raw_relevant_prefix:
  assumes \<open>oracle_number p \<le> k\<close>
  assumes \<open>take k os1 = take k os2\<close>
  shows \<open>substitute_oracles_raw os1 p = substitute_oracles_raw os2 p\<close>
proof (insert assms, induction p arbitrary: os1 os2 k)
  case (Seq p1 p2)
  then show ?case
    by (metis nle_le oracle_number.simps(1) pre_arith_simps(3) substitute_oracles_raw.simps(1))
next
  case Skip
  then show ?case 
    by simp
next
  case (Sample x)
  then show ?case 
    by simp
next
  case (IfThenElse x1 p1 p2)
  then show ?case 
    by (smt (verit, best) max.absorb_iff2 max.assoc max.commute oracle_number.simps(6) order.refl substitute_oracles_raw.simps(2))
next
  case (While x1 p)
  then show ?case 
    by (metis oracle_number.simps(7) substitute_oracles_raw.simps(3))
next
  case (QuantumOp x)
  then show ?case 
    by simp
next
  case (Measurement x)
  then show ?case 
    by simp
next
  case (InstantiateOracles p x2)
  from InstantiateOracles.prems
  have 1: \<open>oracle_number p \<le> length x2 + k\<close>
    by auto
  have 3: \<open>take (oracle_number x) os1 = take (oracle_number x) os2\<close> if \<open>x \<in> set x2\<close> for x
  proof -
    from InstantiateOracles.prems
    have \<open>oracle_number (InstantiateOracles p x2) \<le> k\<close>
      by simp
    then have \<open>(\<Squnion>x\<in>set x2. oracle_number x) \<le> k\<close>
      by simp
    moreover have \<open>oracle_number x \<le> (\<Squnion>x\<in>set x2. oracle_number x)\<close>
      apply (rule Sup_upper_has_Sup)
      using that by (auto intro!: has_Sup_finite)
    ultimately have \<open>oracle_number x \<le> k\<close>
      by simp
    then show ?thesis
      using InstantiateOracles(4) take_greater_eqI by blast
  qed
  have 2: \<open>take (length x2 + k) (map (substitute_oracles_raw os1) x2 @ os1)
         = take (length x2 + k) (map (substitute_oracles_raw os2) x2 @ os2)\<close>
    by (auto simp add: take_add intro!: InstantiateOracles 3)
  have \<open>substitute_oracles_raw (map (substitute_oracles_raw os1) x2 @ os1) p =
    substitute_oracles_raw (map (substitute_oracles_raw os2) x2 @ os2) p\<close>
    using 1 2 by (rule InstantiateOracles.IH(1)[where k=\<open>length x2 + k\<close>])
  then show ?case
    by simp
next
  case (LocalQ x1 x2 p)
  then show ?case 
    by (metis oracle_number.simps(9) substitute_oracles_raw.simps(4))
next
  case (LocalC x1 x2 p)
  then show ?case 
    by (metis oracle_number.simps(10) substitute_oracles_raw.simps(5))
next
  case (OracleCall x)
  then show ?case
    apply auto
    by (metis Suc_le_lessD nth_take)
qed


lemma valid_oracle_program_substitute_oracles_raw[intro]:
  assumes \<open>valid_oracle_program p\<close>
  assumes \<open>\<And>q. q \<in> set os \<Longrightarrow> valid_oracle_program q\<close>
  shows \<open>valid_oracle_program (substitute_oracles_raw os p)\<close>
  using assms
proof (induction arbitrary: os)
  case (valid_oracle_program_Seq c d)
  then show ?case
    by (simp_all add: valid_oracle_program.intros)
next
  case valid_oracle_program_Skip
  then show ?case
    by (simp_all add: valid_oracle_program.intros)
next
  case (valid_oracle_program_Sample e)
  then show ?case 
by (simp_all add: valid_oracle_program.intros)
next
  case (valid_oracle_program_IfThenElse c d e)
  then show ?case
    by (simp_all add: valid_oracle_program.intros)
next
  case (valid_oracle_program_While c e)
  then show ?case
    by (simp_all add: valid_oracle_program.intros)
next
  case (valid_oracle_program_QuantumOp e)
  then show ?case
    by (simp_all add: valid_oracle_program.intros)
next
  case (valid_oracle_program_Measurement e)
  then show ?case
    by (simp_all add: valid_oracle_program.intros)
next
  case (valid_oracle_program_LocalQ c q \<rho>)
  then show ?case
    by (simp_all add: valid_oracle_program.intros)
next
  case (valid_oracle_program_LocalC c x init)
  then show ?case
    by (simp_all add: valid_oracle_program.intros)
next
  case (valid_oracle_program_InstantiateOracles ds c)
  have \<open>substitute_oracles_raw os (InstantiateOracles c ds) = 
      substitute_oracles_raw (map (substitute_oracles_raw os) ds @ os) c\<close>
    by simp
  moreover have \<open>\<dots> = substitute_oracles_raw (map (substitute_oracles_raw os) ds) c\<close>
    apply (rule substitute_oracles_raw_relevant_prefix[where k=\<open>length ds\<close>])
    using valid_oracle_program_InstantiateOracles.hyps
    by auto
  moreover have \<open>valid_oracle_program \<dots>\<close>
    apply (rule valid_oracle_program_InstantiateOracles.IH) 
    by (simp add: local.valid_oracle_program_InstantiateOracles(1) substitute_oracles_raw_no_oracles)
  ultimately show ?case
    by simp
qed


lemma valid_program_substitute_oracles_raw[intro]:
  assumes \<open>valid_program p\<close>
  shows \<open>valid_program (substitute_oracles_raw os p)\<close>
  using assms substitute_oracles_raw_no_oracles valid_program_def by auto

  
lemma valid_program_LocalQ: \<open>valid_program c \<Longrightarrow> ACTUAL_QREGISTER q \<Longrightarrow> norm \<rho> = 1 \<Longrightarrow> valid_program (LocalQ q \<rho> c)\<close>
  using no_oracles.intros(5) valid_oracle_program.intros(9) valid_program_def by blast

lemma valid_program_LocalC: \<open>valid_program c \<Longrightarrow> ACTUAL_CREGISTER x \<Longrightarrow> valid_program (LocalC x init c)\<close>
  using no_oracles.intros(4) valid_oracle_program.intros(10) valid_program_def by blast

typedef program = \<open>Collect valid_program\<close>
  apply (rule exI[of _ Skip])
  by (simp add: valid_oracle_program.intros valid_program_def no_oracles.intros)
setup_lifting type_definition_program

typedef oracle_program = \<open>Collect valid_oracle_program\<close>
  apply (rule exI[of _ Skip])
  by (simp add: valid_oracle_program.intros)
setup_lifting type_definition_oracle_program

lift_definition oracle_program_from_program :: \<open>program \<Rightarrow> oracle_program\<close> is id
  by (simp add: valid_program_def)

lift_definition seq :: \<open>program \<Rightarrow> program \<Rightarrow> program\<close> is Seq
proof -
  fix p q
  assume assms: \<open>p \<in> Collect valid_program\<close> \<open>q \<in> Collect valid_program\<close>
  have \<open>valid_oracle_program (Seq p q)\<close>
    using assms by (auto intro!: valid_oracle_program.intros valid_program_def simp: valid_program_def)
  moreover have \<open>no_oracles (Seq p q)\<close>
    using assms by (auto intro!: valid_oracle_program.intros no_oracles.intros simp: valid_program_def)
  ultimately show \<open>Seq p q \<in> Collect valid_program\<close>
    by (simp add: valid_oracle_program.intros valid_program_def)
qed

lift_definition skip :: program is Skip
  by (auto intro!: valid_oracle_program.intros no_oracles.intros simp: valid_program_def)

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
      by (auto intro!: valid_oracle_program.intros valid_program_def)
    show \<open>oracle_number (fold Seq [] Skip) = 0\<close>
      by simp
  next
    case (snoc p ps)
    then show \<open>valid_oracle_program (fold Seq (ps @ [p]) Skip)\<close>
      if \<open>list_all valid_program (ps @ [p])\<close>
      using that apply (auto intro!: valid_oracle_program.intros valid_program_def)
      using valid_program_def by blast
    show \<open>oracle_number (fold Seq (ps @ [p]) Skip) = 0\<close>
      if \<open>list_all valid_program (ps @ [p])\<close>
      using that snoc apply simp
      using valid_program_def by blast
  qed
  then show \<open>fold Seq ps Skip \<in> Collect valid_program\<close>
    by (simp add: valid_program_def)
qed *)

lift_definition sample :: \<open>'a cvariable \<Rightarrow> 'a distr expression \<Rightarrow> program\<close> is
  \<open>\<lambda>X e. Sample (\<lambda>m::cl. map_distr (\<lambda>x. setter X x m) (e m))\<close>
  by (simp add: valid_oracle_program.intros no_oracles.intros valid_program_def)

definition assign :: \<open>'a cvariable \<Rightarrow> 'a expression \<Rightarrow> program\<close> where
  \<open>assign x e = sample x (point_distr o e)\<close>

lift_definition qapply :: \<open>'a qvariable \<Rightarrow> ('a,'a) l2bounded expression \<Rightarrow> program\<close> is
  \<open>\<lambda>Q e. if qregister Q then
      QuantumOp (\<lambda>m. sandwich_tc (apply_qregister Q (if norm (e m) \<le> 1 then e m else 0))) else Skip\<close>
  apply (auto intro!: valid_oracle_program.intros no_oracles.intros simp: valid_program_def)
  by (simp add: power_le_one)

lift_definition ifthenelse1 :: \<open>bool expression \<Rightarrow> program \<Rightarrow> program \<Rightarrow> program\<close> is IfThenElse
  by (auto intro!: valid_oracle_program.intros no_oracles.intros simp: valid_program_def)

definition ifthenelse :: \<open>bool expression \<Rightarrow> program list \<Rightarrow> program list \<Rightarrow> program\<close> where
  \<open>ifthenelse c p q = ifthenelse1 c (block p) (block q)\<close>

lift_definition while1 :: \<open>bool expression \<Rightarrow> program \<Rightarrow> program\<close> is While
  by (auto intro!: valid_oracle_program.intros no_oracles.intros simp: valid_program_def)

definition while :: \<open>bool expression \<Rightarrow> program list \<Rightarrow> program\<close> where
  \<open>while c p = while1 c (block p)\<close>

(* lift_definition qinit :: \<open>'a qvariable \<Rightarrow> 'a ell2 expression \<Rightarrow> program\<close> is
\<open>\<lambda>... QuantumOp\<close> *)


lift_definition localvars1 :: "'a cvariable \<Rightarrow> 'b qvariable \<Rightarrow> program \<Rightarrow> program" is
  \<open>\<lambda>C Q p. LocalC (CREGISTER_of C) undefined (LocalQ (QREGISTER_of Q) (tc_butterfly (ket undefined) (ket undefined)) p)\<close>
  by (auto intro!: valid_program_LocalC valid_program_LocalQ ACTUAL_QREGISTER_QREGISTER_of simp: norm_tc_butterfly)

definition localvars :: "'a cvariable \<Rightarrow> 'b qvariable \<Rightarrow> program list \<Rightarrow> program" where
  \<open>localvars C Q ps = localvars1 C Q (block ps)\<close>

consts
  qinit :: "'a qvariable \<Rightarrow> 'a ell2 expression \<Rightarrow> program"
  measurement :: "'a cvariable \<Rightarrow> 'b qvariable \<Rightarrow> ('a,'b) measurement expression \<Rightarrow> program"
  instantiateOracles :: "oracle_program \<Rightarrow> program list \<Rightarrow> program"

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


(* definition \<open>swap_QREGISTER' = (\<lambda>(f,U,L,R).
  sandwich (U \<otimes>\<^sub>o U) (classical_operator (Some o map_prod (inv f) (inv f) o (\<lambda>((x,y),(z,w)). ((z,y),(x,w))) o map_prod f f))
)\<close> *)

definition cq_map_local_c :: \<open>'cl CREGISTER \<Rightarrow> 'cl \<Rightarrow> ('cl, 'qu1, 'cl, 'qu2) cq_map \<Rightarrow> ('cl, 'qu1, 'cl, 'qu2) cq_map\<close> where
  \<open>cq_map_local_c F init \<EE> = cq_map_from_pointwise (\<lambda>c.
      kf_map_outcome (\<lambda>d. copy_CREGISTER_from F c d) (cq_map_to_pointwise \<EE> (copy_CREGISTER_from F init c)))\<close>

lemma is_cq_map_cq_map_local_c[intro]:
  assumes \<open>is_cq_map \<EE>\<close>
  shows \<open>is_cq_map (cq_map_local_c F init \<EE>)\<close>
  by (simp add: cq_map_local_c_def)

lemma kf_norm_cq_map_local_c: \<open>kf_norm (cq_map_local_c F init \<EE>) \<le> kf_norm \<EE>\<close> //
  by (auto intro!: kf_norm_cq_map_from_pointwise kf_norm_cq_map_to_pointwise
      simp: cq_map_local_c_def)

lemma cq_map_local_c_cong: //
  assumes \<open>kraus_equivalent \<EE> \<FF>\<close>
  shows \<open>kraus_equivalent (cq_map_local_c F init \<EE>) (cq_map_local_c F init \<FF>)\<close>
  using assms
  by (auto intro!: cq_map_from_pointwise_cong kraus_equivalent'_map_cong cq_map_to_pointwise_cong
      simp: cq_map_local_c_def)

lift_definition denotation_local_c :: \<open>cl CREGISTER \<Rightarrow> cl \<Rightarrow> denotation \<Rightarrow> denotation\<close> is
  cq_map_local_c
proof (rename_tac F init \<EE> \<FF>, rule denotation_relI)
  fix \<EE> \<FF> init F
  assume \<open>denotation_rel \<EE> \<FF>\<close>
  then have \<open>is_cq_map \<EE>\<close>
    using denotation_rel_def by blast
  then show \<open>is_cq_map (cq_map_local_c F init \<EE>)\<close>
    by blast
  have \<open>kf_norm \<EE> \<le> 1\<close>
    using \<open>denotation_rel \<EE> \<FF>\<close> denotation_rel_def by force
  then show \<open>kf_norm (cq_map_local_c F init \<EE>) \<le> 1\<close>
    by (smt (verit) kf_norm_cq_map_local_c)
  have \<open>kraus_equivalent \<EE> \<FF>\<close>
    using \<open>denotation_rel \<EE> \<FF>\<close> denotation_rel_def by blast
  then show \<open>kraus_equivalent (cq_map_local_c F init \<EE>) (cq_map_local_c F init \<FF>)\<close>
    by (simp add: cq_map_local_c_cong)
qed

(* lift_definition cq_map_local_c :: \<open>'cl CREGISTER \<Rightarrow> 'cl \<Rightarrow> ('cl, 'qu1, 'cl, 'qu2) cq_map \<Rightarrow> ('cl, 'qu1, 'cl, 'qu2) cq_map\<close> is
  \<open>\<lambda>F init \<EE> c. kf_map_outcome (\<lambda>d. copy_CREGISTER_from F c d) (\<EE> (copy_CREGISTER_from F init c))\<close>
  by (auto simp: bdd_above_def) *)

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


definition cq_map_local_q :: 
  \<open>'qu QREGISTER \<Rightarrow> ('qu ell2, 'qu ell2) trace_class \<Rightarrow> ('cl,'qu) cq_map2 \<Rightarrow> ('cl,'qu) cq_map2\<close> where
  \<open>cq_map_local_q Q \<rho> \<EE> = cq_map_with_auxiliary_state \<rho> (cq_map_seq [
      cq_map_of_op (\<lambda>_. swap_QREGISTER Q),
      cq_map_tensor_id_right \<EE>,
      cq_map_of_op (\<lambda>_. swap_QREGISTER Q)])\<close>

lift_definition denotation_local_q :: 
  \<open>qu QREGISTER \<Rightarrow> (qu ell2, qu ell2) trace_class \<Rightarrow> denotation \<Rightarrow> denotation\<close>
  is cq_map_local_q
  by x


(* definition cq_map_local_q :: 
  \<open>'qu QREGISTER \<Rightarrow> ('qu ell2, 'qu ell2) trace_class \<Rightarrow> ('cl1,'qu,'cl2,'qu) cq_map \<Rightarrow> ('cl1,'qu,'cl2,'qu) cq_map\<close> where
  \<open>cq_map_local_q Q \<rho> \<EE> = cq_map_with_auxiliary_state \<rho> (
    cq_map_seq  (cq_map_of_op (swap_QREGISTER Q))
    (cq_map_seq (cq_map_tensor_id_right \<EE>)
                (cq_map_of_op (swap_QREGISTER Q))))\<close> *)


(* lemma infsum_le_finite_sums_wot':
  fixes b :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>summable_on_in cweak_operator_topology f A\<close>
  assumes \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> A \<Longrightarrow> sum f F \<le> b\<close>
  shows \<open>infsum_in cweak_operator_topology f A \<le> b\<close> *)

(* lemma infsum_le_finite_sums_wot:
  fixes b :: \<open>('a::chilbert_space, 'a) cblinfun_wot\<close>
  assumes \<open>f summable_on A\<close>
  assumes \<open>\<And>F. finite F \<Longrightarrow> F \<subseteq> A \<Longrightarrow> sum f F \<le> b\<close>
  shows \<open>infsum f A \<le> b\<close>
proof -
 *)


(* lemma kraus_map_from_measurement_norm: 
  assumes \<open>M \<noteq> 0\<close>
  shows \<open>kf_norm (kraus_map_from_measurement M) = 1\<close> *)

(* lemma kraus_map_from_measurement_0: \<open>kraus_equivalent' (kraus_map_from_measurement 0) 0\<close> *)

lift_definition denotation_measurement :: \<open>(cl \<Rightarrow> (cl, qu) measurement) \<Rightarrow> denotation\<close> is
  \<open>\<lambda>M. cq_map_from_pointwise (\<lambda>c. kraus_map_from_measurement (M c))\<close>
  by x

(* lift_definition cq_map_measurement :: \<open>('cl1 \<Rightarrow> ('cl2, 'qu) measurement) \<Rightarrow> ('cl1,'qu,'cl2,'qu) cq_map\<close> is
  \<open>\<lambda>m c. kraus_map_from_measurement (m c)\<close>
  by (auto intro!: kraus_map_from_measurement_norm_leq1 simp: bdd_above_def) *)

lift_definition denotation_id :: denotation is \<open>cq_id qFst\<close>
  by simp

lift_definition denotation_seq :: \<open>denotation \<Rightarrow> denotation \<Rightarrow> denotation\<close> is
  \<open>\<lambda>D E. E o D\<close>
  by x

lift_definition denotation_sample :: \<open>(cl \<Rightarrow> cl distr) \<Rightarrow> denotation\<close> is
  \<open>\<lambda>e. cq_map_sample (\<lambda>c. prob (e c))\<close>
  by x

lift_definition denotation_cases :: \<open>(cl \<Rightarrow> denotation) \<Rightarrow> denotation\<close> is cq_map_cases
  by x

lift_definition denotation_while :: \<open>(cl \<Rightarrow> bool) \<Rightarrow> denotation \<Rightarrow> denotation\<close> is cq_map_while
  by x

lift_definition denotation_on_quantum :: \<open>(cl \<Rightarrow> (qu ell2, qu ell2, 'x) kraus_family) \<Rightarrow> denotation\<close>
  is cq_map_on_q
  by x

fun denotation_raw :: \<open>raw_program \<Rightarrow> denotation\<close> where
  denotation_raw_Skip: \<open>denotation_raw Skip = denotation_id\<close>
| denotation_raw_Seq:  \<open>denotation_raw (Seq c d) = denotation_seq (denotation_raw c) (denotation_raw d)\<close>
| denotation_raw_Sample: \<open>denotation_raw (Sample e) = denotation_sample e\<close>
| denotation_raw_IfThenElse: \<open>denotation_raw (IfThenElse e c d) = denotation_cases (\<lambda>m. if e m then denotation_raw c else denotation_raw d)\<close>
| denotation_raw_While: \<open>denotation_raw (While e c) = denotation_while e (denotation_raw c)\<close>
| denotation_raw_QuantumOp: \<open>denotation_raw (QuantumOp \<EE>) = denotation_on_quantum \<EE>\<close>
| denotation_raw_Measurement: \<open>denotation_raw (Measurement m) = denotation_measurement m\<close>
| denotation_raw_OracleCall: \<open>denotation_raw (OracleCall _) = undefined\<close>
  \<comment> \<open>\<^const>\<open>OracleCall\<close> should not occur in valid programs\<close>
| denotation_raw_InstantiateOracles: \<open>denotation_raw (InstantiateOracles _ _) = undefined\<close>
  \<comment> \<open>\<^const>\<open>InstantiateOracles\<close> should not occur in valid programs\<close>
| denotation_raw_LocalC: \<open>denotation_raw (LocalC F init c) = denotation_local_c F init (denotation_raw c)\<close>
| denotation_raw_LocalQ: \<open>denotation_raw (LocalQ F init c) = denotation_local_q F init (denotation_raw c)\<close>

(* fun denotation_raw :: "raw_program \<Rightarrow> cq_map" where
  denotation_raw_Skip: \<open>denotation_raw Skip = cq_kf_id\<close>
| denotation_raw_Seq: \<open>denotation_raw (Seq c d) = cq_kf_comp (denotation_raw d) (denotation_raw c)\<close>
| denotation_raw_Sample: \<open>denotation_raw (Sample e) = 
      cq_operator_cases (\<lambda>c \<rho>. cq_diagonal_operator (prob (e c)) \<rho>) \<rho>\<close>

fun denotation_raw :: "raw_program \<Rightarrow> cq_operator \<Rightarrow> cq_operator" where
  denotation_raw_Skip: \<open>denotation_raw Skip \<rho> = \<rho>\<close>
| denotation_raw_Seq: \<open>denotation_raw (Seq c d) \<rho> = denotation_raw d (denotation_raw c \<rho>)\<close>
| denotation_raw_Sample: \<open>denotation_raw (Sample e) \<rho> = cq_operator_cases (\<lambda>c \<rho>. cq_from_distrib (e c) \<rho>) \<rho>\<close>
(* TODO missing cases *)
 *)

lift_definition denotation :: "program \<Rightarrow> denotation" is denotation_raw.

lemma denotation_sample: \<open>denotation (sample x e) = denotation_sample (\<lambda>m. map_distr (\<lambda>xa. Classical_Registers.setter x xa m) (e m))\<close>
  apply (transfer' fixing: x e)
  by simp

lemma kf_norm_sample_prob: \<open>kf_norm (kraus_map_sample (prob \<mu>) :: ('a::{chilbert_space,not_singleton},'a,'x) kraus_family) = weight \<mu>\<close>
  apply (subst kraus_map_sample_norm[of \<open>prob \<mu>\<close>])
  by (auto intro!: prob_summable simp: Prob.rep_eq)

lemma kraus_map_sample_point_distr': \<open>kf_remove_0 (kraus_map_sample (prob (point_distr x))) 
                                        = kf_remove_0 (kf_map_outcome_inj (\<lambda>_. x) kf_id)\<close>
  apply (rule Rep_kraus_family_inject[THEN iffD1])
  by (auto intro!: prob_summable
      simp: kraus_map_sample.rep_eq kf_map_outcome_inj.rep_eq kf_id_def
      kf_of_op.rep_eq kf_remove_0.rep_eq image_iff
      simp del: kf_of_op_id)

lemma kraus_map_sample_point_distr: \<open>kraus_equivalent' (kraus_map_sample (prob (point_distr x))) (kf_map_outcome_inj (\<lambda>_. x) kf_id)\<close>
  using kraus_map_sample_point_distr'[of x] kf_remove_0_equivalent'
    kraus_equivalent'_sym kraus_equivalent'_trans
  by metis

lemma cq_map_sample_point_distr: \<open>cq_map_equiv (cq_map_sample (\<lambda>x. point_distr (f x))) (cq_map_classical f)\<close>
  apply (transfer' fixing: )
  by (auto intro!: kraus_map_sample_point_distr simp: kf_norm_sample_prob)

lemma denotation_assign_sample: \<open>denotation (assign x e) = denotation_sample (\<lambda>m. point_distr (Classical_Registers.setter x (e m) m))\<close>
  by (simp add: assign_def denotation_sample)
lemma denotation_assign: \<open>denotation (assign x e) = (cq_map_classical (\<lambda>m. Classical_Registers.setter x (e m) m))\<close>
  by (simp add: denotation_assign_sample cq_map_sample_point_distr)

lemma denotation_skip: \<open>denotation skip = cq_map_id\<close>
  apply transfer' 
  by simp

lemma denotation_seq: \<open>denotation (seq p q) = cq_map_seq (denotation p) (denotation q)\<close>
  apply transfer' by (auto intro!: ext)

lemma denotation_block: "cq_map_equiv (denotation (block ps)) (foldr (\<lambda>p s. cq_map_seq (denotation p) s) ps cq_map_id)"
proof (induction ps rule:block.induct)
  case 1
  show ?case
    by (simp add: block_empty denotation_skip)
next
  case (2 p)
  show ?case
    by (simp add: block_single denotation_skip)
next
  case (3 p q ps)
  have \<open>cq_map_equiv (denotation (block (p # q # ps))) (cq_map_seq (denotation p) (denotation (block (q # ps))))\<close>
    by (simp add: block_cons denotation_seq)
  also have \<open>cq_map_equiv \<dots> (cq_map_seq (denotation p) (foldr (\<lambda>p. cq_map_seq (denotation p)) (q # ps) cq_map_id))\<close>
    apply (rule cq_map_seq_cong)
     apply (rule cq_map_equiv_refl)
    by (rule 3)
  also have \<open>\<dots> = (foldr (\<lambda>p. cq_map_seq (denotation p)) (p # q # ps) cq_map_id)\<close>
    by simp
  finally show ?case
    by -
qed

lemma denotation_ifthenelse1:
  \<open>denotation (ifthenelse1 c p q) = cq_map_if c (denotation p) (denotation q)\<close>
  apply (transfer' fixing: c)
  by simp

lemma denotation_ifthenelse:
  \<open>denotation (ifthenelse c p q) = cq_map_if c (denotation (block p)) (denotation (block q))\<close>
  by (simp add: denotation_ifthenelse1 ifthenelse_def)

lemma denotation_localvars1:
  \<open>denotation (localvars1 C Q p) = cq_map_local_c (CREGISTER_of C) undefined (cq_map_local_q (QREGISTER_of Q) (tc_butterfly |undefined\<rangle> |undefined\<rangle>) (denotation p))\<close>
proof -
  define p' and \<rho>0 :: \<open>(qu ell2, qu ell2) trace_class\<close>
    where \<open>p' = Rep_program p\<close> and \<open>\<rho>0 = tc_butterfly |undefined\<rangle> |undefined\<rangle>\<close>
  have \<open>denotation (localvars1 C Q p) = 
      denotation_raw (LocalC (CREGISTER_of C) undefined (LocalQ (QREGISTER_of Q) \<rho>0 p'))\<close>
    unfolding p'_def \<rho>0_def
    apply transfer'
    by (rule refl)
  also have \<open>\<dots> = cq_map_local_c (CREGISTER_of C) undefined (cq_map_local_q (QREGISTER_of Q) \<rho>0 (denotation_raw p'))\<close>
    by simp
  also have \<open>\<dots> = cq_map_local_c (CREGISTER_of C) undefined (cq_map_local_q (QREGISTER_of Q) \<rho>0 (denotation p))\<close>
    using denotation.rep_eq p'_def by presburger
  finally show ?thesis
    using \<rho>0_def by presburger
qed

(* TODO move *)
lemma option_CARD_1_exhaust[case_names None Some, cases type: option]:
  \<open>(y = (\<lambda>_. None) \<Longrightarrow> P) \<Longrightarrow> (y = Some \<Longrightarrow> P) \<Longrightarrow> P\<close> for y :: \<open>'a::CARD_1 \<Rightarrow> 'a option\<close>
proof (atomize_elim, cases \<open>y undefined\<close>)
  case None
  have \<open>y = (\<lambda>_. None)\<close>
    apply (rule ext)
    apply (subst everything_the_same[where 'a='a and y=undefined])
    using None by simp
  then show \<open>y = (\<lambda>_. None) \<or> y = Some\<close>
    by simp
next
  case (Some a)
  have \<open>y = Some\<close>
    apply (rule ext)
    apply (subst everything_the_same[where 'a='a and y=undefined])
    using Some by simp
  then show \<open>y = (\<lambda>_. None) \<or> y = Some\<close>
    by simp
qed

(* lemmas option_CARD_1_exhaust'[case_names None Some, cases type: option] = option_CARD_1_exhaust[where x=undefined] *)

(* TODO move *)
lemma empty_cregister_raw_None[simp]: \<open>empty_cregister_raw (\<lambda>_. None) = (\<lambda>_. None)\<close>
  by (auto simp add: empty_cregister_raw_def register_from_getter_setter_def)

(* TODO move *)
lemma empty_cregister_raw_Some[simp]: \<open>empty_cregister_raw (\<lambda>_. Some x) = Some\<close>
  by (auto simp add: empty_cregister_raw_def register_from_getter_setter_def)

(* TODO move *)
lemma CREGISTER_of_empty_cregister[simp]: \<open>CREGISTER_of (empty_cregister :: ('a::{CARD_1,enum},'b) cregister) = \<bottom>\<close>
proof -
  let ?empty = \<open>empty_cregister :: ('a,'b) cregister\<close>
  let ?empty_raw = \<open>empty_cregister_raw :: 'a cupdate \<Rightarrow> 'b cupdate\<close>
  have None: \<open>Map.empty \<in> range (apply_cregister ?empty)\<close>
    apply (rule range_eqI[where x=\<open>\<lambda>_. None\<close>])
    by simp
  have Some: \<open>Some \<in> range (apply_cregister ?empty)\<close>
    apply (rule range_eqI[where x=\<open>Some\<close>])
    by simp
  have *: \<open>apply_cregister empty_cregister x = Some\<close> if \<open>apply_cregister empty_cregister x \<noteq> Map.empty\<close> for x :: \<open>'a cupdate\<close>
    apply (cases x rule: option_CARD_1_exhaust)
    using that
    by auto
  have 1: \<open>range (apply_cregister ?empty) = empty_cregister_range\<close>
    by (auto intro!: None Some * simp: empty_cregister_range_def)
  show ?thesis
    apply transfer'
    using 1 by simp
qed

(* TODO move *)
lemma kraus_equivalent'_map_outcome_id: \<open>kraus_equivalent' (kf_map_outcome (\<lambda>x. x) E) E\<close>
  by (simp add: kraus_equivalent'_def kf_apply'_def kf_filter_map_outcome)


lemma cq_map_local_c_bot[simp]:
  shows \<open>cq_map_equiv (cq_map_local_c \<bottom> m E) E\<close>
proof (rule cq_map_eqI)
  fix \<rho>
  show \<open>cq_map_apply (cq_map_local_c \<bottom> m E) \<rho> = cq_map_apply E \<rho>\<close>
    (* apply (rule local_defE[of E]) *)
    apply (transfer' fixing: m)
    by (simp add: copy_CREGISTER_from_bot[abs_def])
qed

(* TODO move *)
lemma one_dim_cblinfun_eqI:
  fixes a b :: \<open>'a::one_dim \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  assumes \<open>a 1 = b 1\<close>
  shows \<open>a = b\<close>
proof (rule cblinfun_eqI)
  fix \<psi> :: 'a
  define c :: complex where \<open>c = one_dim_iso \<psi>\<close>
  have *: \<open>\<psi> = c *\<^sub>C 1\<close>
    by (simp add: c_def)
  from assms have \<open>a (c *\<^sub>C 1) = b (c *\<^sub>C 1)\<close>
    by (metis cblinfun.scaleC_right)
  with * show \<open>a \<psi> = b \<psi>\<close>
    by simp
qed

lemma tensor_ell2_one_dim_1_1: \<open>tensor_ell2 1 1 = 1\<close>
  apply (subst ket_CARD_1_is_1[symmetric])+
  by (simp add: tensor_ell2_ket)

lemma swap_ell2_one_dim_1[simp]: \<open>swap_ell2 = 1\<close>
  apply (rule one_dim_cblinfun_eqI)
  apply (simp flip: tensor_ell2_one_dim_1_1)
  by (simp add: tensor_ell2_one_dim_1_1)

(* TODO move *)
lemma swap_QREGISTER_bot[simp]: \<open>swap_QREGISTER \<bottom> = id_cblinfun\<close>
proof -
  let ?empty = \<open>empty_qregister :: (unit,_) qregister\<close>
  let ?swap = \<open>swap_ell2 :: (unit*unit) ell2 \<Rightarrow>\<^sub>C\<^sub>L _\<close>
  have \<open>swap_QREGISTER \<bottom> = swap_QREGISTER (QREGISTER_of ?empty)\<close>
    by simp
  also have \<open>\<dots> = apply_qregister (qregister_tensor ?empty ?empty) ?swap\<close>
    apply (subst swap_QREGISTER_QREGISTER_of)
    by auto
  also have \<open>\<dots> = apply_qregister (qregister_tensor ?empty ?empty) (one_dim_iso ?swap *\<^sub>C id_cblinfun)\<close>
    by simp
  also have \<open>\<dots> = one_dim_iso ?swap *\<^sub>C apply_qregister (qregister_tensor ?empty ?empty) id_cblinfun\<close>
    by simp
  also have \<open>\<dots> = apply_qregister (qregister_tensor ?empty ?empty) id_cblinfun\<close>
    by simp
  also have \<open>\<dots> = id_cblinfun\<close>
    using apply_qregister_of_id empty_qregister_is_register qregister_qregister_tensor by blast
  finally show ?thesis
    by -
qed

(* TODO move *)
lemma cq_operator_eqI:
  assumes \<open>\<And>c. Rep_cq_operator s c = Rep_cq_operator t c\<close>
  shows \<open>s = t\<close>
  using assms
  apply transfer'
  by auto

lemma kf_apply'_map_outcome_inj[simp]:
  (* assumes \<open>inj_on f (Set.filter (\<lambda>x. f x \<in> X) (kraus_map_domain E)) \<close> *)
  assumes \<open>inj_on f ((f -` X) \<inter> kraus_map_domain E)\<close>
  shows  \<open>kf_apply' X (kf_map_outcome_inj f E) \<rho> = kf_apply' (f -` X) E \<rho>\<close>
proof -
  from assms
  have \<open>inj_on f (Set.filter (\<lambda>x. f x \<in> X) (kraus_map_domain E))\<close>
    by (smt (verit, del_insts) IntI Set.member_filter inj_onD inj_onI vimage_eq)
  then show ?thesis
    by (auto intro!: simp: kf_apply'_def kf_filter_map_outcome_inj)
qed

lemma kf_apply'_empty[simp]:
  \<open>kf_apply' {} E = 0\<close>
  by (simp add: kf_apply'_def)

(* TODO move *)
lemma Rep_cq_map_apply_quantum_op:
  fixes c :: 'c and \<rho> :: \<open>('c,'q) cq_operator\<close> and E :: \<open>'c \<Rightarrow> ('q ell2, 'r ell2, 'd) kraus_family\<close>
  assumes \<open>bdd_above (range (\<lambda>c. kf_norm (E c)))\<close>
  shows \<open>Rep_cq_operator (cq_map_apply (cq_map_quantum_op E) \<rho>) c = kf_apply (E c) (Rep_cq_operator \<rho> c)\<close>
  apply (transfer fixing: E c)
  apply (subst infsum_single[where i=c])
  by (simp_all add: assms)
  
(* TODO move *)
lemma Rep_cq_map_apply_of_op:
  fixes c :: 'c and \<rho> :: \<open>('c,'q) cq_operator\<close> and a :: \<open>'q ell2 \<Rightarrow>\<^sub>C\<^sub>L 'r ell2\<close>
  shows \<open>Rep_cq_operator (cq_map_apply (cq_map_of_op a) \<rho>) c = kf_apply (kf_of_op a) (Rep_cq_operator \<rho> c)\<close>
  by (simp add: cq_map_of_op_def Rep_cq_map_apply_quantum_op power_le_one)


(* lemma kf_apply'_map_outcome[simp]: \<open>kf_apply' X (kf_map_outcome f E) = kf_apply' (f -` X) E\<close>
  by (auto intro!: simp: kf_apply'_def kf_filter_map_outcome) *)

(* TODO move *)
lemma cq_map_of_op_id[simp]: \<open>cq_map_apply (cq_map_of_op id_cblinfun) = id\<close>
  by (auto intro!: ext cq_operator_eqI simp: Rep_cq_map_apply_of_op)

lemma Rep_cq_map_apply_partial_trace: \<open>Rep_cq_operator (cq_map_apply cq_map_partial_trace \<rho>) c
  = kf_apply (kraus_map_partial_trace (range ket)) (Rep_cq_operator \<rho> c)\<close>
  apply (transfer' fixing: c)
  apply (subst infsum_single[of c])
  by auto

lemma cq_norm_raw_pos[iff]: \<open>cq_norm_raw \<rho> \<ge> 0\<close>
  by (auto intro!: infsum_nonneg simp: cq_norm_raw_def)

(* instantiation cq_operator :: (type,type) norm begin
lift_definition norm_cq_operator :: \<open>('a, 'b) cq_operator \<Rightarrow> real\<close> is cq_norm_raw.
instance..
end *)

setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>norm\<close>, SOME \<^typ>\<open>'a::norm \<Rightarrow> real\<close>)\<close>


(* lift_definition cq_tensor :: \<open>('c1,'q1) cq_operator \<Rightarrow> ('c2,'q2) cq_operator \<Rightarrow> ('c1\<times>'c2, 'q1\<times>'q2) cq_operator\<close> is
  \<open>\<lambda>\<rho>1 \<rho>2 (c1,c2). tc_tensor (\<rho>1 c1) (\<rho>2 c2)\<close>
proof (intro conjI allI)
  fix \<rho>1 :: \<open>'c1 \<Rightarrow> ('q1 ell2, 'q1 ell2) trace_class\<close> and \<rho>2 :: \<open>'c2 \<Rightarrow> ('q2 ell2, 'q2 ell2) trace_class\<close> and c :: \<open>'c1\<times>'c2\<close>
  assume asm1: \<open>(\<forall>c. 0 \<le> \<rho>1 c) \<and> \<rho>1 abs_summable_on UNIV\<close>
  assume asm2: \<open>(\<forall>c. 0 \<le> \<rho>2 c) \<and> \<rho>2 abs_summable_on UNIV\<close>
  from asm1 asm2 show \<open>0 \<le> (case c of (c1, c2) \<Rightarrow> tc_tensor (\<rho>1 c1) (\<rho>2 c2))\<close>
    apply (cases c)
    by (simp add: tc_tensor_pos)
  from asm1 have sum1: \<open>(\<lambda>x. norm (\<rho>1 x)) abs_summable_on UNIV\<close>
    by simp
  from asm2 have sum2: \<open>(\<lambda>x. norm (\<rho>2 x)) abs_summable_on UNIV\<close>
    by simp
  show \<open>(\<lambda>(c1, c2). tc_tensor (\<rho>1 c1) (\<rho>2 c2)) abs_summable_on UNIV\<close>
  proof -
    from abs_summable_times[OF sum1 sum2]
    show ?thesis
      by (simp add: norm_tc_tensor case_prod_beta)
  qed
qed *)


(* lemma norm_cq_tensor: \<open>norm (cq_tensor \<rho> \<sigma>) = norm \<rho> * norm \<sigma>\<close>
proof transfer
  fix \<rho> :: \<open>'e \<Rightarrow> ('g ell2, 'g ell2) trace_class\<close> and \<sigma> :: \<open>'b \<Rightarrow> ('d ell2, 'd ell2) trace_class\<close>
  assume asm1: \<open>(\<forall>c. 0 \<le> \<rho> c) \<and> \<rho> abs_summable_on UNIV\<close>
  assume asm2: \<open>(\<forall>c. 0 \<le> \<sigma> c) \<and> \<sigma> abs_summable_on UNIV\<close>
  from asm1 have sum1: \<open>(\<lambda>x. norm (\<rho> x)) abs_summable_on UNIV\<close>
    by simp
  from asm2 have sum2: \<open>(\<lambda>x. norm (\<sigma> x)) abs_summable_on UNIV\<close>
    by simp
  have \<open>cq_norm_raw (\<lambda>(c1, c2). tc_tensor (\<rho> c1) (\<sigma> c2)) = (\<Sum>\<^sub>\<infinity>(c1,c2). norm (\<rho> c1) * norm (\<sigma> c2))\<close>
    by (simp add: cq_norm_raw_def norm_tc_tensor case_prod_unfold)
  also
  from abs_summable_times[OF sum1 sum2]
  have \<open>\<dots> = (\<Sum>\<^sub>\<infinity>c1. norm (\<rho> c1)) * (\<Sum>\<^sub>\<infinity>c2. norm (\<sigma> c2))\<close>
    apply (subst infsum_product)
    by (auto intro!: simp: case_prod_unfold)
  also have \<open>\<dots> = cq_norm_raw \<rho> * cq_norm_raw \<sigma>\<close>
    by (metis cq_norm_raw_def)
  finally show \<open>cq_norm_raw (\<lambda>(c1, c2). tc_tensor (\<rho> c1) (\<sigma> c2)) = cq_norm_raw \<rho> * cq_norm_raw \<sigma>\<close>
    by -
qed *)


definition \<open>cq_tensor_left \<rho> \<sigma> = cq_map_apply (cq_map_classical fst) (cq_tensor \<rho> (fixed_cl_cq_operator () \<sigma>))\<close>
definition \<open>cq_tensor_right \<rho> \<sigma> = cq_map_apply (cq_map_classical snd) (cq_tensor (fixed_cl_cq_operator () \<rho>) \<sigma>)\<close>

lift_definition cq_classical_carrier :: \<open>('c,'q) cq_operator \<Rightarrow> 'c set\<close> is
  \<open>\<lambda>\<rho>. {c. \<rho> c \<noteq> 0}\<close>.

lemma Rep_cq_map_classical_inj:
  assumes inj: \<open>inj_on f X\<close>
  assumes carrier: \<open>cq_classical_carrier \<rho> \<subseteq> X\<close>
  shows \<open>Rep_cq_operator (cq_map_apply (cq_map_classical f) \<rho>) c
       = of_bool (c \<in> f ` X) *\<^sub>C Rep_cq_operator \<rho> (inv_into X f c)\<close>
proof (insert carrier, transfer' fixing: c f X)
  fix \<rho> :: \<open>'a \<Rightarrow> ('c ell2, 'c ell2) trace_class\<close>
  define c' where \<open>c' = inv_into X f c\<close>
  assume carrier: \<open>{c. \<rho> c \<noteq> 0} \<subseteq> X\<close>
  then have 1: \<open>\<rho> j = 0\<close> if \<open>c = f j\<close> and \<open>j \<noteq> c'\<close> for j
    apply (transfer' fixing: j f X)
    using that inj by (auto simp: c'_def)
  have \<open>(\<Sum>\<^sub>\<infinity>d. kf_apply' {c} (kf_map_outcome_inj (\<lambda>_. f d) kf_id) (\<rho> d))
      = (\<Sum>\<^sub>\<infinity>d. kf_apply' ((\<lambda>_::unit. f d) -` {c}) kf_id (\<rho> d))\<close>
    by (simp add: kf_apply'_map_outcome_inj inj_on_def)
  also have \<open>\<dots> = kf_apply' ((\<lambda>_. f c') -` {c}) kf_id (\<rho> c')\<close>
    apply (subst infsum_single[where i=\<open>inv_into X f c\<close>])
    using 1 by (simp_all add: c'_def)
  also from carrier inj have \<open>\<dots> = of_bool (c \<in> f ` X) *\<^sub>C \<rho> c'\<close>
    by (force simp: c'_def)
  finally show \<open>(\<Sum>\<^sub>\<infinity>d. kf_apply' {c} (kf_map_outcome_inj (\<lambda>_. f d) kf_id) (\<rho> d)) = \<dots>\<close>
    by -
qed


lemma Rep_cq_tensor[simp]:
  \<open>Rep_cq_operator (cq_tensor \<rho> \<sigma>) (c,d) = tc_tensor (Rep_cq_operator \<rho> c) (Rep_cq_operator \<sigma> d)\<close>
  apply (transfer' fixing: c d)
  by auto

lemma Rep_fixed_cl_cq_operator[simp]:
  shows \<open>Rep_cq_operator (fixed_cl_cq_operator c \<rho>) d = of_bool (\<rho> \<ge> 0 \<and> c=d) *\<^sub>C \<rho>\<close>
  apply (transfer' fixing: c d \<rho>)
  by auto



lemma Rep_cq_tensor_left[simp]:
  assumes \<open>\<sigma> \<ge> 0\<close> and \<open>trace_tc \<sigma> \<le> 1\<close>
  shows \<open>Rep_cq_operator (cq_tensor_left \<rho> \<sigma>) c = tc_tensor (Rep_cq_operator \<rho> c) \<sigma>\<close>
proof -
  have [simp]: \<open>inv fst c = (c,())\<close>
    by (metis range_fst split_pairs surj_f_inv_f unit.exhaust)
  show ?thesis
    unfolding cq_tensor_left_def
    apply (subst Rep_cq_map_classical_inj[where X=UNIV])
    using assms
    by (auto simp: inj_def)
qed

lemma cq_apply_map_tensor_id_right:
  fixes \<rho> :: \<open>('a ell2, 'a ell2) trace_class\<close> and \<sigma> :: \<open>('b ell2, 'b ell2) trace_class\<close>
    and E :: \<open>('c, 'a, 'd, 'e) cq_map\<close>
  assumes \<open>\<rho> \<ge> 0\<close> and \<open>trace_tc \<rho> \<le> 1\<close>
  assumes \<open>\<sigma> \<ge> 0\<close> and \<open>trace_tc \<sigma> \<le> 1\<close>
  shows \<open>cq_map_apply (cq_map_tensor_id_right E) (fixed_cl_cq_operator c (tc_tensor \<rho> \<sigma>))
        = cq_tensor_left (cq_map_apply E (fixed_cl_cq_operator c \<rho>)) \<sigma>\<close>
proof (rule cq_operator_eqI)
  fix d :: 'd
  have [simp]: \<open>0 \<le> tc_tensor \<rho> \<sigma>\<close>
    using assms tc_tensor_pos by blast
  then have [simp]: \<open>trace_tc (tc_tensor \<rho> \<sigma>) \<le> 1\<close>
    using assms
    by (metis complex_of_real_mono_iff less_eq_complex_def mult_le_one norm_tc_pos norm_tc_pos_Re norm_tc_tensor of_real_hom.hom_zero one_complex.sel(1) trace_tc_pos)
  obtain E' where [transfer_rule]: \<open>cr_cq_map E' E\<close>
    using cq_map.right_total
    by (auto simp: right_total_def)
  have \<open>Rep_cq_operator (cq_map_apply (cq_map_tensor_id_right E) (fixed_cl_cq_operator c (tc_tensor \<rho> \<sigma>))) d
    = (\<Sum>\<^sub>\<infinity>e. kf_apply' (fst -` {d}) (kf_tensor (E' e) kf_id) (of_bool (c = e) *\<^sub>R tc_tensor \<rho> \<sigma>))\<close>
    apply (transfer' fixing: c d \<sigma> \<rho>)
    by simp
  also have \<open>\<dots> = kf_apply' (fst -` {d}) (kf_tensor (E' c) kf_id) (tc_tensor \<rho> \<sigma>)\<close>
    apply (subst infsum_single[where i=c])
    by simp_all
  also have \<open>\<dots> = kf_apply (kf_tensor (kf_filter (\<lambda>x. x=d) (E' c)) (kf_filter (\<lambda>_. True) kf_id)) (tc_tensor \<rho> \<sigma>)\<close>
    apply (subst kf_filter_tensor[symmetric])
    by (simp add: kf_apply'_def case_prod_unfold)
  also have \<open>\<dots> = tc_tensor (kf_apply (kf_filter (\<lambda>x. x = d) (E' c)) \<rho>) \<sigma>\<close>
    by (simp add: kf_apply_tensor)
  also have \<open>\<dots> = tc_tensor (kf_apply' {d} (E' c) \<rho>) \<sigma>\<close>
    by (simp add: kf_apply'_def)
  also have \<open>\<dots> = tc_tensor (\<Sum>\<^sub>\<infinity>da. kf_apply' {d} (E' da) (of_bool (c = da) *\<^sub>R \<rho>)) \<sigma>\<close>
    apply (subst infsum_single[where i=c])
    by auto
  also have \<open>\<dots> = tc_tensor (Rep_cq_operator (cq_map_apply E (fixed_cl_cq_operator c \<rho>)) d) \<sigma>\<close>
    apply (transfer' fixing: \<rho> \<sigma> c d)
    by (simp add: assms)
  also have \<open>\<dots> = Rep_cq_operator (cq_tensor_left (cq_map_apply E (fixed_cl_cq_operator c \<rho>)) \<sigma>) d\<close>
    apply (subst Rep_cq_tensor_left)
    by (simp_all add: assms)
  finally show \<open>Rep_cq_operator (cq_map_apply (cq_map_tensor_id_right E) (fixed_cl_cq_operator c (tc_tensor \<rho> \<sigma>))) d = \<dots>\<close>
    by -
qed

lemma Rep_apply_fixed_cl_cq_operator:
  assumes \<open>\<rho> \<ge> 0\<close>
  shows \<open>Rep_cq_operator (cq_map_apply E (fixed_cl_cq_operator c \<rho>)) d = kf_apply' {d} (Rep_cq_map E c) \<rho>\<close>
  apply (transfer' fixing: c d \<rho>)
  apply (subst infsum_single)
  using assms
  by auto

lemma is_kraus_map_kf_apply'[iff]: \<open>kraus_map (kf_apply' X E)\<close>
  by (simp add: kf_apply'_def)

lemma separating_set_kraus_map_range_irrelevant:
  assumes \<open>separating_set (kraus_map :: (('q::chilbert_space,'q) trace_class \<Rightarrow> ('r::chilbert_space,'r) trace_class) \<Rightarrow> bool) S\<close>
  shows \<open>separating_set (kraus_map :: (('q,'q) trace_class \<Rightarrow> ('s::chilbert_space,'s) trace_class) \<Rightarrow> bool) S\<close>
  by x

lemma kraus_equivalent'_from_separatingI:
  fixes E F :: \<open>('q::chilbert_space,'r::chilbert_space,'x) kraus_family\<close>
  assumes \<open>separating_set (kraus_map :: (('q,'q) trace_class \<Rightarrow> (complex,complex) trace_class) \<Rightarrow> bool) S\<close>
  assumes \<open>\<And>x \<rho>. \<rho> \<in> S \<Longrightarrow> kf_apply' {x} E \<rho> = kf_apply' {x} F \<rho>\<close>
  shows \<open>kraus_equivalent' E F\<close>
proof -
  have \<open>kf_apply' {x} E = kf_apply' {x} F\<close> for x
    apply (rule eq_from_separatingI)
       apply (rule separating_set_kraus_map_range_irrelevant)
       apply (rule assms(1))
    using assms(2) by (auto intro!: simp: )
  then show ?thesis
    by (simp add: kraus_equivalent'I)
qed

lemma cq_map_eq_from_separatingI:
  fixes E F :: \<open>('c1,'q1,'c2,'q2) cq_map\<close>
  assumes sep: \<open>separating_set (kraus_map :: (('q1 ell2,'q1 ell2) trace_class \<Rightarrow> (complex, complex) trace_class) \<Rightarrow> bool) S\<close>
  assumes pos: \<open>\<And>\<rho>. \<rho> \<in> S \<Longrightarrow> \<rho> \<ge> 0\<close>
  assumes eq: \<open>\<And>c \<rho>. \<rho> \<in> S \<Longrightarrow> cq_map_apply E (fixed_cl_cq_operator c \<rho>) = cq_map_apply F (fixed_cl_cq_operator c \<rho>)\<close>
  shows \<open>cq_map_equiv E F\<close>
proof -
  define E' F' where \<open>E' = Rep_cq_map E\<close> and \<open>F' = Rep_cq_map F\<close>
  have \<open>Rep_cq_operator (cq_map_apply E (fixed_cl_cq_operator c \<rho>)) d
     = Rep_cq_operator (cq_map_apply F (fixed_cl_cq_operator c \<rho>)) d\<close> if \<open>\<rho> \<in> S\<close> for c d \<rho>
    using eq that by presburger
  then have \<open>kf_apply' {x} (E' c) \<rho> = kf_apply' {x} (F' c) \<rho>\<close> if \<open>\<rho> \<in> S\<close> for c x \<rho>
    by (simp add: Rep_apply_fixed_cl_cq_operator E'_def F'_def pos that)
  from sep this have \<open>kraus_equivalent' (E' c) (F' c)\<close> for c
    by (rule kraus_equivalent'_from_separatingI)
  then have \<open>kf_apply' {d} (E' c) \<rho> = kf_apply' {d} (F' c) \<rho>\<close> for c d \<rho>
    by (simp add: kf_apply'_eqI)
  then have \<open>cq_map_apply E \<rho> = cq_map_apply F \<rho>\<close> for \<rho>
    unfolding E'_def F'_def
    apply (transfer' fixing: S)
    by auto
  then show \<open>cq_map_equiv E F\<close>
    by (rule cq_map_eqI)
qed

(* TODO move *)
lemma trace_tc_scaleR: \<open>trace_tc (r *\<^sub>R t) = r *\<^sub>R trace_tc t\<close>
  by (simp add: scaleR_scaleC trace_tc_scaleC)


(* TODO move *)
instantiation cq_operator :: (type,type) scaleR begin
lift_definition scaleR_cq_operator :: \<open>real \<Rightarrow> ('a, 'b) cq_operator \<Rightarrow> ('a, 'b) cq_operator\<close> is
  \<open>\<lambda>r \<rho> c. if r \<ge> 0 \<and> r * cq_norm_raw \<rho> \<le> 1 then r *\<^sub>R \<rho> c else 0\<close>
proof (rename_tac r \<rho>, intro conjI allI)
  fix r :: real and \<rho> :: \<open>'a \<Rightarrow> ('b ell2, 'b ell2) trace_class\<close> and c :: 'a
  assume \<open>(\<forall>c. 0 \<le> \<rho> c) \<and> \<rho> abs_summable_on UNIV\<close>
  then have pos: \<open>0 \<le> \<rho> c\<close> and summable: \<open>\<rho> abs_summable_on UNIV\<close> for c
    by auto
  show \<open>0 \<le> (if 0 \<le> r \<and> r * cq_norm_raw \<rho> \<le> 1 then r *\<^sub>R \<rho> c else 0)\<close>
    apply (auto intro!: simp: )
    using pos scaleR_nonneg_nonneg by blast
  show \<open>(\<lambda>c. if 0 \<le> r \<and> r * cq_norm_raw \<rho> \<le> 1 then r *\<^sub>R \<rho> c else 0) abs_summable_on UNIV\<close>
    apply (cases \<open>0 \<le> r \<and> r * cq_norm_raw \<rho> \<le> 1\<close>)
    using summable by (auto intro!: summable_on_cmult_right simp: trace_tc_scaleR)
  have \<open>(\<Sum>\<^sub>\<infinity>c. trace_tc (r *\<^sub>R \<rho> c)) \<le> 1\<close> if \<open>r * cq_norm_raw \<rho> \<le> 1\<close> and \<open>r \<ge> 0\<close>
  proof -
    have \<open>(\<Sum>\<^sub>\<infinity>c. trace_tc (r *\<^sub>R \<rho> c)) = r *\<^sub>R (\<Sum>\<^sub>\<infinity>c. trace_tc (\<rho> c))\<close>
      by (simp add: trace_tc_scaleR infsum_scaleR_right)
    also have \<open>\<dots> = r *\<^sub>R of_real (cq_norm_raw \<rho>)\<close>
      apply (rule arg_cong[of _ _ \<open>scaleR _\<close>])
      unfolding cq_norm_raw_def infsum_of_real[symmetric]
      apply (rule infsum_cong)
      by (simp add: norm_tc_pos pos)
    also have \<open>\<dots> \<le> 1\<close>
      by (simp add: less_eq_complex_def that)
    finally show ?thesis
      by -
  qed
qed
instance..
end

lemma \<open>cq_map_apply cq_map_partial_trace (cq_tensor_left \<rho> \<sigma>) = norm \<sigma> *\<^sub>R \<rho>\<close>

lemma cq_map_partial_trace_tensor_id_right:
  fixes E :: \<open>('c1,'q1,'c2,'q2) cq_map\<close> and \<rho> :: \<open>('c1,'q1\<times>'r) cq_operator\<close>
  shows \<open>cq_map_apply cq_map_partial_trace (cq_map_apply (cq_map_tensor_id_right E) \<rho>)
        = cq_map_apply E (cq_map_apply cq_map_partial_trace \<rho>)\<close>
proof -
  have *: \<open>cq_map_apply cq_map_partial_trace (cq_map_apply (cq_map_tensor_id_right E) (fixed_cl_cq_operator c (tc_tensor \<rho> \<sigma>))) =
           cq_map_apply E (cq_map_apply cq_map_partial_trace (fixed_cl_cq_operator c (tc_tensor \<rho> \<sigma>)))\<close>
    if \<open>\<rho> \<ge> 0\<close> and \<open>trace_tc \<rho> \<le> 1\<close> and \<open>\<sigma> \<ge> 0\<close> and \<open>trace_tc \<sigma> \<le> 1\<close>
    for c \<rho> and \<sigma> :: \<open>('r ell2,'r ell2) trace_class\<close>
    apply (rule cq_operator_eqI)
    apply (simp add: cq_apply_map_tensor_id_right that (* Rep_cq_map_apply_partial_trace *))
        apply (simp add: that)+
by -

    by x
  then have \<open>cq_map_seq (cq_map_tensor_id_right E :: (_,_\<times>'r,_,_) cq_map) cq_map_partial_trace = cq_map_seq cq_map_partial_trace E\<close>
    apply (rule_tac cq_map_eq_from_separatingI)
     apply (rule separating_set_bounded_clinear_tc_tensor)
    by (auto simp add: cq_map_apply_seq)

lemma cq_map_apply_partial_trace_tensor_op_right:
  shows \<open>cq_map_apply cq_map_partial_trace (cq_map_apply (cq_map_tensor_op_right \<rho>) \<rho>')
    = norm \<rho> *\<^sub>R \<rho>'\<close>
  by x

instantiation cq_operator :: (type,type) zero begin
lift_definition zero_cq_operator :: \<open>('a, 'b) cq_operator\<close> is \<open>\<lambda>c. 0\<close>
  by auto
instance..
end

lemma cq_operator_scale_neg:
  fixes \<rho> :: \<open>('c,'q) cq_operator\<close>
  assumes \<open>r \<le> 0\<close>
  shows \<open>r *\<^sub>R \<rho> = 0\<close>
  apply (rule cq_operator_eqI)
  apply (transfer' fixing: r)
  using assms by (simp add: zero_cq_operator.rep_eq)

lemma set_filter_empty[simp]: \<open>Set.filter P {} = {}\<close>
  by auto

lemma cq_map_apply_E0[simp]: \<open>cq_map_apply E 0 = 0\<close>
  apply transfer' by simp

lemma set_filter_image: \<open>Set.filter P (f ` X) = f` (Set.filter (\<lambda>x. P (f x)) X)\<close>
  by auto

lemma scale0_kraus_family[simp]: \<open>0 *\<^sub>R \<EE> = 0\<close> for \<EE> :: \<open>(_,_,_) kraus_family\<close>
  apply transfer'
  by simp

lemma kf_filter_0[simp]: \<open>kf_filter P 0 = 0\<close>
  apply transfer' by simp

lemma kf_apply'_0_left[simp]: \<open>kf_apply' X 0 \<rho> = 0\<close>
  by (simp add: kf_apply'_def)

lemma kf_scale_map':
  assumes \<open>r \<ge> 0\<close>
  shows \<open>kf_apply' X (r *\<^sub>R \<EE>) \<rho> = r *\<^sub>R kf_apply' X \<EE> \<rho>\<close>
proof -
  wlog \<open>r > 0\<close>
    using negation assms
    by auto
  have [simp]: \<open>inj_on (\<lambda>x. (sqrt r *\<^sub>R fst x, snd x)) M\<close> for M :: \<open>('x::real_normed_vector \<times> 'y) set\<close>
    using \<open>r > 0\<close>
    by (auto intro!: inj_onI simp:)
  show ?thesis
    unfolding kf_apply'_def
    apply (transfer' fixing: r)
    using assms
    by (auto intro!: simp: set_filter_image case_prod_unfold infsum_reindex o_def
        sandwich_tc_scaleR_left infsum_scaleR_right)
qed

lemma norm_pos_cq: \<open>norm \<rho> \<ge> 0\<close> for \<rho> :: \<open>(_,_) cq_operator\<close>
  apply transfer
  by (metis Infinite_Sum.infsum_nonneg_complex complex_of_real_nn_iff cq_norm_raw_trace trace_tc_0 trace_tc_mono)

lemma norm_leq1_cq: \<open>norm \<rho> \<le> 1\<close> for \<rho> :: \<open>(_,_) cq_operator\<close>
  apply transfer
  by auto

(* TODO move *)
lemma cq_map_apply_scaleR:
  assumes \<open>r * norm \<rho> \<le> 1\<close>
  shows \<open>cq_map_apply E (r *\<^sub>R \<rho>) = r *\<^sub>R cq_map_apply E \<rho>\<close>
proof -
  wlog r_pos: \<open>r \<ge> 0\<close>
    apply (subst cq_operator_scale_neg)
    using negation apply simp
    apply (subst cq_operator_scale_neg)
    using negation by simp_all

  have leq1': \<open>norm (r *\<^sub>R \<rho>) \<le> 1\<close>
    by (rule norm_leq1_cq)
  have leq1'': \<open>norm (r *\<^sub>R cq_map_apply E \<rho>) \<le> 1\<close>
    by (rule norm_leq1_cq)

  show ?thesis
    using assms leq1' leq1''
    apply (transfer' fixing: r)
    apply (auto intro!: ext simp: r_pos)
    by -
qed

(* TODO move *)
lemma cq_map_local_q_bot:
  fixes E :: \<open>('c, 'q, 'd, 'q) cq_map\<close>
    and \<rho> :: \<open>('q ell2,'q ell2) trace_class\<close> and \<rho>' :: \<open>('c, 'q) cq_operator\<close>
  assumes \<open>\<rho> \<ge> 0\<close> and \<open>norm \<rho> \<le> 1\<close>
  shows \<open>cq_map_apply (cq_map_local_q \<bottom> \<rho> E) \<rho>' = norm \<rho> *\<^sub>R cq_map_apply E \<rho>'\<close>
proof -
  have \<open>cq_map_apply (cq_map_local_q \<bottom> \<rho> E) \<rho>' = cq_map_apply (cq_map_seq (cq_map_tensor_op_right \<rho>) (cq_map_seq (cq_map_tensor_id_right E) cq_map_partial_trace)) \<rho>'\<close>
    by (simp add: cq_map_apply_seq cq_map_local_q_def cq_map_auxiliary_state_def)
  also have \<open>\<dots> = cq_map_apply cq_map_partial_trace (cq_map_apply (cq_map_tensor_id_right E) (cq_map_apply (cq_map_tensor_op_right \<rho>) \<rho>'))\<close>
    by (simp add: cq_map_apply_seq)
  also have \<open>\<dots> = cq_map_apply E (cq_map_apply cq_map_partial_trace (cq_map_apply (cq_map_tensor_op_right \<rho>) \<rho>'))\<close>
    by (simp add: cq_map_partial_trace_tensor_id_right)
  also have \<open>\<dots> = cq_map_apply E (norm \<rho> *\<^sub>R \<rho>')\<close>
    by (simp add: cq_map_apply_partial_trace_tensor_op_right)
  also have \<open>\<dots> = norm \<rho> *\<^sub>R cq_map_apply E \<rho>'\<close>
    using assms
    by (auto simp: mult_le_one norm_leq1_cq norm_pos_cq cq_map_apply_scaleR)
  finally show ?thesis
    by -
qed

lemma scale_1_cq_operator[simp]: 
  fixes \<rho> :: \<open>('c,'q) cq_operator\<close>
  shows \<open>1 *\<^sub>R \<rho> = \<rho>\<close>
  apply transfer
  by simp

lemma cq_map_local_q_bot'[simp]:
  fixes E :: \<open>('c, 'q, 'd, 'q) cq_map\<close>
    and \<rho> :: \<open>('q ell2,'q ell2) trace_class\<close>
  assumes \<open>\<rho> \<ge> 0\<close> and \<open>norm \<rho> = 1\<close>
  shows \<open>cq_map_local_q \<bottom> \<rho> E = E\<close>
  apply (auto intro!: cq_map_eqI simp: )
  apply (subst cq_map_local_q_bot)
  using assms
  by auto

lemma denotation_localvars:
  \<open>denotation (localvars C Q p) = cq_map_local_c (CREGISTER_of C) undefined (cq_map_local_q (QREGISTER_of Q) (tc_butterfly |undefined\<rangle> |undefined\<rangle>) (denotation (block p)))\<close>
  by (simp add: localvars_def denotation_localvars1)

lemma localvars1_empty: "denotation (localvars1 empty_cregister empty_qregister P) = denotation P"
  apply (simp add: denotation_localvars1)
  apply (subst cq_map_local_q_bot')
  by (simp_all add: norm_tc_butterfly)

lemma localvars_empty: "denotation (localvars empty_cregister empty_qregister P) = denotation (block P)"
  by (simp add: localvars1_empty localvars_def)


lift_definition kf_in_qref_strict :: \<open>('qu ell2,'qu ell2,'cl) kraus_family \<Rightarrow> 'qu QREGISTER \<Rightarrow> bool\<close> is
  \<open>\<lambda>\<EE> Q. \<forall>(E,x)\<in>\<EE>. E \<in> Rep_QREGISTER Q\<close>.
definition kf_in_qref :: \<open>('qu ell2,'qu ell2,'cl) kraus_family \<Rightarrow> 'qu QREGISTER \<Rightarrow> bool\<close> where
  \<open>kf_in_qref \<EE> Q \<longleftrightarrow> (\<exists>\<FF>. kraus_equivalent' \<EE> \<FF> \<and> kf_in_qref_strict \<FF> Q)\<close>

lift_definition qc_map_in_qref :: \<open>('cl1,'qu,'cl2,'qu) cq_map \<Rightarrow> 'qu QREGISTER \<Rightarrow> bool\<close> is
  \<open>\<lambda>\<EE> Q. \<forall>x. kf_in_qref (\<EE> x) Q\<close>
  apply (auto intro!: simp: cq_map_rel_def kf_in_qref_def)
  using kraus_equivalent'_trans kraus_equivalent'_sym
  by meson

lemma qc_map_in_qref_seq:
  assumes \<open>qc_map_in_qref E Q\<close>
  assumes \<open>qc_map_in_qref F Q\<close>
  shows \<open>qc_map_in_qref (cq_map_seq E F) Q\<close>
  sorry

lemma qc_map_in_qref_if:
  assumes \<open>qc_map_in_qref E Q\<close>
  assumes \<open>qc_map_in_qref F Q\<close>
  shows \<open>qc_map_in_qref (cq_map_if c E F) Q\<close>
  sorry

lemma qc_map_in_qref_while:
  assumes \<open>qc_map_in_qref E Q\<close>
  shows \<open>qc_map_in_qref (cq_map_while c E) Q\<close>
  sorry

lemma qc_map_in_qref_local_q:
  assumes \<open>qc_map_in_qref E (Q \<squnion> R)\<close>
  shows \<open>qc_map_in_qref (cq_map_local_q Q \<rho> E) R\<close>
  sorry

lemma qc_map_in_qref_local_c:
  assumes \<open>qc_map_in_qref E Q\<close>
  shows \<open>qc_map_in_qref (cq_map_local_c X m E) R\<close>
  sorry

lemma kf_in_qref_map_outcome[iff]:
  assumes \<open>kf_in_qref E Q\<close>
  shows \<open>kf_in_qref (kf_map_outcome f E) Q\<close>
  sorry

lemma kf_in_qref_from_strictI:
  assumes \<open>kf_in_qref_strict E Q\<close>
  shows \<open>kf_in_qref E Q\<close>
  using assms kf_in_qref_def by blast


lemma kf_in_qref_strict_of_op[intro]:
  assumes \<open>A \<in> Rep_QREGISTER Q\<close>
  shows \<open>kf_in_qref_strict (kf_of_op A) Q\<close>
  using assms
  by (simp add: kf_in_qref_strict.rep_eq kf_of_op.rep_eq)

lemma kf_in_qref_of_op[intro]:
  assumes \<open>A \<in> Rep_QREGISTER Q\<close>
  shows \<open>kf_in_qref (kf_of_op A) Q\<close>
  by (simp add: assms kf_in_qref_from_strictI kf_in_qref_strict_of_op)

lemma kf_in_qref_strict_0[iff]: \<open>kf_in_qref_strict 0 Q\<close>
  by (simp add: kf_in_qref_strict.rep_eq zero_kraus_family.rep_eq)

lemma kf_in_qref_0[iff]: \<open>kf_in_qref 0 Q\<close>
  by (auto intro!: kf_in_qref_from_strictI)

lemma qc_map_in_qref_quantum_op:
  assumes \<open>\<And>x. kf_in_qref (E x) Q\<close>
  shows \<open>qc_map_in_qref (cq_map_quantum_op E) Q\<close>
  using assms apply (transfer fixing: E Q)
  by (auto intro!: kf_in_qref_map_outcome)

(* definition fvq_of_cq_map :: \<open>(cl, qu, cl, qu) cq_map \<Rightarrow> QVARIABLE\<close> where
  \<open>fvq_of_cq_map \<EE> = Inf {Q. qc_map_in_qref \<EE> Q}\<close> *)

definition program_in_qref :: \<open>program \<Rightarrow> QVARIABLE \<Rightarrow> bool\<close> where
  \<open>program_in_qref p = qc_map_in_qref (denotation p)\<close>

(* definition fvq_program :: \<open>program \<Rightarrow> QVARIABLE\<close> where
  \<open>fvq_program p = fvq_of_cq_map (denotation p)\<close> *)

inductive raw_program_in_qref :: \<open>raw_program \<Rightarrow> QVARIABLE \<Rightarrow> bool\<close> where
  raw_program_in_qref_no_oracles: \<open>no_oracles p \<Longrightarrow> qc_map_in_qref (denotation_raw p) Q \<Longrightarrow> raw_program_in_qref p Q\<close>
| raw_program_in_qref_Seq: \<open>raw_program_in_qref p Q \<Longrightarrow> raw_program_in_qref q Q \<Longrightarrow> raw_program_in_qref (Seq p q) Q\<close>
| raw_program_in_qref_IfThenElse: \<open>raw_program_in_qref p Q \<Longrightarrow> raw_program_in_qref q Q \<Longrightarrow> raw_program_in_qref (IfThenElse c p q) Q\<close>
| raw_program_in_qref_While: \<open>raw_program_in_qref p Q \<Longrightarrow> raw_program_in_qref (While c p) Q\<close>
| raw_program_in_qref_LocalQ: \<open>raw_program_in_qref p (Q \<squnion> R) \<Longrightarrow> raw_program_in_qref (LocalQ Q \<rho> p) R\<close>
| raw_program_in_qref_LocalC: \<open>raw_program_in_qref p Q \<Longrightarrow> raw_program_in_qref (LocalC X m p) Q\<close>
| raw_program_in_qref_InstantiateOracles: \<open>raw_program_in_qref p Q \<Longrightarrow> (\<And>q. q \<in> set qs \<Longrightarrow> raw_program_in_qref q Q) \<Longrightarrow> raw_program_in_qref (InstantiateOracles p qs) Q\<close>
| raw_program_in_qref_OracleCall: \<open>raw_program_in_qref (OracleCall i) Q\<close>

lemma kf_in_qref_strict_mono:
  assumes \<open>Q \<le> R\<close>
  assumes \<open>kf_in_qref_strict p Q\<close>
  shows \<open>kf_in_qref_strict p R\<close>
  using assms
  apply transfer
  using less_eq_QREGISTER.rep_eq by fastforce

lemma kf_in_qref_mono:
  assumes \<open>Q \<le> R\<close>
  assumes \<open>kf_in_qref p Q\<close>
  shows \<open>kf_in_qref p R\<close>
  using assms
  by (meson kf_in_qref_def kf_in_qref_strict_mono)

lemma qc_map_in_qref_mono:
  assumes \<open>Q \<le> R\<close>
  assumes \<open>qc_map_in_qref p Q\<close>
  shows \<open>qc_map_in_qref p R\<close>
  using assms
  apply transfer
  by (simp add: kf_in_qref_mono)


lemma raw_program_in_qref_mono:
  assumes \<open>Q \<le> R\<close>
  assumes \<open>raw_program_in_qref p Q\<close>
  shows \<open>raw_program_in_qref p R\<close>
  using assms(2,1)
proof (induction arbitrary: R)
  case (raw_program_in_qref_no_oracles p Q)
  then show ?case 
    using qc_map_in_qref_mono raw_program_in_qref.intros by blast
next
  case (raw_program_in_qref_Seq p Q q)
  then show ?case
    by (auto intro: raw_program_in_qref.intros simp: )
next
  case (raw_program_in_qref_IfThenElse p Q q c)
  then show ?case 
    by (auto intro: raw_program_in_qref.intros simp: )
next
  case (raw_program_in_qref_While p Q c)
  then show ?case 
    by (auto intro: raw_program_in_qref.intros simp: )
next
  case (raw_program_in_qref_LocalQ p Q R' \<rho>)
  then have \<open>raw_program_in_qref p (Q \<squnion> R')\<close>
    by -
  moreover have \<open>Q \<squnion> R' \<le> Q \<squnion> R\<close>
    using raw_program_in_qref_LocalQ.prems sup.mono by auto
  ultimately have \<open>raw_program_in_qref p (Q \<squnion> R)\<close>
    by (rule_tac raw_program_in_qref_LocalQ.IH)
  then show ?case 
    by (rule Programs.raw_program_in_qref_LocalQ)
next
  case (raw_program_in_qref_LocalC p X c m)
  then show ?case
    by (auto intro: raw_program_in_qref.intros simp: )
next
  case (raw_program_in_qref_InstantiateOracles p Q qs)
  then show ?case 
    by (auto intro: raw_program_in_qref.intros simp: )
next
  case (raw_program_in_qref_OracleCall i Q R)
  show ?case
    by (auto intro: raw_program_in_qref.intros)
qed


lemma raw_program_in_qref_subst:
  assumes \<open>raw_program_in_qref p Q\<close>
  assumes \<open>\<And>q. q \<in> set qs \<Longrightarrow> raw_program_in_qref q Q\<close>
  shows \<open>raw_program_in_qref (substitute_oracles_raw qs p) Q\<close>
  using assms
proof (induction arbitrary: qs)
  case (raw_program_in_qref_no_oracles p Q)
  then show ?case 
    by (auto intro!: raw_program_in_qref.intros simp: substitute_oracles_raw_no_oracles)
next
  case (raw_program_in_qref_Seq p Q q)
  then show ?case
    using raw_program_in_qref.intros by force
next
  case (raw_program_in_qref_IfThenElse p Q q c)
  then show ?case 
    using raw_program_in_qref.intros by force
next
  case (raw_program_in_qref_While p Q c)
  then show ?case 
    using raw_program_in_qref.intros by force
next
  case (raw_program_in_qref_LocalQ p Q R \<rho>)
  have \<open>raw_program_in_qref (substitute_oracles_raw qs p) (Q \<squnion> R)\<close>
    apply (rule raw_program_in_qref_LocalQ.IH)
    apply (rule raw_program_in_qref_mono[rotated])
     apply (rule raw_program_in_qref_LocalQ.prems)
    by auto
  then show ?case
    by (auto intro!: raw_program_in_qref.intros)
next
  case (raw_program_in_qref_LocalC p X c m)
  then show ?case
    by (auto intro: raw_program_in_qref.intros)
next
  case (raw_program_in_qref_InstantiateOracles p Q qs qs')
  have \<open>raw_program_in_qref (substitute_oracles_raw qs' q) Q\<close> if \<open>q \<in> set qs\<close> for q
    using local.raw_program_in_qref_InstantiateOracles(4) local.raw_program_in_qref_InstantiateOracles(5) that by blast
  then have \<open>raw_program_in_qref q Q\<close> if \<open>q \<in> set (map (substitute_oracles_raw qs') qs @ qs')\<close> for q
    using that 
    by (auto intro: local.raw_program_in_qref_InstantiateOracles simp: )
  then have \<open>raw_program_in_qref (substitute_oracles_raw (map (substitute_oracles_raw qs') qs @ qs') p) Q\<close>
    by (rule raw_program_in_qref_InstantiateOracles.IH)
  then show ?case 
    by (auto intro: raw_program_in_qref.intros)
next
  case (raw_program_in_qref_OracleCall i Q)
  then show ?case
    by (auto intro: raw_program_in_qref.intros)
qed

lemma raw_program_in_qref_implies_qc_map_in_qref:
  assumes \<open>raw_program_in_qref p Q\<close>
  assumes \<open>no_oracles p\<close>
  shows \<open>qc_map_in_qref (denotation_raw p) Q\<close>
  using assms
proof (induction)
  case (raw_program_in_qref_no_oracles p Q)
  then show ?case
    by simp
next
  case (raw_program_in_qref_Seq p Q q)
  then show ?case
    using no_oracles.cases qc_map_in_qref_seq by fastforce
next
  case (raw_program_in_qref_IfThenElse p Q q c)
  then show ?case
    using no_oracles.cases qc_map_in_qref_if by fastforce
next
  case (raw_program_in_qref_While p Q c)
  then show ?case
    using no_oracles.cases qc_map_in_qref_while by fastforce
next
  case (raw_program_in_qref_LocalQ p Q R \<rho>)
  then show ?case
    using no_oracles.cases qc_map_in_qref_local_q by fastforce
next
  case (raw_program_in_qref_LocalC p Q X m)
  then show ?case
  using no_oracles.cases qc_map_in_qref_local_c by fastforce
next
  case (raw_program_in_qref_InstantiateOracles p Q qs)
  then show ?case
    using no_oracles.cases by fastforce
next
  case (raw_program_in_qref_OracleCall i Q)
  then show ?case
    using no_oracles.cases by fastforce
qed

(* function fvq_raw_program :: \<open>raw_program \<Rightarrow> QVARIABLE\<close> where
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
termination by lexicographic_order *)

lift_definition oracle_program_in_qref :: \<open>oracle_program \<Rightarrow> QVARIABLE \<Rightarrow> bool\<close> is raw_program_in_qref.

lemma program_in_qref_raw_program_in_qref: \<open>program_in_qref p Q \<longleftrightarrow> raw_program_in_qref (Rep_program p) Q\<close>
proof (rule iffI)
  define p' where \<open>p' = Rep_program p\<close>
  assume \<open>program_in_qref p Q\<close>
  then have \<open>qc_map_in_qref (denotation_raw p') Q\<close>
    by (simp add: program_in_qref_def denotation.rep_eq p'_def)
  moreover have \<open>no_oracles p'\<close>
    using Rep_program p'_def valid_program_def by force
  ultimately show \<open>raw_program_in_qref p' Q\<close>
    using raw_program_in_qref.intros(1) by blast
next
  define p' where \<open>p' = Rep_program p\<close>
  assume \<open>raw_program_in_qref p' Q\<close>
  then have \<open>qc_map_in_qref (denotation_raw p') Q\<close>
    using Rep_program p'_def raw_program_in_qref_implies_qc_map_in_qref valid_program_def by force
  then show \<open>program_in_qref p Q\<close>
    by (simp add: denotation.rep_eq p'_def program_in_qref_def)
qed

axiomatization program_in_cref :: "program \<Rightarrow> CVARIABLE \<Rightarrow> bool"
axiomatization expression_in_cref :: "'a expression \<Rightarrow> CVARIABLE \<Rightarrow> bool"
axiomatization program_write_in_cref :: "program \<Rightarrow> CVARIABLE \<Rightarrow> bool"
(* consts fvcw_program :: "program \<Rightarrow> CVARIABLE" *)
(* consts fvc_oracle_program :: "oracle_program \<Rightarrow> CVARIABLE" *)
(* consts fvcw_oracle_program :: "oracle_program \<Rightarrow> CVARIABLE" *)

lemma kf_in_qref_strict_map:
  assumes \<open>kf_in_qref_strict \<EE> Q\<close>
  shows \<open>kf_in_qref_strict (kf_map_outcome f \<EE>) Q\<close>
proof -
  have \<open>E \<in> Rep_QREGISTER Q\<close> if \<open>(E,x) \<in> Rep_kraus_family (kf_map_outcome f \<EE>)\<close> for E x
  proof -
    from that
    have \<open>(norm E)\<^sup>2 = kf_op_weight (kf_filter (\<lambda>y. f y = x) \<EE>) E\<close> and \<open>E \<noteq> 0\<close>
      by (simp_all add: kf_map_outcome.rep_eq)
    then have \<open>kf_op_weight (kf_filter (\<lambda>y. f y = x) \<EE>) E \<noteq> 0\<close>
      by auto
    then have \<open>(\<Sum>\<^sub>\<infinity>(F,_)\<in>kf_related_ops (kf_filter (\<lambda>y. f y = x) \<EE>) E. norm (F* o\<^sub>C\<^sub>L F)) \<noteq> 0\<close>
      by (simp add: kf_op_weight_def)
    then have \<open>kf_related_ops (kf_filter (\<lambda>y. f y = x) \<EE>) E \<noteq> {}\<close>
      by force
    then obtain F y r where \<open>(F,y) \<in> Rep_kraus_family (kf_filter (\<lambda>y. f y = x) \<EE>)\<close> and \<open>E = r *\<^sub>R F\<close>
      by (auto simp add: kf_related_ops_def)
    then have \<open>(F,y) \<in> Rep_kraus_family \<EE>\<close>
      by (simp add: kf_filter.rep_eq)
    with assms have \<open>F \<in> Rep_QREGISTER Q\<close>
      by (metis (no_types, lifting) case_prodE fst_conv kf_in_qref_strict.rep_eq)
    with \<open>E = r *\<^sub>R F\<close> show \<open>E \<in> Rep_QREGISTER Q\<close>
      using Rep_QREGISTER[of Q]
      by (auto intro!: complex_vector.subspace_scale
          simp: scaleR_scaleC valid_qregister_range_def von_neumann_algebra_def_sot)
  qed
  then show ?thesis
    by (force simp: kf_in_qref_strict.rep_eq)
qed


lemma kf_in_qref_map:
  assumes \<open>kf_in_qref \<EE> Q\<close>
  shows \<open>kf_in_qref (kf_map_outcome f \<EE>) Q\<close>
proof -
  from assms
  obtain \<FF> where eq: \<open>kraus_equivalent' \<EE> \<FF>\<close> and qref: \<open>kf_in_qref_strict \<FF> Q\<close>
    by (auto simp: kf_in_qref_def)
  define \<FF>' where \<open>\<FF>' = kf_map_outcome f \<FF>\<close>
  have eq': \<open>kraus_equivalent' (kf_map_outcome f \<EE>) \<FF>'\<close>
    by (simp add: \<FF>'_def eq kraus_equivalent'_map_cong)
  have qref': \<open>kf_in_qref_strict \<FF>' Q\<close>
    using qref[THEN kf_in_qref_strict_map]
    by (auto simp: \<FF>'_def )
  from eq' qref' show \<open>kf_in_qref (kf_map_outcome f \<EE>) Q\<close>
    by (auto intro!: exI[of _ \<FF>'] simp add: kf_in_qref_def)
qed

lemma kf_in_qref_strict_id[iff]: \<open>kf_in_qref_strict kf_id Q\<close>
  using Rep_QREGISTER valid_qregister_range_def_sot
  by (auto intro!: simp: kf_id_def  kf_of_op.rep_eq kf_in_qref_strict_def
      simp del: kf_of_op_id)

lemma kf_in_qref_id[iff]: \<open>kf_in_qref kf_id Q\<close>
  by (auto intro!: exI[of _ kf_id] simp: kf_in_qref_def)

lemma qc_map_in_qref_id[iff]: \<open>qc_map_in_qref cq_map_id Q\<close>
  apply (transfer fixing: Q)
  by (auto intro!: kf_in_qref_map)

lemma program_in_qref_mono:
  assumes \<open>Q \<le> R\<close>
  assumes \<open>program_in_qref p Q\<close>
  shows \<open>program_in_qref p R\<close>
  using assms(1) assms(2) program_in_qref_def qc_map_in_qref_mono by auto

lemma program_in_qref_seq:
  assumes \<open>program_in_qref a Q\<close>
  assumes \<open>program_in_qref b Q\<close>
  shows \<open>program_in_qref (seq a b) Q\<close>
  using assms(1) assms(2) program_in_qref_raw_program_in_qref raw_program_in_qref.intros(2) seq.rep_eq by force

(* lemma fvq_program_seq: \<open>fvq_program (seq a b) = fvq_program a \<squnion> fvq_program b\<close>
  by xxx *)
lemma program_in_qref_skip[iff]: \<open>program_in_qref skip Q\<close>
  by (simp add: denotation_skip program_in_qref_def)

lemma program_in_qref_block:
  assumes \<open>\<And>p. p \<in> set b \<Longrightarrow> program_in_qref p Q\<close>
  shows \<open>program_in_qref (block b) Q\<close>
  using assms 
  apply (induction b)
  by (auto intro!: qc_map_in_qref_seq simp add: denotation_block program_in_qref_def)

lemma program_in_cref_block:
  assumes \<open>\<And>p. p \<in> set b \<Longrightarrow> program_in_cref p Q\<close>
  shows \<open>program_in_cref (block b) Q\<close>
  using assms 
  apply (induction b)
  sorry

lemma program_write_in_cref_block:
  assumes \<open>\<And>p. p \<in> set b \<Longrightarrow> program_write_in_cref p Q\<close>
  shows \<open>program_write_in_cref (block b) Q\<close>
  using assms 
  apply (induction b)
  sorry

(* (* TODO Truth is \<le> *)
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
qed *)


lemma kf_in_qref_strict_sample[iff]: \<open>kf_in_qref_strict (kraus_map_sample f) Q\<close>
  using Rep_QREGISTER[of Q]
  by (auto intro!:complex_vector.subspace_scale
      simp: valid_qregister_range_def_sot scaleR_scaleC kraus_map_sample.rep_eq kf_in_qref_strict_def)

lemma kf_in_qref_sample[iff]: \<open>kf_in_qref (kraus_map_sample f) Q\<close>
  by (auto intro!: exI[of _ \<open>kraus_map_sample f\<close>] simp: kf_in_qref_def)

lemma qc_map_in_qref_sample[iff]: \<open>qc_map_in_qref (cq_map_sample f) Q\<close>
  apply (transfer fixing: Q)
  by (auto intro!: kf_in_qref_map)

lemma program_in_qref_sample:
  shows \<open>program_in_qref (sample X f) Q\<close>
  apply (simp add: program_in_qref_raw_program_in_qref)
  by (metis Rep_program denotation.rep_eq denotation_sample mem_Collect_eq qc_map_in_qref_sample raw_program_in_qref_no_oracles valid_program_def)

lemma program_in_cref_sample:
  assumes \<open>CREGISTER_of X \<le> Y\<close>
  assumes \<open>expression_in_cref f Y\<close>
  shows \<open>program_in_cref (sample X f) Q\<close>
  sorry

lemma program_write_in_cref_sample:
  assumes \<open>CREGISTER_of X \<le> Y\<close>
  shows \<open>program_write_in_cref (sample X f) Q\<close>
  sorry

lemma program_in_qref_assign:
  shows \<open>program_in_qref (assign X f) Q\<close>
  by (simp add: denotation_assign_sample program_in_qref_def)

lemma program_in_cref_assign:
  assumes \<open>CREGISTER_of X \<le> Y\<close>
  assumes \<open>expression_in_cref f Y\<close>
  shows \<open>program_in_cref (assign X f) Y\<close>
  sorry

lemma program_write_in_cref_assign:
  assumes \<open>CREGISTER_of X \<le> Y\<close>
  shows \<open>program_write_in_cref (assign X f) Y\<close>
  sorry

(* lemma fvq_of_cq_map_sample[simp]: \<open>fvq_of_cq_map (cq_map_sample f) = \<bottom>\<close>
  by (simp add: fvq_of_cq_map_def) *)

(* lemma fvq_program_sample: "fvq_program (sample xs e2) = QREGISTER_unit"
  by (simp add: fvq_program_def denotation_sample) *)
(* lemma fvq_program_assign: "fvq_program (assign x e) = QREGISTER_unit"
  by (simp add: fvq_program_def denotation_assign_sample) *)

lemma kf_in_qref_top[iff]: \<open>kf_in_qref E \<top>\<close>
  by (auto intro!: exI[of _ E] simp add: kf_in_qref_def kf_in_qref_strict_def top_QREGISTER.rep_eq)

lemma program_in_qref_ifthenelse1:
  assumes \<open>program_in_qref p Q\<close>
  assumes \<open>program_in_qref q Q\<close>
  shows \<open>program_in_qref (ifthenelse1 c p q) Q\<close>
  by (metis assms(1) assms(2) denotation_ifthenelse1 program_in_qref_def qc_map_in_qref_if)

lemma program_in_cref_ifthenelse1:
  assumes \<open>program_in_cref p X\<close>
  assumes \<open>program_in_cref q X\<close>
  assumes \<open>expression_in_cref c X\<close>
  shows \<open>program_in_cref (ifthenelse1 c p q) X\<close>
  sorry

lemma program_write_in_cref_ifthenelse1:
  assumes \<open>program_write_in_cref p X\<close>
  assumes \<open>program_write_in_cref q X\<close>
  shows \<open>program_write_in_cref (ifthenelse1 c p q) X\<close>
  sorry

lemma program_in_qref_ifthenelse:
  assumes \<open>program_in_qref (block p) Q\<close>
  assumes \<open>program_in_qref (block q) Q\<close>
  shows \<open>program_in_qref (ifthenelse c p q) Q\<close>
  by (metis assms(1) assms(2) denotation_ifthenelse program_in_qref_def qc_map_in_qref_if)

lemma program_in_cref_ifthenelse:
  assumes \<open>program_in_cref (block p) Q\<close>
  assumes \<open>program_in_cref (block q) Q\<close>
  assumes \<open>expression_in_cref c Q\<close>
  shows \<open>program_in_cref (ifthenelse c p q) Q\<close>
  sorry

lemma program_write_in_cref_ifthenelse:
  assumes \<open>program_write_in_cref (block p) Q\<close>
  assumes \<open>program_write_in_cref (block q) Q\<close>
  shows \<open>program_write_in_cref (ifthenelse c p q) Q\<close>
  sorry

(* lemma fvq_of_cq_map_if: \<open>fvq_of_cq_map (cq_map_if c E F) \<le> fvq_of_cq_map E \<squnion> fvq_of_cq_map F\<close> *)


(* lemma fvq_program_ifthenelse1: "fvq_program (ifthenelse1 c p1 p2) \<le>
  QREGISTER_pair (fvq_program p1) (fvq_program p2)"
  by (auto intro!: fvq_of_cq_map_if simp: fvq_program_def denotation_ifthenelse1)
lemma fvq_program_ifthenelse: "fvq_program (ifthenelse c p1 p2) \<le>
  QREGISTER_pair (fvq_program (block p1)) (fvq_program (block p2))"
  using fvq_program_ifthenelse1 ifthenelse_def by presburger *)

lemma program_in_qref_while1:
  assumes \<open>program_in_qref p Q\<close>
  shows \<open>program_in_qref (while1 c p) Q\<close>
  using assms program_in_qref_raw_program_in_qref raw_program_in_qref.intros(4) while1.rep_eq by auto

lemma program_in_cref_while1:
  assumes \<open>program_in_cref p Q\<close>
  assumes \<open>expression_in_cref c Q\<close>
  shows \<open>program_in_cref (while1 c p) Q\<close>
  sorry

lemma program_write_in_cref_while1:
  assumes \<open>program_write_in_cref p Q\<close>
  shows \<open>program_write_in_cref (while1 c p) Q\<close>
  sorry

lemma program_in_qref_while:
  assumes \<open>program_in_qref (block p) Q\<close>
  shows \<open>program_in_qref (while c p) Q\<close>
  by (simp add: assms program_in_qref_while1 while_def)

lemma program_in_cref_while:
  assumes \<open>program_in_cref (block p) Q\<close>
  assumes \<open>expression_in_cref c Q\<close>
  shows \<open>program_in_cref (while c p) Q\<close>
  by (simp add: assms program_in_cref_while1 while_def)


lemma program_write_in_cref_while:
  assumes \<open>program_write_in_cref (block p) Q\<close>
  shows \<open>program_write_in_cref (while c p) Q\<close>
  by (simp add: assms program_write_in_cref_while1 while_def)


(* (* TODO Truth is \<le> *)
lemma fvq_program_while: "fvq_program (while c b) = (fvq_program (block b))"
  by xxx *)

lemma program_in_qref_qapply[iff]: \<open>program_in_qref (qapply Q e) (QREGISTER_of Q)\<close>
  by (auto intro!: qc_map_in_qref_quantum_op kf_in_qref_of_op
      simp add: program_in_qref_def denotation.rep_eq qapply.rep_eq QREGISTER_of.rep_eq)

lemma program_in_cref_qapply[intro]: 
  assumes \<open>expression_in_cref e X\<close>
  shows \<open>program_in_cref (qapply Q e) X\<close>
  sorry

lemma program_write_in_cref_qapply[iff]: \<open>program_write_in_cref (qapply Q e) X\<close>
  sorry

lemma program_in_qref_qinit[iff]: \<open>program_in_qref (qinit Q e) (QREGISTER_of Q)\<close>
  sorry

lemma program_in_cref_qinit[intro]: 
  assumes \<open>expression_in_cref e X\<close>
  shows \<open>program_in_cref (qinit Q e) X\<close>
  sorry

lemma program_write_in_cref_qinit[iff]: \<open>program_write_in_cref (qinit Q e) X\<close>
  sorry


lemma program_in_qref_measurement: \<open>program_in_qref (measurement X Q e) (QREGISTER_of Q)\<close>
  sorry

lemma program_in_cref_measurement:
  assumes \<open>CREGISTER_of X \<le> Y\<close>
  assumes \<open>expression_in_cref e Y\<close>
  shows \<open>program_in_cref (measurement X Q e) Y\<close>
  sorry



lemma program_write_in_cref_measurement:
  assumes \<open>CREGISTER_of X \<le> Y\<close>
  shows \<open>program_write_in_cref (measurement X Q e) Y\<close>
  sorry



(* (* TODO Truth is \<le>. Or is = correct? *)
lemma fvq_program_qinit: "fvq_program (qinit Q e3) = QREGISTER_of Q"
  by xxx *)

(* (* TODO Truth is \<le> *)
lemma fvq_program_qapply: "fvq_program (qapply Q e4) = QREGISTER_of Q"
  by xxx
(* TODO Truth is \<le> *)
lemma fvq_program_measurement: "fvq_program (measurement x R e5) = QREGISTER_of R"
  by xxx *)

(* TODO Truth is \<le> *)
(* lemma fvc_program_sequence: "fvc_program (block b) = fold (\<lambda>p v. CREGISTER_pair (fvc_program p) v) b CREGISTER_unit"
  by xxx *)
(* TODO Truth is \<le> *)
(* lemma fvc_program_assign: "fvc_program (assign x e) = CREGISTER_pair (CREGISTER_of x) (fv_expression e)"
  by xxx *)
(* TODO Truth is \<le> *)
(* lemma fvc_program_sample: "fvc_program (sample x e) = CREGISTER_pair (CREGISTER_of x) (fv_expression e)"
  by xxx *)
(* TODO Truth is \<le> *)
(* lemma fvc_program_ifthenelse: "fvc_program (ifthenelse c p1 p2) =
  CREGISTER_pair (fv_expression c) (CREGISTER_pair (fvc_program (block p1)) (fvc_program (block p2)))"
  by xxx *)
(* TODO Truth is \<le> *)
(* lemma fvc_program_while: "fvc_program (while c b) = 
  CREGISTER_pair (fv_expression c) (fvc_program (block b))"
  by xxx *)
(* TODO Truth is \<le> *)
(* lemma fvc_program_qinit: "fvc_program (qinit Q e3) = fv_expression e3"
  by xxx
(* TODO Truth is \<le> *)
lemma fvc_program_qapply: "fvc_program (qapply Q e4) = fv_expression e4"
  by xxx
(* TODO Truth is \<le> *)
lemma fvc_program_measurement: "fvc_program (measurement x R e) = CREGISTER_pair (CREGISTER_of x) (fv_expression e)"
  by xxx *)

(* (* TODO Truth is \<le> *)
lemma fvcw_program_sequence: "fvcw_program (block b) = fold (\<lambda>p v. CREGISTER_pair (fvcw_program p) v) b CREGISTER_unit"
  by xxx
(* TODO Truth is \<le> *)
lemma fvcw_program_assign: "fvcw_program (assign x e) = CREGISTER_of x"
  by xxx
(* TODO Truth is \<le> *)
lemma fvcw_program_sample: "fvcw_program (sample x e2) = CREGISTER_of x"
  by xxx
(* TODO Truth is \<le> *)
lemma fvcw_program_ifthenelse: "fvcw_program (ifthenelse c p1 p2) =
  CREGISTER_pair (fvc_program (block p1)) (fvc_program (block p2))"
  by xxxx
(* TODO Truth is \<le> *)
lemma fvcw_program_while: "fvcw_program (while c b) = fvcw_program (block b)"
  by xxxx
lemma fvcw_program_qinit: "fvcw_program (qinit Q e3) = CREGISTER_unit"
  by xxx
lemma fvcw_program_qapply: "fvcw_program (qapply Q e4) = CREGISTER_unit"
  by xxx
(* TODO Truth is \<le> *)
lemma fvcw_program_measurement: "fvcw_program (measurement x R e5) = CREGISTER_of x"
  by xxx *)

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
