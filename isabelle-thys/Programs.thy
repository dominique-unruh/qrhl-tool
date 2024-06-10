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

fun no_oracles :: \<open>raw_program \<Rightarrow> bool\<close> where
\<open>no_oracles (Seq c d) \<longleftrightarrow> no_oracles c \<and> no_oracles d\<close>
| \<open>no_oracles (IfThenElse e c d) \<longleftrightarrow> no_oracles c \<and> no_oracles d\<close>
| \<open>no_oracles (While e c) \<longleftrightarrow> no_oracles c\<close>
| \<open>no_oracles (LocalQ _ _ c) \<longleftrightarrow> no_oracles c\<close>
| \<open>no_oracles (LocalC _ _ c) \<longleftrightarrow> no_oracles c\<close>
| \<open>no_oracles (OracleCall _) \<longleftrightarrow> False\<close>
| \<open>no_oracles (InstantiateOracles _ _) \<longleftrightarrow> False\<close>
| \<open>no_oracles p \<longleftrightarrow> True\<close>

fun substitute_oracles_raw :: \<open>raw_program list \<Rightarrow> raw_program \<Rightarrow> raw_program\<close> where
\<open>substitute_oracles_raw os (Seq c d) = Seq (substitute_oracles_raw os c) (substitute_oracles_raw os d)\<close>
| \<open>substitute_oracles_raw os (IfThenElse e c d) = IfThenElse e (substitute_oracles_raw os c) (substitute_oracles_raw os d)\<close>
| \<open>substitute_oracles_raw os (While e c) = While e (substitute_oracles_raw os c)\<close>
| \<open>substitute_oracles_raw os (LocalQ Q \<rho> c) = LocalQ Q \<rho> (substitute_oracles_raw os c)\<close>
| \<open>substitute_oracles_raw os (LocalC C m c) = LocalC C m (substitute_oracles_raw os c)\<close>
| \<open>substitute_oracles_raw os (OracleCall i) = (if i < length os then os!i else OracleCall (i - length os))\<close>
| \<open>substitute_oracles_raw os (InstantiateOracles c ds) = substitute_oracles_raw (map (substitute_oracles_raw os) ds @ os) c\<close>
| \<open>substitute_oracles_raw os p = p\<close>

lemma max_diff_distrib_left_nat: "max x y - z = max (x - z) (y - z)" for x y z :: nat
  by (simp add: max_def)

(* lemma cSUP_mono_simple: "bdd_above (g ` A) \<Longrightarrow> (\<And>n. n \<in> A \<Longrightarrow> f n \<le> g n) \<Longrightarrow> \<Squnion>(f ` A) \<le> \<Squnion>(g ` A)"
  for f g :: \<open>_ \<Rightarrow> _::conditionally_complete_lattice\<close>
  apply (cases \<open>A = {}\<close>)
apply (simp add: )
try0
sledgehammer [dont_slice]
by -
 *)

lemma [iff]: \<open>is_Sup {} (\<bottom>::_::order_bot)\<close>
  by (simp add: is_Sup_def)


lemma OFCLASS_conditionally_complete_lattice_Sup_orderI:
  assumes \<open>Sup {} = (\<bottom>::'a)\<close>
  shows \<open>OFCLASS('a::{conditionally_complete_lattice, order_bot}, Sup_order_class)\<close>
proof
  show \<open>is_Sup X (\<Squnion> X)\<close> if \<open>has_Sup X\<close> for X :: \<open>'a set\<close>
  proof (cases \<open>X = {}\<close>)
    case True
    then show ?thesis
      by (simp add: assms)
  next
    case False
    with that show ?thesis
      by (auto intro!: is_Sup_cSup has_Sup_bdd_above simp: )
  qed
  show \<open>is_Sup {x, y} (x \<squnion> y)\<close> if \<open>has_Sup {x, y}\<close> for x y :: 'a
  by (simp add: is_Sup_def)
qed

instance nat :: Sup_order
  apply (rule OFCLASS_conditionally_complete_lattice_Sup_orderI)
  by (simp add: bot_nat_def)

lemma (in Sup_order) Sup_eqI:
  "(\<And>y. y \<in> A \<Longrightarrow> y \<le> x) \<Longrightarrow> (\<And>y. (\<And>z. z \<in> A \<Longrightarrow> z \<le> y) \<Longrightarrow> x \<le> y) \<Longrightarrow> \<Squnion>A = x"
  apply (rule is_Sup_eq_Sup[symmetric])
  using local.is_SupI by blast

lemma SUP_diff_nat:
  "(SUP i\<in>I. f i - c :: nat) = (SUP i\<in>I. f i) - c"
  apply (rule antisym)
apply (rule mono_ccSUP)
  apply (rule Sup_eqI)
  thm Sup_eqI
  apply (auto intro!: SUP_eqI diff_le_mono SUP_least intro: SUP_upper
           simp: ennreal_minus_cancel_iff ennreal_minus_le_iff less_top[symmetric])

try0
sledgehammer [dont_slice]
by -


lemma oracle_number_substitute_oracles_raw[simp]: \<open>oracle_number (substitute_oracles_raw os p) \<le> max (oracle_number p - length os) (\<Squnion>q\<in>set os. oracle_number q)\<close>
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
      by x
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
        apply (rule max.mono)
        try0
        apply auto
        sledgehammer [dont_slice]
        by -
        
      finally show \<open>(\<Squnion>a\<in>set x2. oracle_number (substitute_oracles_raw os a)) \<le> max ((\<Squnion>x\<in>set x2. oracle_number x) - length os) (\<Squnion>a\<in>set os. oracle_number a)\<close>
        by -
      by x
    also have \<open>\<dots> = max (oracle_number (InstantiateOracles p x2) - length os) (\<Squnion>a\<in>set os. oracle_number a)\<close>
      by simp
  
  
  also have \<open>\<dots> \<le> max (oracle_number (InstantiateOracles p x2) - length os)
        (\<Squnion>a\<in>set (map (substitute_oracles_raw os) x2 @ os). oracle_number a)\<close>
    apply (rule max.mono[OF _ order.refl])
    by simp
  also have \<open>\<dots> \<le> max (oracle_number (InstantiateOracles p x2) - length os) (\<Squnion>a\<in>set os. oracle_number a)\<close>
  proof (rule max.mono[OF order.refl], cases \<open>x2 = []\<close>)
    case True
    then show \<open>(\<Squnion>a\<in>set (map (substitute_oracles_raw os) x2 @ os). oracle_number a) \<le> (\<Squnion>a\<in>set os. oracle_number a)\<close>
      by simp
  next
    case False
    have \<open>(\<Squnion>a\<in>set (map (substitute_oracles_raw os) x2 @ os). oracle_number a)
           = max \<close>
    apply (auto intro!: simp: )
    try0
sledgehammer [dont_slice]
by -
  also have \<open>\<dots> \<le> (\<Squnion>a\<in>set os. oracle_number a)\<close>
    apply (rule max.boundedI[OF _ order.refl])
  proof (rule cSUP_least)
    show \<open>set x2 \<noteq> {}\<close>
      using False by simp
    fix x assume \<open>x \<in> set x2\<close>
    show \<open>oracle_number (substitute_oracles_raw os x) \<le> (\<Squnion>a\<in>set os. oracle_number a)\<close>
      using InstantiateOracles.IH(2)[where os=os, OF \<open>x \<in> set x2\<close>]
try0
sledgehammer [dont_slice]
by -
qed
  finally    show \<open>(\<Squnion>a\<in>set (map (substitute_oracles_raw os) x2 @ os). oracle_number a) \<le> (\<Squnion>a\<in>set os. oracle_number a)\<close> 
    by -
qed
  finally show ?case
    by -
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
  assumes \<open>oracle_number p = 0\<close>
  shows \<open>no_oracles (substitute_oracles_raw p)\<close>
  sorry

lemma substitute_oracles_raw_no_oracles:
  assumes \<open>no_oracles p\<close>
  shows \<open>substitute_oracles_raw p = p\<close>
  sorry



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

lemma valid_oracle_program_substitute_oracles_raw[intro]:
  assumes \<open>valid_oracle_program p\<close>
  shows \<open>valid_oracle_program (substitute_oracles_raw p)\<close>
  sorry


lemma valid_program_substitute_oracles_raw[intro]:
  assumes \<open>valid_oracle_program p\<close> and \<open>oracle_number p = 0\<close>
  shows \<open>valid_program (substitute_oracles_raw p)\<close>
  using assms(1) assms(2) no_oracles_substitute_oracles_raw valid_oracle_program_valid_program.intros(11) by blast

  

lemma valid_program_LocalQ: \<open>valid_program c \<Longrightarrow> ACTUAL_QREGISTER q \<Longrightarrow> norm \<rho> = 1 \<Longrightarrow> valid_program (LocalQ q \<rho> c)\<close>
  by (meson no_oracles.simps(4) valid_oracle_program_valid_program.intros(11) valid_oracle_program_valid_program.intros(9) valid_program.cases)


lemma valid_program_LocalC: \<open>valid_program c \<Longrightarrow> ACTUAL_CREGISTER x \<Longrightarrow> valid_program (LocalC x init c)\<close>
  by (simp add: valid_oracle_program_valid_program.intros(10) valid_program.simps)


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

lemma actual_cregister_range_empty[iff]: \<open>actual_cregister_range empty_cregister_range\<close>
proof (intro actual_cregister_range_def[THEN iffD2] conjI allI)
  show \<open>valid_cregister_range empty_cregister_range\<close>
  using valid_empty_cregister_range by blast
  fix m m' :: 'a
  show \<open>\<exists>a\<in>empty_cregister_range. \<exists>b\<in>map_commutant empty_cregister_range. (a \<circ>\<^sub>m b) m = Some m'\<close>
    apply (rule bexI[of _ Some, rotated])
     apply (simp add: empty_cregister_range_def)
    apply (rule bexI[of _ \<open>\<lambda>_. Some m'\<close>])
    by simp_all
qed

lemma ACTUAL_CREGISTER_CREGISTER_of[iff]: \<open>ACTUAL_CREGISTER (CREGISTER_of F)\<close>
  apply (cases \<open>cregister F\<close>)
   apply (simp add: ACTUAL_CREGISTER.rep_eq CREGISTER_of.rep_eq actual_register_range)
  by (simp add: non_cregister ACTUAL_CREGISTER.rep_eq bot_CREGISTER.rep_eq)


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


lemma localvars_empty: "localvars empty_cregister empty_qregister P = block P"
(* TODO: not true with current definition. Only denotationally equal.
Do we need this lemma? If yes, we can change the definition of localvars to skip the LocalC/LocalQ for one_dim_algebras. *)
apply (auto intro!: Rep_program_inject[THEN iffD1] simp add: localvars_def localvars1.rep_eq)
  thm Rep_program_inject  sorry


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

definition cq_map_local_q :: 
  \<open>'qu QREGISTER \<Rightarrow> ('qu ell2, 'qu ell2) trace_class \<Rightarrow> ('cl1,'qu,'cl2,'qu) cq_map \<Rightarrow> ('cl1,'qu,'cl2,'qu) cq_map\<close> where
  \<open>cq_map_local_q Q \<rho> \<EE> = cq_map_auxiliary_state \<rho> (
    cq_map_seq  (cq_map_of_op (swap_QREGISTER Q))
    (cq_map_seq (cq_map_tensor_id_right \<EE>)
                (cq_map_of_op (swap_QREGISTER Q))))\<close>


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

lemma kraus_family_norm_sample_prob: \<open>kraus_family_norm (kraus_map_sample (prob \<mu>) :: ('a::{chilbert_space,not_singleton},'a,'x) kraus_family) = weight \<mu>\<close>
  apply (subst kraus_map_sample_norm[of \<open>prob \<mu>\<close>])
  by (auto intro!: prob_summable simp: Prob.rep_eq)

lemma kraus_map_sample_point_distr': \<open>kraus_family_remove_0 (kraus_map_sample (prob (point_distr x))) = kraus_family_remove_0 (kraus_family_map_outcome_inj (\<lambda>_. x) kraus_family_id)\<close>
  apply (rule Rep_kraus_family_inject[THEN iffD1])
  by (auto intro!: prob_summable
      simp: kraus_map_sample.rep_eq kraus_family_map_outcome_inj.rep_eq kraus_family_id_def
      kraus_family_of_op.rep_eq kraus_family_remove_0.rep_eq image_iff)

lemma kraus_map_sample_point_distr: \<open>kraus_equivalent' (kraus_map_sample (prob (point_distr x))) (kraus_family_map_outcome_inj (\<lambda>_. x) kraus_family_id)\<close>
  using kraus_map_sample_point_distr'[of x] kraus_family_remove_0_equivalent'
    kraus_equivalent'_sym kraus_equivalent'_trans
  by metis

lemma cq_map_eqI:
  assumes \<open>cq_map_rel (rep_cq_map E) (rep_cq_map F)\<close>
  shows \<open>E = F\<close>
  using assms Quotient3_cq_map Quotient3_rel_rep by fastforce

lemma cq_map_sample_point_distr: \<open>cq_map_sample (\<lambda>x. point_distr (f x)) = cq_map_classical f\<close>
  apply (transfer' fixing: )
  by (auto intro!: kraus_map_sample_point_distr simp: cq_map_rel_def kraus_family_norm_sample_prob)

lemma denotation_assign_sample: \<open>denotation (assign x e) = cq_map_sample (\<lambda>m. point_distr (Classical_Registers.setter x (e m) m))\<close>
  by (simp add: assign_def denotation_sample)
lemma denotation_assign: \<open>denotation (assign x e) = cq_map_classical (\<lambda>m. Classical_Registers.setter x (e m) m)\<close>
  by (simp add: denotation_assign_sample cq_map_sample_point_distr)

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

lemma denotation_ifthenelse1:
  \<open>denotation (ifthenelse1 c p q) = cq_map_if c (denotation p) (denotation q)\<close>
  apply (transfer' fixing: c)
  by simp

lemma denotation_ifthenelse:
  \<open>denotation (ifthenelse c p q) = cq_map_if c (denotation (block p)) (denotation (block q))\<close>
  by (simp add: denotation_ifthenelse1 ifthenelse_def)


lift_definition kraus_family_in_qref_strict :: \<open>('qu ell2,'qu ell2,'cl) kraus_family \<Rightarrow> 'qu QREGISTER \<Rightarrow> bool\<close> is
  \<open>\<lambda>\<EE> Q. \<forall>(E,x)\<in>\<EE>. E \<in> Rep_QREGISTER Q\<close>.
definition kraus_family_in_qref :: \<open>('qu ell2,'qu ell2,'cl) kraus_family \<Rightarrow> 'qu QREGISTER \<Rightarrow> bool\<close> where
  \<open>kraus_family_in_qref \<EE> Q \<longleftrightarrow> (\<exists>\<FF>. kraus_equivalent' \<EE> \<FF> \<and> kraus_family_in_qref_strict \<FF> Q)\<close>

lift_definition qc_map_in_qref :: \<open>('cl1,'qu,'cl2,'qu) cq_map \<Rightarrow> 'qu QREGISTER \<Rightarrow> bool\<close> is
  \<open>\<lambda>\<EE> Q. \<forall>x. kraus_family_in_qref (\<EE> x) Q\<close>
  apply (auto intro!: simp: cq_map_rel_def kraus_family_in_qref_def)
  using kraus_equivalent'_trans kraus_equivalent'_sym
  by meson

(* definition fvq_of_cq_map :: \<open>(cl, qu, cl, qu) cq_map \<Rightarrow> QVARIABLE\<close> where
  \<open>fvq_of_cq_map \<EE> = Inf {Q. qc_map_in_qref \<EE> Q}\<close> *)

definition program_in_qref :: \<open>program \<Rightarrow> QVARIABLE \<Rightarrow> bool\<close> where
  \<open>program_in_qref p = qc_map_in_qref (denotation p)\<close>

(* definition fvq_program :: \<open>program \<Rightarrow> QVARIABLE\<close> where
  \<open>fvq_program p = fvq_of_cq_map (denotation p)\<close> *)

inductive raw_program_in_qref :: \<open>raw_program \<Rightarrow> QVARIABLE \<Rightarrow> bool\<close> where
  \<open>no_oracles p \<Longrightarrow> qc_map_in_qref (denotation_raw p) Q \<Longrightarrow> raw_program_in_qref p Q\<close>
| \<open>raw_program_in_qref p Q \<Longrightarrow> raw_program_in_qref q Q \<Longrightarrow> raw_program_in_qref (Seq p q) Q\<close>
| \<open>raw_program_in_qref p Q \<Longrightarrow> raw_program_in_qref q Q \<Longrightarrow> raw_program_in_qref (IfThenElse c p q) Q\<close>
| \<open>raw_program_in_qref p Q \<Longrightarrow> raw_program_in_qref (While c p) Q\<close>
| \<open>fvq_raw_program (InstantiateOracles p qs) = fvq_raw_program p \<squnion> (\<Squnion>q\<in>set qs. fvq_raw_program q)\<close>


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

lemma kraus_family_in_qref_strict_map:
  assumes \<open>kraus_family_in_qref_strict \<EE> Q\<close>
  shows \<open>kraus_family_in_qref_strict (kraus_family_map_outcome f \<EE>) Q\<close>
proof -
  have \<open>E \<in> Rep_QREGISTER Q\<close> if \<open>(E,x) \<in> Rep_kraus_family (kraus_family_map_outcome f \<EE>)\<close> for E x
  proof -
    from that
    have \<open>(norm E)\<^sup>2 = kraus_family_op_weight (kraus_family_filter (\<lambda>y. f y = x) \<EE>) E\<close> and \<open>E \<noteq> 0\<close>
      by (simp_all add: kraus_family_map_outcome.rep_eq)
    then have \<open>kraus_family_op_weight (kraus_family_filter (\<lambda>y. f y = x) \<EE>) E \<noteq> 0\<close>
      by auto
    then have \<open>(\<Sum>\<^sub>\<infinity>(F,_)\<in>kraus_family_related_ops (kraus_family_filter (\<lambda>y. f y = x) \<EE>) E. norm (F* o\<^sub>C\<^sub>L F)) \<noteq> 0\<close>
      by (simp add: kraus_family_op_weight_def)
    then have \<open>kraus_family_related_ops (kraus_family_filter (\<lambda>y. f y = x) \<EE>) E \<noteq> {}\<close>
      by force
    then obtain F y r where \<open>(F,y) \<in> Rep_kraus_family (kraus_family_filter (\<lambda>y. f y = x) \<EE>)\<close> and \<open>E = r *\<^sub>R F\<close>
      by (auto simp add: kraus_family_related_ops_def)
    then have \<open>(F,y) \<in> Rep_kraus_family \<EE>\<close>
      by (simp add: kraus_family_filter.rep_eq)
    with assms have \<open>F \<in> Rep_QREGISTER Q\<close>
      by (metis (no_types, lifting) case_prodE fst_conv kraus_family_in_qref_strict.rep_eq)
    with \<open>E = r *\<^sub>R F\<close> show \<open>E \<in> Rep_QREGISTER Q\<close>
      using Rep_QREGISTER[of Q]
      by (auto intro!: complex_vector.subspace_scale
          simp: scaleR_scaleC valid_qregister_range_def von_neumann_algebra_def_sot)
  qed
  then show ?thesis
    by (force simp: kraus_family_in_qref_strict.rep_eq)
qed


lemma kraus_family_in_qref_map:
  assumes \<open>kraus_family_in_qref \<EE> Q\<close>
  shows \<open>kraus_family_in_qref (kraus_family_map_outcome f \<EE>) Q\<close>
proof -
  from assms
  obtain \<FF> where eq: \<open>kraus_equivalent' \<EE> \<FF>\<close> and qref: \<open>kraus_family_in_qref_strict \<FF> Q\<close>
    by (auto simp: kraus_family_in_qref_def)
  define \<FF>' where \<open>\<FF>' = kraus_family_map_outcome f \<FF>\<close>
  have eq': \<open>kraus_equivalent' (kraus_family_map_outcome f \<EE>) \<FF>'\<close>
    by (simp add: \<FF>'_def eq kraus_equivalent'_map_cong)
  have qref': \<open>kraus_family_in_qref_strict \<FF>' Q\<close>
    using qref[THEN kraus_family_in_qref_strict_map]
    by (auto simp: \<FF>'_def )
  from eq' qref' show \<open>kraus_family_in_qref (kraus_family_map_outcome f \<EE>) Q\<close>
    by (auto intro!: exI[of _ \<FF>'] simp add: kraus_family_in_qref_def)
qed

lemma kraus_family_in_qref_strict_id[iff]: \<open>kraus_family_in_qref_strict kraus_family_id Q\<close>
  using Rep_QREGISTER valid_qregister_range_def_sot
  by (auto intro!: simp: kraus_family_id_def  kraus_family_of_op.rep_eq kraus_family_in_qref_strict_def)

lemma kraus_family_in_qref_id[iff]: \<open>kraus_family_in_qref kraus_family_id Q\<close>
  by (auto intro!: exI[of _ kraus_family_id] simp: kraus_family_in_qref_def)

lemma qc_map_in_qref_id[iff]: \<open>qc_map_in_qref cq_map_id Q\<close>
  apply (transfer fixing: Q)
  by (auto intro!: kraus_family_in_qref_map)

lemma fvq_of_cq_map_id[iff]: \<open>fvq_of_cq_map cq_map_id = \<bottom>\<close>
  by (simp add: fvq_of_cq_map_def)

lemma fvq_program_skip[simp]: \<open>fvq_program skip = \<bottom>\<close>
  by (auto intro!: simp: fvq_program_def denotation_skip)

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


lemma kraus_family_in_qref_strict_sample[iff]: \<open>kraus_family_in_qref_strict (kraus_map_sample f) Q\<close>
  using Rep_QREGISTER[of Q]
  by (auto intro!:complex_vector.subspace_scale
      simp: valid_qregister_range_def_sot scaleR_scaleC kraus_map_sample.rep_eq kraus_family_in_qref_strict_def)

lemma kraus_family_in_qref_sample[iff]: \<open>kraus_family_in_qref (kraus_map_sample f) Q\<close>
  by (auto intro!: exI[of _ \<open>kraus_map_sample f\<close>] simp: kraus_family_in_qref_def)

lemma qc_map_in_qref_sample[iff]: \<open>qc_map_in_qref (cq_map_sample f) Q\<close>
  apply (transfer fixing: Q)
  by (auto intro!: kraus_family_in_qref_map)

lemma fvq_of_cq_map_sample[simp]: \<open>fvq_of_cq_map (cq_map_sample f) = \<bottom>\<close>
  by (simp add: fvq_of_cq_map_def)

lemma fvq_program_sample: "fvq_program (sample xs e2) = QREGISTER_unit"
  by (simp add: fvq_program_def denotation_sample)
lemma fvq_program_assign: "fvq_program (assign x e) = QREGISTER_unit"
  by (simp add: fvq_program_def denotation_assign_sample)

lemma kraus_family_in_qref_top[iff]: \<open>kraus_family_in_qref E \<top>\<close>
  by (auto intro!: exI[of _ E] simp add: kraus_family_in_qref_def kraus_family_in_qref_strict_def top_QREGISTER.rep_eq)

lemma
  assumes \<open>\<close>
  shows \<open>qc_map_in_qref (cq_map_if c E F) Q\<close>

lemma fvq_of_cq_map_if: \<open>fvq_of_cq_map (cq_map_if c E F) \<le> fvq_of_cq_map E \<squnion> fvq_of_cq_map F\<close>

  by xxx
proof (unfold fvq_of_cq_map_def, transfer' fixing: c)
  fix E F :: \<open>cl \<Rightarrow> (qu ell2, qu ell2, cl) kraus_family\<close>

  have aux: \<open>A \<subseteq> commutant (commutant B)\<close> if \<open>A \<subseteq> B\<close> for A B
try0
sledgehammer [dont_slice]
  using double_commutant_grows that by blast
by -


  show \<open>\<Sqinter> {Q. \<forall>x. kraus_family_in_qref (if c x then E x else F x) Q}
           \<le> \<Sqinter> {Q. \<forall>x. kraus_family_in_qref (E x) Q} \<squnion> \<Sqinter> {Q. \<forall>x. kraus_family_in_qref (F x) Q}\<close>
    apply (simp add: less_eq_QREGISTER_def Inf_QREGISTER.rep_eq sup_QREGISTER.rep_eq)
    apply (rule aux)
    apply (auto intro!: simp: )
try0
sledgehammer [dont_slice]
by -

apply (transfer' fixing: )

    
    
    by -



  have \<open>\<Sqinter> {Q. \<forall>x. kraus_family_in_qref (if c x then E x else F x) Q}
\<le> \<Sqinter> {Q. \<forall>x. kraus_family_in_qref (E x) Q \<or> kraus_family_in_qref (F x) Q}\<close>
apply (rule Inf_superset_mono)
try0
sledgehammer [dont_slice]
by -
  also have \<open>\<dots> \<le> \<Sqinter> {Q. \<forall>x. kraus_family_in_qref (E x) Q} \<squnion> \<Sqinter> {Q. \<forall>x. kraus_family_in_qref (F x) Q}\<close>
  by (simp add: Inf_superset_mono Set.basic_monos(6) sup.coboundedI2)
  finally 
  show \<open>\<Sqinter> {Q. \<forall>x. kraus_family_in_qref (if c x then E x else F x) Q}
           \<le> \<Sqinter> {Q. \<forall>x. kraus_family_in_qref (E x) Q} \<squnion> \<Sqinter> {Q. \<forall>x. kraus_family_in_qref (F x) Q}\<close>
    by -


  proof (rule Inf_less_eq, rename_tac Q)
    show \<open>{Q. \<forall>x. kraus_family_in_qref (if c x then E x else F x) Q} \<noteq> {}\<close>
      by (auto intro!: exI[of _ \<top>])
    fix Q assume asm: \<open>Q \<in> {Q. \<forall>x. kraus_family_in_qref (if c x then E x else F x) Q}\<close>
    then have \<open>kraus_family_in_qref (E x) Q\<close> if \<open>c x\<close> for x
      using that by (smt (verit, ccfv_threshold) mem_Collect_eq)
    moreover from asm have \<open>kraus_family_in_qref (F x) Q\<close> if \<open>\<not> c x\<close> for x
      by (smt (verit, ccfv_SIG) mem_Collect_eq that)
    ultimately have \<open>Q \<le> \<Sqinter> {Q. \<forall>x. kraus_family_in_qref (E x) Q \<or> kraus_family_in_qref (F x) Q}\<close>
apply (auto intro!: Inf_greatest simp: )
try0
sledgehammer [dont_slice]
by -
  also have \<open>\<dots> \<le> \<Sqinter> {Q. \<forall>x. kraus_family_in_qref (E x) Q} \<squnion> \<Sqinter> {Q. \<forall>x. kraus_family_in_qref (F x) Q}\<close>
  by (simp add: Inf_superset_mono Set.basic_monos(6) sup.coboundedI2)
by -


  have \<open>\<Sqinter> {Q. \<forall>x. kraus_family_in_qref (E x) Q} \<squnion> \<Sqinter> {Q. \<forall>x. kraus_family_in_qref (F x) Q}
      = (\<Sqinter>x. Collect (kraus_family_in_qref (E x))) \<squnion> (\<Sqinter>x. Collect (kraus_family_in_qref (F x)))\<close>
try0
sledgehammer [dont_slice]
by -

    show \<open>Q \<le> \<Sqinter> {Q. \<forall>x. kraus_family_in_qref (E x) Q} \<squnion> \<Sqinter> {Q. \<forall>x. kraus_family_in_qref (F x) Q}\<close>

  apply (auto intro!: simp: fvq_of_cq_map_def)
  apply (transfer' fixing: )
apply (auto intro!: Inf_less_eq simp: )

  by x
lemma fvq_program_ifthenelse1: "fvq_program (ifthenelse1 c p1 p2) \<le>
  QREGISTER_pair (fvq_program p1) (fvq_program p2)"
  by (auto intro!: fvq_of_cq_map_if simp: fvq_program_def denotation_ifthenelse1)
lemma fvq_program_ifthenelse: "fvq_program (ifthenelse c p1 p2) \<le>
  QREGISTER_pair (fvq_program (block p1)) (fvq_program (block p2))"
  using fvq_program_ifthenelse1 ifthenelse_def by presburger
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
