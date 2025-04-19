theory Quantum_From_Classical_Reg
  imports Classical_Reg_Ranges Quantum_Reg_Ranges
begin

lemma permute_and_tensor1_cblinfun_exists_register: \<open>permute_and_tensor1_cblinfun_exists (getter F) (same_outside_cregister F) a\<close> if \<open>cregister F\<close>
  apply (auto intro!: permute_and_tensor1_cblinfun_exists simp add: equivp_implies_part_equivp)
  by (smt (verit, del_insts) equivp_def equivp_same_outside_cregister inj_onI mem_Collect_eq same_outside_cregister_def)

lemma qregister_raw_permute_and_tensor1_cblinfun:
  assumes \<open>cregister F\<close>
  shows \<open>qregister_raw (permute_and_tensor1_cblinfun (getter F) (same_outside_cregister F))\<close>
proof -
  from permute_and_tensor1_cblinfun_as_register[where f=\<open>getter F\<close>]
  have \<open>let 'c::type = permute_and_tensor1_cblinfun_basis (same_outside_cregister F) in
        qregister_raw (permute_and_tensor1_cblinfun (getter F) (same_outside_cregister F))\<close>
  proof with_type_mp
    show \<open>equivp (same_outside_cregister F)\<close>
      by simp
    show \<open>bij_betw (getter F) (Collect (same_outside_cregister F a)) UNIV\<close> for a
      apply (rule bij_betw_byWitness[where f'=\<open>\<lambda>b. setter F b a\<close>])
      apply (auto simp add: same_outside_cregister_def[abs_def] assms)
      by (metis setter_getter_same setter_setter_same)
  next
    with_type_case Rep Abs
    define U where \<open>U = permute_and_tensor1_cblinfun_U Rep (getter F) (same_outside_cregister F)\<close>
    (* assume asm: \<open>(\<forall>A. sandwich U *\<^sub>V (A \<otimes>\<^sub>o id_cblinfun) =
                  permute_and_tensor1_cblinfun (getter F) (same_outside_cregister F) A)
          \<and> unitary U\<close> *)
    from with_type_mp.premise
    have \<open>permute_and_tensor1_cblinfun (getter F) (same_outside_cregister F) = (sandwich U) o Laws_Quantum.Fst\<close>
      by (auto intro!: ext simp: Laws_Quantum.Fst_def U_def)  
    moreover have \<open>qregister_raw \<dots>\<close>
      apply (rule Axioms_Quantum.register_comp)
      using with_type_mp.premise by (simp_all add: unitary_sandwich_register U_def)
    ultimately show \<open>qregister_raw (permute_and_tensor1_cblinfun (getter F) (same_outside_cregister F))\<close>
      by simp
  qed
  from this[cancel_with_type]
  show ?thesis
    by -
qed


lift_definition qregister_of_cregister :: \<open>('a,'b) cregister \<Rightarrow> ('a,'b) qregister\<close> is
  \<open>\<lambda>F a. if cregister F then permute_and_tensor1_cblinfun (getter F) (same_outside_cregister F) a else 0\<close>
  subgoal for F
    apply (cases \<open>cregister F\<close>)
    using qregister_raw_permute_and_tensor1_cblinfun[of F]
    by (auto simp add: non_qregister_raw_def[abs_def])
  by -
(* lift_definition qregister_of_cregister :: \<open>('a,'b) cregister \<Rightarrow> ('a,'b) qregister\<close> is
  \<open>\<lambda>F a. if cregister F then
      explicit_cblinfun (\<lambda>i j. if same_outside_cregister F i j then Rep_ell2 (a *\<^sub>V ket (getter F j)) (getter F i) else 0)
    else 0\<close>
   *)



lemma qregister_of_cregister_non_register[simp]: \<open>qregister_of_cregister non_cregister = non_qregister\<close>
proof -
  define t where \<open>t = non_cregister\<close>
  show \<open>qregister_of_cregister t = non_qregister\<close>
    apply (transfer fixing: t)
    apply (simp add: t_def)
    using non_qregister_raw_def by fastforce
qed

lemma qregister_qregister_of_cregister[simp]: \<open>qregister (qregister_of_cregister F) \<longleftrightarrow> cregister F\<close>
  apply (transfer fixing: F)
  apply (cases \<open>cregister F\<close>)
  using qregister_raw_permute_and_tensor1_cblinfun[of F]
  by auto

lemma qregister_of_cregister_Fst: \<open>qregister_of_cregister cFst = qFst\<close>
proof -
  have *: \<open>Rep_ell2 (apply_qregister (qregister_of_cregister cFst) (butterfly (ket i) (ket j)) *\<^sub>V ket x) y =
       Rep_ell2 (apply_qregister qFst (butterfly (ket i) (ket j)) *\<^sub>V ket x) y\<close> (is \<open>?lhs = ?rhs\<close>)
    for i j :: 'a and x y :: \<open>'a \<times> 'c\<close>
  proof -
    obtain x1 x2 where x12: \<open>x = (x1, x2)\<close> by force
    obtain y1 y2 where y12: \<open>y = (y1, y2)\<close> by force
    have 1: \<open>inj_on fst (Collect (same_outside_cregister cFst x))\<close> for x :: \<open>'a \<times> 'c\<close>
      by (smt (verit) equivp_def equivp_same_outside_cregister getter_cFst inj_onI mem_Collect_eq same_outside_cregister_def)
    have \<open>?lhs = (if same_outside_cregister cFst y x then Rep_ell2 (butterfly (ket i) (ket j) *\<^sub>V ket x1) y1 else 0)\<close>
      by (auto intro!: permute_and_tensor1_cblinfun_exists_register simp add: equivp_implies_part_equivp 
          qregister_of_cregister.rep_eq permute_and_tensor1_cblinfun_ket 1 x12 y12)
    also have \<open>\<dots> = ?rhs\<close>
      apply (auto simp add: qFst.rep_eq Fst_def x12 y12 tensor_op_ell2 cinner_ket
          simp flip: tensor_ell2_ket)
      by (auto simp add: ket.rep_eq zero_ell2.rep_eq same_outside_cregister_def 
          tensor_ell2_ket setter_cFst)
    finally show ?thesis
      by -
  qed
  have \<open>apply_qregister (qregister_of_cregister cFst) (butterfly (ket i) (ket j)) =
           apply_qregister qFst (butterfly (ket i) (ket j))\<close> for i j :: 'a
    by (auto intro!: equal_ket Rep_ell2_inject[THEN iffD1] ext simp: * )
  then show ?thesis
    by (auto intro!: apply_qregister_inject[THEN iffD1]
        weak_star_clinear_eq_butterfly_ketI[where T=weak_star_topology])
(*     using Axioms_Quantum.register_def cFst_register qregister.rep_eq qregister_qregister_of_cregister apply blast
    by (simp add: qFst.rep_eq weak_star_cont_register) *)
qed

lemma qregister_of_cregister_Snd: \<open>qregister_of_cregister cSnd = qSnd\<close>
proof -
  have *: \<open>Rep_ell2 (apply_qregister (qregister_of_cregister cSnd) (butterfly (ket i) (ket j)) *\<^sub>V ket x) y =
       Rep_ell2 (apply_qregister qSnd (butterfly (ket i) (ket j)) *\<^sub>V ket x) y\<close> (is \<open>?lhs = ?rhs\<close>)
    for i j :: 'a and x y :: \<open>'c \<times> 'a\<close>
  proof -
    obtain x1 x2 where x12: \<open>x = (x1, x2)\<close> by force
    obtain y1 y2 where y12: \<open>y = (y1, y2)\<close> by force
    have 1: \<open>inj_on snd (Collect (same_outside_cregister cSnd x))\<close> for x :: \<open>'c \<times> 'a\<close>
      by (smt (verit) equivp_def equivp_same_outside_cregister getter_cSnd inj_onI mem_Collect_eq same_outside_cregister_def)
    have \<open>?lhs = (if same_outside_cregister cSnd y x then Rep_ell2 (butterfly (ket i) (ket j) *\<^sub>V ket x2) y2 else 0)\<close>
      by (auto intro!: permute_and_tensor1_cblinfun_exists simp add: equivp_implies_part_equivp 
          qregister_of_cregister.rep_eq permute_and_tensor1_cblinfun_ket 1 x12 y12)
    also have \<open>\<dots> = ?rhs\<close>
      apply (auto simp add: qSnd.rep_eq Snd_def x12 y12 tensor_op_ell2 cinner_ket
          simp flip: tensor_ell2_ket)
      by (auto simp add: ket.rep_eq zero_ell2.rep_eq same_outside_cregister_def 
          tensor_ell2_ket setter_cSnd)
    finally show ?thesis
      by -
  qed
  have \<open>apply_qregister (qregister_of_cregister cSnd) (butterfly (ket i) (ket j)) =
           apply_qregister qSnd (butterfly (ket i) (ket j))\<close> for i j :: 'a
    by (auto intro!: equal_ket Rep_ell2_inject[THEN iffD1] ext simp: * )
  then show ?thesis
    by (auto intro!: apply_qregister_inject[THEN iffD1]
        weak_star_clinear_eq_butterfly_ketI[where T=weak_star_topology])
(*     using Axioms_Quantum.register_def cSnd_register qregister.rep_eq qregister_qregister_of_cregister apply blast
    by (simp add: qSnd.rep_eq weak_star_cont_register) *)
qed

lemmas qcompatible_FS_qregister_of_cregister[simp] =
  qcompatible_Fst_Snd[unfolded qregister_of_cregister_Fst[symmetric]]
  qcompatible_Fst_Snd[unfolded qregister_of_cregister_Snd[symmetric]]
  qcompatible_Fst_Snd[unfolded qregister_of_cregister_Fst[symmetric] qregister_of_cregister_Snd[symmetric]]
  qcompatible_Snd_Fst[unfolded qregister_of_cregister_Fst[symmetric]]
  qcompatible_Snd_Fst[unfolded qregister_of_cregister_Snd[symmetric]]
  qcompatible_Snd_Fst[unfolded qregister_of_cregister_Fst[symmetric] qregister_of_cregister_Snd[symmetric]]

lemma apply_qregister_of_cregister:
  assumes \<open>cregister F\<close>
  shows \<open>apply_qregister (qregister_of_cregister F) a =
          permute_and_tensor1_cblinfun (getter F) (same_outside_cregister F) a\<close>
  unfolding qregister_of_cregister.rep_eq using assms by simp


lemma apply_qregister_qregister_of_cregister_butterket:
  assumes \<open>cregister F\<close>
  shows \<open>apply_qregister (qregister_of_cregister F) (butterfly (ket x) (ket y)) (ket z) =
          of_bool (y = getter F z) *\<^sub>C ket (setter F x z)\<close>
proof (rule Rep_ell2_inject[THEN iffD1], rule ext)
  fix w
  have \<open>Rep_ell2 (apply_qregister (qregister_of_cregister F) (butterfly (ket x) (ket y)) *\<^sub>V ket z) w
      = Rep_ell2 (permute_and_tensor1_cblinfun (getter F) (same_outside_cregister F) (butterfly (ket x) (ket y)) (ket z)) w\<close>
    using \<open>cregister F\<close> by (simp add: apply_qregister_of_cregister)
  also have \<open>\<dots> = of_bool (same_outside_cregister F w z) * Rep_ell2 (butterfly (ket x) (ket y) *\<^sub>V ket (getter F z)) (getter F w)\<close>
    apply (subst permute_and_tensor1_cblinfun_ket)
     apply (rule permute_and_tensor1_cblinfun_exists)
      apply (simp add: equivp_implies_part_equivp)
     apply (smt (verit, best) inj_onI mem_Collect_eq same_outside_cregister_def setter_getter_same setter_setter_same)
    by simp
  also have \<open>\<dots> = of_bool (same_outside_cregister F w z \<and> x = getter F w \<and> y = getter F z)\<close>
    by (auto simp add: cinner_ket ket.rep_eq zero_ell2.rep_eq)
  also have \<open>\<dots> = of_bool (w = setter F x z \<and> y = getter F z)\<close>
    apply (rule arg_cong[where f=of_bool])
    by (auto simp: same_outside_cregister_def \<open>cregister F\<close>)
  also have \<open>\<dots> = Rep_ell2 (of_bool (y = getter F z) *\<^sub>C ket (setter F x z)) w\<close>
    by (auto simp add: ket.rep_eq zero_ell2.rep_eq)
  finally show \<open>Rep_ell2 (apply_qregister (qregister_of_cregister F) (butterfly (ket x) (ket y)) *\<^sub>V ket z) w
              = Rep_ell2 (of_bool (y = getter F z) *\<^sub>C ket (setter F x z)) w\<close>
    by -
qed

lemma qcompatible_qregister_of_cregister[simp]:
  \<open>qcompatible (qregister_of_cregister F) (qregister_of_cregister G) \<longleftrightarrow> ccompatible F G\<close>
proof (rule iffI)
  assume compat: \<open>ccompatible F G\<close>
  then have [simp]: \<open>cregister F\<close> \<open>cregister G\<close>
    using ccompatible_register1 ccompatible_register2 by auto

  have [simp]: \<open>getter F (setter G b m) = getter F m\<close> for b m
    by (simp add: compat)
  have [simp]: \<open>getter G (setter F a m) = getter G m\<close> for a m
    by (simp add: ccompatible_sym compat)
  have [simp]: \<open>setter F a (setter G b z) = setter G b (setter F a z)\<close> for a b z
    by (simp add: compat setter_setter_compat)

  have [simp]: \<open>clinear (\<lambda>a. apply_qregister X a o\<^sub>C\<^sub>L B)\<close> for a B X
    using clinear_compose[OF clinear_apply_qregister[of X] clinear_cblinfun_compose_left[of B]]
    by (simp add: o_def)
  have [simp]: \<open>clinear (\<lambda>a. B o\<^sub>C\<^sub>L apply_qregister X a)\<close> for a B X
    using clinear_compose[OF clinear_apply_qregister[of X] clinear_cblinfun_compose_right[of B]]
    by (simp add: o_def)
  have [intro]: \<open>continuous_map weak_star_topology weak_star_topology 
         (\<lambda>a. apply_qregister X a o\<^sub>C\<^sub>L B)\<close> for B X
    using continuous_map_compose[OF apply_qregister_weak_star_continuous[of X] continuous_map_right_comp_weak_star[of B]]
    by (simp add: o_def)
  have [intro]: \<open>continuous_map weak_star_topology weak_star_topology 
         (\<lambda>a. B o\<^sub>C\<^sub>L apply_qregister X a)\<close> for B X
    using continuous_map_compose[OF apply_qregister_weak_star_continuous[of X] continuous_map_left_comp_weak_star[of B]]
    by (simp add: o_def)

  have *: \<open>apply_qregister (qregister_of_cregister F) (butterfly (ket x) (ket y)) *\<^sub>V apply_qregister (qregister_of_cregister G) (butterfly (ket x') (ket y')) *\<^sub>V ket z
      = apply_qregister (qregister_of_cregister G) (butterfly (ket x') (ket y')) *\<^sub>V apply_qregister (qregister_of_cregister F) (butterfly (ket x) (ket y)) *\<^sub>V ket z\<close>
    for x y x' y' z
    by (auto simp add: apply_qregister_qregister_of_cregister_butterket)
  have *: \<open>apply_qregister (qregister_of_cregister F) (butterfly (ket x) (ket y)) o\<^sub>C\<^sub>L apply_qregister (qregister_of_cregister G) (butterfly (ket x') (ket y'))
      = apply_qregister (qregister_of_cregister G) (butterfly (ket x') (ket y')) o\<^sub>C\<^sub>L apply_qregister (qregister_of_cregister F) (butterfly (ket x) (ket y))\<close>
    for x y x' y'
    apply (rule equal_ket)
    using *[of x y x' y']
    by simp
  have *: \<open>apply_qregister (qregister_of_cregister F) a o\<^sub>C\<^sub>L apply_qregister (qregister_of_cregister G) (butterfly (ket x') (ket y'))
      = apply_qregister (qregister_of_cregister G) (butterfly (ket x') (ket y')) o\<^sub>C\<^sub>L apply_qregister (qregister_of_cregister F) a\<close>
    for x' y' a
    apply (rule fun_cong[where x=a])
    apply (rule weak_star_clinear_eq_butterfly_ketI)
    using * by auto
  have \<open>apply_qregister (qregister_of_cregister F) a o\<^sub>C\<^sub>L apply_qregister (qregister_of_cregister G) b
      = apply_qregister (qregister_of_cregister G) b o\<^sub>C\<^sub>L apply_qregister (qregister_of_cregister F) a\<close>
    for a b
    apply (rule fun_cong[where x=b])
    apply (rule weak_star_clinear_eq_butterfly_ketI)
    using * by auto
  then show \<open>qcompatible (qregister_of_cregister F) (qregister_of_cregister G)\<close>
    by (simp add: qcompatibleI)
next
  assume compat: \<open>qcompatible (qregister_of_cregister F) (qregister_of_cregister G)\<close>
  then have qqF: \<open>qregister (qregister_of_cregister F)\<close> and qqG: \<open>qregister (qregister_of_cregister G)\<close>
    by (auto simp add: qcompatible_def)
  from qqF have [simp]: \<open>cregister F\<close>
    apply (transfer fixing: F)
    apply (cases \<open>cregister F\<close>)
    by auto
  from qqG have [simp]: \<open>cregister G\<close>
    apply (transfer fixing: G)
    apply (cases \<open>cregister G\<close>)
    by auto

  have \<open>setter F a (setter G b m) = setter G b (setter F a m)\<close> for a b m
  proof (rule ccontr)
    assume assm: \<open>setter F a (setter G b m) \<noteq> setter G b (setter F a m)\<close>
    have *: \<open>(apply_qregister (qregister_of_cregister F) (butterfly (ket a) (ket a')) o\<^sub>C\<^sub>L apply_qregister (qregister_of_cregister G) (butterfly (ket b) (ket b'))) *\<^sub>V ket m
      = (apply_qregister (qregister_of_cregister G) (butterfly (ket b) (ket b')) o\<^sub>C\<^sub>L apply_qregister (qregister_of_cregister F) (butterfly (ket a) (ket a'))) *\<^sub>V ket m\<close>
      for a' b'
      by (simp add: compat qcompatible_commute)
    have *: \<open>of_bool (b' = getter G m \<and> a' = getter F (setter G b m)) *\<^sub>C ket (setter F a (setter G b m))
             = of_bool (a' = getter F m \<and> b' = getter G (setter F a m)) *\<^sub>C ket (setter G b (setter F a m))\<close>
      for a' b'
      using *[of a' b']
      by (simp add: apply_qregister_qregister_of_cregister_butterket cblinfun.scaleC_right flip: of_bool_conj)
    with assm have \<open>\<not> (b' = getter G m \<and> a' = getter F (setter G b m)) \<and> \<not> (a' = getter F m \<and> b' = getter G (setter F a m))\<close> 
      for a' b'
      by (smt (z3) complex_vector.scale_cancel_left ket_injective of_bool_eq(1) of_bool_eq_iff)
    then show False
      by blast
  qed
  then show \<open>ccompatible F G\<close>
    apply (rule setter_setter_compatI[rotated -1])
    by simp_all
qed


lemma qregister_of_cregister_pair: 
  \<open>qregister_of_cregister (cregister_pair x y) = qregister_pair (qregister_of_cregister x) (qregister_of_cregister y)\<close>
proof (cases \<open>ccompatible x y\<close>)
  case True
  then have [simp]: \<open>ccompatible x y\<close> \<open>cregister x\<close> \<open>cregister y\<close>
    by (auto simp add: ccompatible_def)
  have \<open>apply_qregister (qregister_of_cregister (cregister_pair x y)) (butterfly (ket k) (ket l)) *\<^sub>V ket z =
        apply_qregister (qregister_pair (qregister_of_cregister x) (qregister_of_cregister y)) (butterfly (ket k) (ket l)) *\<^sub>V ket z\<close> for k l z
  proof -
    obtain k1 k2 where [simp]: \<open>k = (k1,k2)\<close>
      by force
    obtain l1 l2 where [simp]: \<open>l = (l1,l2)\<close>
      by force
    show ?thesis
      apply (simp add: apply_qregister_pair flip: tensor_ell2_ket tensor_butterfly)
      by (simp add: apply_qregister_qregister_of_cregister_butterket getter_pair setter_pair
          tensor_ell2_ket tensor_butterfly)
  qed
  then have \<open>apply_qregister (qregister_of_cregister (cregister_pair x y)) (butterfly (ket k) (ket l)) =
        apply_qregister (qregister_pair (qregister_of_cregister x) (qregister_of_cregister y)) (butterfly (ket k) (ket l))\<close> for k l
    by (simp add: equal_ket)
  then show ?thesis
    apply (rule_tac qregister_eqI_separating[OF separating_butterket])
    by auto
next
  case False
  then have \<open>\<not> qcompatible (qregister_of_cregister x) (qregister_of_cregister y)\<close>
    by simp
  then have 1: \<open>qregister_pair (qregister_of_cregister x) (qregister_of_cregister y) = non_qregister\<close>
    using non_qregister by blast
  from False have 2: \<open>cregister_pair x y = non_cregister\<close>
    using non_cregister by blast
  from 1 2 show ?thesis
    by simp
qed

lemma qregister_of_cregister_chain: \<open>qregister_of_cregister (cregister_chain x y) = qregister_chain (qregister_of_cregister x) (qregister_of_cregister y)\<close>
proof (cases \<open>cregister x \<and> cregister y\<close>)
  case True
  then have [simp]: \<open>cregister x\<close> \<open>cregister y\<close>
    by (auto simp add: ccompatible_def)
  have \<open>apply_qregister (qregister_of_cregister (cregister_chain x y)) (butterfly (ket k) (ket l)) *\<^sub>V ket z =
        apply_qregister (qregister_chain (qregister_of_cregister x) (qregister_of_cregister y)) (butterfly (ket k) (ket l)) *\<^sub>V ket z\<close> for k l z
    apply (auto intro!: Rep_ell2_inject[THEN iffD1] ext 
        simp add: apply_qregister_qregister_of_cregister_butterket getter_chain setter_chain)
     apply (auto simp add: apply_qregister_of_cregister permute_and_tensor1_cblinfun_ket
        permute_and_tensor1_cblinfun_exists_register ket.rep_eq same_outside_cregister_def
        scaleC_ell2.rep_eq cinner_ket zero_ell2.rep_eq)
     apply (metis getter_setter_same[OF \<open>cregister x\<close>])
    by (metis getter_setter_same[OF \<open>cregister x\<close>])
  then have \<open>apply_qregister (qregister_of_cregister (cregister_chain x y)) (butterfly (ket k) (ket l)) =
        apply_qregister (qregister_chain (qregister_of_cregister x) (qregister_of_cregister y)) (butterfly (ket k) (ket l))\<close> for k l
    by (simp add: equal_ket)
  then show ?thesis
    apply (rule_tac qregister_eqI_separating[OF separating_butterket])
    by auto
next
  case False
  then show ?thesis
    by (auto simp add: non_cregister)
qed


lemma qregister_of_cregister_alt_def_has_sum:
  assumes \<open>cregister F\<close>
  shows \<open>((\<lambda>(x,y). ket y \<bullet>\<^sub>C a (ket x)) has_sum
      of_bool (same_outside_cregister F n m) *\<^sub>C ket (Classical_Registers.getter F n) \<bullet>\<^sub>C a (ket (Classical_Registers.getter F m)))
          {(x,y). apply_cregister F [x\<mapsto>y] m = Some n}\<close>
proof (rule has_sum_single[where i=\<open>(getter F m, getter F n)\<close>])
  show \<open>j \<in> {(x, y). apply_cregister F [x \<mapsto> y] m = Some n} \<Longrightarrow> (case j of (x, y) \<Rightarrow> ket y \<bullet>\<^sub>C a (ket x)) = 0\<close>
    if \<open>j \<noteq> (Classical_Registers.getter F m, Classical_Registers.getter F n)\<close> for j
    apply (simp add: case_prod_unfold)
    using that
    by (metis (no_types, lifting) \<open>cregister F\<close> apply_cregister_getter_setter apply_cregister_of_0 array_rules(2) getter_setter_same option.case(2) option.simps(2)
        surjective_pairing )
  have *: \<open>apply_cregister F [Classical_Registers.getter F m \<mapsto> Classical_Registers.getter F n] m = Some n \<longleftrightarrow> same_outside_cregister F n m\<close>
    by (auto simp: same_outside_cregister_def \<open>cregister F\<close> apply_cregister_getter_setter)
  show \<open>of_bool (same_outside_cregister F n m) *\<^sub>C ket (Classical_Registers.getter F n) \<bullet>\<^sub>C a (ket (Classical_Registers.getter F m)) =
    (if (Classical_Registers.getter F m, Classical_Registers.getter F n) \<in> {(x, y). apply_cregister F [x \<mapsto> y] m = Some n}
     then case (Classical_Registers.getter F m, Classical_Registers.getter F n) of (x, y) \<Rightarrow> ket y \<bullet>\<^sub>C a (ket x) else 0)\<close>
    by (simp add: * )
qed


lemma qregister_of_cregister_alt_def_exists: \<open>explicit_cblinfun_exists (\<lambda>n m. 
          \<Sum>\<^sub>\<infinity>(x,y) | apply_cregister F [x\<mapsto>y] m = Some n. ket y \<bullet>\<^sub>C (a *\<^sub>V ket x))\<close>
proof -
  wlog \<open>cregister F\<close>
    using negation
    by (simp add: non_cregister non_cregister.rep_eq non_cregister_raw_def case_prod_unfold)
  have \<open>explicit_cblinfun_exists (\<lambda>n m. 
          \<Sum>\<^sub>\<infinity>(x,y) | apply_cregister F [x\<mapsto>y] m = Some n. ket y \<bullet>\<^sub>C (a *\<^sub>V ket x))
              = permute_and_tensor1_cblinfun_exists (getter F) (same_outside_cregister F) a\<close>
    unfolding permute_and_tensor1_cblinfun_exists_def
    apply (intro arg_cong[where f=explicit_cblinfun_exists] ext)
    unfolding infsumI[OF qregister_of_cregister_alt_def_has_sum[OF \<open>cregister F\<close>]]
    by (simp add: cinner_ket_left)
  moreover have \<open>permute_and_tensor1_cblinfun_exists (getter F) (same_outside_cregister F) a\<close>
    by (simp add: \<open>cregister F\<close> permute_and_tensor1_cblinfun_exists_register)
  ultimately show ?thesis
    by simp
qed

lemma qregister_of_cregister_alt_def:
  shows \<open>apply_qregister (qregister_of_cregister F) a = explicit_cblinfun (\<lambda>n m. 
          \<Sum>\<^sub>\<infinity>(x,y) | apply_cregister F [x\<mapsto>y] m = Some n. ket y \<bullet>\<^sub>C (a *\<^sub>V ket x))\<close>
proof -
  wlog [iff]: \<open>cregister F\<close>
    using negation
    by (simp add: non_cregister non_cregister.rep_eq non_cregister_raw_def)
  have \<open>apply_qregister (qregister_of_cregister F) a = permute_and_tensor1_cblinfun (Classical_Registers.getter F) (same_outside_cregister F) a\<close>
    by (simp add: apply_qregister_of_cregister)
  also have \<open>\<dots> = explicit_cblinfun (\<lambda>n m. of_bool (same_outside_cregister F n m) * Rep_ell2 (a *\<^sub>V ket (Classical_Registers.getter F m)) (Classical_Registers.getter F n))\<close>
    by (simp add: permute_and_tensor1_cblinfun_def)
  also have \<open>\<dots> = explicit_cblinfun (\<lambda>n m. \<Sum>\<^sub>\<infinity>(x,y) | apply_cregister F [x\<mapsto>y] m = Some n. ket y \<bullet>\<^sub>C (a *\<^sub>V ket x))\<close>
    apply (intro arg_cong[where f=explicit_cblinfun] ext)
    unfolding infsumI[OF qregister_of_cregister_alt_def_has_sum[OF \<open>cregister F\<close>], symmetric]
    using infsumI[OF qregister_of_cregister_alt_def_has_sum[OF \<open>cregister F\<close>], symmetric]
    by (simp add: cinner_ket_left)
  finally show ?thesis
    by -
qed

lift_definition QREGISTER_of_CREGISTER :: \<open>'a CREGISTER \<Rightarrow> 'a QREGISTER\<close> is
  \<open>\<lambda>C :: ('a \<rightharpoonup> 'a) set. commutant (commutant (let ops = {classical_operator f | f. f \<in> C \<and> inj_map f} in ops \<union> adj ` ops))\<close>
proof (intro CollectI valid_qregister_range_def[THEN iffD2] von_neumann_algebra_def[THEN iffD2] conjI ballI)
  fix C :: \<open>('a \<rightharpoonup> 'a) set\<close> and a :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close>
  assume \<open>C \<in> Collect valid_cregister_range\<close>
  then have \<open>valid_cregister_range C\<close>
    by simp
  define ops where \<open>ops = {classical_operator f | f. f \<in> C \<and> inj_map f}\<close>
  show \<open>commutant (commutant (commutant (commutant (let ops = ops in ops \<union> adj ` ops)))) = commutant (commutant (let ops = ops in ops \<union> adj ` ops))\<close>
    by simp
  fix a
  assume \<open>a \<in> commutant (commutant (let ops = ops in ops \<union> adj ` ops))\<close>
  then have \<open>a* \<in> adj ` \<dots>\<close>
    by blast
  also have \<open>\<dots> = commutant (commutant (adj ` ops \<union> ops))\<close>
    by (simp add: commutant_adj image_Un image_image)
  also have \<open>\<dots> = commutant (commutant (let ops = ops in ops \<union> adj ` ops))\<close>
    by (simp add: Un_commute)
  finally show \<open>a* \<in> commutant (commutant (let ops = ops in ops \<union> adj ` ops))\<close>
    by simp
qed

lemma QREGISTER_of_CREGISTER_bot[simp]: \<open>QREGISTER_of_CREGISTER \<bottom> = \<bottom>\<close>
proof transfer'
  define ops where \<open>ops = {classical_operator f | f::'a\<rightharpoonup>'a. f \<in> empty_cregister_range \<and> inj_map f}\<close>

  have \<open>ops \<subseteq> one_algebra\<close>
    apply (simp add: ops_def empty_cregister_range_def one_algebra_def)
    by force
  moreover then have \<open>adj ` ops \<subseteq> one_algebra\<close>
    by (metis (mono_tags, lifting) commutant_UNIV commutant_adj commutant_one_algebra image_mono image_subset_iff subset_UNIV von_neumann_algebra_adj_image
        von_neumann_algebra_def)
  ultimately have \<open>commutant (commutant (let ops = ops in ops \<union> adj ` ops)) \<subseteq> commutant (commutant one_algebra)\<close>
    by (auto intro!: commutant_antimono Un_least simp: Let_def)
  also have \<open>\<dots> = one_algebra\<close>
    by (simp add: commutant_UNIV commutant_one_algebra)
  finally have \<open>commutant (commutant (let ops = ops in ops \<union> adj ` ops)) \<subseteq> one_algebra\<close>
    by -
  then show \<open>commutant (commutant (let ops = ops in ops \<union> adj ` ops)) = one_algebra\<close>
    by (metis (no_types, lifting) \<open>adj ` ops \<subseteq> one_algebra\<close> \<open>ops \<subseteq> one_algebra\<close> commutant_UNIV commutant_empty commutant_one_algebra double_commutant_Un_right
        subset_Un_eq sup_bot.comm_neutral)
qed

lemma QREGISTER_of_qregister_of_cregister: \<open>QREGISTER_of (qregister_of_cregister X) = QREGISTER_of_CREGISTER (CREGISTER_of X)\<close>
proof -
  have 1: \<open>QREGISTER_of (qregister_of_cregister X) = QREGISTER_of_CREGISTER (CREGISTER_of X)\<close>
    if \<open>\<not> cregister X\<close>
    using that by (simp add: non_cregister)
  define ops where \<open>ops = {classical_operator f |f. f \<in> range (apply_cregister X) \<and> inj_map f}\<close>
  define ccops where \<open>ccops = commutant (commutant (ops \<union> adj ` ops))\<close>
  define apply_qX where \<open>apply_qX = apply_qregister (qregister_of_cregister X)\<close>
  have [iff]: \<open>bounded_clinear apply_qX\<close>
    by (simp add: apply_qX_def)
  have [iff]: \<open>continuous_map weak_star_topology weak_star_topology apply_qX\<close>
    using apply_qX_def by fastforce
  define gX sX where \<open>gX = getter X\<close> and \<open>sX = setter X\<close>
  have 2: \<open>QREGISTER_of (qregister_of_cregister X) \<le> QREGISTER_of_CREGISTER (CREGISTER_of X)\<close>
    if [iff]: \<open>cregister X\<close>
  proof -
    have \<open>range apply_qX \<subseteq> ccops\<close>
    proof (intro image_subsetI)
      fix x :: \<open>'b ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
      have [iff]: \<open>csubspace ccops\<close>
        by (simp add: ccops_def)
      have [iff]: \<open>closedin weak_star_topology ccops\<close>
        using ccops_def by auto
      have \<open>apply_qX (butterfly (ket a) (ket b)) \<in> ops\<close> for a b
      proof (unfold ops_def, intro CollectI exI conjI)
        show \<open>apply_cregister X [b \<mapsto> a] \<in> range (apply_cregister X)\<close>
          by fast
        have \<open>inj_map [b\<mapsto>a]\<close>
          by (simp add: inj_map_def)
        then show inj: \<open>inj_map (apply_cregister X [b\<mapsto>a])\<close>
          by (simp add: apply_cregister_inj_map_iff \<open>cregister X\<close>)
        show \<open>apply_qX (butterfly (ket a) (ket b)) = classical_operator (apply_cregister X [b \<mapsto> a])\<close>
        proof (intro equal_ket cinner_ket_eqI, rename_tac m n)
          fix m n :: 'a
          have \<open>ket n \<bullet>\<^sub>C (apply_qX (butterfly (ket a) (ket b)) *\<^sub>V ket m)
                 = of_bool (same_outside_cregister X n m) *\<^sub>C ket (gX n) \<bullet>\<^sub>C (butterfly (ket a) (ket b) *\<^sub>V ket (gX m))\<close>
            unfolding qregister_of_cregister_alt_def apply_qX_def
            apply (subst Rep_ell2_explicit_cblinfun_ket[folded cinner_ket_left])
             apply (rule qregister_of_cregister_alt_def_exists)
            apply (subst qregister_of_cregister_alt_def_has_sum[THEN infsumI, OF \<open>cregister X\<close>])
            by (simp add: gX_def)
          also 
          have \<open>\<dots> = of_bool (same_outside_cregister X n m \<and> gX n = a \<and> gX m = b)\<close>
            by (auto simp: cinner_ket)
          also
          have \<open>\<dots> = of_bool (apply_cregister X [b \<mapsto> a] m = Some n)\<close>
            apply (rule arg_cong[where f=of_bool])
            by (auto simp add: gX_def sX_def apply_cregister_getter_setter same_outside_cregister_def)
          also
          have \<open>\<dots> = ket n \<bullet>\<^sub>C (classical_operator (apply_cregister X [b \<mapsto> a]) *\<^sub>V ket m)\<close>
            apply (cases \<open>apply_cregister X [b \<mapsto> a] m\<close>)
            using inj
            by (auto simp add: classical_operator_ket classical_operator_exists_inj apply_cregister_inj_map_iff
                cinner_ket)
          finally
          show \<open>ket n \<bullet>\<^sub>C (apply_qX (butterfly (ket a) (ket b)) *\<^sub>V ket m) = ket n \<bullet>\<^sub>C (classical_operator (apply_cregister X [b \<mapsto> a]) *\<^sub>V ket m)\<close>
            by -
        qed
      qed
      then have \<open>apply_qX (butterfly (ket a) (ket b)) \<in> ccops\<close> for a b
        by (simp add: ccops_def double_commutant_grows')
      then have *: \<open>apply_qX (butterfly (ket a) (ket a) o\<^sub>C\<^sub>L x o\<^sub>C\<^sub>L butterfly (ket b) (ket b)) \<in> ccops\<close> for a b
        using \<open>csubspace ccops\<close>
        by (simp add: cblinfun_comp_butterfly clinear.scaleC bounded_clinear.clinear complex_vector.subspace_scale)
      have **: \<open>apply_qX (butterfly (ket a) (ket a) o\<^sub>C\<^sub>L x o\<^sub>C\<^sub>L id_cblinfun) \<in> ccops\<close> for a
      proof -
        define f where \<open>f p = apply_qX (butterfly (ket a) (ket a) o\<^sub>C\<^sub>L x o\<^sub>C\<^sub>L p)\<close> for p
        have cont: \<open>continuous_map weak_star_topology weak_star_topology f\<close>
          unfolding f_def
          apply (rule continuous_map_compose[unfolded o_def, where g=apply_qX])
           apply (rule continuous_map_left_comp_weak_star)
          by blast
        have add: \<open>Modules.additive f\<close>
          by (simp add: Modules.additive_def f_def bounded_clinear.clinear
              cblinfun_compose_add_right complex_vector.linear_add)
        from has_sum_butterfly_ket
        have sum: \<open>has_sum_in weak_star_topology (\<lambda>a. f (selfbutter (ket a))) UNIV (f id_cblinfun)\<close>
          apply (rule has_sum_in_comm_additive[unfolded o_def, where g=f, rotated -1])
          by (auto intro!: cont add)
        from * have \<open>f (butterfly (ket b) (ket b)) \<in> ccops\<close> for b
          by (simp add: f_def)
        with sum have \<open>f id_cblinfun \<in> ccops\<close>
          apply (rule has_sum_in_in_closedsubspace)
          by auto
        then show ?thesis
          by (simp add: f_def)
      qed
      then have \<open>apply_qX (id_cblinfun o\<^sub>C\<^sub>L x) \<in> ccops\<close>
      proof -
        define f where \<open>f p = apply_qX (p o\<^sub>C\<^sub>L x)\<close> for p
        have cont: \<open>continuous_map weak_star_topology weak_star_topology f\<close>
          unfolding f_def
          apply (rule continuous_map_compose[unfolded o_def, where g=apply_qX])
           apply (rule continuous_map_right_comp_weak_star)
          by blast
        have add: \<open>Modules.additive f\<close>
          by (simp add: Modules.additive_def f_def bounded_clinear.clinear
              cblinfun_compose_add_left complex_vector.linear_add)
        from has_sum_butterfly_ket
        have sum: \<open>has_sum_in weak_star_topology (\<lambda>a. f (selfbutter (ket a))) UNIV (f id_cblinfun)\<close>
          apply (rule has_sum_in_comm_additive[unfolded o_def, where g=f, rotated -1])
          by (auto intro!: cont add)
        from ** have \<open>f (butterfly (ket b) (ket b)) \<in> ccops\<close> for b
          by (simp add: f_def)
        with sum have \<open>f id_cblinfun \<in> ccops\<close>
          apply (rule has_sum_in_in_closedsubspace)
          by auto
        then show ?thesis
          by (simp add: f_def)
      qed
      then show \<open>apply_qX x \<in> ccops\<close>
        by simp
    qed
    then show ?thesis
      by (simp add: less_eq_QREGISTER_def QREGISTER_of.rep_eq QREGISTER_of_CREGISTER.rep_eq CREGISTER_of.rep_eq ccops_def apply_qX_def
          flip: ops_def)
  qed
  have 3: \<open>QREGISTER_of_CREGISTER (CREGISTER_of X) \<le> QREGISTER_of (qregister_of_cregister X)\<close>
    if \<open>cregister X\<close>
  proof -
    have ops1: \<open>ops \<subseteq> range (apply_qregister (qregister_of_cregister X))\<close>
    proof (intro subsetI)
      fix x assume \<open>x \<in> ops\<close>
      then obtain f where x_def: \<open>x = classical_operator f\<close> and [iff]: \<open>inj_map f\<close> and \<open>f \<in> range (apply_cregister X)\<close>
        by (auto simp: ops_def)
      then obtain g where fg: \<open>f = apply_cregister X g\<close>
        by auto
      then have f_get_set: \<open>f m = (case g (gX m) of None \<Rightarrow> None | Some b \<Rightarrow> Some (sX b m))\<close> for m
        by (metis apply_cregister_getter_setter gX_def sX_def that)
      from fg \<open>inj_map f\<close> have [iff]: \<open>inj_map g\<close>
        by (simp add: fg apply_cregister_inj_map_iff \<open>cregister X\<close>)
      have aux1: \<open>same_outside_cregister X m n \<Longrightarrow> ket m \<bullet>\<^sub>C ket (sX a n) = ket (gX m) \<bullet>\<^sub>C ket a\<close> for a n m
        by (metis cinner_ket_same gX_def getter_setter_same orthogonal_ket sX_def same_outside_cregister_def that)
      have aux2: \<open>g (gX n) = Some a \<Longrightarrow> \<not> same_outside_cregister X (sX a n) n \<Longrightarrow> m = sX a n \<Longrightarrow> False\<close> for a n m
        by (simp add: sX_def same_outside_cregister_def that)

      define a where \<open>a = classical_operator g\<close>
      have *: \<open>ket m \<bullet>\<^sub>C (x *\<^sub>V ket n) =
           of_bool (same_outside_cregister X m n) *\<^sub>C ket (gX m) \<bullet>\<^sub>C (a *\<^sub>V ket (gX n))\<close> for m n
        apply (cases \<open>g (gX n)\<close>)
         apply (simp_all add: a_def x_def classical_operator_ket classical_operator_exists_inj f_get_set
            flip: sX_def gX_def)
        using aux1 aux2           
        by blast
      have \<open>x = explicit_cblinfun (\<lambda>n m. \<Sum>\<^sub>\<infinity>(x, y) | apply_cregister X [x \<mapsto> y] m = Some n. ket y \<bullet>\<^sub>C (a *\<^sub>V ket x))\<close>
        apply (intro equal_ket cinner_ket_eqI)
        apply (subst Rep_ell2_explicit_cblinfun_ket[folded cinner_ket_left])
         apply (rule qregister_of_cregister_alt_def_exists)
        apply (subst qregister_of_cregister_alt_def_has_sum[THEN infsumI, OF \<open>cregister X\<close>])
        using *
        by (simp flip: gX_def)
      also have \<open>\<dots> \<in> range (apply_qregister (qregister_of_cregister X))\<close>
        by (simp add: qregister_of_cregister_alt_def[abs_def])
      finally show \<open>x \<in> \<dots>\<close>
        by -
    qed
    then have ops2: \<open>adj ` ops \<subseteq> range (apply_qregister (qregister_of_cregister X))\<close>
      apply (subst von_neumann_algebra_adj_image[where X=\<open>range _\<close>, symmetric])
      using qregister_qregister_of_cregister that valid_qregister_range valid_qregister_range_def apply blast 
      by fast
    from ops1 ops2 have \<open>ops \<union> adj ` ops \<subseteq> range (apply_qregister (qregister_of_cregister X))\<close>
      by fast
    then have \<open>commutant (commutant (ops \<union> adj ` ops)) \<subseteq> range (apply_qregister (qregister_of_cregister X))\<close>
      apply (rule double_commutant_in_vn_algI[rotated])
      using qregister_qregister_of_cregister that valid_qregister_range valid_qregister_range_def by blast 
    then show ?thesis
      by (simp add: less_eq_QREGISTER_def QREGISTER_of.rep_eq that QREGISTER_of_CREGISTER.rep_eq CREGISTER_of.rep_eq 
        flip: ops_def)
  qed
  from 1 2 3 show ?thesis
    apply (cases \<open>cregister X\<close>)
    by (auto intro!: order.antisym simp: )
qed



end
