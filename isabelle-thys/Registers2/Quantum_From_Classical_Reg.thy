theory Quantum_From_Classical_Reg
  imports Classical_Registers Quantum_Registers
begin

lemma permute_and_tensor1_cblinfun_exists_register: \<open>permute_and_tensor1_cblinfun_exists (getter F) (same_outside_cregister F) a\<close> if \<open>cregister F\<close>
  apply (auto intro!: permute_and_tensor1_cblinfun_exists simp add: equivp_implies_part_equivp)
  by (smt (verit, del_insts) equivp_def equivp_same_outside_cregister inj_onI mem_Collect_eq same_outside_cregister_def)

lemma qregister_raw_permute_and_tensor1_cblinfun:
  assumes \<open>cregister F\<close>
  shows \<open>qregister_raw (permute_and_tensor1_cblinfun (getter F) (same_outside_cregister F))\<close>
proof -
  have \<open>\<forall>\<^sub>\<tau> 'c::type = permute_and_tensor1_cblinfun_basis (same_outside_cregister F).
        qregister_raw (permute_and_tensor1_cblinfun (getter F) (same_outside_cregister F))\<close>
  proof (rule with_type_mp[OF permute_and_tensor1_cblinfun_as_register])
    show \<open>equivp (same_outside_cregister F)\<close>
      by simp
    show \<open>bij_betw (getter F) (Collect (same_outside_cregister F a)) UNIV\<close> for a
      apply (rule bij_betw_byWitness[where f'=\<open>\<lambda>b. setter F b a\<close>])
      apply (auto simp add: same_outside_cregister_def[abs_def] assms)
      by (metis setter_getter_same setter_setter_same)
    fix Rep :: \<open>'c \<Rightarrow> 'b set\<close>
    define U where \<open>U = permute_and_tensor1_cblinfun_U Rep (getter F) (same_outside_cregister F)\<close>
    assume asm: \<open>(\<forall>A. sandwich U *\<^sub>V (A \<otimes>\<^sub>o id_cblinfun) =
                  permute_and_tensor1_cblinfun (getter F) (same_outside_cregister F) A)
          \<and> unitary U\<close>
    then have \<open>permute_and_tensor1_cblinfun (getter F) (same_outside_cregister F) = (sandwich U) o Laws_Quantum.Fst\<close>
      by (auto intro!: ext simp: Laws_Quantum.Fst_def)  
    moreover have \<open>qregister_raw \<dots>\<close>
      apply (rule Axioms_Quantum.register_comp)
      using asm by (simp_all add: unitary_sandwich_register)
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
  have *: \<open>Rep_ell2 (apply_qregister (qregister_of_cregister cFst) (butterket i j) *\<^sub>V ket x) y =
       Rep_ell2 (apply_qregister qFst (butterket i j) *\<^sub>V ket x) y\<close> (is \<open>?lhs = ?rhs\<close>)
    for i j :: 'a and x y :: \<open>'a \<times> 'c\<close>
  proof -
    obtain x1 x2 where x12: \<open>x = (x1, x2)\<close> by force
    obtain y1 y2 where y12: \<open>y = (y1, y2)\<close> by force
    have 1: \<open>inj_on fst (Collect (same_outside_cregister cFst x))\<close> for x :: \<open>'a \<times> 'c\<close>
      by (smt (verit) equivp_def equivp_same_outside_cregister getter_cFst inj_onI mem_Collect_eq same_outside_cregister_def)
    have \<open>?lhs = (if same_outside_cregister cFst y x then Rep_ell2 (butterket i j *\<^sub>V ket x1) y1 else 0)\<close>
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
  have \<open>apply_qregister (qregister_of_cregister cFst) (butterket i j) =
           apply_qregister qFst (butterket i j)\<close> for i j :: 'a
    by (auto intro!: equal_ket Rep_ell2_inject[THEN iffD1] ext simp: * )
  then show ?thesis
    by (auto intro!: apply_qregister_inject[THEN iffD1]
        weak_star_clinear_eq_butterfly_ketI[where T=weak_star_topology])
(*     using Axioms_Quantum.register_def cFst_register qregister.rep_eq qregister_qregister_of_cregister apply blast
    by (simp add: qFst.rep_eq weak_star_cont_register) *)
qed

lemma qregister_of_cregister_Snd: \<open>qregister_of_cregister cSnd = qSnd\<close>
proof -
  have *: \<open>Rep_ell2 (apply_qregister (qregister_of_cregister cSnd) (butterket i j) *\<^sub>V ket x) y =
       Rep_ell2 (apply_qregister qSnd (butterket i j) *\<^sub>V ket x) y\<close> (is \<open>?lhs = ?rhs\<close>)
    for i j :: 'a and x y :: \<open>'c \<times> 'a\<close>
  proof -
    obtain x1 x2 where x12: \<open>x = (x1, x2)\<close> by force
    obtain y1 y2 where y12: \<open>y = (y1, y2)\<close> by force
    have 1: \<open>inj_on snd (Collect (same_outside_cregister cSnd x))\<close> for x :: \<open>'c \<times> 'a\<close>
      by (smt (verit) equivp_def equivp_same_outside_cregister getter_cSnd inj_onI mem_Collect_eq same_outside_cregister_def)
    have \<open>?lhs = (if same_outside_cregister cSnd y x then Rep_ell2 (butterket i j *\<^sub>V ket x2) y2 else 0)\<close>
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
  have \<open>apply_qregister (qregister_of_cregister cSnd) (butterket i j) =
           apply_qregister qSnd (butterket i j)\<close> for i j :: 'a
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
  shows \<open>apply_qregister (qregister_of_cregister F) (butterket x y) (ket z) =
          of_bool (y = getter F z) *\<^sub>C ket (setter F x z)\<close>
proof (rule Rep_ell2_inject[THEN iffD1], rule ext)
  fix w
  have \<open>Rep_ell2 (apply_qregister (qregister_of_cregister F) (butterket x y) *\<^sub>V ket z) w
      = Rep_ell2 (permute_and_tensor1_cblinfun (getter F) (same_outside_cregister F) (butterket x y) (ket z)) w\<close>
    using \<open>cregister F\<close> by (simp add: apply_qregister_of_cregister)
  also have \<open>\<dots> = of_bool (same_outside_cregister F w z) * Rep_ell2 (butterket x y *\<^sub>V ket (getter F z)) (getter F w)\<close>
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
  finally show \<open>Rep_ell2 (apply_qregister (qregister_of_cregister F) (butterket x y) *\<^sub>V ket z) w
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

  have *: \<open>apply_qregister (qregister_of_cregister F) (butterket x y) *\<^sub>V apply_qregister (qregister_of_cregister G) (butterket x' y') *\<^sub>V ket z
      = apply_qregister (qregister_of_cregister G) (butterket x' y') *\<^sub>V apply_qregister (qregister_of_cregister F) (butterket x y) *\<^sub>V ket z\<close>
    for x y x' y' z
    by (auto simp add: apply_qregister_qregister_of_cregister_butterket)
  have *: \<open>apply_qregister (qregister_of_cregister F) (butterket x y) o\<^sub>C\<^sub>L apply_qregister (qregister_of_cregister G) (butterket x' y')
      = apply_qregister (qregister_of_cregister G) (butterket x' y') o\<^sub>C\<^sub>L apply_qregister (qregister_of_cregister F) (butterket x y)\<close>
    for x y x' y'
    apply (rule equal_ket)
    using *[of x y x' y']
    by simp
  have *: \<open>apply_qregister (qregister_of_cregister F) a o\<^sub>C\<^sub>L apply_qregister (qregister_of_cregister G) (butterket x' y')
      = apply_qregister (qregister_of_cregister G) (butterket x' y') o\<^sub>C\<^sub>L apply_qregister (qregister_of_cregister F) a\<close>
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
    have *: \<open>(apply_qregister (qregister_of_cregister F) (butterket a a') o\<^sub>C\<^sub>L apply_qregister (qregister_of_cregister G) (butterket b b')) *\<^sub>V ket m
      = (apply_qregister (qregister_of_cregister G) (butterket b b') o\<^sub>C\<^sub>L apply_qregister (qregister_of_cregister F) (butterket a a')) *\<^sub>V ket m\<close>
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
  have \<open>apply_qregister (qregister_of_cregister (cregister_pair x y)) (butterket k l) *\<^sub>V ket z =
        apply_qregister (qregister_pair (qregister_of_cregister x) (qregister_of_cregister y)) (butterket k l) *\<^sub>V ket z\<close> for k l z
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
  then have \<open>apply_qregister (qregister_of_cregister (cregister_pair x y)) (butterket k l) =
        apply_qregister (qregister_pair (qregister_of_cregister x) (qregister_of_cregister y)) (butterket k l)\<close> for k l
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
  have \<open>apply_qregister (qregister_of_cregister (cregister_chain x y)) (butterket k l) *\<^sub>V ket z =
        apply_qregister (qregister_chain (qregister_of_cregister x) (qregister_of_cregister y)) (butterket k l) *\<^sub>V ket z\<close> for k l z
    apply (auto intro!: Rep_ell2_inject[THEN iffD1] ext 
        simp add: apply_qregister_qregister_of_cregister_butterket getter_chain setter_chain)
     apply (auto simp add: apply_qregister_of_cregister permute_and_tensor1_cblinfun_ket
        permute_and_tensor1_cblinfun_exists_register ket.rep_eq same_outside_cregister_def
        scaleC_ell2.rep_eq cinner_ket zero_ell2.rep_eq)
     apply (metis getter_setter_same[OF \<open>cregister x\<close>])
    by (metis getter_setter_same[OF \<open>cregister x\<close>])
  then have \<open>apply_qregister (qregister_of_cregister (cregister_chain x y)) (butterket k l) =
        apply_qregister (qregister_chain (qregister_of_cregister x) (qregister_of_cregister y)) (butterket k l)\<close> for k l
    by (simp add: equal_ket)
  then show ?thesis
    apply (rule_tac qregister_eqI_separating[OF separating_butterket])
    by auto
next
  case False
  then show ?thesis
    by (auto simp add: non_cregister)
qed

end
