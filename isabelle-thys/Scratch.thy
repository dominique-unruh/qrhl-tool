theory Scratch
  imports QRHL.QRHL
begin

no_notation m_inv ("inv\<index> _" [81] 80)
unbundle no_vec_syntax
unbundle jnf_notation

derive (eq) ceq bit
derive (compare) ccompare bit
derive (dlist) set_impl bit

ML \<open>open Prog_Variables\<close>

lemma qregister_chain_pair_Fst[simp]:
  assumes \<open>qregister G\<close>
  shows \<open>qregister_chain (qregister_pair F G) qFst = F\<close>
  sorry

lemma qregister_chain_pair_Snd[simp]:
  assumes \<open>qregister F\<close>
  shows \<open>qregister_chain (qregister_pair F G) qSnd = G\<close>
  sorry

lemma qregister_chain_empty_right[simp]: \<open>qregister_chain F empty_qregister = empty_qregister\<close>
  sorry
lemma qregister_chain_empty_left[simp]: \<open>qregister_chain empty_qregister F = empty_qregister\<close>
  sorry

lemma qregister_chain_is_qregister[simp]: \<open>qregister (qregister_chain F G) \<longleftrightarrow> qregister F \<and> qregister G\<close>
  apply transfer
  by (auto simp: non_qregister_raw qregister_raw_chain)


ML \<open>
fun is_empty_qregisterT ctxt (\<^Type>\<open>qregister T _\<close>) = Sign.of_sort (Proof_Context.theory_of ctxt) (T,\<^sort>\<open>CARD_1\<close>)
  | is_empty_qregisterT _ T = raise TYPE("is_empty_qregisterT: not a qregister type", [T], [])
fun is_empty_qregister ctxt t = is_empty_qregisterT ctxt (fastype_of t)
  handle TYPE(_, Ts, _) => raise TYPE("is_empty_qregister: not a qregister type", Ts, [t])
fun mk_ct_equals ct1 ct2 = let
  val eq = \<^instantiate>\<open>'a=\<open>Thm.ctyp_of_cterm ct1\<close> in cterm Pure.eq\<close>
  in
    Thm.apply (Thm.apply eq ct1) ct2
  end
\<close>

lemma qcompatible_empty_left[simp]: \<open>qcompatible (U::(_::CARD_1,_) qregister) F \<longleftrightarrow> qregister U \<and> qregister F\<close>
  sorry
lemma qcompatible_empty_right[simp]: \<open>qcompatible F (U::(_::CARD_1,_) qregister) \<longleftrightarrow> qregister U \<and> qregister F\<close>
  sorry

lemma empty_qregisters_same: \<open>qregister F \<Longrightarrow> qregister G \<Longrightarrow> F = G\<close> for F G :: \<open>('a::CARD_1,'b) qregister\<close>
  sorry

definition explicit_cblinfun :: \<open>('a \<Rightarrow> 'b \<Rightarrow> complex) \<Rightarrow> ('b ell2, 'a ell2) cblinfun\<close> where
  \<open>explicit_cblinfun m = cblinfun_extension (range ket) (\<lambda>a. Abs_ell2 (\<lambda>j. m j (inv ket a)))\<close>

lemma explicit_cblinfun_ket[simp]: \<open>explicit_cblinfun m *\<^sub>V ket a = Abs_ell2 (\<lambda>b. m b a)\<close> for m :: "_ \<Rightarrow> _ :: finite \<Rightarrow> _"
  by (auto simp: cblinfun_extension_exists_finite_dim explicit_cblinfun_def cblinfun_extension_apply)

definition same_outside_cregister :: \<open>('a,'b) cregister \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool\<close> where
  \<open>same_outside_cregister F x y \<longleftrightarrow> x = setter F (getter F x) y\<close>

lemma same_outside_cregister_non_cregister[simp]: \<open>same_outside_cregister non_cregister = (=)\<close>
  unfolding same_outside_cregister_def
  by simp

lemma equivp_same_outside_cregister[simp]: \<open>equivp (same_outside_cregister F)\<close>
proof (cases \<open>cregister F\<close>)
  case False
  then have [simp]: \<open>F = non_cregister\<close>
    using non_cregister by force
  show ?thesis
    using identity_equivp by simp
next
  case True
  have \<open>reflp (same_outside_cregister F)\<close>
    by (simp add: same_outside_cregister_def reflpI)
  moreover have \<open>symp (same_outside_cregister F)\<close>
    by (metis same_outside_cregister_def setter_getter_same setter_setter_same sympI)
  moreover have \<open>transp (same_outside_cregister F)\<close>
    by (smt (verit, del_insts) same_outside_cregister_def setter_setter_same transpI)
  ultimately show ?thesis
    by (rule equivpI)
qed

lemma qregister_conversion_id[simp]: \<open>qregister_conversion F qregister_id = F\<close>
  apply transfer by auto


lemma register_conversion_non_reg_right[simp]: \<open>register_conversion F non_qregister = non_qregister\<close>
  apply transfer by (auto simp add: non_qregister_raw)

lemma register_conversion_non_reg_left[simp]: \<open>register_conversion non_qregister F = non_qregister\<close>
  apply transfer by (auto simp add: non_qregister_raw)

lemma inv_eq_move: \<open>inv f o g = h\<close> if \<open>inj f\<close> and \<open>g = f o h\<close> for f g
  using that(1) that(2) by fastforce

lemma qregister_conversion_rename: 
  fixes F :: \<open>('a,'c) qregister\<close> and G :: \<open>('b,'c) qregister\<close> and H :: \<open>('d, 'c) qregister\<close> and F' G'
  assumes \<open>qregister H\<close>
  assumes \<open>F = qregister_chain H F'\<close> \<open>G = qregister_chain H G'\<close>
  shows \<open>qregister_conversion F G = qregister_conversion F' G'\<close>
proof (cases \<open>qregister F'\<close>, cases \<open>qregister G'\<close>)
  assume \<open>\<not> qregister G'\<close>
  then have [simp]: \<open>G' = non_qregister\<close>
    using non_qregister by blast
  then show ?thesis
    apply (simp add: \<open>G = qregister_chain H G'\<close>)
    by -
next
  assume \<open>\<not> qregister F'\<close>
  then have [simp]: \<open>F' = non_qregister\<close>
    using non_qregister by blast
  then show ?thesis
    by (simp add: \<open>F = qregister_chain H F'\<close>)
next
  have range_le_preserve: \<open>range F' \<subseteq> range G'\<close> if \<open>range (\<lambda>x. H (F' x)) \<subseteq> range (\<lambda>x. H (G' x))\<close> and \<open>qregister_raw H\<close> 
    for H :: \<open>'d qupdate \<Rightarrow> 'c qupdate\<close> and F' :: \<open>'a qupdate \<Rightarrow> 'd qupdate\<close> and G' :: \<open>'b qupdate \<Rightarrow> 'd qupdate\<close>
    using qregister_raw_inj[OF \<open>qregister_raw H\<close>] using that(1)
    by (smt (verit, best) image_subset_iff inj_def rangeE rangeI)
  have H_cancel: \<open>inv (H \<circ> G') \<circ> (H \<circ> F') = inv G' \<circ> F'\<close> if \<open>qregister_raw H\<close> and \<open>qregister_raw G'\<close>
    and \<open>range F' \<subseteq> range G'\<close>
    for H :: \<open>'d qupdate \<Rightarrow> 'c qupdate\<close> and F' :: \<open>'a qupdate \<Rightarrow> 'd qupdate\<close> and G' :: \<open>'b qupdate \<Rightarrow> 'd qupdate\<close>
    apply (rule inv_eq_move)
    using qregister_raw_inj[OF \<open>qregister_raw H\<close>] qregister_raw_inj[OF \<open>qregister_raw G'\<close>]
    using inj_compose that by (auto simp add: ext f_inv_into_f subset_iff)
  assume [simp]: \<open>qregister F'\<close> \<open>qregister G'\<close>
  then show ?thesis
    using assms apply transfer
    using range_le_preserve H_cancel by (auto simp: qregister_raw_chain)
qed


lemma qregister_conversion_as_register: 
  fixes F :: \<open>('a,'c) qregister\<close> and F' G'
  assumes \<open>qregister G\<close>
  assumes \<open>F = qregister_chain G F'\<close>
  shows \<open>qregister_conversion F G = F'\<close>
  apply (subst qregister_conversion_rename[where H=G and G'=qregister_id and F'=F'])
  using assms by auto


lift_definition qregister_of_cregister :: \<open>('a,'b) cregister \<Rightarrow> ('a,'b) qregister\<close> is
  \<open>\<lambda>F a. if cregister F then 
      explicit_cblinfun (\<lambda>i j. if same_outside_cregister F i j then Rep_ell2 (a *\<^sub>V ket (getter F j)) (getter F i) else 0)
    else 0\<close>
  sorry

lemma apply_qregister_of_cregister:
  assumes \<open>cregister F\<close>
  shows \<open>apply_qregister (qregister_of_cregister F) a = explicit_cblinfun
            (\<lambda>i j. if same_outside_cregister F i j then Rep_ell2 (a \<cdot> ket (getter F j)) (getter F i) else 0)\<close>
  unfolding qregister_of_cregister.rep_eq using assms by simp


lemma qregister_of_cregister_Fst: \<open>qregister_of_cregister cFst = qFst\<close>
  sorry
lemma qregister_of_cregister_Snd: \<open>qregister_of_cregister cSnd = qSnd\<close>
  sorry

lemma qregister_qregister_of_cregister[simp]: \<open>qregister (qregister_of_cregister F) \<longleftrightarrow> cregister F\<close>
  sorry

lemma qcompatible_qregister_of_cregister[simp]: 
  \<open>qcompatible (qregister_of_cregister F) (qregister_of_cregister G) \<longleftrightarrow> ccompatible F G\<close>
  sorry

lemmas [simp] = qcompatible_Fst_Snd[unfolded qregister_of_cregister_Fst[symmetric]]
                          qcompatible_Fst_Snd[unfolded qregister_of_cregister_Snd[symmetric]]
                          qcompatible_Fst_Snd[unfolded qregister_of_cregister_Fst[symmetric] qregister_of_cregister_Snd[symmetric]]
                          qcompatible_Snd_Fst[unfolded qregister_of_cregister_Fst[symmetric]]
                          qcompatible_Snd_Fst[unfolded qregister_of_cregister_Snd[symmetric]]
                          qcompatible_Snd_Fst[unfolded qregister_of_cregister_Fst[symmetric] qregister_of_cregister_Snd[symmetric]]


ML \<open>
val qregister_conversion_to_register_conv_simpset = 
  \<^context> addsimps @{thms qregister_chain_pair qregister_chain_assoc[symmetric] 
                          qregister_of_cregister_Fst qregister_of_cregister_Snd
                          qvariable_unit_def empty_qregisters_same[OF _ empty_qregister_is_register]}
  |> simpset_of

\<close>

(* declare [[ML_source_trace]] *)
ML \<open>
fun qregister_conversion_to_register_conv ctxt ct = let
  val (lhs,rhs) = case Thm.term_of ct of Const(\<^const_name>\<open>qregister_conversion\<close>,_) $ lhs $ rhs => (lhs,rhs)
                                       | _ => raise CTERM ("qregister_conversion_to_register_conv: not a register conversion", [ct])
  val (rhs_inT, _) = dest_qregisterT (fastype_of rhs)
  fun add_to_path prefix path = if Term.is_dummy_pattern path then prefix else
    let val (prefix_inT, _) = Prog_Variables.dest_qregisterT (fastype_of prefix)
        val (path_inT, path_outT) = Prog_Variables.dest_qregisterT (fastype_of path)
    in \<^Const>\<open>qregister_chain path_inT path_outT prefix_inT\<close> $ path $ prefix end
  fun get_rhs_registers (\<^Const_>\<open>qregister_pair T1 _ T2\<close> $ r1 $ r2) path found = 
      found |> get_rhs_registers r1 (add_to_path \<^Const>\<open>qFst T1 T2\<close> path)
            |> get_rhs_registers r2 (add_to_path \<^Const>\<open>qSnd T2 T1\<close> path)
   | get_rhs_registers reg path found = 
      if is_empty_qregister ctxt reg then found
      else (reg,path) :: found
  val rhs_registers = get_rhs_registers rhs Term.dummy []
  fun map_lhs (Const(\<^const_name>\<open>qregister_pair\<close>,_) $ r1 $ r2) : term = let
    val r1' = map_lhs r1
    val r2' = map_lhs r2
    val (r1'in, r1'out) = dest_qregisterT (fastype_of r1')
    val (r2'in, _) = dest_qregisterT (fastype_of r2')
    in
      \<^Const>\<open>qregister_pair r1'in r1'out r2'in for r1' r2'\<close>
    end
    | map_lhs r = 
      if is_empty_qregister ctxt r
      then \<^Const>\<open>empty_qregister \<open>fastype_of r |> dest_qregisterT |> fst\<close> rhs_inT\<close>
      else
        (case AList.lookup (op aconv) rhs_registers r of
          NONE => raise TERM ("qregister_conversion_to_register_conv: could not find register from lhs in rhs", [r,Thm.term_of ct])
        | SOME path => path)
  val new_reg = map_lhs lhs |> Thm.cterm_of ctxt
  val new_reg = Conv.bottom_rewrs_conv @{thms qregister_chain_assoc[THEN eq_reflection]} ctxt new_reg |> Thm.rhs_of
  val goal = mk_ct_equals ct new_reg
  val outer_simpset = simpset_of ctxt
  val simpset_ctxt = ctxt 
          |> put_simpset qregister_conversion_to_register_conv_simpset
          (* |> Raw_Simplifier.set_subgoaler (fn ctxt => K (print_tac ctxt "xxx") THEN' simp_tac (put_simpset outer_simpset ctxt)) *)
          |> Raw_Simplifier.set_subgoaler (fn ctxt => distinct_vars_tac (put_simpset outer_simpset ctxt))
  val tac = resolve_tac ctxt @{thms qregister_conversion_as_register[THEN eq_reflection]} 1
            THEN
            distinct_vars_tac ctxt 1
            THEN
            Misc.succeed_or_error_tac' (SOLVED' (simp_tac simpset_ctxt))
            ctxt (fn t => "qregister_conversion_to_register_conv: cannot prove precondition for rewriting '" ^ 
                Syntax.string_of_term ctxt (Thm.term_of ct) ^ "' into a register:\n" ^ Syntax.string_of_term ctxt t) 1
  val thm = Goal.prove_internal ctxt [] goal (K tac)
in
  thm
end
\<close>

simproc_setup qregister_conversion_to_register (\<open>qregister_conversion x y\<close>) = 
  \<open>fn m => fn ctxt => fn ct => 
    SOME (qregister_conversion_to_register_conv ctxt ct)
    handle e => (tracing ("qregister_conversion_to_register: " ^ \<^make_string> e); NONE)\<close>


experiment
  fixes a b c :: \<open>bit qvariable\<close>
  assumes [variable]: \<open>qregister \<lbrakk>a,b,c\<rbrakk>\<close>
begin
ML \<open>
qregister_conversion_to_register_conv \<^context>
\<^cterm>\<open>\<lbrakk>a,\<lbrakk>\<rbrakk>,c \<mapsto> a,b,c,\<lbrakk>\<rbrakk>\<rbrakk>\<close>
\<close>
end


lemma cregister_chain_is_cregister[simp]: \<open>cregister (cregister_chain F G) \<longleftrightarrow> cregister F \<and> cregister G\<close>
  by (metis Cccompatible_CREGISTER_of Cccompatible_comp_right ccompatible_CCcompatible cregister.rep_eq cregister_chain.rep_eq non_cregister_raw)


lemma qregister_chain_pair_Fst_chain[simp]:
  assumes \<open>qregister G\<close>
  shows \<open>qregister_chain (qregister_pair F G) (qregister_chain qFst H) = qregister_chain F H\<close>
  by (metis Scratch.qregister_chain_pair_Fst assms qregister_chain_assoc)

lemma qregister_chain_pair_Snd_chain[simp]:
  assumes \<open>qregister F\<close>
  shows \<open>qregister_chain (qregister_pair F G) (qregister_chain qSnd H) = qregister_chain G H\<close>
  by (metis Scratch.qregister_chain_pair_Snd assms qregister_chain_assoc)


lemma qregister_chain_unit_right[simp]: \<open>qregister_chain F qvariable_unit = qvariable_unit\<close>
  by (simp add: qvariable_unit_def)
lemma qregister_chain_unit_left[simp]: \<open>qregister_chain qvariable_unit F = qvariable_unit\<close>
  by (simp add: qvariable_unit_def)


(* TODO: move to bounded operators *)
lemma Abs_ell2_inverse_finite[simp]: \<open>Rep_ell2 (Abs_ell2 \<psi>) = \<psi>\<close> for \<psi> :: \<open>_::finite \<Rightarrow> complex\<close>
  by (simp add: Abs_ell2_inverse)

lemma explicit_cblinfun_Rep_ket: \<open>Rep_ell2 (explicit_cblinfun m *\<^sub>V ket a) b = m b a\<close> for m :: "_ :: finite \<Rightarrow> _ :: finite \<Rightarrow> _"
  by simp


lemma non_cregister'[simp]: \<open>\<not> cregister non_cregister\<close>
  by (simp add: non_cregister)

lemma qregister_of_cregister_non_register: \<open>qregister_of_cregister non_cregister = non_qregister\<close>
proof -
  define t where \<open>t = non_cregister\<close>
  show \<open>qregister_of_cregister t = non_qregister\<close>
    apply (transfer fixing: t)
    apply (simp add: t_def)
    using non_qregister_raw_def by fastforce
qed

lemma qregister_of_cregister_compatible: \<open>ccompatible x y \<longleftrightarrow> qcompatible (qregister_of_cregister x) (qregister_of_cregister y)\<close>
  sorry
lemma qregister_of_cregister_pair: \<open>qregister_of_cregister (cregister_pair x y) = qregister_pair (qregister_of_cregister x) (qregister_of_cregister y)\<close>
  sorry
lemma qregister_of_cregister_chain: \<open>qregister_of_cregister (cregister_chain x y) = qregister_chain (qregister_of_cregister x) (qregister_of_cregister y)\<close>
  sorry


lemma getter_pair: 
  assumes \<open>cregister F\<close> \<open>cregister G\<close>
  shows \<open>getter (cregister_pair F G) = (\<lambda>m. (getter F m, getter G m))\<close>
  sorry

lemma setter_pair:
  assumes \<open>cregister F\<close> \<open>cregister G\<close>
  shows \<open>setter (cregister_pair F G) = (\<lambda>(x,y). setter F x o setter G y)\<close>
  sorry

lemma getter_chain:
  assumes \<open>cregister F\<close>
  shows \<open>getter (cregister_chain F G) = getter G o getter F\<close>
  sorry

lemma apply_qregister_Fst: \<open>apply_qregister qFst x = x \<otimes> id_cblinfun\<close>
  sorry

lemma apply_qregister_Snd: \<open>apply_qregister qSnd x = id_cblinfun \<otimes> x\<close>
  sorry



lemma butterfly_tensor: \<open>butterfly (a \<otimes> b) (c \<otimes> d) = butterfly a c \<otimes> butterfly b d\<close>
  sorry

lemma clinear_tensorOp_left[simp]: \<open>clinear (\<lambda>x. x \<otimes> y)\<close> for y :: \<open>(_,_) cblinfun\<close>
  sorry

lemma clinear_tensorOp_right[simp]: \<open>clinear (\<lambda>y. x \<otimes> y)\<close> for x :: \<open>(_,_) cblinfun\<close>
  sorry

lemma bounded_clinear_apply_qregister[simp]: \<open>bounded_clinear (apply_qregister F)\<close>
  apply transfer
  apply (auto simp: non_qregister_raw_def[abs_def])
  sorry

lemma clinear_apply_qregister[simp]: \<open>clinear (apply_qregister F)\<close>
  using bounded_clinear.clinear bounded_clinear_apply_qregister by blast

(* lemma qregister_chain_pair:
  shows "qregister_pair (qregister_chain F G) (qregister_chain F H) = qregister_chain F (qregister_pair G H)"
  sorry *)


lemma rew1: \<open>qregister_le F G \<Longrightarrow> apply_qregister F x = apply_qregister G (apply_qregister (qregister_conversion F G) x)\<close>
  apply (subst qregister_chain_conversion[where F=F and G=G, symmetric])
  by auto

lemma lepairI: \<open>qregister_le F H \<Longrightarrow> qregister_le G H \<Longrightarrow> qcompatible F G \<Longrightarrow> qregister_le (qregister_pair F G) H\<close>
  unfolding qregister_le_def
  sorry

lemma lepairI1: \<open>qregister_le F G \<Longrightarrow> qcompatible G H \<Longrightarrow> qregister_le F (qregister_pair G H)\<close>
  sorry
lemma lepairI2: \<open>qregister_le F H \<Longrightarrow> qcompatible G H \<Longrightarrow> qregister_le F (qregister_pair G H)\<close>
  sorry
lemma lerefl: \<open>qregister F \<Longrightarrow> qregister_le F F\<close>
  unfolding qregister_le_def by simp

lemma qregister_conversion_chain: 
  assumes \<open>qregister_le F G\<close> \<open>qregister_le G H\<close>
  shows \<open>qregister_chain (qregister_conversion G H) (qregister_conversion F G) = qregister_conversion F H\<close>
  using assms unfolding qregister_le_def apply (transfer fixing: F G H) apply transfer
  by (auto intro!: ext qregister_conversion_raw_register simp: f_inv_into_f range_subsetD)

lemma tensor_ext2: 
  assumes \<open>\<And>x y. apply_qregister F (x\<otimes>y) = apply_qregister G (x\<otimes>y)\<close>
  shows \<open>F = G\<close>
  sorry

lemma tensor_ext3: 
  assumes \<open>\<And>x y z. apply_qregister F (x\<otimes>y\<otimes>z) = apply_qregister G (x\<otimes>y\<otimes>z)\<close>
  shows \<open>F = G\<close>
  sorry

lemma qcompatible_Abs_qregister[simp]:
  assumes \<open>qregister_raw F\<close> \<open>qregister_raw G\<close>
  (* assumes \<open>qcommuting_raw F G\<close> *)
  shows \<open>qcompatible (Abs_qregister F) (Abs_qregister G) \<longleftrightarrow> qcommuting_raw F G\<close>
  using assms by (simp add: eq_onp_same_args qcompatible.abs_eq qcompatible_raw_def qcommuting_raw_def)

lemma qcompatible_Abs_qregister_id_tensor_left[simp]:
  shows \<open>qcommuting_raw (\<lambda>x. id_cblinfun \<otimes> f x) (\<lambda>x. g x \<otimes> id_cblinfun)\<close>
  by (auto simp: qcommuting_raw_def)

lemma qcompatible_Abs_qregister_id_tensor_right[simp]:
  shows \<open>qcommuting_raw (\<lambda>x. g x \<otimes> id_cblinfun) (\<lambda>x. id_cblinfun \<otimes> f x)\<close>
  by (auto simp: qcommuting_raw_def)

lemma qcompatible_Abs_qregister_id_tensor_idid_tensor_left[simp]:
  shows \<open>qcommuting_raw (\<lambda>x. id_cblinfun \<otimes> f x) (\<lambda>x. id_cblinfun \<otimes> g x) \<longleftrightarrow> qcommuting_raw f g\<close>
  sorry

lemma qcompatible_Abs_qregister_id_tensor_idid_tensor_right[simp]:
  shows \<open>qcommuting_raw (\<lambda>x. f x \<otimes> id_cblinfun) (\<lambda>x. g x \<otimes> id_cblinfun) \<longleftrightarrow> qcommuting_raw f g\<close>
  sorry

lemma qregister_raw_tensor_left[simp]:
  shows \<open>qregister_raw (\<lambda>x. id_cblinfun \<otimes> F x) \<longleftrightarrow> qregister_raw F\<close>
  sorry

lemma qregister_raw_tensor_right[intro!, simp]:
  shows \<open>qregister_raw (\<lambda>x. F x \<otimes> id_cblinfun) \<longleftrightarrow> qregister_raw F\<close>
  sorry

lemma qregister_raw_id'[simp]: \<open>qregister_raw (\<lambda>x. x)\<close>
  by (metis eq_id_iff qregister_raw_id)



lemma mat_of_cblinfun_explicit_cblinfun[code,simp]:
  fixes m :: \<open>'a::enum \<Rightarrow> 'b::enum \<Rightarrow> complex\<close>
  defines \<open>m' \<equiv> (\<lambda>(i,j). m (Enum.enum!i) (Enum.enum!j))\<close>
  shows \<open>mat_of_cblinfun (explicit_cblinfun m) = mat CARD('a) CARD('b) m'\<close> 
proof (rule eq_matI)
  fix i j
  assume \<open>i < dim_row (mat CARD('a) CARD('b) m')\<close> \<open>j < dim_col (mat CARD('a) CARD('b) m')\<close>
  then have ij[simp]: \<open>i < CARD('a)\<close> \<open>j < CARD('b)\<close>
    by auto
  have \<open>m (enum_class.enum ! i) (enum_class.enum ! j) = m' (i, j)\<close>
    by (auto simp: m'_def)
  then show \<open>mat_of_cblinfun (explicit_cblinfun m) $$ (i, j) = Matrix.mat CARD('a) CARD('b) m' $$ (i, j)\<close>
    by (simp add: mat_of_cblinfun_ell2_component)
next
  show \<open>dim_row (mat_of_cblinfun (explicit_cblinfun m)) = dim_row (Matrix.mat CARD('a) CARD('b) m')\<close> by simp
  show \<open>dim_col (mat_of_cblinfun (explicit_cblinfun m)) = dim_col (Matrix.mat CARD('a) CARD('b) m')\<close> by simp
qed

definition reorder_cblinfun :: \<open>('d \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'a) \<Rightarrow> ('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2) \<Rightarrow> ('c ell2 \<Rightarrow>\<^sub>C\<^sub>L 'd ell2)\<close> where
  \<open>reorder_cblinfun r c A = explicit_cblinfun (\<lambda>i j. Rep_ell2 (A *\<^sub>V ket (c j)) (r i))\<close>

abbreviation "reorder_cblinfun2 f \<equiv> reorder_cblinfun f f"

lemma reorder_cblinfun_ket[simp]: \<open>Rep_ell2 (reorder_cblinfun r c A *\<^sub>V ket a) b = Rep_ell2 (A *\<^sub>V ket (c a)) (r b)\<close> for a b :: \<open>_::finite\<close>
  by (simp add: reorder_cblinfun_def)


lemma clinear_reorder_cblinfun[simp]: \<open>clinear (reorder_cblinfun r c)\<close> for r c :: \<open>_::finite \<Rightarrow> _\<close>
proof (rule clinearI)
  show \<open>reorder_cblinfun r c (A + B) = reorder_cblinfun r c A + reorder_cblinfun r c B\<close> for A B
    apply (rule equal_ket)
    by (auto simp: plus_ell2.rep_eq cblinfun.add_left simp flip: Rep_ell2_inject)
  show \<open>reorder_cblinfun r c (s *\<^sub>C A) = s *\<^sub>C reorder_cblinfun r c A\<close> for s A
    apply (rule equal_ket)
    by (auto simp: scaleC_ell2.rep_eq simp flip: Rep_ell2_inject)
qed

lemma reorder_cblinfun_butterfly: 
  fixes r c :: \<open>_::finite \<Rightarrow> _::finite\<close>
  assumes \<open>bij r\<close> \<open>bij c\<close>
  shows \<open>reorder_cblinfun r c (butterket a b) = butterket (inv r a) (inv c b)\<close>
proof (rule equal_ket, rule Rep_ell2_inject[THEN iffD1], rule ext)
  fix i j
  have \<open>Rep_ell2 (reorder_cblinfun r c (butterket a b) \<cdot> ket i) j = Rep_ell2 ((ket b \<bullet>\<^sub>C ket (c i)) *\<^sub>C ket a) (r j)\<close>
    by auto
  also have \<open>\<dots> = (if b=c i then 1 else 0) * (if a=r j then 1 else 0)\<close>
    by (simp add: scaleC_ell2.rep_eq ket.rep_eq)
  also have \<open>\<dots> = (if inv c b=i then 1 else 0) * (if inv r a=j then 1 else 0)\<close>
    by (smt (verit, del_insts) assms(1) assms(2) bij_inv_eq_iff)
  also have \<open>\<dots> = Rep_ell2 ((ket (inv c b) \<bullet>\<^sub>C ket i) *\<^sub>C ket (inv r a)) j\<close>
    by (simp add: scaleC_ell2.rep_eq ket.rep_eq)
  also have \<open>\<dots> = Rep_ell2 (butterket (inv r a) (inv c b) \<cdot> ket i) j\<close>
    by auto
  finally show \<open>Rep_ell2 (reorder_cblinfun r c (butterket a b) \<cdot> ket i) j = Rep_ell2 (butterket (inv r a) (inv c b) \<cdot> ket i) j\<close>
    by -
qed

lemma reorder_cblinfun2_butterfly: 
  fixes f :: \<open>_::finite \<Rightarrow> _::finite\<close>
  assumes \<open>bij f\<close>
  shows \<open>reorder_cblinfun2 f (butterket a b) = butterket (inv f a) (inv f b)\<close>
  by (simp add: assms reorder_cblinfun_butterfly)

definition reorder_mat :: \<open>nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> complex mat \<Rightarrow> complex mat\<close> where 
  \<open>reorder_mat n m r c A = Matrix.mat n m (\<lambda>(i, j). A $$ (r i, c j))\<close>

(* TODO: to bounded operators *)
declare enum_idx_correct[simp]

lemma mat_of_cblinfun_reorder[code]: 
  fixes r :: \<open>'a::enum \<Rightarrow> 'c::enum\<close> and c :: \<open>'b::enum \<Rightarrow> 'd::enum\<close>
  shows \<open>mat_of_cblinfun (reorder_cblinfun r c A) = reorder_mat CARD('a) CARD('b)
(\<lambda>i. enum_idx (r (enum_class.enum ! i))) (\<lambda>j. enum_idx (c (enum_class.enum ! j))) (mat_of_cblinfun A)\<close>
proof -
  have aux: \<open>Rep_ell2 \<psi> i = vec_of_basis_enum \<psi> $ (enum_idx i)\<close> if \<open>enum_idx i < CARD('z)\<close> 
    for \<psi> :: \<open>'z::enum ell2\<close> and i
    apply (subst vec_of_basis_enum_ell2_component)
    using that by auto

  show ?thesis
    apply (subst reorder_cblinfun_def)
    apply (subst mat_of_cblinfun_explicit_cblinfun)
    apply (subst aux)
     apply (simp add: card_UNIV_length_enum enum_idx_bound)
    apply (subst mat_of_cblinfun_cblinfun_apply)
    apply (subst vec_of_basis_enum_ket)
    apply (subst mat_entry_explicit)
    by (auto simp add: card_UNIV_length_enum enum_idx_bound reorder_mat_def)
qed

lemma enum_idx_correct': \<open>enum_idx (enum_class.enum ! i :: 'a::enum) = i\<close> if \<open>i < CARD('a)\<close>
  sorry

definition \<open>enum_idx_enum_nth_code n (_::'a::enum itself) i = (if i < n then i else 
    Code.abort STR ''enum_idx_enum_nth_code: index out of bounds'' (\<lambda>_. enum_idx (enum_class.enum ! i :: 'a)))\<close>

lemma enum_idx_enum_nth_code: \<open>enum_idx (enum_class.enum ! i :: 'a::enum) = enum_idx_enum_nth_code CARD('a) TYPE('a) i\<close>
  unfolding enum_idx_enum_nth_code_def
  apply (cases \<open>i < CARD('a)\<close>)
   apply (subst enum_idx_correct', simp, simp)
  by auto

lemma enum_idx_pair: \<open>enum_idx (a,b) = enum_idx a * CARD('b) + enum_idx b\<close> for a :: \<open>'a::enum\<close> and b :: \<open>'b::enum\<close>
proof -
  let ?enumab = \<open>Enum.enum :: ('a \<times> 'b) list\<close>
  let ?enuma = \<open>Enum.enum :: 'a list\<close>
  let ?enumb = \<open>Enum.enum :: 'b list\<close>
  have bound: \<open>i < CARD('a) \<Longrightarrow> j < CARD('b) \<Longrightarrow> i * CARD('b) + j < CARD('a) * CARD('b)\<close> for i j
    sorry
  have *: \<open>?enumab ! (i * CARD('b) + j) = (?enuma ! i, ?enumb ! j)\<close> 
    if \<open>i < CARD('a)\<close> \<open>j < CARD('b)\<close> for i j
    unfolding enum_prod_def 
    apply (subst List.product_nth)
    using that bound by (auto simp flip: card_UNIV_length_enum)
  note ** = *[where i=\<open>enum_idx a\<close> and j=\<open>enum_idx b\<close>, simplified, symmetric]
  show ?thesis
    apply (subst **)
    using enum_idx_bound[of a] enum_idx_bound[of b]
    by (auto simp: bound enum_idx_correct' simp flip: card_UNIV_length_enum)
qed

lemma enum_idx_fst: \<open>enum_idx (fst ab) = enum_idx ab div CARD('b)\<close> for ab :: \<open>'a::enum \<times> 'b::enum\<close>
  apply (cases ab, hypsubst_thin)
  apply (subst enum_idx_pair)
  using enum_idx_bound
  by (auto intro!: div_less simp flip: card_UNIV_length_enum)

lemma enum_idx_snd: \<open>enum_idx (snd ab) = enum_idx ab mod CARD('b)\<close> for ab :: \<open>'a::enum \<times> 'b::enum\<close>
  apply (cases ab, hypsubst_thin)
  apply (subst enum_idx_pair)
  using enum_idx_bound
  by (auto intro!: mod_less[symmetric] simp flip: card_UNIV_length_enum)

term qregister_pair

lemma prod_eqI': \<open>x = fst z \<Longrightarrow> y = snd z \<Longrightarrow> (x,y) = z\<close>
  by auto

lemma [code]: \<open>vec_of_ell2 (Abs_ell2 f) = vec CARD('a) (\<lambda>n. f (Enum.enum ! n))\<close> for f :: \<open>'a::enum \<Rightarrow> complex\<close>
  by (auto simp: vec_of_ell2_def vec_eq_iff vec_of_basis_enum_ell2_component)

lemma [code]: \<open>Rep_ell2 \<psi> i = vec_of_ell2 \<psi> $ (enum_idx i)\<close> for i :: \<open>'a::enum\<close>
  by (auto simp: vec_of_ell2_def vec_eq_iff vec_of_basis_enum_ell2_component card_UNIV_length_enum enum_idx_bound)

experiment fixes a :: \<open>bool qvariable\<close> and b :: \<open>bit qvariable\<close> and c :: \<open>3 qvariable\<close> and d :: \<open>3 qvariable\<close>
  assumes xxx[variable]: \<open>qregister \<lbrakk>a,b,c,d\<rbrakk>\<close> begin

ML \<open>
is_empty_qregister \<^context> \<^term>\<open>bla :: 1 qvariable\<close>
\<close>

lemmas xxxy = [[ML_thm \<open>K (K @{thm refl})\<close>]]

(* declare [[ML_source_trace]] *)
ML \<open>
mk_ct_equals \<^cterm>\<open>1::nat\<close> \<^cterm>\<open>2::nat\<close>
\<close>


thm empty_qregisters_same[OF _ empty_qregister_is_register]



lemma Test
proof -
  fix a b c

  have t[variable]: \<open>qregister (\<lbrakk>a,b,c\<rbrakk> :: (bit*bit*bit) qvariable)\<close> sorry

  have le: \<open>\<lbrakk>a,c \<le> a,b,c\<rbrakk>\<close>
    by (auto intro!: lepairI lerefl simp: lepairI1 lepairI2 lepairI lerefl)

  define CNOT' where \<open>CNOT' = apply_qregister \<lbrakk>a,c \<mapsto> a,b,c\<rbrakk> CNOT\<close>

  have \<open>apply_qregister \<lbrakk>a,c\<rbrakk> CNOT = apply_qregister \<lbrakk>a,b,c\<rbrakk> CNOT'\<close>
    apply (subst rew1[where G=\<open>\<lbrakk>a,b,c\<rbrakk>\<close>])
     apply (fact le)
    by (simp add: CNOT'_def)

  have \<open>variable_concat a c =
                                   register_chain (variable_concat a (variable_concat b c))
                                    (variable_concat Fst (register_chain Snd Snd))\<close>
    apply (subst
                  qregister_chain_pair qregister_chain_assoc[symmetric] 
                  qregister_of_cregister_Fst qregister_of_cregister_Snd
                  qvariable_unit_def empty_qregisters_same[OF _ empty_qregister_is_register], simp)+
    by -

  have \<open>CNOT' *\<^sub>V ket (1,1,1) = (ket (1,1,0) :: (bit*bit*bit) ell2)\<close>
    unfolding CNOT'_def
    using if_weak_cong[cong del] apply fail?

    apply (simp 

        add:  apply_qregister_of_cregister getter_pair getter_chain setter_chain setter_pair setter_Fst
              case_prod_beta setter_Snd
          
              same_outside_cregister_def
              prod_eq_iff

        flip: qregister_of_cregister_Fst qregister_of_cregister_Snd
        qregister_of_cregister_pair qregister_of_cregister_chain

    )
    by normalization


  oops
