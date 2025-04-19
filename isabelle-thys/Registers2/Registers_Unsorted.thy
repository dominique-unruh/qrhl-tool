theory Registers_Unsorted
  imports Quantum_From_Classical_Reg Quantum_Reg_Conversions Classical_Reg_Ranges
    Register_Syntax Registers_Automation
  keywords "debug_translate_to_index_registers" :: "diag"
begin

(* lemma distinct_cvars_split2: "cregister (cregister_pair S (cregister_pair Q R)) = (cregister (cregister_pair Q R) \<and> cregister (cregister_pair Q S) \<and> cregister (cregister_pair R S))"
  by (metis ccompatible3' ccompatible_sym)

lemma distinct_qvars_split2: "qregister (qregister_pair S (qregister_pair Q R)) \<longleftrightarrow> qregister (qregister_pair Q R) \<and> qregister (qregister_pair Q S) \<and> qregister (qregister_pair R S)"
  by (metis qcompatible3 qcompatible_sym) *)


(* TODO remove *)
lemma distinct_cvarsL: "cregister (cregister_pair Q R) \<Longrightarrow> cregister Q"
  by (rule ccompatible_register1)
lemma distinct_cvarsR: "cregister (cregister_pair Q R) \<Longrightarrow> cregister R"
  by (rule ccompatible_register2)
lemma distinct_qvarsL: "qregister (qregister_pair Q R) \<Longrightarrow> qregister Q"
  by (simp add: qcompatible_QQcompatible)
lemma distinct_qvarsR: "qregister (qregister_pair Q R) \<Longrightarrow> qregister R"
  by (simp add: qcompatible_def)


(* lemma TTIR_INVERSE_aux1:
  assumes \<open>qregister_chain Y X = qregister_id\<close>
  shows \<open>TTIR_INVERSE X Y\<close>
  by (simp add: TTIR_INVERSE_def assms qregister_left_right_inverse) *)


ML_file \<open>registers_unsorted.ML\<close>


method_setup translate_to_index_registers = \<open>
  Scan.succeed (fn ctxt => SIMPLE_METHOD (CONVERSION (Registers_Unsorted.translate_to_index_registers_conv ctxt 
        Registers_Unsorted.translate_to_index_registers_conv_default_options) 1))
\<close>

text \<open>Invocation: \<open>debug_translate_to_index_registers term for x y z and w z\<close>.
Meaning: x y z are assumed compatible, and so are w z.\<close>
ML \<open>
  Outer_Syntax.command \<^command_keyword>\<open>debug_translate_to_index_registers\<close> "try what translate_to_index_registers does to a subterm"
    ((Parse.term -- Scan.optional (Parse.$$$ "for" |-- Parse.!!! (Parse.and_list1 (Scan.repeat Parse.name))) []) >> 
  (fn (term_str,fixes) => Toplevel.keep (fn state => let
  val ctxt = Toplevel.context_of state
  val ctxt = Config.put Syntax.ambiguity_limit 0 ctxt
  val term_parsed = Syntax.parse_term ctxt term_str
  fun mk_tuple [] = error "unexpected"
    | mk_tuple [x] = Free(x,dummyT)
    | mk_tuple (x::xs) = \<^Const>\<open>qregister_pair dummyT dummyT dummyT\<close> $ mk_tuple [x] $ mk_tuple xs
  val assms_parsed = map (fn f => \<^Const>\<open>qregister dummyT dummyT\<close> $ mk_tuple f |> HOLogic.mk_Trueprop) fixes
  (* val _ = assms_parsed |> map (Syntax.string_of_term ctxt) |> map writeln *)
  val term :: assms = Syntax.check_terms ctxt (term_parsed :: assms_parsed)
  val ctxt = fold (fn assm => Context.proof_map (Registers_Unsorted.declare_register_simps_from_thm (Thm.assume (Thm.cterm_of ctxt assm)))) assms ctxt
  val ct = Thm.cterm_of ctxt term
  val rhs = Registers_Unsorted.translate_to_index_registers_conv ctxt Registers_Unsorted.translate_to_index_registers_conv_default_options ct |> Thm.rhs_of
  val result = Syntax.string_of_term ctxt (Thm.term_of rhs)
  val _ = writeln result
  in () end)));
\<close>

simproc_setup qregister_conversion_to_register (\<open>qregister_conversion x y\<close>) =
  \<open>fn m => fn ctxt => fn ct => \<^try>\<open>SOME (Registers_Unsorted.qregister_conversion_to_register_conv ctxt ct)
    catch e => NONE\<close>\<close>

(* TODO: check if we keep this mechanism. *)
definition \<open>JOIN_REGISTERS F G FG \<equiv> True\<close>

(* TODO: check if we keep this mechanism. *)
definition \<open>REGISTER_SOLVE x \<equiv> x\<close>
lemma REGISTER_SOLVER_cong[cong]: \<open>REGISTER_SOLVE x = REGISTER_SOLVE x\<close>
  by (rule refl)

named_theorems join_registers

(* TODO: remove or move *)
(* Indicates to the simplifier that the (schematic) variable x should be instantiated as y *)
definition \<open>INSTANTIATE_VARIABLE x y = True\<close>
lemma INSTANTIATE_VARIABLE_cong[cong]: \<open>INSTANTIATE_VARIABLE x y = INSTANTIATE_VARIABLE x y\<close>
  by simp
lemma INSTANTIATE_VARIABLE_instantiate: \<open>INSTANTIATE_VARIABLE x x\<close>
  by (simp add: INSTANTIATE_VARIABLE_def)
setup \<open>
map_theory_simpset (fn ctxt => ctxt
    addSolver 
      Simplifier.mk_solver "INSTANTIATE_VARIABLE" (fn ctxt => 
        resolve_tac ctxt @{thms INSTANTIATE_VARIABLE_instantiate}))\<close>

(* 
(* TODO outdated doc comment *)

Simproc that proves a goal of the form \<open>JOIN_REGISTERS F G ?H ?L\<close> where
  F G are qregisters and H,L will be instantiated.
  (Strictly speaking, they will not be instantiated because simprocs cannot do that.
   Instead, the JOIN_REGISTERS term will be rewritten into (?H=\<dots> \<and> ?L=\<dots>).
   Strictly speaking, H,L do not need to be schematic therefore.)

  Both H, L will instantiated to \<open>(\<lambda>F. register_conversion_hint FG F)\<close> where FG is an upper bound (not proven!)
  for F,G (w.r.t., qregister_le).

  (We have two variables H,L because they may need different types.)
  (* TODO: Do they? Do we have cases where the types are different? Let's see in the end and possibly simplify. *)
*)
(* simproc_setup JOIN_REGISTERS (\<open>JOIN_REGISTERS F G H L\<close>) = \<open>fn _ => fn ctxt => fn ct => let
  val (((F,G),H),L) = ct |> Thm.dest_comb |> apfst Thm.dest_comb |> apfst (apfst Thm.dest_comb) |> apfst (apfst (apfst Thm.dest_arg))
  val F' = Thm.term_of F val G' = Thm.term_of G
  val index = Prog_Variables.is_index_qregister F' andalso Prog_Variables.is_index_qregister G'
  val FG_option = if index then NONE else Prog_Variables.join_registers ctxt F' G' |> Option.map (Thm.cterm_of ctxt)
  in case FG_option of
    NONE => NONE
    | SOME FG =>
        SOME \<^instantiate>\<open>FG and F and G and H and L and 'f=\<open>Thm.ctyp_of_cterm F\<close> and 'g=\<open>Thm.ctyp_of_cterm G\<close> and
              'h=\<open>Thm.ctyp_of_cterm H |> Thm.dest_funT |> fst\<close> and 'l=\<open>Thm.ctyp_of_cterm L |> Thm.dest_funT |> fst\<close> and
              'fg=\<open>Thm.ctyp_of_cterm FG\<close> in
              lemma \<open>JOIN_REGISTERS (F::'f) (G::'g) (H::'h\<Rightarrow>'h) (L::'l\<Rightarrow>'l) \<equiv>
              H = (\<lambda>F. register_conversion_hint (FG::'fg) F) \<and> L = (\<lambda>F. register_conversion_hint FG F)\<close>
              by (auto simp add: JOIN_REGISTERS_def register_conversion_hint_def id_def)\<close> (* |> \<^print> *)
end\<close> *)
simproc_setup JOIN_REGISTERS (\<open>JOIN_REGISTERS F G FG\<close>) = \<open>fn _ => fn ctxt => fn ct => let
  val ((F,G),FG) = ct |> Thm.dest_comb |> apfst Thm.dest_comb |> apfst (apfst Thm.dest_arg)
  val F' = Thm.term_of F val G' = Thm.term_of G
  val FG_option = Registers_Unsorted.join_registers ctxt F' G' |> Option.map (Thm.cterm_of ctxt)
  (* val _ = \<^print> ("JOIN_REGISTERS", Option.map Thm.typ_of_cterm FG_option, Thm.typ_of_cterm FG) *)
  in case FG_option of
    NONE => NONE
    | SOME FG' =>
        SOME \<^instantiate>\<open>FG and FG' and F and G and 'f=\<open>Thm.ctyp_of_cterm F\<close> and 'g=\<open>Thm.ctyp_of_cterm G\<close> and
              'fg=\<open>Thm.ctyp_of_cterm FG\<close> and 'fg'=\<open>Thm.ctyp_of_cterm FG'\<close> in
              lemma \<open>JOIN_REGISTERS (F::'f) (G::'g) (FG::'fg) \<equiv> INSTANTIATE_VARIABLE FG (FG'::'fg')\<close>
              by (auto simp add: JOIN_REGISTERS_def INSTANTIATE_VARIABLE_def)\<close> (* |> \<^print> *)
end\<close>

(* TODO move to .ML *)
ML \<open>
(* ct is of the form REGISTER_SOLVE (X :: bool) *)
fun register_solve_simproc_of_tac ctxt tac ct = let
    val goal = ct |> Thm.dest_arg |> Thm.apply \<^cterm>\<open>Trueprop\<close>
(* val _ = goal |> Thm.term_of |> \<^print> *)
    val thm = SOME (Goal.prove_internal ctxt [] goal (fn _ => tac))
           (* handle _ => NONE *)
(* val _ = \<^print> thm *)
    val lemma = @{lemma \<open>X \<Longrightarrow> REGISTER_SOLVE X \<equiv> True\<close> by (simp add: REGISTER_SOLVE_def)}
    val eq = Option.map (fn thm => lemma OF [thm]) thm
(* val _ = \<^print> eq *)
  in eq end

(* TODO: support cregisters as well *)
fun register_solve_le_simproc (_:morphism) ctxt ct =
  case Thm.term_of ct of
    \<^Const_>\<open>REGISTER_SOLVE _\<close> $ (\<^Const_>\<open>qregister_le _ _ _\<close> $ _ $ _) =>
      register_solve_simproc_of_tac ctxt (Registers_Unsorted.qregister_le_tac ctxt 1) ct
\<close>

(* TODO: support cregisters as well *)
simproc_setup register_solve_le (\<open>REGISTER_SOLVE (qregister_le Q R)\<close>) = register_solve_le_simproc

definition \<open>NOT_INDEX_REGISTER x = True\<close>
lemma NOT_INDEX_REGISTER_cong[cong]: \<open>NOT_INDEX_REGISTER x = NOT_INDEX_REGISTER x\<close>
  by simp

simproc_setup NOT_INDEX_REGISTER (\<open>NOT_INDEX_REGISTER R\<close>) = \<open>fn _ => fn ctxt => fn ct => let
  val R = Thm.dest_arg ct
  in
      if Registers_Unsorted.is_index_qregister (Thm.term_of R) |> \<^print>
      then NONE
      else SOME \<^instantiate>\<open>R and 'r=\<open>Thm.ctyp_of_cterm R\<close> in lemma \<open>NOT_INDEX_REGISTER (R::'r) \<equiv> True\<close> by (simp add: NOT_INDEX_REGISTER_def)\<close> |> \<^print>
  end
\<close>


lemma apply_qregister_trace_class_transfer:
  assumes \<open>\<rho> \<noteq> 0\<close>
  assumes \<open>trace_class (apply_qregister Q \<rho>)\<close>
  assumes \<open>trace_class \<sigma>\<close>
  shows \<open>trace_class (apply_qregister Q \<sigma>)\<close>
proof -
  wlog \<open>qregister Q\<close>
    using negation by (simp add: non_qregister)
  from qregister_decomposition[OF this]
  have \<open>let 'c::type = qregister_decomposition_basis Q in
        trace_class (apply_qregister Q \<sigma>)\<close>
  proof with_type_mp
    with_type_case
    from with_type_mp.premise
    obtain U :: \<open>('a \<times> 'c) ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
      where \<open>unitary U\<close> and QU: \<open>Q = qregister_chain (transform_qregister U) qFst\<close>
      by auto
    let ?idc = \<open>id_cblinfun :: 'c ell2 \<Rightarrow>\<^sub>C\<^sub>L _\<close>
    have \<open>trace_class ?idc\<close>
    proof -
      from assms 
      have \<open>trace_class (sandwich U (\<rho> \<otimes>\<^sub>o ?idc))\<close>
        by (simp add: QU \<open>unitary U\<close> apply_qregister_fst transform_qregister.rep_eq)
      then have \<open>trace_class (sandwich (U*) (sandwich U (\<rho> \<otimes>\<^sub>o ?idc)))\<close>
        using trace_class_sandwich by blast
      then have \<open>trace_class (\<rho> \<otimes>\<^sub>o ?idc)\<close>
        by (simp add: unitaryD1 \<open>unitary U\<close> flip: cblinfun_apply_cblinfun_compose sandwich_compose)
      then show \<open>trace_class ?idc\<close>
        by (simp add: assms(1) trace_class_tensor_iff)
    qed
    then show \<open>trace_class (apply_qregister Q \<sigma>)\<close>
      by (auto intro!: trace_class_sandwich trace_class_tensor assms simp add: QU apply_qregister_fst transform_qregister.rep_eq \<open>unitary U\<close>)
  qed
  from this[cancel_with_type]
  show ?thesis
    by -
qed

definition qregister_co_dim :: \<open>('a,'b) qregister \<Rightarrow> real\<close> where
  \<open>qregister_co_dim Q = trace_norm (apply_qregister Q (selfbutter (ket undefined)))\<close>

lift_definition apply_qregister_tc :: \<open>('a,'b) qregister \<Rightarrow> ('a ell2, 'a ell2) trace_class \<Rightarrow> ('b ell2, 'b ell2) trace_class\<close> is
  \<open>\<lambda>Q. if qregister_co_dim Q \<noteq> 0 then apply_qregister Q else 0\<close>
proof (erule CollectE, rule CollectI, rename_tac Q t)
  fix Q :: \<open>('a, 'b) qregister\<close> and t :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'a ell2\<close>
  assume \<open>trace_class t\<close>
  have \<open>trace_class (apply_qregister Q t)\<close> if \<open>qregister_co_dim Q \<noteq> 0\<close>
  proof -
    from that have norm: \<open>trace_norm (apply_qregister Q (selfbutter (ket undefined))) \<noteq> 0\<close>
      by (simp add: qregister_co_dim_def)
    then have \<open>trace_class (apply_qregister Q (selfbutter (ket undefined)))\<close>
      apply (rule_tac ccontr)
      by (simp_all add: trace_norm_def)
    then show \<open>trace_class (apply_qregister Q t)\<close>
      apply (rule apply_qregister_trace_class_transfer[rotated])
      using norm \<open>trace_class t\<close> by auto
  qed
  then show \<open>trace_class ((if qregister_co_dim Q \<noteq> 0 then apply_qregister Q else 0) t)\<close>
    by simp
qed

(* TODO move *)
lemma iso_qregister_decomposition:
  assumes \<open>iso_qregister X\<close>
  shows \<open>\<exists>U. unitary U \<and> apply_qregister X = sandwich U\<close>
proof -
  have \<open>iso_register (apply_qregister X)\<close>
    using assms
    unfolding iso_qregister_def iso_register_def
    apply (transfer' fixing: )
    by auto
  from iso_register_decomposition[OF this]
  show ?thesis
    apply transfer' by auto
qed

lemma iso_qregister_co_dim: 
  assumes \<open>iso_qregister X\<close>
  shows \<open>qregister_co_dim X = 1\<close>
proof -
  from iso_qregister_decomposition[OF assms(1)]
  obtain U where \<open>unitary U\<close> and \<open>apply_qregister X = sandwich U\<close>
    by auto
  with assms show ?thesis
    by (simp add: trace_class_sandwich qregister_co_dim_def trace_butterfly trace_norm_sandwich_isometry trace_norm_butterfly)
qed

lemma apply_qregister_tc_codim0: \<open>qregister_co_dim Q = 0 \<Longrightarrow> apply_qregister_tc Q t = 0\<close>
  by (metis (mono_tags, lifting) apply_qregister_tc.rep_eq from_trace_class_inverse func_zero zero_trace_class_def)

(* TODO move *)
lemma apply_qregister_trace_class:
  assumes \<open>qregister_co_dim X \<noteq> 0\<close>
  assumes \<open>trace_class t\<close>
  shows \<open>trace_class (apply_qregister X t)\<close>
proof -
  from assms have norm: \<open>trace_norm (apply_qregister X (selfbutter (ket undefined))) \<noteq> 0\<close>
    by (simp add: qregister_co_dim_def)
  then have \<open>trace_class (apply_qregister X (selfbutter (ket undefined)))\<close>
    apply (rule_tac ccontr)
    by (simp_all add: trace_norm_def)
  then show \<open>trace_class (apply_qregister X t)\<close>
    apply (rule apply_qregister_trace_class_transfer[rotated])
    using norm \<open>trace_class t\<close> by auto
qed


(* TODO move *)
lemma apply_iso_qregister_trace_norm:
  assumes \<open>iso_qregister X\<close>
  shows \<open>trace_norm (apply_qregister X t) = trace_norm t\<close>
proof -
  from iso_qregister_decomposition[OF assms(1)]
  obtain U where \<open>unitary U\<close> and \<open>apply_qregister X = sandwich U\<close>
    by auto
  with assms show ?thesis
    by (metis apply_qregister_abs_op of_real_hom.injectivity trace_abs_op trace_sandwich_isometry unitary_isometry)
qed

lemma apply_iso_qregister_tc_norm:
  assumes \<open>iso_qregister X\<close>
  shows \<open>norm (apply_qregister_tc X t) = norm t\<close>
  apply (transfer' fixing: X)
  by (simp add: apply_iso_qregister_trace_norm assms iso_qregister_co_dim)


lemma apply_qregister_tc_0[simp]: \<open>apply_qregister_tc Q 0 = 0\<close>
  apply (transfer' fixing: Q)
  by auto


(* TODO move *)
lemma qregister_inv_non_qregister[simp]: \<open>qregister_inv non_qregister = non_qregister\<close>
  apply transfer
  using [[simproc del: Laws_Quantum.compatibility_warn]]
  using iso_register_is_register by auto

lemma qregister_inv_non_iso_qregister: 
  assumes \<open>\<not> iso_qregister Q\<close>
  shows \<open>qregister_inv Q = non_qregister\<close>
  using assms
  apply transfer'
  by simp

lemma apply_qregister_inv_inverse:
  assumes \<open>iso_qregister Q\<close>
  shows \<open>apply_qregister (qregister_inv Q) (apply_qregister Q a) = a\<close>
  using assms
  apply transfer'
  using iso_register_is_register register_inj by (auto intro!: inv_f_f simp: )

lemma apply_non_qregister_tc[simp]: \<open>apply_qregister_tc non_qregister x = 0\<close>
  apply transfer'
  by simp

lemma apply_qregister_sandwich:
  (* assumes \<open>qregister Q\<close> (* TODO remove *) *)
  shows \<open>apply_qregister Q (sandwich a b) = sandwich (apply_qregister Q a) (apply_qregister Q b)\<close>
  apply (cases \<open>qregister Q\<close>)
  using qregister.rep_eq register_sandwich apply blast
  by (simp add: non_qregister)


lemma apply_qregister_tc_sandwich:
  shows \<open>apply_qregister_tc Q (sandwich_tc a b) = sandwich_tc (apply_qregister Q a) (apply_qregister_tc Q b)\<close>
proof -
  wlog qreg: \<open>qregister Q\<close>
    using negation by (simp add: non_qregister)
  wlog dim: \<open>qregister_co_dim Q \<noteq> 0\<close> keeping qreg
    using negation by (simp add: apply_qregister_tc_codim0)
  show ?thesis
    using qreg
    apply (transfer' fixing: Q)
    by (simp add: dim apply_qregister_sandwich)
qed


lemma apply_qregister_tc_plus:
  \<open>apply_qregister_tc Q (t + u) = apply_qregister_tc Q t + apply_qregister_tc Q u\<close>
    apply transfer'
    by (simp add: apply_qregister_plus)

lemma apply_qregister_tc_scale:
  \<open>apply_qregister_tc Q (c *\<^sub>C t) = c *\<^sub>C apply_qregister_tc Q t\<close>
    apply transfer'
    by (simp add: apply_qregister_plus apply_qregister_scaleC)

lemma bounded_clinear_apply_qregister_tc[bounded_clinear]:
  assumes \<open>iso_qregister Q\<close>
    \<comment> \<open>This assumption is actually not needed\<close>
  shows \<open>bounded_clinear (apply_qregister_tc Q)\<close>
  apply (rule bounded_clinearI[where K=1])
  by (simp_all add: assms apply_iso_qregister_tc_norm apply_qregister_tc_scale apply_qregister_tc_plus)

lemma clinear_apply_qregister_tc:
  shows \<open>clinear (apply_qregister_tc Q)\<close>
  apply (rule clinearI)
  by (simp_all add: apply_qregister_tc_scale apply_qregister_tc_plus)

lemma bij_iso_qregister_tc:
  assumes \<open>iso_qregister Q\<close>
  shows \<open>bij (apply_qregister_tc Q)\<close>
proof (rule bijI)
  have \<open>qregister Q\<close>
    using assms iso_qregister_def' by blast
  then show \<open>inj (apply_qregister_tc Q)\<close>
    by (smt (verit) apply_qregister_inject' apply_qregister_tc.rep_eq assms from_trace_class_inverse inj_onI
        iso_qregister_co_dim)
  show \<open>surj (apply_qregister_tc Q)\<close>
    apply (rule surjI[where f=\<open>apply_qregister_tc (qregister_inv Q)\<close>])
    by (smt (verit, ccfv_SIG) apply_qregister_inv_inverse apply_qregister_tc.rep_eq assms from_trace_class_inverse iso_qregister_co_dim
        iso_qregister_inv_iso)
qed


lemma separating_set_bounded_clinear_iso_qregister_tc_nested:
  fixes Q :: \<open>('a,'b) qregister\<close> and S :: \<open>('a ell2, 'a ell2) trace_class set\<close>
  assumes \<open>iso_qregister Q\<close>
  assumes \<open>separating_set (bounded_clinear :: (_\<Rightarrow>'c::complex_normed_vector) \<Rightarrow> _) S\<close>
  shows \<open>separating_set (bounded_clinear :: (_\<Rightarrow>'c::complex_normed_vector) \<Rightarrow> _) (apply_qregister_tc Q ` S)\<close>
proof (intro separating_setI)
  fix f g :: \<open>('b ell2, 'b ell2) trace_class \<Rightarrow> 'c\<close>
  assume \<open>bounded_clinear f\<close> and \<open>bounded_clinear g\<close>
  assume fg_QS: \<open>f u = g u\<close> if \<open>u \<in> apply_qregister_tc Q ` S\<close> for u
  define f' g' where \<open>f' t = f (apply_qregister_tc Q t)\<close> and \<open>g' t = g (apply_qregister_tc Q t)\<close> for t
  have [iff]: \<open>bounded_clinear f'\<close>  \<open>bounded_clinear g'\<close>
    by (auto intro!: 
        comp_bounded_clinear[OF \<open>bounded_clinear f\<close>, unfolded o_def]
        comp_bounded_clinear[OF \<open>bounded_clinear g\<close>, unfolded o_def] 
        bounded_clinear_apply_qregister_tc assms
        simp: f'_def[abs_def] g'_def[abs_def])
  have \<open>f' t = g' t\<close> if \<open>t \<in> S\<close> for t
    by (simp add: f'_def fg_QS g'_def that)
  then have \<open>f' = g'\<close>
    apply (rule_tac eq_from_separatingI[OF assms(2)])
    by auto
  show \<open>f = g\<close>
  proof (rule ext)
    fix t :: \<open>('b ell2, 'b ell2) trace_class\<close>
    from assms have surj_Q: \<open>surj (apply_qregister_tc Q)\<close>
      by (meson bij_def bij_iso_qregister_tc)
    then obtain u where u: \<open>t = apply_qregister_tc Q u\<close>
      by fast
    with \<open>f' = g'\<close>
    have \<open>f' u = g' u\<close>
      by simp
    then show \<open>f t = g t\<close>
      by (simp add: f'_def g'_def u)
  qed
qed


lemma qregister_chain_apply_tc:
  assumes \<open>iso_qregister F\<close> and \<open>iso_qregister G\<close>
  shows \<open>apply_qregister_tc (qregister_chain F G) = apply_qregister_tc F o apply_qregister_tc G\<close>
  apply (transfer' fixing: F G)
  using assms
  by (simp add: iso_qregister_co_dim)

lemma apply_qregister_tc_id[simp]: \<open>apply_qregister_tc qregister_id = id\<close>
  apply transfer'
  by (simp add: iso_qregister_co_dim iso_qregister_def')


lemma apply_qregister_tc_transform_qregister: \<open>unitary U \<Longrightarrow> apply_qregister_tc (transform_qregister U) a = sandwich_tc U a\<close>
  apply (transfer' fixing: U)
  using apply_qregister_transform_qregister
  by (smt (verit, best) iso_qregister_co_dim iso_qregister_def' qregister_chain_transform_qregister qregister_transform_qregister
      transform_qregister_id unitary_adj unitary_def)

lemma iso_qregister_transform_qregister:
  assumes \<open>unitary U\<close>
  shows \<open>iso_qregister (transform_qregister U)\<close>
  by (metis assms iso_qregister_def' qregister_chain_transform_qregister qregister_transform_qregister transform_qregister_id
      unitary_adj unitary_def)

lemma inv_transform_qregister:
  assumes \<open>unitary U\<close>
  shows \<open>qregister_inv (transform_qregister U) = transform_qregister (U*)\<close>
proof -
  have [simp]: \<open>apply_qregister (transform_qregister U) = (*\<^sub>V) (sandwich U)\<close>
    by (simp add: assms transform_qregister.rep_eq)
  have [simp]: \<open>apply_qregister (transform_qregister (U*)) = (*\<^sub>V) (sandwich (U*))\<close>
    by (simp add: assms transform_qregister.rep_eq)
  have [simp]: \<open>inv ((*\<^sub>V) (sandwich U)) x = sandwich (U*) *\<^sub>V x\<close> for x
    by (smt (verit, ccfv_SIG) \<open>apply_qregister (transform_qregister (U*)) = (*\<^sub>V) (sandwich (U*))\<close>
        \<open>apply_qregister (transform_qregister U) = (*\<^sub>V) (sandwich U)\<close> apply_qregister_inv_inverse assms cblinfun_apply_cblinfun_compose
        cblinfun_compose_id_right iso_qregister_inv_iso_apply iso_qregister_transform_qregister sandwich_compose unitary_adj
        unitary_def)

  show ?thesis
    apply (rule qregister_eqI_separating)
     apply (rule separating_UNIV)
    apply (subst iso_qregister_inv_iso_apply)
    using assms apply (rule iso_qregister_transform_qregister)
    by simp
qed

lemma qregister_tensor_empty_empty[simp]: \<open>qregister_tensor empty_qregister empty_qregister = empty_qregister\<close>
  apply (rule empty_qregisters_same)
  by (simp add: qregister_qregister_tensor)

lemma swap_QREGISTER_bot[simp]: \<open>swap_QREGISTER (\<bottom> :: 'a QREGISTER) = id_cblinfun\<close>
proof -
  let ?empty = \<open>empty_qregister :: (unit,'a) qregister\<close>
  have \<open>swap_QREGISTER (\<bottom> :: 'a QREGISTER) = swap_QREGISTER (QREGISTER_of ?empty)\<close>
    by fastforce
  also have \<open>\<dots> = apply_qregister (qregister_tensor ?empty ?empty) swap_ell2\<close>
    using empty_qregister_is_register swap_QREGISTER_QREGISTER_of by blast
  also have \<open>\<dots> = id_cblinfun\<close>
    by simp
  finally show ?thesis
    by -
qed

lemma norm_swap_QREGISTER_01: \<open>norm (swap_QREGISTER Q) \<in> {0,1}\<close>
proof (cases \<open>card (Collect (is_swap_on_qupdate_set (Rep_QREGISTER Q))) = 1\<close>)
  case True
  have \<open>is_swap_on_qupdate_set (Rep_QREGISTER Q) (swap_QREGISTER Q)\<close>
    using the_default_memI[OF True, of 0]
    by (simp add: swap_QREGISTER.rep_eq)
  then have \<open>unitary (swap_QREGISTER Q)\<close>
    using is_swap_on_qupdate_set_def by blast
  then show ?thesis
    using unitary_norm_01 by auto
next
  case False
  have \<open>swap_QREGISTER Q = 0\<close>
    using the_default_default[OF False, of 0]
    by (simp add: swap_QREGISTER.rep_eq)
  then show ?thesis
    by simp
qed



end
