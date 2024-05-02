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


end
