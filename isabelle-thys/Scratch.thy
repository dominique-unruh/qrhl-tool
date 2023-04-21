theory Scratch
  imports QRHL
 (* "HOL-ex.Sketch_and_Explore" *) 
(* "HOL-Eisbach.Eisbach" *)
(* QRHL_Operations  *)
begin

no_notation eq_closure_of ("closure'_of\<index>")

ML "open Prog_Variables"



abbreviation \<open>upfst x \<equiv> apfst (\<lambda>_. x)\<close>
abbreviation \<open>upsnd x \<equiv> apsnd (\<lambda>_. x)\<close>

(* lemma valid_qregister_range_raw:
  assumes \<open>qregister_raw F\<close>
  shows \<open>valid_qregister_range (range F)\<close>
  by (simp add: assms valid_qregister_range_UNIV valid_qregister_range_pres_raw) *)

lemma INDEX_REGISTER_norm_conv_aux2: \<open>QREGISTER_pair (QREGISTER_chain A F) (QREGISTER_pair (QREGISTER_chain A G) B)
            = QREGISTER_pair B (QREGISTER_chain A (QREGISTER_pair F G))\<close>
  apply (simp flip: QREGISTER_pair_QREGISTER_chain)
  using QREGISTER_pair_assoc QREGISTER_pair_sym
  by metis

lemma INDEX_REGISTER_norm_conv_aux1: \<open>QREGISTER_pair (QREGISTER_chain A F) (QREGISTER_pair B (QREGISTER_chain A G))
            = QREGISTER_pair B (QREGISTER_chain A (QREGISTER_pair F G))\<close>
  apply (simp flip: QREGISTER_pair_QREGISTER_chain)
  using QREGISTER_pair_assoc QREGISTER_pair_sym
  by metis


ML \<open>
(* Brings an INDEX-REGISTER into normal form. *)
local
  val rules = (map (fn thm => thm RS @{thm eq_reflection}) @{thms 
    INDEX_REGISTER_norm_conv_aux1 QREGISTER_pair_QREGISTER_chain QREGISTER_pair_assoc 
    INDEX_REGISTER_norm_conv_aux2 QREGISTER_pair_unit_left 
    QREGISTER_pair_unit_right
    QREGISTER_chain_id_left QREGISTER_chain_all_right
    QREGISTER_pair_all_left QREGISTER_pair_all_right
    QREGISTER_pair_fst_snd QREGISTER_pair_snd_fst
    QREGISTER_chain_unit_left QREGISTER_chain_unit_right})
in
fun INDEX_REGISTER_norm_conv ctxt = Raw_Simplifier.rewrite ctxt false rules
end
\<close>

ML \<open>
(* Converts "QREGISTER_of F" for index register F into an INDEX-REGISTER.
   An INDEX-REGISTER is a QREGISTER built from
  "QREGISTER_chain QREGISTER_pair QREGISTER_fst QREGISTER_snd qFst qSnd QREGISTER_all QREGISTER_unit".
(While keeping the structure of the index-register. That is, can be undone be QREGISTER_of_index_reg_reverse_conv.)
 *)
val QREGISTER_of_index_reg_conv =
  Misc.rewrite_with_prover (fn ctxt => distinct_vars_tac ctxt 1)
    (map (fn thm => thm RS @{thm eq_reflection})
          @{thms 
            QREGISTER_of_qregister_pair QREGISTER_of_qregister_chain QREGISTER_of_empty_qregister
            QREGISTER_of_qFst QREGISTER_of_qSnd QREGISTER_of_qregister_id})
\<close>

lemma z1:
  assumes F: \<open>qregister F\<close>
  assumes CF: \<open>QCOMPLEMENT (QREGISTER_of F) = QREGISTER_of G\<close>
  assumes G: \<open>qregister G\<close>
  shows \<open>qcomplements F G\<close>
  using F apply (rule qcomplements_via_rangeI)
  using assms(2)[THEN Rep_QREGISTER_inject[THEN iffD2]]
  by (simp add: uminus_QREGISTER.rep_eq QREGISTER_of.rep_eq F G)


(* TODO: Just add an assumption and a comment that the assumption is not strictly necessary by Takesaki? *)
lemma y2:
  assumes \<open>ACTUAL_QREGISTER F\<close> \<open>ACTUAL_QREGISTER G\<close> (* TODO comment on assumptions *)
  shows \<open>QCOMPLEMENT (QREGISTER_pair (QREGISTER_chain qFst F) (QREGISTER_chain qSnd G))
    = QREGISTER_pair (QREGISTER_chain qFst (QCOMPLEMENT F)) (QREGISTER_chain qSnd (QCOMPLEMENT G))\<close>
(* 
  apply (rule Rep_QREGISTER_inject[THEN iffD1])
  apply (simp add: uminus_QREGISTER.rep_eq Rep_QREGISTER_pair_fst_snd)
  apply (subst commutant_tensor_vn)
  using Rep_QREGISTER Rep_QREGISTER
  by (force simp add: valid_qregister_range_def)+
 *)
proof -
  let ?goal = ?thesis
  from ACTUAL_QREGISTER_ex_register[OF \<open>ACTUAL_QREGISTER F\<close>]
  have \<open>\<forall>\<^sub>\<tau> 'f::type = ACTUAL_QREGISTER_content F. ?goal\<close>
  proof (rule with_type_mp)
    assume \<open>\<exists>A :: ('f, 'a) qregister. qregister A \<and> QREGISTER_of A = F\<close>
    then obtain A :: \<open>('f, 'a) qregister\<close> where [simp]: \<open>qregister A\<close> and qregF: \<open>QREGISTER_of A = F\<close>
      by auto
    from ACTUAL_QREGISTER_ex_register[OF \<open>ACTUAL_QREGISTER G\<close>]
    have \<open>\<forall>\<^sub>\<tau> 'g::type = ACTUAL_QREGISTER_content G. ?goal\<close>
    proof (rule with_type_mp)
      assume \<open>\<exists>B :: ('g, 'b) qregister. qregister B \<and> QREGISTER_of B = G\<close>
      then obtain B :: \<open>('g, 'b) qregister\<close> where [simp]: \<open>qregister B\<close> and qregG: \<open>QREGISTER_of B = G\<close>
        by auto
      from qcomplement_exists[OF \<open>qregister A\<close>]
      have \<open>\<forall>\<^sub>\<tau> 'i::type = qregister_decomposition_basis A. ?goal\<close>
      proof (rule with_type_mp)
        assume \<open>\<exists>AC :: ('i, 'a) qregister. qcomplements A AC\<close>
        then obtain AC :: \<open>('i, 'a) qregister\<close> where \<open>qcomplements A AC\<close>
          by auto
        from qcomplement_exists[OF \<open>qregister B\<close>]
        have \<open>\<forall>\<^sub>\<tau> 'j::type = qregister_decomposition_basis B. ?goal\<close>
        proof (rule with_type_mp)
          assume \<open>\<exists>BC :: ('j, 'b) qregister. qcomplements B BC\<close>
          then obtain BC :: \<open>('j, 'b) qregister\<close> where \<open>qcomplements B BC\<close>
            by auto
          from \<open>qcomplements A AC\<close>
          have [simp]: \<open>qregister AC\<close>
            using iso_qregister_def qcompatible_register2 qcomplements_def' by blast
          from \<open>qcomplements A AC\<close>
          have [simp]: \<open>qcompatible A AC\<close>
            using iso_qregister_def qcomplements_def' by blast
          from \<open>qcomplements B BC\<close>
          have [simp]: \<open>qregister BC\<close>
            using iso_qregister_def qcompatible_register2 qcomplements_def' by blast
          from \<open>qcomplements B BC\<close>
          have [simp]: \<open>qcompatible B BC\<close>
            using iso_qregister_def qcomplements_def' by blast
          have [simp]: \<open>iso_qregister \<lbrakk>A, AC\<rbrakk>\<close>
            using \<open>qcomplements A AC\<close> qcomplements_def' by blast
          have [simp]: \<open>iso_qregister \<lbrakk>B, BC\<rbrakk>\<close>
            using \<open>qcomplements B BC\<close> qcomplements_def' by blast
          have QCOMPLEMENT_A: \<open>QCOMPLEMENT (QREGISTER_of A) = QREGISTER_of AC\<close>
            by (auto intro!: QCOMPLEMENT_QREGISTER_of_eqI \<open>qcomplements A AC\<close>)
          have QCOMPLEMENT_B: \<open>QCOMPLEMENT (QREGISTER_of B) = QREGISTER_of BC\<close>
            by (auto intro!: QCOMPLEMENT_QREGISTER_of_eqI \<open>qcomplements B BC\<close>)
          have \<open>qcomplements \<lbrakk>qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q A, qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q B\<rbrakk>\<^sub>q
                             \<lbrakk>qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q AC, qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q BC\<rbrakk>\<^sub>q\<close>
          proof -
            write equivalent_qregisters (infix "\<approx>" 50)
            have \<open>\<lbrakk> \<lbrakk>qregister_chain qFst A, qregister_chain qSnd B\<rbrakk>,
                    \<lbrakk>qregister_chain qFst AC, qregister_chain qSnd BC\<rbrakk> \<rbrakk>
                \<approx> \<lbrakk> \<lbrakk>qregister_chain qFst A, qregister_chain qSnd B\<rbrakk>,
                    \<lbrakk>qregister_chain qSnd BC, qregister_chain qFst AC\<rbrakk> \<rbrakk>\<close>
              apply (rule equivalent_qregisters_pair)
                apply (rule equivalent_qregisters_refl)
                apply simp
               apply (rule equivalent_qregisters_swap)
              by simp_all
            also have \<open>\<dots> \<approx> \<lbrakk>qregister_chain qFst A, \<lbrakk>qregister_chain qSnd B,
                    \<lbrakk>qregister_chain qSnd BC, qregister_chain qFst AC\<rbrakk>\<rbrakk>\<rbrakk>\<close>
              apply (rule equivalent_qregisters_triple2)
              by simp
            also have \<open>\<dots> \<approx> \<lbrakk>qregister_chain qFst A, \<lbrakk>\<lbrakk>qregister_chain qSnd B,
                    qregister_chain qSnd BC\<rbrakk>, qregister_chain qFst AC\<rbrakk>\<rbrakk>\<close>
              apply (rule equivalent_qregisters_pair)
                apply (rule equivalent_qregisters_refl)
                apply simp
              apply (rule equivalent_qregisters_triple1)
              by simp_all
            also have \<open>\<dots> = \<lbrakk>qregister_chain qFst A, 
                              \<lbrakk>qregister_chain qSnd \<lbrakk>B,BC\<rbrakk>, qregister_chain qFst AC\<rbrakk>\<rbrakk>\<close>
              by (simp add: pair_chain_fst_snd)
            also have \<open>\<dots> \<approx> \<lbrakk>qregister_chain qFst A, 
                    \<lbrakk>qregister_chain qFst AC, qregister_chain qSnd \<lbrakk>B,BC\<rbrakk>\<rbrakk>\<rbrakk>\<close>
              apply (rule equivalent_qregisters_pair)
                apply (rule equivalent_qregisters_refl)
                apply simp
               apply (rule equivalent_qregisters_swap)
              by simp_all
            also have \<open>\<dots> \<approx> \<lbrakk>\<lbrakk>qregister_chain qFst A, qregister_chain qFst AC\<rbrakk>, 
                             qregister_chain qSnd \<lbrakk>B,BC\<rbrakk>\<rbrakk>\<close>
              apply (rule equivalent_qregisters_triple1)
              by simp
            also have \<open>\<dots> = \<lbrakk>qregister_chain qFst \<lbrakk>A,AC\<rbrakk>, 
                             qregister_chain qSnd \<lbrakk>B,BC\<rbrakk>\<rbrakk>\<close>
              by (simp add: pair_chain_fst_snd)
            also have \<open>\<dots> \<approx> \<lbrakk>qregister_chain qFst qregister_id, 
                             qregister_chain qSnd qregister_id\<rbrakk>\<close>
              apply (rule equivalent_qregisters_pair)
                apply (rule equivalent_qregisters_chain)
                 apply (simp flip: iso_qregister_equivalent_id)
              apply simp
               apply (rule equivalent_qregisters_chain)
              by (simp_all flip: iso_qregister_equivalent_id)
            also have \<open>\<dots> = qregister_id\<close>
              by simp
            finally show ?thesis
              by (simp add: iso_qregister_equivalent_id qcomplements_def')
          qed
          then show ?goal
            by (auto intro!: QCOMPLEMENT_QREGISTER_of_eqI
                simp add: QCOMPLEMENT_A QCOMPLEMENT_B
                simp flip: QREGISTER_of_qregister_chain QREGISTER_of_qregister_pair qregF qregG)
        qed
        from this[cancel_with_type]
        show ?goal
          by -
      qed
      from this[cancel_with_type]
      show ?goal
        by -
    qed
    from this[cancel_with_type]
    show ?goal
      by -
  qed
  from this[cancel_with_type]
  show ?goal
    by -
qed


lemma y1:
  assumes \<open>ACTUAL_QREGISTER F\<close>
  shows \<open>QCOMPLEMENT (QREGISTER_pair QREGISTER_fst (QREGISTER_chain qSnd F))
    = QREGISTER_chain qSnd (QCOMPLEMENT F)\<close>
  using y2[where F=\<top> and G=F] assms
  by simp

lemma y3:
  assumes \<open>ACTUAL_QREGISTER F\<close>
  shows \<open>QCOMPLEMENT (QREGISTER_pair (QREGISTER_chain qFst F) QREGISTER_snd)
    = QREGISTER_chain qFst (QCOMPLEMENT F)\<close>
  using y2[where F=F and G=\<top>] assms
  by simp

(*
ML \<open>
(* Rewrites QCOMPLEMENT (INDEX-QREGISTER) into an INDEX-QREGISTER *)
local
  val rules = (map (fn thm => thm RS @{thm eq_reflection}) @{thms 
      y1 y2 y3 QCOMPLEMENT_chain QCOMPLEMENT_snd QCOMPLEMENT_fst QREGISTER_of_qFst QREGISTER_of_qSnd
      QREGISTER_pair_fst_snd QREGISTER_pair_snd_fst QCOMPLEMENT_bot QCOMPLEMENT_top})
in
fun QCOMPLEMENT_INDEX_REGISTER_conv ctxt = Raw_Simplifier.rewrite ctxt false rules
end
\<close>
*)

lemma zz0: \<open>ACTUAL_QREGISTER (QREGISTER_pair (QREGISTER_chain qFst F) (QREGISTER_chain qSnd G))\<close> if \<open>ACTUAL_QREGISTER F\<close> and \<open>ACTUAL_QREGISTER G\<close>
proof -
  let ?goal = ?thesis
  from ACTUAL_QREGISTER_ex_register[OF \<open>ACTUAL_QREGISTER F\<close>]
  have \<open>\<forall>\<^sub>\<tau> 'f::type = ACTUAL_QREGISTER_content F. ?goal\<close>
  proof (rule with_type_mp)
    assume \<open>\<exists>A :: ('f, 'a) qregister. qregister A \<and> QREGISTER_of A = F\<close>
    then obtain A :: \<open>('f, 'a) qregister\<close> where [simp]: \<open>qregister A\<close> and qregF: \<open>QREGISTER_of A = F\<close>
      by auto
    from ACTUAL_QREGISTER_ex_register[OF \<open>ACTUAL_QREGISTER G\<close>]
    have \<open>\<forall>\<^sub>\<tau> 'g::type = ACTUAL_QREGISTER_content G. ?goal\<close>
    proof (rule with_type_mp)
      assume \<open>\<exists>B :: ('g, 'b) qregister. qregister B \<and> QREGISTER_of B = G\<close>
      then obtain B :: \<open>('g, 'b) qregister\<close> where [simp]: \<open>qregister B\<close> and qregG: \<open>QREGISTER_of B = G\<close>
        by auto
      have \<open>QREGISTER_pair (QREGISTER_chain qFst F) (QREGISTER_chain qSnd G)
          = QREGISTER_of (qregister_pair (qregister_chain qFst A) (qregister_chain qSnd B))\<close>
        by (simp add: QREGISTER_of_qregister_pair QREGISTER_of_qregister_chain qregG qregF)
      then show ?goal
        by (auto intro!: ACTUAL_QREGISTER_QREGISTER_of)
    qed
    from this[cancel_with_type]
    show ?goal
      by -
  qed
  from this[cancel_with_type]
  show ?goal
    by -
qed

lemma zz0': \<open>ACTUAL_QREGISTER (QREGISTER_pair (QREGISTER_chain qSnd G) (QREGISTER_chain qFst F))\<close> if \<open>ACTUAL_QREGISTER F \<and> ACTUAL_QREGISTER G\<close>
  by (simp add: QREGISTER_pair_sym that zz0)
lemma zz1: \<open>ACTUAL_QREGISTER (QREGISTER_pair QREGISTER_fst (QREGISTER_chain qSnd F))\<close> if \<open>ACTUAL_QREGISTER F\<close>
  by (metis ACTUAL_QREGISTER_top QREGISTER_chain_fst_top that zz0)
lemma zz2: \<open>ACTUAL_QREGISTER (QREGISTER_pair QREGISTER_snd (QREGISTER_chain qFst F))\<close> if \<open>ACTUAL_QREGISTER F\<close>
  by (metis ACTUAL_QREGISTER_top QREGISTER_chain_snd_top that zz0')
lemma zz3: \<open>ACTUAL_QREGISTER (QREGISTER_pair (QREGISTER_chain qSnd F) QREGISTER_fst)\<close> if \<open>ACTUAL_QREGISTER F\<close>
  by (simp add: QREGISTER_pair_sym that zz1)
lemma zz4: \<open>ACTUAL_QREGISTER (QREGISTER_pair (QREGISTER_chain qFst F) QREGISTER_snd)\<close> if \<open>ACTUAL_QREGISTER F\<close>
  by (simp add: QREGISTER_pair_sym that zz2)

ML \<open>
local
  val simpset = \<^context>  addsimps @{thms 
       ACTUAL_QREGISTER_fst ACTUAL_QREGISTER_snd ACTUAL_QREGISTER_chain
       ACTUAL_QREGISTER_bot ACTUAL_QREGISTER_top ACTUAL_QREGISTER_pair
       zz0 zz0' zz1 zz2 zz3 zz4
    distinct_cvars_split2 ccompatible3 ccompatible3'
    distinct_qvars_split1 distinct_qvars_split2 qcompatible3 qcompatible3'
    Cccompatible_CREGISTER_of Qqcompatible_QREGISTER_of}
    |> simpset_of
in
(* Proves "ACTUAL_QREGISTER INDEX-QREGISTER" *)
fun ACTUAL_QREGISTER_tac ctxt =
  (* K (Misc.print_here_tac ctxt \<^here>) THEN'  *)
  let
  val ctxt = ctxt |> Config.put Simplifier.simp_trace false
                  |> put_simpset simpset
  in Misc.succeed_or_error_tac' (SOLVED' (simp_tac ctxt)) ctxt (fn t => "Cannot prove (using simp): " ^ Syntax.string_of_term ctxt t) end
end
\<close>


ML \<open>
(* Rewrites QCOMPLEMENT (INDEX-QREGISTER) into an INDEX-QREGISTER *)
  val simpctxt =
      put_simpset HOL_ss \<^context>
      addsimps
        @{thms 
           y1 y2 y3 QCOMPLEMENT_chain QCOMPLEMENT_snd QCOMPLEMENT_fst QREGISTER_of_qFst QREGISTER_of_qSnd
           QREGISTER_pair_fst_snd QREGISTER_pair_snd_fst QCOMPLEMENT_bot QCOMPLEMENT_top}
  val simpset = Simplifier.simpset_of simpctxt
local
in
fun QCOMPLEMENT_INDEX_REGISTER_conv ctxt = let
  val solver = mk_solver "ACTUAL_QREGISTER" (fn _ => ACTUAL_QREGISTER_tac ctxt)
  val ctxt = Simplifier.put_simpset simpset ctxt 
      addSSolver solver
      addSolver solver
  in
    Simplifier.rewrite ctxt
  end
end
\<close>

ML \<open>
QCOMPLEMENT_INDEX_REGISTER_conv \<^context> \<^cterm>\<open>QCOMPLEMENT
     (QREGISTER_pair QREGISTER_fst
       (QREGISTER_chain \<lbrakk>#2.\<rbrakk>\<^sub>q
         (QREGISTER_pair QREGISTER_fst
           (QREGISTER_chain \<lbrakk>#2.\<rbrakk>\<^sub>q
             (QREGISTER_pair QREGISTER_fst (QREGISTER_chain \<lbrakk>#2.\<rbrakk>\<^sub>q QREGISTER_snd))))))\<close>
\<close>

ML \<open>
(* Opposite of QREGISTER_of_index_reg_conv *)
val QREGISTER_of_index_reg_reverse_conv =
  Misc.rewrite_with_prover (fn ctxt => distinct_vars_tac ctxt 1)
    (map (fn thm => thm RS @{thm sym} RS @{thm eq_reflection})
          @{thms 
            QREGISTER_of_qregister_pair QREGISTER_of_qregister_chain QREGISTER_of_empty_qregister
            QREGISTER_of_qFst QREGISTER_of_qSnd QREGISTER_of_qregister_id})\<close>


ML \<open>
fun qcomplements_tac ctxt =
  resolve_tac ctxt @{thms z1} (* Creates three subgoals *)
  THEN'
  distinct_vars_tac ctxt (* Solve first subgoal *)
  THEN'
  (* Second subgoal *)
  CONVERSION ((QREGISTER_of_index_reg_conv |> Misc.mk_ctxt_conv Conv.arg_conv |> Misc.mk_ctxt_conv Conv.arg1_conv |> Misc.concl_conv_Trueprop) ctxt)
  THEN'
  (* Second subgoal *)
  CONVERSION ((INDEX_REGISTER_norm_conv |> Misc.mk_ctxt_conv Conv.arg_conv |> Misc.mk_ctxt_conv Conv.arg1_conv |> Misc.concl_conv_Trueprop) ctxt)
  THEN'
  (* Second subgoal *)
  CONVERSION ((QCOMPLEMENT_INDEX_REGISTER_conv |> Misc.mk_ctxt_conv Conv.arg1_conv |> Misc.concl_conv_Trueprop) ctxt)
  THEN'
  (* Second subgoal *)
  CONVERSION ((QREGISTER_of_index_reg_reverse_conv |> Misc.mk_ctxt_conv Conv.arg1_conv |> Misc.concl_conv_Trueprop) ctxt)
  THEN'
  (* Solve second subgoal *)
  resolve_tac ctxt @{thms refl}
  THEN'
  distinct_vars_tac ctxt (* Solve third subgoal *)
\<close>

schematic_goal \<open>qcomplements \<lbrakk>\<lbrakk>#2\<rbrakk>\<^sub>q, \<lbrakk>#3\<rbrakk>\<^sub>q, \<lbrakk>#1\<rbrakk>\<^sub>q, \<lbrakk>#5.\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q (?X :: (?'x,_) qregister)\<close>
  by (tactic \<open>qcomplements_tac \<^context> 1\<close>)


(* END MOVE *)


(* (* TODO used? *)
lemma filterlim_bot: \<open>filterlim f \<bottom> F \<longleftrightarrow> (F = \<bottom>)\<close>
proof -
  have \<open>F = \<bottom>\<close> if \<open>filtermap f F \<le> \<bottom>\<close>
  proof -
    from that have \<open>filtermap f F = \<bottom>\<close>
      by (simp add: le_bot)
    then have \<open>eventually (\<lambda>_. False) (filtermap f F)\<close>
      by simp
    then have \<open>eventually (\<lambda>_. False) F\<close>
      by (simp add: eventually_filtermap)
    then show \<open>F = \<bottom>\<close>
      using eventually_False by auto
  qed
  then show ?thesis
    by (auto simp add: filterlim_def)
qed *)



ML \<open>
open Prog_Variables
\<close>


experiment
  fixes C :: "(bit, qu) qregister" and A :: "(bit, qu) qregister" and B :: "(bit, qu) qregister"
  assumes [register]: \<open>declared_qvars \<lbrakk>C, A, B\<rbrakk>\<close>
begin

ML \<open>
val config =
Prog_Variables.translate_to_index_registers_conv_options_trace false
Prog_Variables.translate_to_index_registers_conv_default_options
\<close>

ML \<open>
val ct = \<^cterm>\<open>

(((((((let P = apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q A) (mproj M z) *\<^sub>S \<top> in (let M = computational_basis in \<CC>\<ll>\<aa>[mtotal M] \<sqinter> (\<Sqinter>za. let P = apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q C) (mproj M za) *\<^sub>S \<top> in (\<CC>\<ll>\<aa>[z \<noteq> 1] + \<CC>\<ll>\<aa>[isometry pauliX] \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B) pauliX* *\<^sub>S ((\<CC>\<ll>\<aa>[za \<noteq> 1] + \<CC>\<ll>\<aa>[isometry pauliZ] \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B) pauliZ* *\<^sub>S (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B \<equiv>\<qq> qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q A \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B) pauliZ *\<^sub>S \<top>)))) \<sqinter> (\<CC>\<ll>\<aa>[za = 1] + qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B \<equiv>\<qq> qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q A) \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B) pauliX *\<^sub>S \<top>)))) \<sqinter> (\<CC>\<ll>\<aa>[z = 1] + (\<CC>\<ll>\<aa>[za \<noteq> 1] + \<CC>\<ll>\<aa>[isometry pauliZ] \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B) pauliZ* *\<^sub>S (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B \<equiv>\<qq> qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q A \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B) pauliZ *\<^sub>S \<top>)))) \<sqinter> (\<CC>\<ll>\<aa>[za = 1] + qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B \<equiv>\<qq> qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q A)) \<sqinter> P + - P)) \<sqinter> P + - P)) \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q C) hadamard *\<^sub>S \<top>))) \<sqinter> (apply_qregister \<lbrakk>qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q C, qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q A\<rbrakk>\<^sub>q CNOT *\<^sub>S \<top>)))) \<div> EPR\<guillemotright>\<lbrakk>qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q A, qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B\<rbrakk>\<^sub>q

\<close>
\<close>

ML \<open>Prog_Variables.translate_to_index_registers_conv \<^context>
  config
  ct
  |> Thm.rhs_of\<close>

end


lemmas prepare_for_code_add =
  (* qregister_of_cregister_Fst[symmetric] qregister_of_cregister_Snd[symmetric] *)
  (* qregister_of_cregister_pair[symmetric] qregister_of_cregister_chain[symmetric] *)
  apply_qregister_of_cregister permute_and_tensor1_cblinfun_code_prep
  same_outside_cregister_def

  apply_qregister_space_code_hack (* TODO think of something more efficient *)

  case_prod_beta if_distrib[of fst] if_distrib[of snd] prod_eq_iff

  div_leq_simp mod_mod_cancel

  getter_pair getter_chain setter_chain setter_pair setter_cFst setter_cSnd

  enum_index_prod_def fst_enum_nth snd_enum_nth enum_index_nth if_distrib[of enum_index]
  enum_nth_injective

  quantum_equality_full_def_let space_div_space_div_unlifted INF_lift Cla_inf_lift Cla_plus_lift Cla_sup_lift
  top_leq_lift top_geq_lift bot_leq_lift bot_geq_lift top_eq_lift bot_eq_lift top_eq_lift2 bot_eq_lift2

lemmas prepare_for_code_flip =
  qregister_of_cregister_Fst qregister_of_cregister_Snd
  qregister_of_cregister_pair qregister_of_cregister_chain
lemma xxx: \<open>apply_qregister_space \<lbrakk>\<lbrakk>#3\<rbrakk>\<^sub>q, \<lbrakk>#4.\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q (\<lbrakk>#1\<rbrakk>\<^sub>q \<equiv>\<qq> \<lbrakk>#2.\<rbrakk>\<^sub>q) = a\<close>
  apply (simp add: join_registers cong del: if_weak_cong add: prepare_for_code_add flip: prepare_for_code_flip)
  oops

lemma permute_and_tensor1_mat'_cong:
\<open>n=m \<Longrightarrow> a=b \<Longrightarrow> permute_and_tensor1_mat' n f g a = permute_and_tensor1_mat' m f g b\<close>
  by simp

definition "Proj_code = Proj"
lemma apply_qregister_space_code_hack': \<open>apply_qregister_space (qregister_of_cregister F) S = apply_qregister (qregister_of_cregister F) (Proj_code S) *\<^sub>S \<top>\<close>
  unfolding Proj_code_def by (rule apply_qregister_space_def)

ML \<open>
fun top_everywhere_conv conv ctxt = Conv.top_conv (fn ctxt => Conv.try_conv (conv ctxt)) ctxt
fun bottom_everywhere_conv conv ctxt = Conv.bottom_conv (fn ctxt => Conv.try_conv (conv ctxt)) ctxt
\<close>


lemma xxx:
\<open>apply_qregister_space \<lbrakk>\<lbrakk>#3\<rbrakk>\<^sub>q, \<lbrakk>#4.\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q (\<lbrakk>#1\<rbrakk>\<^sub>q \<equiv>\<qq> \<lbrakk>#2.\<rbrakk>\<^sub>q)
    \<le> apply_qregister_space \<lbrakk>\<lbrakk>#1\<rbrakk>\<^sub>q, \<lbrakk>#2\<rbrakk>\<^sub>q, \<lbrakk>#3\<rbrakk>\<^sub>q, \<lbrakk>#4.\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q
        (apply_qregister_space \<lbrakk>\<lbrakk>#1\<rbrakk>\<^sub>q, \<lbrakk>#2\<rbrakk>\<^sub>q, \<lbrakk>#3\<rbrakk>\<^sub>q, \<lbrakk>#4.\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q
          (apply_qregister_space \<lbrakk>\<lbrakk>#1\<rbrakk>\<^sub>q, \<lbrakk>#2\<rbrakk>\<^sub>q, \<lbrakk>#3\<rbrakk>\<^sub>q, \<lbrakk>#4.\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q
            (apply_qregister_space empty_qregister \<CC>\<ll>\<aa>[isometry CNOT] \<sqinter>
             apply_qregister_space \<lbrakk>\<lbrakk>#1\<rbrakk>\<^sub>q, \<lbrakk>#2\<rbrakk>\<^sub>q, \<lbrakk>#3\<rbrakk>\<^sub>q, \<lbrakk>#4.\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q
              (apply_qregister \<lbrakk>\<lbrakk>#3\<rbrakk>\<^sub>q, \<lbrakk>#1\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q (CNOT*) *\<^sub>S
               apply_qregister_space \<lbrakk>\<lbrakk>#1\<rbrakk>\<^sub>q, \<lbrakk>#2\<rbrakk>\<^sub>q, \<lbrakk>#3\<rbrakk>\<^sub>q, \<lbrakk>#4.\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q
                (apply_qregister_space \<lbrakk>\<lbrakk>#1\<rbrakk>\<^sub>q, \<lbrakk>#2\<rbrakk>\<^sub>q, \<lbrakk>#3\<rbrakk>\<^sub>q, \<lbrakk>#4.\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q
                  (apply_qregister_space empty_qregister \<CC>\<ll>\<aa>[isometry hadamard] \<sqinter>
                   apply_qregister_space \<lbrakk>\<lbrakk>#1\<rbrakk>\<^sub>q, \<lbrakk>#2\<rbrakk>\<^sub>q, \<lbrakk>#3\<rbrakk>\<^sub>q, \<lbrakk>#4.\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q
                    (apply_qregister \<lbrakk>#3\<rbrakk>\<^sub>q (hadamard*) *\<^sub>S
                      ( (top)))) \<sqinter>
                 apply_qregister_space \<lbrakk>\<lbrakk>#3\<rbrakk>\<^sub>q, \<lbrakk>#1\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q
                  (apply_qregister \<lbrakk>\<lbrakk>#1\<rbrakk>\<^sub>q, \<lbrakk>#2.\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q CNOT *\<^sub>S
                   apply_qregister_space empty_qregister \<top>)))) \<div> EPR\<guillemotright>\<lbrakk>\<lbrakk>#1\<rbrakk>\<^sub>q, \<lbrakk>#2\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q))\<close>

  apply (simp add: join_registers cong: permute_and_tensor1_mat'_cong cong del: if_weak_cong 
        add: prepare_for_code_add  flip: prepare_for_code_flip)
  oops

lemma apply_qregister_space_of_cregister:
  assumes \<open>cregister F\<close>
  shows \<open>apply_qregister_space (qregister_of_cregister F) a =
          permute_and_tensor1_cblinfun (getter F) (same_outside_cregister F) (Proj a) *\<^sub>S \<top>\<close>
  by (simp add: apply_qregister_of_cregister apply_qregister_space_def assms)

lemma qregister_to_cregister_conv_aux1: \<open>Q \<equiv> qregister_of_cregister F \<Longrightarrow> R \<equiv> qregister_of_cregister G \<Longrightarrow> \<lbrakk>Q,R\<rbrakk>\<^sub>q \<equiv> qregister_of_cregister \<lbrakk>F,G\<rbrakk>\<^sub>c\<close>
  by (simp add: Scratch.prepare_for_code_flip(3))

lemma qregister_to_cregister_conv_aux2: 
  \<open>Q \<equiv> qregister_of_cregister F \<Longrightarrow> R \<equiv> qregister_of_cregister G \<Longrightarrow> 
      qregister_chain Q R \<equiv> qregister_of_cregister (cregister_chain F G)\<close>
   by (simp add: Scratch.prepare_for_code_flip(4))

lemma qregister_of_cregister_empty: \<open>qregister_of_cregister empty_cregister = empty_qregister\<close>
  by (metis empty_cregister_is_register empty_qregisters_same qregister_qregister_of_cregister)

lemma qregister_of_cregister_id: \<open>qregister_of_cregister cregister_id = qregister_id\<close>
  by (metis cregister_chain_id cregister_id qregister_chain_id qregister_conversion_as_register qregister_of_cregister_chain qregister_qregister_of_cregister)

ML \<open>
fun qregister_to_cregister_conv_tac ctxt st =
  ((DETERM (resolve_tac ctxt @{thms qregister_to_cregister_conv_aux1 qregister_to_cregister_conv_aux2} 1)
    THEN qregister_to_cregister_conv_tac ctxt THEN qregister_to_cregister_conv_tac ctxt)
  ORELSE (DETERM (resolve_tac ctxt 
    @{thms qregister_of_cregister_Fst[symmetric, THEN eq_reflection]
           qregister_of_cregister_Snd[symmetric, THEN eq_reflection]
           qregister_of_cregister_empty[symmetric, THEN eq_reflection]
           qregister_of_cregister_id[symmetric, THEN eq_reflection]} 1))) st\<close>


ML \<open>
val qregister_to_cregister_conv = Misc.conv_from_tac
  (fn _ => fn t => Prog_Variables.is_index_qregister t orelse raise CTERM ("not an index qregister", [ct]))
  qregister_to_cregister_conv_tac\<close>

ML \<open>
fun apply_qregister_to_cregister_conv_tac ctxt =
  (DETERM (resolve_tac ctxt @{thms apply_qregister_of_cregister[THEN eq_reflection] apply_qregister_space_of_cregister[THEN eq_reflection]} 1))
  THEN Prog_Variables.distinct_vars_tac ctxt 1\<close>

(* schematic_goal \<open>apply_qregister (qregister_of_cregister \<lbrakk>\<lbrakk>#1\<rbrakk>\<^sub>c, \<lbrakk>#2\<rbrakk>\<^sub>c, \<lbrakk>#3\<rbrakk>\<^sub>c, \<lbrakk>#4.\<rbrakk>\<^sub>c\<rbrakk>\<^sub>c) A \<equiv> ?Q\<close>
  apply (tactic \<open>apply_qregister_to_cregister_conv_tac \<^context>\<close>)
  apply (tactic \<open>Prog_Variables.distinct_vars_tac \<^context> 1\<close>)  
  apply (rule apply_qregister_of_cregister[THEN eq_reflection] apply_qregister_space_of_cregister[THEN eq_reflection]) *)

ML \<open>
val apply_qregister_to_cregister_conv = Misc.conv_from_tac
  (fn _ => fn t => case t of \<^Const_>\<open>apply_qregister _ _\<close> $ (\<^Const_>\<open>qregister_of_cregister _ _\<close> $ _) $ _ => ()
                           | \<^Const_>\<open>apply_qregister_space _ _\<close> $ (\<^Const_>\<open>qregister_of_cregister _ _\<close> $ _) $ _ => ()
                           | _ => raise TERM ("not of the form `apply_qregister (qregister_of_cregister _) _`", [t]))
  apply_qregister_to_cregister_conv_tac\<close>

lemma cregister_lens_getter_conv_pair_aux:
  assumes \<open>cregister \<lbrakk>F,G\<rbrakk>\<^sub>c\<close>
  assumes \<open>getter F \<equiv> f\<close>
  assumes \<open>getter G \<equiv> g\<close>
  shows \<open>getter \<lbrakk>F,G\<rbrakk>\<^sub>c \<equiv> BNF_Def.convol f g\<close>
  by (simp add: Scratch.prepare_for_code_add(11) assms(1) assms(2) assms(3) BNF_Def.convol_def)

lemma cregister_lens_getter_conv_chain_aux:
  assumes \<open>cregister F\<close>
  assumes \<open>getter F \<equiv> f\<close>
  assumes \<open>getter G \<equiv> g\<close>
  shows \<open>getter (cregister_chain F G) \<equiv> g o f\<close>
  by (simp add: assms(1) assms(2) assms(3) getter_chain)

lemma cregister_lens_setter_conv_pair_aux:
  assumes \<open>cregister \<lbrakk>F,G\<rbrakk>\<^sub>c\<close>
  assumes \<open>setter F \<equiv> f\<close>
  assumes \<open>setter G \<equiv> g\<close>
  shows \<open>setter \<lbrakk>F,G\<rbrakk>\<^sub>c \<equiv> (\<lambda>(x,y). f x o g y)\<close>
  by (simp add: Scratch.prepare_for_code_add(14) assms(1) assms(2) assms(3))

lemma cregister_lens_setter_conv_chain_aux:
  assumes \<open>cregister F\<close>
  assumes \<open>cregister G\<close>
  assumes \<open>setter F \<equiv> sF\<close>
  assumes \<open>setter G \<equiv> sG\<close>
  assumes \<open>getter F \<equiv> gF\<close>
  shows \<open>setter (cregister_chain F G) \<equiv> (\<lambda>a m. sF (sG a (gF m)) m)\<close>
  using setter_chain[OF assms(1,2), abs_def]
  by (simp add: assms(3-5))

lemma same_outside_cregister_sym:
  \<open>cregister F \<Longrightarrow> same_outside_cregister F n m \<longleftrightarrow> same_outside_cregister F m n\<close>
  apply (simp add: same_outside_cregister_def)
  by (metis setter_getter_same setter_setter_same)

(* TODO unused? *)
lemma cregister_lens_soc_conv_chain_aux:
  assumes [simp]: \<open>cregister F\<close>
  assumes [simp]: \<open>cregister G\<close>
  assumes socF: \<open>same_outside_cregister F \<equiv> socF\<close>
  assumes socG: \<open>same_outside_cregister G \<equiv> socG\<close>
  assumes gF: \<open>getter F \<equiv> gF\<close>
  shows \<open>same_outside_cregister (cregister_chain F G) \<equiv> 
            (\<lambda>m n. socF m n \<and> socG (gF m) (gF n))\<close>
proof (intro eq_reflection ext iffI)
  fix m n
  define gG sF sG where \<open>gG = getter G\<close> and \<open>sF = setter F\<close> and \<open>sG = setter G\<close>
  have sF_twice: \<open>sF a (sF b m) = sF a m\<close> for a b m
    by (simp add: sF_def)
  have sG_twice: \<open>sG a (sG b m) = sG a m\<close> for a b m
    by (simp add: sG_def)
  have sF_gF: \<open>sF (gF m) m = m\<close> for m
    by (simp add: sF_def flip: gF)
  have sG_gG: \<open>sG (gG m) m = m\<close> for m
    by (simp add: sG_def gG_def)
  have gF_sF: \<open>gF (sF a m) = a\<close> for a m
    by (simp add: sF_def flip: gF)

  show \<open>socF m n \<and> socG (gF m) (gF n)\<close> if \<open>same_outside_cregister (cregister_chain F G) m n\<close>
  proof (rule conjI)
    from that have m_def: \<open>m = sF (sG (gG (gF m)) (gF n)) n\<close>
      by (simp add: same_outside_cregister_def setter_chain getter_chain gF
          flip: sF_def sG_def gG_def)
    have \<open>socF n m\<close>
    proof (simp flip: socF sF_def add: gF same_outside_cregister_def)
      have \<open>sF (gF n) m = sF (gF n) (sF (sG (gG (gF m)) (gF n)) n)\<close>
        apply (subst m_def) by simp
      also have \<open>\<dots> = n\<close>
        by (simp add: sF_twice sF_gF)
      finally show \<open>n = sF (gF n) m\<close>
        by simp
    qed
    then show \<open>socF m n\<close>
      by (metis assms(1) assms(3) same_outside_cregister_sym)
    have \<open>socG (gF n) (gF m)\<close>
    proof (simp flip: socG sG_def gG_def add: gF same_outside_cregister_def)
      have \<open>sG (gG (gF n)) (gF m) = sG (gG (gF n)) (gF (sF (sG (gG (gF m)) (gF n)) n))\<close>
        apply (subst m_def) by simp
      also have \<open>\<dots> = gF n\<close>
        by (simp add: gF_sF sG_twice sG_gG)
      finally show \<open>gF n = sG (gG (gF n)) (gF m)\<close>
        by simp
    qed
    then show \<open>socG (gF m) (gF n)\<close>
      by (metis assms(2) assms(4) same_outside_cregister_sym)
  qed

  show \<open>same_outside_cregister (cregister_chain F G) m n\<close> if \<open>socF m n \<and> socG (gF m) (gF n)\<close> 
  proof -
    from that have \<open>socF m n\<close> and \<open>socG (gF m) (gF n)\<close>
      by auto
    from \<open>socG (gF m) (gF n)\<close>
    have 1: \<open>sG (gG (gF m)) (gF n) = gF m\<close>
      by (simp add: same_outside_cregister_def flip: socG sG_def gG_def)
    from \<open>socF m n\<close>
    have 2: \<open>sF (gF m) n = m\<close>
      by (simp add: same_outside_cregister_def gF flip: socF sF_def)

    have \<open>setter (cregister_chain F G)
     (getter (cregister_chain F G) m) n = sF (sG (gG (gF m)) (gF n)) n\<close>
      by (simp add: getter_chain setter_chain gF flip: gG_def sG_def sF_def)
    also have \<open>\<dots> = sF (gF m) n\<close>
      by (simp add: 1)
    also from 2 have \<open>\<dots> = m\<close>
      by -
    finally show \<open>same_outside_cregister (cregister_chain F G) m n\<close>
      by (simp add: same_outside_cregister_def)
  qed
qed

lemma getter_empty: \<open>getter empty_cregister a = undefined\<close>
  by (rule everything_the_same)

ML \<open>
fun cregister_lens_getter_conv_tac ctxt st =
  ((DETERM (resolve_tac ctxt @{thms cregister_lens_getter_conv_pair_aux cregister_lens_getter_conv_chain_aux} 1)
    THEN Prog_Variables.distinct_vars_tac ctxt 1 THEN cregister_lens_getter_conv_tac ctxt THEN cregister_lens_getter_conv_tac ctxt)
  ORELSE (DETERM (resolve_tac ctxt 
    @{thms getter_cFst[THEN eq_reflection] getter_cSnd[THEN eq_reflection] getter_id[abs_def] getter_empty[abs_def]} 1))) st\<close>

ML \<open>
val cregister_lens_getter_conv = Misc.conv_from_tac
  (fn _ => fn t => case t of \<^Const_>\<open>getter _ _\<close> $ F => is_index_cregister F orelse raise TERM ("not an index register", [t])
                           | _ => raise TERM ("not of the form `getter \<dots>`", [t]))
  cregister_lens_getter_conv_tac\<close>

lemma setter_cregister: \<open>setter empty_cregister a m = m\<close>
  by (metis getter_empty setter_getter_same setter_setter_same)

ML \<open>
fun cregister_lens_setter_conv_tac ctxt st =
  ((DETERM (resolve_tac ctxt @{thms cregister_lens_setter_conv_pair_aux} 1)
    THEN Prog_Variables.distinct_vars_tac ctxt 1 THEN cregister_lens_setter_conv_tac ctxt THEN cregister_lens_setter_conv_tac ctxt)
  ORELSE (DETERM (resolve_tac ctxt @{thms cregister_lens_setter_conv_chain_aux} 1)
    THEN Prog_Variables.distinct_vars_tac ctxt 1 THEN Prog_Variables.distinct_vars_tac ctxt 1
    THEN cregister_lens_setter_conv_tac ctxt THEN cregister_lens_setter_conv_tac ctxt
    THEN cregister_lens_getter_conv_tac ctxt)
  ORELSE (DETERM (resolve_tac ctxt 
    @{thms setter_cFst[abs_def] setter_cSnd[abs_def] setter_id[abs_def] setter_cregister[abs_def]} 1))) st\<close>

thm setter_cFst[abs_def] setter_cSnd[abs_def] setter_id[abs_def] setter_cregister[abs_def]

ML \<open>
val cregister_lens_setter_conv = Misc.conv_from_tac
  (fn _ => fn t => case t of \<^Const_>\<open>setter _ _\<close> $ F => is_index_cregister F orelse raise TERM ("not an index register", [t])
                           | _ => raise TERM ("not of the form `setter \<dots>`", [t]))
  cregister_lens_setter_conv_tac\<close>

ML \<open>
fun tmp_conv ct = let
  val goal = Logic.mk_equals (Thm.term_of ct, Free ("HELLO", Thm.typ_of_cterm ct --> Thm.typ_of_cterm ct) $ Thm.term_of ct)
  val thm = Skip_Proof.make_thm (Thm.theory_of_cterm ct) goal
in thm end 
\<close>

ML \<open>
fun abs_conv' conv = Conv.abs_conv (fn (_,ctxt) => conv ctxt)
\<close>


ML \<open>
open Conv
(* Converts same_outside_qregister F into (\<lambda>m n. \<dots>) for an index-register F *)
fun cregister_lens_soc_conv ctxt = 
Conv.rewr_conv @{lemma \<open>same_outside_cregister F \<equiv> (\<lambda>x y. x = setter F (getter F x) y)\<close> by (simp add: same_outside_cregister_def[abs_def])}
then_conv
(
 Misc.mk_ctxt_conv2 combination_conv 
      cregister_lens_setter_conv
      (Misc.mk_ctxt_conv fun_conv cregister_lens_getter_conv)
 |> Misc.mk_ctxt_conv fun_conv
 |> Misc.mk_ctxt_conv arg_conv
 |> abs_conv'
 |> abs_conv'
) ctxt
\<close>

ML \<open>
fun cregister_lens_conv ctxt = 
  cregister_lens_getter_conv ctxt
  else_conv cregister_lens_setter_conv ctxt
  else_conv cregister_lens_soc_conv ctxt
\<close>


lemma permute_and_tensor1_cblinfun_conv_tac_aux:
  fixes f :: \<open>'a::eenum \<Rightarrow> 'b::eenum\<close> and g h :: \<open>'a \<Rightarrow> 'a \<Rightarrow> 'c::eenum\<close>
  assumes \<open>\<And>a. enum_index (f a) \<equiv> f' (enum_index a)\<close>
  assumes \<open>\<And>a b. enum_index (g a b) \<equiv> g' (enum_index a) (enum_index b)\<close>
  assumes \<open>\<And>a b. enum_index (h a b) \<equiv> h' (enum_index a) (enum_index b)\<close>
  (* assumes \<open>\<And>a b. R a b = R' (enum_index a) (enum_index b)\<close> *)
  shows \<open>permute_and_tensor1_cblinfun f (\<lambda>a b. g a b = h a b) \<equiv> 
      (\<lambda>a. permute_and_tensor1_mat' CARD('a) f' (\<lambda>a b. g' a b = h' b b) (mat_of_cblinfun a))\<close>
  sorry

lemma enum_index_apfst:
  fixes f :: \<open>'a::eenum \<Rightarrow> 'c::eenum\<close> and x :: \<open>'a \<times> 'b::eenum\<close>
  assumes \<open>\<And>a. enum_index (f a) = f' (enum_index a)\<close>
  shows \<open>enum_index (apfst f x) = f' (enum_index x div CARD('b)) * CARD('b) + enum_index x mod CARD('b)\<close>
  by (simp add: apfst_def map_prod_def case_prod_beta enum_index_prod_def assms)

lemma enum_index_apsnd:
  fixes f :: \<open>'b::eenum \<Rightarrow> 'c::eenum\<close> and x :: \<open>'a::eenum \<times> 'b\<close>
  assumes \<open>\<And>a. enum_index (f a) = f' (enum_index a)\<close>
  shows \<open>enum_index (apsnd f x) = enum_index x div CARD('b) * CARD('c) + f' (enum_index (snd x))\<close>
  by (simp add: apsnd_def map_prod_def case_prod_beta enum_index_prod_def assms)

lemma enum_index_upfst:
  fixes a :: \<open>'c::eenum\<close> and x :: \<open>'a::eenum \<times> 'b::eenum\<close>
  shows \<open>enum_index (upfst a x) = enum_index a * CARD('b) + enum_index x mod CARD('b)\<close>
  by (simp add: enum_index_apfst)

lemma enum_index_upsnd:
  fixes a :: \<open>'c::eenum\<close> and x :: \<open>'a::eenum \<times> 'b::eenum\<close>
  shows \<open>enum_index (upsnd a x) = enum_index x div CARD('b) * CARD('c) + enum_index a\<close>
  by (simp add: enum_index_apsnd)

lemma enum_index_convol:
  fixes f :: \<open>'a \<Rightarrow> 'b::eenum\<close> and g :: \<open>'a \<Rightarrow> 'c::eenum\<close>
  shows \<open>enum_index (BNF_Def.convol f g a) = enum_index (f a) * CARD('c) + enum_index (g a)\<close>
  by (simp add: enum_index_prod_def convol_def)

lemma upsnd_twice: \<open>upsnd a (upsnd b x) = upsnd a x\<close>
  by (simp add: prod.expand)

lemma upfst_twice: \<open>upfst a (upfst b x) = upfst a x\<close>
  by (simp add: prod.expand)

lemma upfst_upsnd: \<open>upfst a (upsnd b x) = (a,b)\<close>
  by simp

lemma upsnd_upfst: \<open>upsnd b (upfst a x) = (a,b)\<close>
  by simp

lemma snd_upsnd: \<open>snd (upsnd a x) = a\<close>
  by simp

lemma fst_upfst: \<open>fst (upfst a x) = a\<close>
  by simp

lemma enum_index_pair: \<open>enum_index (a,b) = enum_index a * CARD('b) + enum_index b\<close> for a :: \<open>'a::eenum\<close> and b :: \<open>'b::eenum\<close>
  by (simp add: enum_index_prod_def)

lemma enum_index_CARD_1: \<open>enum_index a = 0\<close> for a :: \<open>'a::{eenum,CARD_1}\<close>
  apply (subst everything_the_same[of a \<open>enum_nth 0\<close>])
  apply (subst enum_index_nth)
  by simp

instantiation unit :: eenum begin
definition \<open>enum_nth_unit (_::nat) = ()\<close>
definition \<open>enum_index_unit (_::unit) = (0::nat)\<close>
instance
  apply intro_classes
  by (simp_all add: enum_index_unit_def)
end

ML \<open>
local
  val round1_simps = @{thms case_prod_beta snd_convol' fst_convol' o_def
      upsnd_twice upfst_twice prod.collapse fst_conv snd_conv
      upfst_upsnd upsnd_upfst snd_upsnd fst_upfst}
  val round2_simps = @{thms enum_index_convol enum_index_upsnd enum_index_upfst
      enum_index_fst enum_index_snd enum_index_pair div_leq_simp mod_mod_cancel
      enum_index_CARD_1}
in
fun enum_index_conv ctxt = let
  val round1_ctxt = (clear_simpset ctxt) addsimps round1_simps
  val round2_ctxt = ctxt addsimps round2_simps
in Simplifier.rewrite round1_ctxt then_conv Simplifier.rewrite round2_ctxt end
end
\<close>

ML \<open>
fun permute_and_tensor1_cblinfun_conv_tac ctxt =
  resolve_tac ctxt @{thms permute_and_tensor1_cblinfun_conv_tac_aux} 1
  THEN
  CONVERSION ((enum_index_conv |> Misc.mk_ctxt_conv arg1_conv |> params_conv ~1) ctxt) 1
  THEN
  resolve_tac ctxt @{thms reflexive} 1
  THEN
  CONVERSION ((enum_index_conv |> Misc.mk_ctxt_conv arg1_conv |> params_conv ~1) ctxt) 1
  THEN
  resolve_tac ctxt @{thms reflexive} 1
  THEN
  CONVERSION ((enum_index_conv |> Misc.mk_ctxt_conv arg1_conv |> params_conv ~1) ctxt) 1
  THEN
  resolve_tac ctxt @{thms reflexive} 1
\<close>

ML \<open>
val permute_and_tensor1_cblinfun_conv = Misc.conv_from_tac
  (fn ctxt => fn t => case t of \<^Const_>\<open>permute_and_tensor1_cblinfun _ _\<close> $ _ $ _  => (* \<^print> ("Found one") *) ()
                           | _ => raise TERM ("permute_and_tensor1_cblinfun_conv", [t]))
  permute_and_tensor1_cblinfun_conv_tac
\<close>



ML \<open>
fun wrap_dbg conv ctxt ct = let val res : thm
 = conv ctxt ct (* handle e => (\<^print> ("exn"); raise e) *) 
val orig = Thm.term_of ct
val new = Thm.term_of (Thm.lhs_of res)
val _ = new = orig orelse error
   (\<^make_string> ("BLA", 
orig = new, orig aconv new, Envir.beta_eta_contract orig = Envir.beta_eta_contract new,
Envir.beta_norm orig = Envir.beta_norm new,
Envir.aeconv (orig, new),
orig, new))
val _ = \<^print> ("Success") in res end
\<close>

ML \<open>
cregister_lens_getter_conv \<^context> \<^cterm>\<open>getter empty_cregister\<close>
\<close>

schematic_goal \<open>permute_and_tensor1_cblinfun (\<lambda>a::'a::eenum. undefined :: unit) (\<lambda>x y. x = y) \<equiv> ?X\<close>
  apply (tactic \<open>CONVERSION (top_everywhere_conv (wrap_dbg  permute_and_tensor1_cblinfun_conv) \<^context>) 1\<close>)
  oops
schematic_goal \<open>(Proj (apply_qregister qregister_id pauliZ *\<^sub>S apply_qregister_space (empty_qregister :: (unit,_) qregister) \<top>))
=xxx\<close>
  for XXX :: \<open>bit ell2 \<Rightarrow>\<^sub>C\<^sub>L bit ell2 \<Rightarrow> (bit \<times> bit \<times> bit) ell2 \<Rightarrow>\<^sub>C\<^sub>L (bit \<times> bit \<times> bit) ell2\<close>
    apply (tactic \<open>CONVERSION (top_everywhere_conv qregister_to_cregister_conv \<^context>) 1\<close>)
  apply (tactic \<open>CONVERSION (top_everywhere_conv apply_qregister_to_cregister_conv \<^context>) 1\<close>)
  apply (tactic \<open>CONVERSION (top_everywhere_conv cregister_lens_conv \<^context>) 1\<close>)

  apply (tactic \<open>CONVERSION (top_everywhere_conv (wrap_dbg  permute_and_tensor1_cblinfun_conv) \<^context>) 1\<close>)
  oops

ML \<open>
fun foc l = CSUBGOAL (fn (ct,i) => let
  val t = Thm.term_of ct
  val thy = Thm.theory_of_cterm ct
  fun subterm (t $ u) (0::ls) = subterm t ls
    | subterm (t $ u) (_::ls) = subterm u ls
    | subterm (Abs (n,T,t)) (_::ls) = subterm (subst_bound (Free(":"^n,T), t)) ls
    | subterm t _ = t
  val t' = subterm t l
  val new_goal = Logic.mk_equals (t', Var(("XXX",0),fastype_of t'))
  fun conv ct = Logic.mk_equals (Thm.term_of ct, new_goal) |> Skip_Proof.make_thm thy
in CONVERSION conv i end) 1
\<close>

ML \<open>
normalize_register_conv \<^context> \<^cterm>\<open>\<lbrakk>\<lbrakk>#1\<rbrakk>\<^sub>q, \<lbrakk>#2\<rbrakk>\<^sub>q, \<lbrakk>#3\<rbrakk>\<^sub>q, \<lbrakk>#4.\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q\<close>
\<close>

ML \<open>
(* TODO *)
fun complement_of_index_register ctxt ct = let
  val thm1 = normalize_register_conv2 ctxt ct  (* ct \<equiv> ct' *)
  val ct' = Thm.rhs_of thm1 |> \<^print>
in () end
;;

complement_of_index_register \<^context> \<^cterm>\<open>\<lbrakk>\<lbrakk>#3\<rbrakk>\<^sub>q, \<lbrakk>#2\<rbrakk>\<^sub>q, \<lbrakk>#1\<rbrakk>\<^sub>q, \<lbrakk>#5.\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q\<close>
\<close>

definition \<open>equivalent_qregisters' F G \<longleftrightarrow> equivalent_qregisters F G \<or> (F = non_qregister \<and> G = non_qregister)\<close>

definition QREGISTER_of' where \<open>QREGISTER_of' F = (if qregister F then Some (QREGISTER_of F) else None)\<close>

lemma x1:
  assumes \<open>qregister F\<close>
  assumes \<open>equivalent_qregisters' F H\<close>
  assumes \<open>qcomplements H G\<close>
  shows \<open>qcomplements F G\<close>
  sorry



(* 
lemma x2:
  assumes \<open>QREGISTER_of' F \<equiv> QREGISTER_of' F'\<close>
  assumes \<open>QREGISTER_of' G \<equiv> QREGISTER_of' G'\<close>
  assumes \<open>QREGISTER_of' \<lbrakk>F',G'\<rbrakk> \<equiv> QREGISTER_of' H\<close>
  shows \<open>QREGISTER_of' \<lbrakk>F,G\<rbrakk> \<equiv> QREGISTER_of' H\<close>
  sorry

lemma x3:
  assumes \<open>QREGISTER_of' F \<equiv> QREGISTER_of' F'\<close>
  shows \<open>QREGISTER_of' (qregister_chain qFst F) \<equiv> QREGISTER_of' (qregister_chain qFst F')\<close>
  sorry

lemma x4:
  assumes \<open>QREGISTER_of' F \<equiv> QREGISTER_of' F'\<close>
  shows \<open>QREGISTER_of' (qregister_chain qSnd F) \<equiv> QREGISTER_of' (qregister_chain qSnd F')\<close>
  sorry

lemma x5:
  shows \<open>QREGISTER_of' \<lbrakk>qFst, qSnd\<rbrakk> \<equiv> QREGISTER_of' qregister_id\<close>
  sorry

lemma x6:
  shows \<open>QREGISTER_of' \<lbrakk>qFst, qregister_chain qSnd F\<rbrakk> \<equiv> QREGISTER_of' \<lbrakk>qFst, qregister_chain qSnd F\<rbrakk>\<close>
  by simp
  sorry

ML \<open>
open Misc
\<close>

ML \<open>
(* Given \<open>QREGISTER_of' F \<equiv> QREGISTER_of' ?Q\<close>, instantiates ?Q with a "sorted" F.
   Assumes F is index-register.
   "Sorted" means: \<open>Q = Fst o \<dots>\<close> or \<open>Q = Snd o \<dots>\<close> or \<open>Q = id\<close> or \<open>Q = empty\<close>
    or \<open>Q = \<lbrakk>Fst o \<dots>, Snd o \<dots>\<rbrakk> where \<dots> is also sorted and not empty/id\<close>
 *)
fun QREGISTER_of'_index_reg_norm_tac ctxt = SUBGOAL (fn (t,i) => 
  (\<^print> (Thm.cterm_of ctxt t);
  case t of
    \<^Const_>\<open>Pure.eq _\<close> $ (\<^Const_>\<open>QREGISTER_of' _ _\<close> $ (\<^Const_>\<open>qregister_pair _ _ _\<close> $ _ $ _)) $ _ =>
      resolve_tac ctxt @{thms x2} i
      THEN
      QREGISTER_of'_index_reg_norm_tac ctxt i
      THEN
      QREGISTER_of'_index_reg_norm_tac ctxt i
      THEN
      print_here_tac ctxt \<^here>
      THEN
      resolve_tac ctxt @{thms x5 x6} i
  | \<^Const_>\<open>Pure.eq _\<close> $ (\<^Const_>\<open>QREGISTER_of' _ _\<close> $ 
         (\<^Const_>\<open>qregister_chain _ _ _\<close> $ \<^Const_>\<open>qFst _ _\<close> $ _)) $ _ =>
      resolve_tac ctxt @{thms x3} i
      THEN
      QREGISTER_of'_index_reg_norm_tac ctxt i
  | \<^Const_>\<open>Pure.eq _\<close> $ (\<^Const_>\<open>QREGISTER_of' _ _\<close> $ 
         (\<^Const_>\<open>qregister_chain _ _ _\<close> $ \<^Const_>\<open>qSnd _ _\<close> $ _)) $ _ =>
      resolve_tac ctxt @{thms x4} i
      THEN
      QREGISTER_of'_index_reg_norm_tac ctxt i
  | \<^Const_>\<open>Pure.eq _\<close> $ (\<^Const_>\<open>QREGISTER_of' _ _\<close> $ \<^Const_>\<open>qFst _ _\<close>) $ _ =>
      resolve_tac ctxt @{thms reflexive} i
  | \<^Const_>\<open>Pure.eq _\<close> $ (\<^Const_>\<open>QREGISTER_of' _ _\<close> $ \<^Const_>\<open>qSnd _ _\<close>) $ _ =>
      resolve_tac ctxt @{thms reflexive} i
  | \<^Const_>\<open>Pure.eq _\<close> $ (\<^Const_>\<open>QREGISTER_of' _ _\<close> $ _) $ _ =>
      print_here_tac ctxt \<^here>
      THEN
      resolve_tac ctxt @{thms} 1
    ))
\<close>
 *)

definition \<open>QREGISTER_pair' F G = (case (F,G) of (Some F', Some G') \<Rightarrow> Some (QREGISTER_pair F' G')
  | _ \<Rightarrow> None)\<close>

lemma x7: \<open>QREGISTER_pair (QREGISTER_chain qSnd F) (QREGISTER_chain qFst G)
= QREGISTER_pair (QREGISTER_chain qFst G) (QREGISTER_chain qSnd F)\<close>
  sorry
lemma x6: \<open>QREGISTER_pair (QREGISTER_chain qSnd F) QREGISTER_fst
= QREGISTER_pair QREGISTER_fst (QREGISTER_chain qSd F)\<close>
  sorry
lemma x8: \<open>QREGISTER_pair QREGISTER_snd (QREGISTER_chain qFst G)
= QREGISTER_pair (QREGISTER_chain qFst G) QREGISTER_snd\<close>
  sorry


ML "open Misc"

lemma QREGISTER_of_empty_qregister: \<open>QREGISTER_of empty_qregister = QREGISTER_unit\<close>
  sorry


ML \<open>
fun qcomplement_of_index_qregister ctxt ct = let
  val _ = Prog_Variables.is_index_qregister (Thm.term_of ct)
          orelse raise CTERM ("qcomplement_of_index_qregister: not an index qregister", [ct])
  val index = Thm.maxidx_of_cterm ct + 1
  val (inT,outT) = dest_qregisterT (Thm.typ_of_cterm ct)
  val x_inT = TVar(("'x", index), [])
  val qcomplement_const = Thm.cterm_of ctxt \<^Const>\<open>qcomplements inT outT x_inT\<close>
  val x = Thm.cterm_of ctxt (Var (("x", index), \<^Type>\<open>qregister x_inT outT\<close>))
  val goal =  (* qcomplements ct ? *)
      Thm.apply (Thm.apply qcomplement_const ct) x |> Thm.apply \<^cterm>\<open>Trueprop\<close>
  val thm = Goal.prove_internal \<^context> [] goal (K (qcomplements_tac ctxt 1))
  val complement = thm |> Thm.cprop_of |> Thm.dest_arg |> Thm.dest_arg
  val _ = Prog_Variables.is_index_qregister (Thm.term_of complement)
          orelse raise CTERM ("qcomplement_of_index_qregister: failed to compute index-register", [ct, complement])
in (complement, thm) end
;;
qcomplement_of_index_qregister \<^context> \<^cterm>\<open>\<lbrakk>\<lbrakk>#2\<rbrakk>\<^sub>q, \<lbrakk>#3\<rbrakk>\<^sub>q, \<lbrakk>#1\<rbrakk>\<^sub>q, \<lbrakk>#5.\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q\<close>
\<close>


(* TODO: Implement TTIR-tactics for this. *)
(* For index-register F *)
definition \<open>TTIR_COMPLEMENT F G \<longleftrightarrow> qcomplements F G\<close>
(* For index-iso-register F *)
definition \<open>TTIR_INVERSE F G \<longleftrightarrow> 
  qregister_chain F G = qregister_id \<and> qregister_chain G F = qregister_id\<close>

lemma translate_to_index_registers_space_div_unlift:
  fixes A' :: \<open>'a ell2 ccsubspace\<close> and G :: \<open>('b,'a) qregister\<close>
    and F :: \<open>('c,'a) qregister\<close> and FG :: \<open>('d,'a) qregister\<close>
  assumes \<open>TTIR_APPLY_QREGISTER_SPACE A' F A\<close>
  assumes \<open>TTIR_LUB F G FG F' G'\<close>
  assumes \<open>TTIR_COMPLEMENT G' L\<close>
  assumes \<open>TTIR_INVERSE \<lbrakk>L, G'\<rbrakk>\<^sub>q H\<close>
  shows \<open>TTIR_APPLY_QREGISTER_SPACE (space_div A' \<psi> G)
          (qregister_chain FG L) (space_div_unlifted (apply_qregister_space (qregister_chain H F') A) \<psi>)\<close>
proof -
  from \<open>TTIR_COMPLEMENT G' L\<close>
  have [simp]: \<open>qregister \<lbrakk>G', L\<rbrakk>\<^sub>q\<close>
    by (simp add: TTIR_COMPLEMENT_def iso_qregister_def qcomplements_def')
  have F'_decomp: \<open>F' = qregister_chain (qregister_chain \<lbrakk>L, G'\<rbrakk> H) F'\<close>
    using TTIR_INVERSE_def assms(4) by force

  have \<open>space_div A' \<psi> G = space_div (A \<guillemotright> F') \<psi> G' \<guillemotright> FG\<close>
    using assms by (simp add: space_div_lift TTIR_APPLY_QREGISTER_SPACE_def TTIR_LUB_def)
  also have \<open>\<dots> = space_div (A \<guillemotright> F' \<guillemotright> H \<guillemotright> \<lbrakk>L,G'\<rbrakk>) \<psi> G' \<guillemotright> FG\<close>
    apply (subst F'_decomp) by simp
  also have \<open>\<dots> = space_div_unlifted (A \<guillemotright> F' \<guillemotright> H) \<psi> \<guillemotright> L \<guillemotright> FG\<close>
    by (simp add: space_div_space_div_unlifted)
  also have \<open>\<dots> = (space_div_unlifted (A \<guillemotright> qregister_chain H F') \<psi>) \<guillemotright> (qregister_chain FG L)\<close>
    by simp
  finally show ?thesis
    by (simp add: TTIR_APPLY_QREGISTER_SPACE_def)
qed

(* Use in this form? *)
lemma space_div_space_div_unlifted_inv:
  assumes \<open>qcomplements Q R\<close>
  shows \<open>space_div A \<psi> Q = 
            space_div_unlifted (apply_qregister_space (qregister_inv \<lbrakk>R,Q\<rbrakk>) A) \<psi> \<guillemotright> R\<close>
proof -
  from assms have \<open>qcomplements R Q\<close>
    by (meson complements_sym qcomplements.rep_eq)
  define A' where \<open>A' = apply_qregister_space (qregister_inv \<lbrakk>R,Q\<rbrakk>) A\<close>
  have \<open>qregister_chain \<lbrakk>R,Q\<rbrakk> (qregister_inv \<lbrakk>R,Q\<rbrakk>) = qregister_id\<close>
    apply (rule iso_qregister_chain_inv)
    using \<open>qcomplements R Q\<close> by (simp add: qcomplements_def')
  then have \<open>space_div A \<psi> Q = space_div (apply_qregister_space \<lbrakk>R,Q\<rbrakk> A') \<psi> Q\<close>
    by (metis (no_types, opaque_lifting) A'_def apply_qregister_space_id qregister_chain_apply_space)
  also have \<open>\<dots> = apply_qregister_space R (space_div_unlifted A' \<psi>)\<close>
    using space_div_space_div_unlifted assms iso_qregister_def qcomplements_def' by blast
  finally show ?thesis
    by (simp add: A'_def)
qed

lemma \<open>qregister_chain (\<lbrakk>\<lbrakk>#1\<rbrakk>\<^sub>q, \<lbrakk>#2\<rbrakk>\<^sub>q, \<lbrakk>#4.\<rbrakk>\<^sub>q\<rbrakk>\<^sub>q) empty_qregister = xxx\<close>
  apply (tactic \<open>CONVERSION (top_sweep_conv normalize_register_conv \<^context>) 1\<close>)
  oops

lemma lemma_724698:
  fixes C :: "(bit, qu) qregister" and A :: "(bit, qu) qregister" and B :: "(bit, qu) qregister"
  assumes [register]: \<open>declared_qvars \<lbrakk>C, A, B\<rbrakk>\<close>
  shows "qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q (C::(bit, qu) qregister) \<equiv>\<qq> qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q A \<le> \<CC>\<ll>\<aa>[\<parallel>EPR\<parallel> = 1] \<sqinter> (\<CC>\<ll>\<aa>[isometry CNOT] \<sqinter> (apply_qregister \<lbrakk>qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q C, qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q A\<rbrakk>\<^sub>q CNOT* *\<^sub>S (\<CC>\<ll>\<aa>[isometry hadamard] \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q C) hadamard* *\<^sub>S ((let M = computational_basis in \<CC>\<ll>\<aa>[mtotal M] \<sqinter> (\<Sqinter>z. let P = apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q A) (mproj M z) *\<^sub>S \<top> in (let M = computational_basis in \<CC>\<ll>\<aa>[mtotal M] \<sqinter> (\<Sqinter>za. let P = apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q C) (mproj M za) *\<^sub>S \<top> in (\<CC>\<ll>\<aa>[z \<noteq> 1] + \<CC>\<ll>\<aa>[isometry pauliX] \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B) pauliX* *\<^sub>S ((\<CC>\<ll>\<aa>[za \<noteq> 1] + \<CC>\<ll>\<aa>[isometry pauliZ] \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B) pauliZ* *\<^sub>S (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B \<equiv>\<qq> qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q A \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B) pauliZ *\<^sub>S \<top>)))) \<sqinter> (\<CC>\<ll>\<aa>[za = 1] + qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B \<equiv>\<qq> qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q A) \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B) pauliX *\<^sub>S \<top>)))) \<sqinter> (\<CC>\<ll>\<aa>[z = 1] + (\<CC>\<ll>\<aa>[za \<noteq> 1] + \<CC>\<ll>\<aa>[isometry pauliZ] \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B) pauliZ* *\<^sub>S (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B \<equiv>\<qq> qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q A \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B) pauliZ *\<^sub>S \<top>)))) \<sqinter> (\<CC>\<ll>\<aa>[za = 1] + qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B \<equiv>\<qq> qregister_chain \<lbrakk>#2.\<rbrakk>\<^sub>q A)) \<sqinter> P + - P)) \<sqinter> P + - P)) \<sqinter> (apply_qregister (qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q C) hadamard *\<^sub>S \<top>))) \<sqinter> (apply_qregister \<lbrakk>qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q C, qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q A\<rbrakk>\<^sub>q CNOT *\<^sub>S \<top>)))) \<div> EPR\<guillemotright>\<lbrakk>qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q A, qregister_chain \<lbrakk>#1\<rbrakk>\<^sub>q B\<rbrakk>\<^sub>q"
  apply translate_to_index_registers
  apply (simp add: quantum_equality_full_def_let space_div_space_div_unlifted)
  apply (tactic \<open>CONVERSION (top_everywhere_conv normalize_register_conv \<^context>) 1\<close>)
  apply (simp only: apply_qregister_id apply_qregister_space_id)
  apply (tactic \<open>CONVERSION (top_everywhere_conv qregister_to_cregister_conv \<^context>) 1\<close>)
  apply (tactic \<open>CONVERSION (top_everywhere_conv apply_qregister_to_cregister_conv \<^context>) 1\<close>)
  apply (tactic \<open>CONVERSION (top_everywhere_conv cregister_lens_conv \<^context>) 1\<close>)
  using [[ML_print_depth=30]]
  using [[show_types]]
  apply (tactic \<open>CONVERSION (top_everywhere_conv ((* wrap_dbg *) permute_and_tensor1_cblinfun_conv) \<^context>) 1\<close>)
  (* apply (tactic \<open>foc [1,1,0,1,1,1,1,0,1,1,1,0,0,1,0,1,1,1,1,0,1,1,1,1,0,1,1,1,0,1,0,1,1,1,1,0,1,1,1,1]\<close>) *)
  (* apply (tactic \<open>foc [0,1,0,1,1,1,0,1,0,1,1,1,1,1,1,0,1,1,1,1,0,1,1,1,1,0,1,0,1,1,1,0,1,0,1,1,1,1,1,1]\<close>) *)
  (* apply (tactic \<open>foc [0,1,0,1,1,1,1,0,1,1,1,1,1,0,1,0]\<close>) *)
  (* apply (tactic \<open>CONVERSION Thm.eta_conversion 1\<close>) *)
  (* apply (tactic \<open>CONVERSION (Thm.beta_conversion true) 1\<close>) *)
  (* apply (tactic \<open>CONVERSION (top_everywhere_conv (wrap_dbg permute_and_tensor1_cblinfun_conv) \<^context>) 1\<close>) *)
(* TODO: Still contains: (Proj (apply_qregister qregister_id pauliZ *\<^sub>S apply_qregister_space empty_qregister \<top>))) *)
  apply simp x

(* XXXXXX *)

  apply (simp add: join_registers   ZZZ
cong del: if_weak_cong 
cong: permute_and_tensor1_mat'_cong
add:
    permute_and_tensor1_cblinfun_code_prep 
    

   case_prod_beta if_distrib[of fst] if_distrib[of snd] prod_eq_iff 

  div_leq_simp mod_mod_cancel 

   enum_index_prod_def fst_enum_nth snd_enum_nth enum_index_nth if_distrib[of enum_index] 
   enum_nth_injective 

  (* quantum_equality_full_def_let space_div_space_div_unlifted INF_lift Cla_inf_lift Cla_plus_lift Cla_sup_lift *)
  (* top_leq_lift top_geq_lift bot_leq_lift bot_geq_lift top_eq_lift bot_eq_lift top_eq_lift2 bot_eq_lift2 *)


 flip:
 (* prepare_for_code_flip *)

)
  
  (* apply prepare_for_code *)
   apply eval 
  by -

(* (* TODO keep? *)
lemma qregister_chain_unit_right[simp]: \<open>qregister F \<Longrightarrow> qregister_chain F qvariable_unit = qvariable_unit\<close>
  by (simp add: qvariable_unit_def)
lemma qregister_chain_unit_left[simp]: \<open>qregister F \<Longrightarrow> qregister_chain qvariable_unit F = qvariable_unit\<close>
  by (simp add: qvariable_unit_def) *)


(* TODO keep? *)
lemma qregister_conversion_chain:
  assumes \<open>qregister_le F G\<close> \<open>qregister_le G H\<close>
  shows \<open>qregister_chain (qregister_conversion G H) (qregister_conversion F G) = qregister_conversion F H\<close>
  using assms unfolding qregister_le_def apply (transfer fixing: F G H) apply transfer
  by (auto intro!: ext qregister_conversion_raw_register simp: f_inv_into_f range_subsetD)


(* TODO keep? *)
lemma permute_and_tensor1_cblinfun_butterfly: 
  fixes f :: \<open>_::finite \<Rightarrow> _::finite\<close>
  assumes [simp]: \<open>bij f\<close> \<open>\<And>x y. R x y\<close>
  shows \<open>permute_and_tensor1_cblinfun f R (butterket a b) = butterket (inv f a) (inv f b)\<close>
proof (rule equal_ket, rule Rep_ell2_inject[THEN iffD1], rule ext)
  fix i j
  have \<open>Rep_ell2 (permute_and_tensor1_cblinfun f R (butterket a b) \<cdot> ket i) j = 
          Rep_ell2 ((ket b \<bullet>\<^sub>C ket (f i)) *\<^sub>C ket a) (f j)\<close>
    by auto
  also have \<open>\<dots> = (if b=f i then 1 else 0) * (if a=f j then 1 else 0)\<close>
    by (auto simp add: scaleC_ell2.rep_eq ket.rep_eq)
  also have \<open>\<dots> = (if inv f b=i then 1 else 0) * (if inv f a=j then 1 else 0)\<close>
    by (smt (verit, del_insts) assms(1) assms(2) bij_inv_eq_iff)
  also have \<open>\<dots> = Rep_ell2 ((ket (inv f b) \<bullet>\<^sub>C ket i) *\<^sub>C ket (inv f a)) j\<close>
    by (simp add: scaleC_ell2.rep_eq ket.rep_eq)
  also have \<open>\<dots> = Rep_ell2 (butterket (inv f a) (inv f b) \<cdot> ket i) j\<close>
    by auto
  finally show \<open>Rep_ell2 (permute_and_tensor1_cblinfun f R (butterket a b) \<cdot> ket i) j
                   = Rep_ell2 (butterket (inv f a) (inv f b) \<cdot> ket i) j\<close>
    by -
qed

(* TODO: to bounded operators *)
declare enum_idx_correct[simp]


