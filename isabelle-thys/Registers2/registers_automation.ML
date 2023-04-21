structure Registers_Automation : sig

val distinct_vars_tac : Proof.context -> int -> tactic
val normalize_register_conv : Proof.context -> conv
val normalize_register_conv2 : Proof.context -> conv
val qregister_le_tac : Proof.context -> int -> tactic
val join_registers : Proof.context -> term -> term -> term option
val qregister_lub_tac : Proof.context -> int -> tactic
val register_compats_of : thm -> thm list -> thm list
val register_thms_of : thm -> thm list -> thm list
val QREGISTER_of_index_reg_conv : Proof.context -> conv
val QREGISTER_of_index_reg_reverse_conv : Proof.context -> conv
val INDEX_REGISTER_norm_conv : Proof.context -> conv
val ACTUAL_QREGISTER_tac : Proof.context -> int -> tactic
val QCOMPLEMENT_INDEX_REGISTER_conv : Proof.context -> conv
val qcomplements_tac : Proof.context -> int -> tactic

end = struct

open Registers

(* TODO something more reliable than just simp'ing *)
fun distinct_vars_tac ctxt = let
  val ctxt = (Config.put Simplifier.simp_trace false ctxt) addsimps @{thms 
    ccompatible3 ccompatible3' (* cregister_chain_id *)
    qcompatible3 qcompatible3 qcompatible3' (* qregister_chain_id *)
    Cccompatible_CREGISTER_of Qqcompatible_QREGISTER_of}
  in Misc.succeed_or_error_tac' (SOLVED' (simp_tac ctxt)) ctxt (fn t => "Cannot prove that the variables are variables and distinct (using simp): " ^ Syntax.string_of_term ctxt t) end


(* Normalizes a register (e.g., removes id registers etc.) *)
val normalize_register_conv = 
  Misc.rewrite_with_prover (fn ctxt => distinct_vars_tac ctxt 1)
    @{thms qregister_chain_id[THEN eq_reflection] qregister_id_chain[THEN eq_reflection]
           qregister_chain_pair[symmetric, THEN eq_reflection] pair_fst_snd[THEN eq_reflection]
           qregister_chain_empty_right[THEN eq_reflection] qregister_chain_empty_left[THEN eq_reflection]}

(* Like normalize_register_conv, but prefers \<lbrakk>Fst o X, Fst o Y\<rbrakk> over Fst o \<lbrakk>X, Y\<rbrakk> *)
fun normalize_register_conv2 ctxt = 
  normalize_register_conv ctxt then_conv Conv.top_rewrs_conv @{thms qregister_chain_pair[THEN eq_reflection]} ctxt

(* Tactic to fully prove a goal of the form `qregister_le F G` *)
(* TODO: support cregisters as well *)
fun qregister_le_tac ctxt = let
  fun tac' ctxt i st = st |>
          ((resolve_tac ctxt @{thms qregister_le_refl qregister_le_id} i THEN distinct_vars_tac ctxt i)
          ORELSE
          (resolve_tac ctxt @{thms qregister_le_pair_rightI1 qregister_le_pair_rightI2} i THEN distinct_vars_tac ctxt i THEN tac' ctxt i)
          ORELSE
          (resolve_tac ctxt @{thms qregister_le_pair_leftI} i THEN distinct_vars_tac ctxt i THEN tac' ctxt i THEN tac' ctxt i)
          ORELSE
          (resolve_tac ctxt [@{lemma \<open>qregister Q ==> qregister_le empty_qregister Q\<close> by simp}] i THEN distinct_vars_tac ctxt i)
          )
in SUBGOAL (fn (t,i) => 
  CONVERSION (normalize_register_conv2 ctxt) i 
  (* THEN print_tac ctxt "qregister_le_tac" *)
  THEN 
  (case t of Const(\<^const_name>\<open>Trueprop\<close>,_) $ (Const(\<^const_name>\<open>qregister_le\<close>,_) $ (Const(\<^const_name>\<open>qregister_pair\<close>,_) $ _ $ _) $ _) =>
    (* Why to we have this special case? *)
    resolve_tac ctxt @{thms qregister_le_pair_leftI} i THEN distinct_vars_tac ctxt i THEN qregister_le_tac ctxt i THEN qregister_le_tac ctxt i
  | _ =>  tac' ctxt i))
end

(* Given variables F,G, returns an upper bound FG.
   (Heuristically. Is not guaranteed to be a true upper bound.
   But in simple cases, should be a lub.) *)
(* TODO: support cregisters as well *)
(* TODO: rename \<rightarrow> something with lub *)
fun join_registers (_:Proof.context) F G = if F aconv G then SOME F else let
  val Fs = explode_variable F
  val Gs = explode_variable G
  fun is_id \<^Const_>\<open>qregister_id _\<close> = true
    | is_id _ = false
  val (_, memoryT) = dest_qregisterT (fastype_of F)
  in if exists is_id Fs orelse exists is_id Fs then
        SOME \<^Const>\<open>qregister_id memoryT\<close>
     else if subset (op aconv) (Gs, Fs) then SOME F
     else if subset (op aconv) (Fs, Gs) then SOME G
     else let
      val FGs = Fs @ Gs |> sort_distinct Term_Ord.fast_term_ord
      val FG = implode_variable memoryT FGs
      in
      SOME FG
      end
  end


(* Solves a goal of the form \<open>qregister_le Q ?QR \<and> qregister_le R ?QR\<close> by instantiating ?QR
   as small as possible.
*)
fun qregister_lub_tac ctxt = Misc.MY_SUBGOAL ctxt (fn {ctxt, csubgoal, ...} => let
  (* val _ = \<^print>("qregister_lub_tac", Thm.cterm_of ctxt t) *)
  val (Q,R) = case Thm.term_of csubgoal of
            \<^Const_>\<open>Trueprop\<close> $ (\<^Const_>\<open>conj\<close> $ (\<^Const_>\<open>qregister_le _ _ _\<close> $ Q $ _)
                                              $ (\<^Const_>\<open>qregister_le _ _ _\<close> $ R $ _))
                => (Q,R)
          | _ => error "qregister_lub_tac"
  (* val _ = \<^print> (Q,R) *)
  val QR = case join_registers ctxt Q R of
             SOME QR => QR | NONE => error ("could not find upper bound of " ^ Syntax.string_of_term ctxt Q ^ " and " ^ Syntax.string_of_term ctxt R)
  (* val _ = \<^print> QR *)
  val lemma = @{lemma \<open>qregister_le Q QR \<Longrightarrow> qregister_le R QR \<Longrightarrow> qregister_le Q QR \<and> qregister_le R QR\<close> by simp}
  val lemma = infer_instantiate ctxt [(("QR",0), Thm.cterm_of ctxt QR), (("Q",0), Thm.cterm_of ctxt Q), (("R",0), Thm.cterm_of ctxt R)] lemma
  val tac =
   (* Misc.print_here_tac ctxt \<^here> THEN  *)
    resolve_tac ctxt [lemma] 1
 (* THEN Misc.print_here_tac ctxt \<^here>  *)
    THEN qregister_le_tac ctxt 1
 (* THEN Misc.print_here_tac ctxt \<^here>  *)
    THEN qregister_le_tac ctxt 1
  (* THEN Misc.print_here_tac ctxt \<^here>  *)
  in
    tac ORELSE Misc.error_tac (K "qregister_lub_tac: failed to prove le") ctxt
  end
)


(* Given a term of the form \<open>q/cregister X\<close>, descends into X to find all "elementary" 
registers F (i.e., not pairs) and adds \<open>q/cregister F\<close> to the passed list `regs`.

Useful for adding all those theorems to the simplifier.
*)
fun register_thms_of thm regs = let
  val reg = case Thm.prop_of thm of
      Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>cregister\<close>, _) $ reg) => reg
    | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>qregister\<close>, _) $ reg) => reg
    | _ => raise THM ("register_thms_of: expecting a fact of the form \<open>c/qregister ...\<close>", 0, [thm])
  val regs = case reg of
      Free _ => thm::regs
    | Const(\<^const_name>\<open>cregister_pair\<close>,_) $ _ $ _ =>
        regs |> register_thms_of (@{thm ccompatible_register2} OF [thm])
             |> register_thms_of (@{thm ccompatible_register1} OF [thm])
    | Const(\<^const_name>\<open>qregister_pair\<close>,_) $ _ $ _ =>
        regs |> register_thms_of (@{thm qcompatible_register2} OF [thm])
             |> register_thms_of (@{thm qcompatible_register1} OF [thm])
    | t => raise TERM ("register_thms_of: expecting a fact of the form \<open>c/register ...\<close> where ... is a register tuple of free variables. Got:", [t])
  in regs end

(* Given a term of the form \<open>q/cregister X\<close>, descends into X to find all "elementary" 
pairs of registers that can be deduced to be compatible and adds \<open>q/cregister \<lbrakk>F,G\<rbrakk>\<close> 
to the passed list `compats`

Useful for adding all those theorems to the simplifier.
*)
fun register_compats_of thm compats = case Thm.prop_of thm of
      \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>cregister _ _\<close> $ (\<^Const>\<open>cregister_pair _ _ _\<close> $ (\<^Const>\<open>cregister_pair _ _ _\<close> $ _ $ _) $ _)) =>
        compats |> register_compats_of (@{thm ccompatible3[THEN iffD1, THEN conjunct2, THEN conjunct2]} OF [thm])
                |> register_compats_of (@{thm ccompatible3[THEN iffD1, THEN conjunct2, THEN conjunct1]} OF [thm])
                |> register_compats_of (@{thm ccompatible3[THEN iffD1, THEN conjunct1]} OF [thm])
    | \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>qregister _ _\<close> $ (\<^Const>\<open>qregister_pair _ _ _\<close> $ (\<^Const>\<open>qregister_pair _ _ _\<close> $ _ $ _) $ _)) =>
        compats |> register_compats_of (@{thm qcompatible3[THEN iffD1, THEN conjunct2, THEN conjunct2]} OF [thm])
                |> register_compats_of (@{thm qcompatible3[THEN iffD1, THEN conjunct2, THEN conjunct1]} OF [thm])
                |> register_compats_of (@{thm qcompatible3[THEN iffD1, THEN conjunct1]} OF [thm])
    | \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>cregister _ _\<close> $ (\<^Const>\<open>cregister_pair _ _ _\<close> $ _ $ (\<^Const>\<open>cregister_pair _ _ _\<close> $ _ $ _))) =>
        compats |> register_compats_of (@{thm ccompatible3'[THEN iffD1, THEN conjunct2, THEN conjunct2]} OF [thm])
                |> register_compats_of (@{thm ccompatible3'[THEN iffD1, THEN conjunct2, THEN conjunct1]} OF [thm])
                |> register_compats_of (@{thm ccompatible3'[THEN iffD1, THEN conjunct1]} OF [thm])
    | \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>qregister _ _\<close> $ (\<^Const>\<open>qregister_pair _ _ _\<close> $ _ $ (\<^Const>\<open>qregister_pair _ _ _\<close> $ _ $ _))) =>
        compats |> register_compats_of (@{thm qcompatible3'[THEN iffD1, THEN conjunct2, THEN conjunct2]} OF [thm])
                |> register_compats_of (@{thm qcompatible3'[THEN iffD1, THEN conjunct2, THEN conjunct1]} OF [thm])
                |> register_compats_of (@{thm qcompatible3'[THEN iffD1, THEN conjunct1]} OF [thm])
    | \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>cregister _ _\<close> $ (\<^Const>\<open>cregister_pair _ _ _\<close> $ _ $ _)) =>
        thm :: (@{thm ccompatible_sym} OF [thm]) :: compats
    | \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>qregister _ _\<close> $ (\<^Const>\<open>qregister_pair _ _ _\<close> $ _ $ _)) =>
        thm :: (@{thm qcompatible_sym} OF [thm]) :: compats
    | \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>cregister _ _\<close> $ Free _) => compats
    | \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>qregister _ _\<close> $ Free _) => compats
    | _ => raise THM ("register_compats_of: expecting a fact of the form \<open>c/qregister \<dots>\<close> or \<open>c/qcompatible \<dots>\<close>", 0, [thm])

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

(* Opposite of QREGISTER_of_index_reg_conv *)
val QREGISTER_of_index_reg_reverse_conv =
  Misc.rewrite_with_prover (fn ctxt => distinct_vars_tac ctxt 1)
    (map (fn thm => thm RS @{thm sym} RS @{thm eq_reflection})
          @{thms 
            QREGISTER_of_qregister_pair QREGISTER_of_qregister_chain QREGISTER_of_empty_qregister
            QREGISTER_of_qFst QREGISTER_of_qSnd QREGISTER_of_qregister_id})

(* Brings an INDEX-REGISTER into normal form. (Only for quantum registers)

The normal form of an INDEX-REGISTER is one of the following:
- id
- empty
- R ::= fst | snd | fst o R | snd o R | \<lbrakk>fst o R; snd o R\<rbrakk>

*)
local
  val rules = (map (fn thm => thm RS @{thm eq_reflection}) @{thms 
    Registers_Automation.INDEX_REGISTER_norm_conv_aux1 QREGISTER_pair_QREGISTER_chain QREGISTER_pair_assoc 
    Registers_Automation.INDEX_REGISTER_norm_conv_aux2 QREGISTER_pair_unit_left 
    QREGISTER_pair_unit_right
    QREGISTER_chain_id_left QREGISTER_chain_all_right
    QREGISTER_pair_all_left QREGISTER_pair_all_right
    QREGISTER_pair_fst_snd QREGISTER_pair_snd_fst
    QREGISTER_chain_unit_left QREGISTER_chain_unit_right})
in
fun INDEX_REGISTER_norm_conv ctxt = Raw_Simplifier.rewrite ctxt false rules
end

local
  val simpset = \<^context>  addsimps @{thms 
       ACTUAL_QREGISTER_fst ACTUAL_QREGISTER_snd ACTUAL_QREGISTER_chain
       ACTUAL_QREGISTER_bot ACTUAL_QREGISTER_top ACTUAL_QREGISTER_pair
       ACTUAL_QREGISTER_pair_fst_snd Registers_Automation.ACTUAL_QREGISTER_tac_aux1 Registers_Automation.ACTUAL_QREGISTER_tac_aux2 Registers_Automation.ACTUAL_QREGISTER_tac_aux3 Registers_Automation.ACTUAL_QREGISTER_tac_aux4 Registers_Automation.ACTUAL_QREGISTER_tac_aux5
     ccompatible3 ccompatible3'
      qcompatible3 qcompatible3'
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

(* Rewrites QCOMPLEMENT (INDEX-QREGISTER) into an INDEX-QREGISTER *)
  val simpctxt =
      put_simpset HOL_ss \<^context>
      addsimps
        @{thms 
           Registers_Automation.QCOMPLEMENT_INDEX_REGISTER_conv_aux1 Registers_Automation.QCOMPLEMENT_INDEX_REGISTER_conv_aux2 QCOMPLEMENT_pair_fst_snd QCOMPLEMENT_chain QCOMPLEMENT_snd QCOMPLEMENT_fst QREGISTER_of_qFst QREGISTER_of_qSnd
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

(* Proves a goal of the form \<open>qcomplements F ?X\<close> (instantiating ?X).

TODO: For which F's does this work? Only index-registers?

TODO: If only for index-registers, rename?
*)
fun qcomplements_tac ctxt =
  resolve_tac ctxt @{thms Registers_Automation.qcomplements_tac_aux1} (* Creates three subgoals *)
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

end
