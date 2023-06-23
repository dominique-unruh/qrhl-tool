theory O2H
  imports Programs
begin

lemma o2h:
  fixes q :: nat and b :: "bit cvariable" and rho :: program_state and count :: "nat cvariable"
    and Find :: "bool cvariable" and distr :: "_ distr"
    and z :: "_ cvariable" and G H :: "('a \<Rightarrow> 'b::xor_group) cvariable" and S :: "'a set cvariable"
    and adv :: oracle_program and X :: "'a qvariable" and Y :: "'b qvariable"
    and in_S :: "bit cvariable" and Count :: "oracle_program"
    and localsC :: "'c cvariable" and localsQ :: "'d qvariable"

  assumes "game_left = (block [assign count (\<lambda>_.0), sample \<lbrakk>S,G,H,z\<rbrakk>\<^sub>c Expr[distr], localvars localsC localsQ [instantiateOracles adv [instantiateOracles Count [queryG]]]])"
  assumes "game_right = (block [assign count (\<lambda>_.0), sample \<lbrakk>S,G,H,z\<rbrakk>\<^sub>c Expr[distr], localvars localsC localsQ [instantiateOracles adv [instantiateOracles Count [queryH]]]])"
  assumes "game_find = (block [assign count (\<lambda>_.0), sample \<lbrakk>S,G,H,z\<rbrakk>\<^sub>c Expr[distr], assign Find (\<lambda>_. False), localvars localsC localsQ [instantiateOracles adv [instantiateOracles Count [queryGS]]]])"

  assumes "\<And>P. (instantiateOracles Count [P]) = (block [P, assign \<lbrakk>count\<rbrakk> (\<lambda>mem. getter count mem + 1)])"

  assumes "queryG = (block [qapply \<lbrakk>X,Y\<rbrakk> (\<lambda>mem. Uoracle (getter G mem))])"
  assumes "queryGS = (block [measurement \<lbrakk>in_S\<rbrakk> \<lbrakk>X\<rbrakk> (\<lambda>m. binary_measurement (proj_classical_set (getter S m))),
                            ifthenelse (\<lambda>m. getter in_S m = 1) [assign \<lbrakk>Find\<rbrakk> Expr[True]] [],
                            queryG])"
  assumes "queryH = (block [qapply \<lbrakk>X,Y\<rbrakk> (\<lambda>m. Uoracle (getter H m))])"

  assumes "distinct_cvars \<lbrakk>b,count,Find,z,G,H,S,in_S\<rbrakk>\<^sub>c"
  assumes "distinct_qvars \<lbrakk>X,Y\<rbrakk>"

  assumes "Cccompatible (fvc_oracle_program adv) \<lbrakk>count,Find,G,H,S,in_S\<rbrakk>\<^sub>c" (* adv can access b,z,X,Y *)

  assumes "probability (\<lambda>m. getter count m \<le> q) game_left rho = 1"
  assumes "probability (\<lambda>m. getter count m \<le> q) game_right rho = 1"
  assumes "probability (\<lambda>m. getter count m \<le> q) game_find rho = 1"

  defines "Pleft == probability (\<lambda>m. getter b m = 1) game_left rho"
  defines "Pright == probability (\<lambda>m. getter b m = 1) game_right rho"
  defines "Pfind == probability (\<lambda>m. getter Find m) game_find rho"

  assumes "\<And>S G H z x. (S,G,H,z) \<in> supp distr \<Longrightarrow> x\<notin>S \<Longrightarrow> G x = H x"

  shows "abs (Pleft - Pright) \<le> 2 * sqrt( (1 + real q)*Pfind )"
  sorry

lemmas o2h' = o2h[where localsC="empty_cregister" and localsQ="empty_qregister", 
        unfolded localvars_empty[of "[_]", unfolded block_single]]

ML \<open>
structure O2H = struct
fun program_body_tac forwhom ctxt = SUBGOAL (fn (t,i) =>
  let val fact = Proof_Context.get_fact ctxt (Facts.named "program_bodies")
      val prog = case Logic.strip_assums_concl t of
         Const(\<^const_name>\<open>Trueprop\<close>,_) $ (Const(\<^const_name>\<open>HOL.eq\<close>,_) $ prog $ _) => prog
       | _ => raise TERM("program_body_tac: internal error",[t])
      val progname = Syntax.string_of_term ctxt prog
      val _ = if null (Term.add_vars prog []) then () else 
        raise TERM("program_body_tac: expected program name without schematic vars",[t,prog])
  in 
    Misc.succeed_or_error_tac' (resolve_tac ctxt @{thms trans}) ctxt (K "internal error") i
  THEN
    Misc.succeed_or_error_tac' (solve_tac ctxt fact) ctxt (fn _ =>
           "'" ^ progname ^ "' is not the name of a concrete program") i
  THEN
    Misc.succeed_or_error_tac' (resolve_tac ctxt @{thms refl}) ctxt (fn t =>
          "The body of program '" ^ progname ^ "' is not of the right form for "^forwhom^":\n(The following does not hold: " ^
          Syntax.string_of_term ctxt t ^ ")") i
  end)

(* fun free_vars_tac ctxt =
  let val fact = Proof_Context.get_fact ctxt (Facts.named \<^named_theorems>\<open>program_fv\<close>)
  in 
     Misc.succeed_or_error_tac' (simp_tac (clear_simpset ctxt addsimps fact)) ctxt
      (fn t => "Could not determine free variables of adversary. Problematic claim: "^Syntax.string_of_term ctxt t)
    THEN'
     Misc.succeed_or_error_tac' (SOLVED' (simp_tac ctxt))
        ctxt (fn t => "Could not prove that the adversary contains no forbidden variables. Problematic claim: "^Syntax.string_of_term ctxt t)
  end
 *)

fun o2h_tac' o2h_rule ctxt = 
  let val pb_tac = program_body_tac "O2H" ctxt
      val resolve_o2h = Misc.succeed_or_error_tac' (resolve_tac ctxt [o2h_rule]) ctxt
         (K "Goal should be exactly of the form '(Pr[b=1:left(rho)] - Pr[b=1:right(rho)]) <= 2 * sqrt( (1+real q) * Pr[Find:find(rho)])'")
   in
    resolve_o2h
    THEN' pb_tac (* game_left *)
    THEN' pb_tac (* game_right *)
    THEN' pb_tac (* game_find *)
    THEN' pb_tac (* Count *)
    THEN' pb_tac (* queryG *)
    THEN' pb_tac (* queryGS *)
    THEN' pb_tac (* queryH *)
    THEN' Prog_Variables.distinct_vars_tac ctxt (* cvars *)
    THEN' Prog_Variables.distinct_vars_tac ctxt (* qvars *)
    THEN' Programs.free_vars_tac ctxt
  end

fun o2h_tac ctxt i = Misc.fail_tac_on_LAZY_ERROR (DETERM (o2h_tac' @{thm o2h'} ctxt i))
                     ORELSE o2h_tac' @{thm o2h} ctxt i

(* (* DETERM is needed to make sure LAZY_ERROR is thrown early enough for fail_on_LAZY_ERROR
   to catch it *)
fun o2h_tac ctxt i = Misc.fail_on_LAZY_ERROR (DETERM (o2h_tac' @{thm o2h'} ctxt i))
                     ORELSE o2h_tac' @{thm o2h} ctxt i *)
end
\<close>


typedecl sometype (* TODO remove *)
(* instance sometype :: finite sorry *)

experiment 
  fixes b :: \<open>bit cvariable\<close>
    and Find :: \<open>bool cvariable\<close>
    and S :: \<open>sometype set cvariable\<close>
    and G :: \<open>(sometype \<Rightarrow> bit) cvariable\<close>
    and H :: \<open>(sometype \<Rightarrow> bit) cvariable\<close>
    and z :: \<open>nat list cvariable\<close>
    and count :: \<open>nat cvariable\<close>
    and X :: \<open>sometype qvariable\<close>
    and Y :: \<open>bit qvariable\<close>
    and in_S :: \<open>bit cvariable\<close>
  assumes [simp]: \<open>qcompatible X Y\<close>
    and [simp]: \<open>mutually ccompatible (b,count,Find,z,G,H,S,in_S)\<close>
    and [register]: \<open>cregister b\<close> \<open>cregister Find\<close>
    \<open>cregister count\<close>
begin

definition test_distr :: "(sometype set * (sometype\<Rightarrow>bit) * (sometype\<Rightarrow>bit) * nat list) distr" where "test_distr = undefined"
definition adv :: oracle_program where "adv = undefined"
definition Count :: oracle_program where "Count = undefined"

definition [program_bodies]: "queryG = (block [qapply \<lbrakk>X,Y\<rbrakk> (\<lambda>m. Uoracle (getter G m))])"
definition [program_bodies]: "queryH = (block [qapply \<lbrakk>X,Y\<rbrakk> (\<lambda>m. Uoracle (getter H m))])"
definition [program_bodies]: "queryGS =  (block [measurement \<lbrakk>in_S\<rbrakk> \<lbrakk>X\<rbrakk> (\<lambda>m. binary_measurement (proj_classical_set (getter S m))),
                            ifthenelse (\<lambda>m. getter in_S m=1) [assign \<lbrakk>Find\<rbrakk> Expr[True]] [],
                            queryG])"

(* definition [program_bodies]: "left = block [assign \<lbrakk>count\<rbrakk> (\<lambda>_.0), sample \<lbrakk>S, G, H, z\<rbrakk> (\<lambda>_. test_distr),
        instantiateOracles adv [instantiateOracles Count [queryG]]]"
definition [program_bodies]: "right = block [assign \<lbrakk>count\<rbrakk> (\<lambda>_.0), sample \<lbrakk>S, G, H, z\<rbrakk> (\<lambda>_. test_distr),
        instantiateOracles adv [instantiateOracles Count [queryH]]]"
definition [program_bodies]: "findG = (block [assign \<lbrakk>count\<rbrakk> (\<lambda>_.0), sample \<lbrakk>S,G,H,z\<rbrakk> (\<lambda>_. test_distr), assign \<lbrakk>Find\<rbrakk> (\<lambda>_. False), 
        instantiateOracles adv [instantiateOracles Count [queryGS]]])"
*)

definition [program_bodies]: "left = block [assign \<lbrakk>count\<rbrakk>\<^sub>c (\<lambda>_.0), sample \<lbrakk>S, G, H, z\<rbrakk>\<^sub>c (\<lambda>_. test_distr),
        localvars \<lbrakk>\<rbrakk>\<^sub>c \<lbrakk>X\<rbrakk> [instantiateOracles adv [instantiateOracles Count [queryG]]]]"
definition [program_bodies]: "right = block [assign \<lbrakk>count\<rbrakk>\<^sub>c (\<lambda>_.0), sample \<lbrakk>S, G, H, z\<rbrakk>\<^sub>c (\<lambda>_. test_distr),
        localvars \<lbrakk>\<rbrakk>\<^sub>c \<lbrakk>X\<rbrakk> [instantiateOracles adv [instantiateOracles Count [queryH]]]]"
definition [program_bodies]: "findG = (block [assign \<lbrakk>count\<rbrakk>\<^sub>c (\<lambda>_.0), sample \<lbrakk>S,G,H,z\<rbrakk>\<^sub>c (\<lambda>_. test_distr), assign \<lbrakk>Find\<rbrakk>\<^sub>c (\<lambda>_. False), 
        localvars \<lbrakk>\<rbrakk>\<^sub>c \<lbrakk>X\<rbrakk> [instantiateOracles adv [instantiateOracles Count [queryGS]]]])"

lemma [program_bodies]: "instantiateOracles Count [P] = block [P, assign \<lbrakk>count\<rbrakk>\<^sub>c (\<lambda>m. getter count m + 1)]" for P  
  sorry

lemma fvc_adv[program_fv]: "fvc_oracle_program adv \<le> CREGISTER_of \<lbrakk>b,z\<rbrakk>\<^sub>c" sorry
lemma fvq_adv[program_fv]: "fvq_oracle_program adv \<le> QREGISTER_of \<lbrakk>X,Y\<rbrakk>\<^sub>q" sorry

lemma 
  assumes \<open>Pr[count \<le> q : left(rho)] = 1\<close>
  assumes \<open>Pr[count \<le> q : right(rho)] = 1\<close>
  assumes \<open>Pr[count \<le> q : findG(rho)] = 1\<close>
  assumes \<open>\<And>S G H z x. (S, G, H, z) \<in> supp test_distr \<Longrightarrow> x \<notin> S \<Longrightarrow> G x = H x\<close>
  shows "abs ( Pr[b=1:left(rho)] - Pr[b=1:right(rho)] ) 
            <= 2 * sqrt( (1+real q) * Pr[Find:findG(rho)] )"
  ML_val \<open>Proof_Context.get_fact \<^context> (Facts.named \<^named_theorems>\<open>program_fv\<close>)\<close>
  apply (tactic \<open>O2H.o2h_tac \<^context> 1\<close>)
     apply (auto intro: assms)[4]
  by -
end

end

