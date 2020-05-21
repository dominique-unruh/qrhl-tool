theory O2H
  imports Programs
begin

(* TODO remove *)
definition "PROGRAM_EQUAL x y = (x=y)" for x y :: program

lemma o2h[unfolded PROGRAM_EQUAL_def]:
  fixes q :: nat and b :: "bit variable" and rho :: program_state and count :: "nat variable"
    and Find :: "bool variable" and distr :: "_ distr"
    and z :: "_ variable" and G H :: "('a::universe \<Rightarrow> 'b::{universe,xor_group}) variable" and S :: "'a set variable"
    and adv :: oracle_program and X :: "'a variable" and Y :: "'b variable"
    and in_S :: "bit variable" and Count :: "oracle_program"
    and localsC :: "'c variables" and localsQ :: "'d variables"

  assumes "PROGRAM_EQUAL game_left (block [assign \<lbrakk>count\<rbrakk> Expr[0], sample \<lbrakk>S,G,H,z\<rbrakk> Expr[distr], localvars localsC localsQ [instantiateOracles adv [instantiateOracles Count [queryG]]]])"
  assumes "PROGRAM_EQUAL game_right (block [assign \<lbrakk>count\<rbrakk> Expr[0], sample \<lbrakk>S,G,H,z\<rbrakk> Expr[distr], localvars localsC localsQ [instantiateOracles adv [instantiateOracles Count [queryH]]]])"
  assumes "PROGRAM_EQUAL game_find (block [assign \<lbrakk>count\<rbrakk> Expr[0], sample \<lbrakk>S,G,H,z\<rbrakk> Expr[distr], assign \<lbrakk>Find\<rbrakk> Expr[False], localvars localsC localsQ [instantiateOracles adv [instantiateOracles Count [queryGS]]]])"

  assumes "\<And>P. PROGRAM_EQUAL (instantiateOracles Count [P]) (block [P, assign \<lbrakk>count\<rbrakk> (expression \<lbrakk>count\<rbrakk> (\<lambda>count. count+1))])"

  assumes "PROGRAM_EQUAL queryG (block [qapply \<lbrakk>X,Y\<rbrakk> (expression \<lbrakk>G\<rbrakk> (\<lambda>G. Uoracle G))])"
  assumes "PROGRAM_EQUAL queryGS (block [measurement \<lbrakk>in_S\<rbrakk> \<lbrakk>X\<rbrakk> (expression \<lbrakk>S\<rbrakk> (\<lambda>S. binary_measurement (proj_classical_set S))),
                            ifthenelse (expression \<lbrakk>in_S\<rbrakk> (\<lambda>in_S. in_S=1)) [assign \<lbrakk>Find\<rbrakk> Expr[True]] [],
                            queryG])"
  assumes "PROGRAM_EQUAL queryH (block [qapply \<lbrakk>X,Y\<rbrakk> (expression \<lbrakk>H\<rbrakk> (\<lambda>H. Uoracle H))])"

  assumes "distinct_qvars \<lbrakk>b,count,Find,z,G,H,S,in_S,X,Y\<rbrakk>"

  assumes "disjnt (fvc_oracle_program adv) (set (variable_names \<lbrakk>count,Find,G,H,S,in_S\<rbrakk>))" (* adv can access b,z,X,Y *)

  assumes "probability (expression \<lbrakk>count\<rbrakk> (\<lambda>count. count\<le>q)) game_left rho = 1"
  assumes "probability (expression \<lbrakk>count\<rbrakk> (\<lambda>count. count\<le>q)) game_right rho = 1"
  assumes "probability (expression \<lbrakk>count\<rbrakk> (\<lambda>count. count\<le>q)) game_find rho = 1"

  defines "Pleft == probability (expression \<lbrakk>b\<rbrakk> (\<lambda>b. b=1)) game_left rho"
  defines "Pright == probability (expression \<lbrakk>b\<rbrakk> (\<lambda>b. b=1)) game_right rho"
  defines "Pfind == probability (expression \<lbrakk>Find\<rbrakk> (\<lambda>Find. Find)) game_find rho"

  assumes "\<And>S G H z x. (S,G,H,z) \<in> supp distr \<Longrightarrow> x\<notin>S \<Longrightarrow> G x = H x"

  shows "abs (Pleft - Pright) \<le> 2 * sqrt( (1 + real q)*Pfind )"
    by (cheat O2H)

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

fun free_vars_tac ctxt =
  let val fact = Proof_Context.get_fact ctxt (Facts.named "program_fv")
  in 
     Misc.succeed_or_error_tac' (simp_tac (clear_simpset ctxt addsimps fact)) ctxt
      (fn t => "Could not determine free variables of adversary. Problematic claim: "^Syntax.string_of_term ctxt t)
   THEN'
     Misc.succeed_or_error_tac' (SOLVED' (simp_tac ctxt))
        ctxt (fn t => "Could not prove that the adversary contains no forbidden variables. Problematic claim: "^Syntax.string_of_term ctxt t)
  end

fun distinct_vars_tac ctxt =
  Misc.succeed_or_error_tac' (SOLVED' (simp_tac ctxt)) ctxt (fn t => "Cannot prove that the variables are distinct: " ^ Syntax.string_of_term ctxt t)

fun o2h_tac ctxt = 
  let val pb_tac = program_body_tac "O2H" ctxt
      val resolve_o2h = Misc.succeed_or_error_tac' (resolve_tac ctxt @{thms o2h}) ctxt
         (K "Goal should be exactly of the form '(Pr[b=1:left(rho)] - Pr[b=1:right(rho)]) <= 2 * sqrt( (1+real q) * Pr[Find:find(rho)])'")
   in
    resolve_o2h
    THEN' pb_tac
    THEN' pb_tac
    THEN' pb_tac
    THEN' pb_tac
    THEN' pb_tac
    THEN' pb_tac
    THEN' pb_tac
    THEN' distinct_vars_tac ctxt
    THEN' free_vars_tac ctxt
  end
end
\<close>

variables classical b :: bit and classical Find :: bool
  and classical S :: "string set" and classical G :: "string \<Rightarrow> bit" and classical H :: "string \<Rightarrow> bit"
  and classical z :: "nat list" and classical count :: nat and quantum X :: string and quantum Y :: bit
and classical in_S :: bit
begin
definition test_distr :: "(string set * (string\<Rightarrow>bit) * (string\<Rightarrow>bit) * nat list) distr" where "test_distr = undefined"
definition adv :: oracle_program where "adv = undefined"
definition Count :: oracle_program where "Count = undefined"

definition [program_bodies]: "queryG = (block [qapply \<lbrakk>X,Y\<rbrakk> Expr[Uoracle G]])"
definition [program_bodies]: "queryH = (block [qapply \<lbrakk>X,Y\<rbrakk> Expr[Uoracle H]])"
definition [program_bodies]: "queryGS =  (block [measurement \<lbrakk>var_in_S\<rbrakk> \<lbrakk>X\<rbrakk> Expr[binary_measurement (proj_classical_set S)],
                            ifthenelse Expr[in_S=1] [assign \<lbrakk>var_Find\<rbrakk> Expr[True]] [],
                            queryG])"

definition [program_bodies]: "left = block [assign \<lbrakk>var_count\<rbrakk> Expr[0], sample \<lbrakk>var_S, var_G, var_H, var_z\<rbrakk> Expr[test_distr],
        localvars \<lbrakk>\<rbrakk> \<lbrakk>\<rbrakk> [instantiateOracles adv [instantiateOracles Count [queryG]]]]"
definition [program_bodies]: "right = block [assign \<lbrakk>var_count\<rbrakk> Expr[0], sample \<lbrakk>var_S, var_G, var_H, var_z\<rbrakk> Expr[test_distr],
        localvars \<lbrakk>\<rbrakk> \<lbrakk>\<rbrakk> [instantiateOracles adv [instantiateOracles Count [queryH]]]]"
definition [program_bodies]: "findG = (block [assign \<lbrakk>var_count\<rbrakk> Expr[0], sample \<lbrakk>var_S,var_G,var_H,var_z\<rbrakk> Expr[test_distr], assign \<lbrakk>var_Find\<rbrakk> Expr[False], 
        localvars \<lbrakk>\<rbrakk> \<lbrakk>\<rbrakk> [instantiateOracles adv [instantiateOracles Count [queryGS]]]])"

lemma [program_bodies]: "instantiateOracles Count [P] = block [P, assign \<lbrakk>var_count\<rbrakk> Expr[count+1]]" for P  
  by (cheat Count)

lemma fv_adv[program_fv]: "fvc_oracle_program adv = set (variable_names \<lbrakk>X,Y,var_b,var_z\<rbrakk>)" by (cheat fv_adv)

lemma "abs ( Pr[b=1:left(rho)] - Pr[b=1:right(rho)] ) <= 2 * sqrt( (1+real q) * Pr[Find:findG(rho)] )"
  apply (tactic \<open>O2H.o2h_tac \<^context> 1\<close>)
  oops

end

end

