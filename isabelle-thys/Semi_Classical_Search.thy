theory Semi_Classical_Search
  imports Programs O2H
begin

lemma semi_classical_search:
  fixes q :: nat and b :: "bit variable" and rho :: program_state and count :: "nat variable"
    and Find :: "bool variable" and distr :: "_ distr"
    and z :: "_ variable" and G :: "('a::universe \<Rightarrow> 'b::{universe,xor_group}) variable" and S :: "'a set variable"
    and adv :: oracle_program and X :: "'a variable" and Y :: "'b variable"
    and in_S :: "bit variable" and Count :: "oracle_program"
    and stop_at :: "nat variable" and "guess" :: "'a variable"

  assumes "game_left  = block [assign \<lbrakk>count\<rbrakk> Expr[0], sample \<lbrakk>S,G,z\<rbrakk> Expr[distr], 
                        assign \<lbrakk>var_Find\<rbrakk> Expr[False],
                        instantiateOracles adv [instantiateOracles Count [queryGS]]]"
  assumes "game_right = (block [assign \<lbrakk>count\<rbrakk> Expr[0], sample \<lbrakk>stop_at\<rbrakk> Expr[uniform {..<q}],
                         sample \<lbrakk>S,G,z\<rbrakk> Expr[distr], 
                         instantiateOracles adv [instantiateOracles Count [queryGM]]])"

  assumes "\<And>P. (instantiateOracles Count [P]) = (block [P, assign \<lbrakk>count\<rbrakk> (expression \<lbrakk>count\<rbrakk> (\<lambda>count. count+1))])"

  assumes "queryGS = (block [measurement \<lbrakk>in_S\<rbrakk> \<lbrakk>X\<rbrakk> (expression \<lbrakk>S\<rbrakk> (\<lambda>S. binary_measurement (proj_classical_set S))),
                            ifthenelse (expression \<lbrakk>in_S\<rbrakk> (\<lambda>in_S. in_S=1)) [assign \<lbrakk>Find\<rbrakk> Expr[True]] [],
                            queryG])"
  assumes "queryGM = block [ifthenelse (expression \<lbrakk>count,stop_at\<rbrakk> (\<lambda>(c,s). c=s)) 
                             [measurement \<lbrakk>guess\<rbrakk> \<lbrakk>X\<rbrakk> Expr[computational_basis]] [], 
                            queryG]"
  assumes "queryG = (block [qapply \<lbrakk>X,Y\<rbrakk> (expression \<lbrakk>G\<rbrakk> (\<lambda>G. Uoracle G))])"

  assumes "distinct_qvars \<lbrakk>count,Find,z,G,S,in_S,X,Y,stop_at,guess\<rbrakk>"

  assumes "disjnt (fvc_oracle_program adv) (set (variable_names \<lbrakk>count,stop_at,guess,Find,G,S,in_S\<rbrakk>))" (* adv can access b,z,X,Y *)

  assumes "probability (expression \<lbrakk>count\<rbrakk> (\<lambda>count. count\<le>q)) game_left rho = 1"
  assumes "probability (expression \<lbrakk>count\<rbrakk> (\<lambda>count. count\<le>q)) game_right rho = 1"

  defines "Pleft == probability (expression \<lbrakk>Find\<rbrakk> (\<lambda>Find. Find)) game_left rho"
  defines "Pright == probability (expression \<lbrakk>guess,S\<rbrakk> (\<lambda>(g,S). g\<in>S)) game_right rho"

  shows "Pleft \<le> 4 * real q * Pright"
    by (cheat Semi_Classical_Search)

ML \<open>
structure Semi_Classical_Search = struct

fun semi_classical_search_tac ctxt = 
  let val pb_tac = O2H.program_body_tac "semiclassical search" ctxt
      val resolve_scs = Misc.succeed_or_error_tac' (resolve_tac ctxt @{thms semi_classical_search}) ctxt
         (K "Goal should be exactly of the form 'Pr[Find:left(rho)] \<le> 4 * real q * Pr[guess\<in>S:right(rho)]'")
   in
    resolve_scs
    THEN' pb_tac
    THEN' pb_tac
    THEN' pb_tac
    THEN' pb_tac
    THEN' pb_tac
    THEN' pb_tac
    THEN' O2H.distinct_vars_tac ctxt
    THEN' O2H.free_vars_tac ctxt
  end
end
\<close>

(* Test *)
variables classical b :: bit and classical Find :: bool
  and classical S :: "string set" and classical G :: "string \<Rightarrow> bit"
  and classical z :: "nat list" and classical count :: nat and quantum X :: string and quantum Y :: bit
  and classical in_S :: bit and classical "guess" :: "string" and classical stop_at :: nat
begin
definition test_distr :: "(string set * (string\<Rightarrow>bit) * nat list) distr" where "test_distr = undefined"
definition adv :: oracle_program where "adv = undefined"
definition Count :: oracle_program where "Count = undefined"

definition [program_bodies]: "queryG = (block [qapply \<lbrakk>X,Y\<rbrakk> Expr[Uoracle G]])"
definition [program_bodies]: "queryGS =  (block [measurement \<lbrakk>var_in_S\<rbrakk> \<lbrakk>X\<rbrakk> Expr[binary_measurement (proj_classical_set S)],
                            ifthenelse Expr[in_S=1] [assign \<lbrakk>var_Find\<rbrakk> Expr[True]] [],
                            queryG])"
definition [program_bodies]: "queryGM = block [
  ifthenelse Expr[count=stop_at] [measurement \<lbrakk>var_guess\<rbrakk> \<lbrakk>X\<rbrakk> Expr[computational_basis]] [], queryG]"

(*   assumes "game_right = (block [assign \<lbrakk>count\<rbrakk> Expr[0], sample \<lbrakk>stop_at\<rbrakk> Expr[uniform {..<q}],
                         sample \<lbrakk>S,G,z\<rbrakk> Expr[distr], 
                         instantiateOracles adv [instantiateOracles Count [queryGM]]])"
 *)

definition "q = (123::nat)"

definition [program_bodies]: "left = block [assign \<lbrakk>var_count\<rbrakk> Expr[0], 
        sample \<lbrakk>var_S, var_G, var_z\<rbrakk> Expr[test_distr],
        assign \<lbrakk>var_Find\<rbrakk> (const_expression False),
        instantiateOracles adv [instantiateOracles Count [queryGS]]]"
definition [program_bodies]: "right = block [assign \<lbrakk>var_count\<rbrakk> Expr[0], 
        sample \<lbrakk>var_stop_at\<rbrakk> Expr[uniform {..<q}],
        sample \<lbrakk>var_S, var_G, var_z\<rbrakk> Expr[test_distr],
        instantiateOracles adv [instantiateOracles Count [queryGM]]]"

lemma [program_bodies]: "instantiateOracles Count [P] = block [P, assign \<lbrakk>var_count\<rbrakk> Expr[count+1]]" for P  
  by (cheat Count)

lemma fv_adv[program_fv]: "fvc_oracle_program adv = set (variable_names \<lbrakk>X,Y,var_b,var_z\<rbrakk>)" by (cheat fv_adv)

lemma "Pr[Find:left(rho)] \<le> 4 * real q * Pr[guess\<in>S:right(rho)]"
  apply (tactic \<open>Semi_Classical_Search.semi_classical_search_tac \<^context> 1\<close>)
  oops

end

end

