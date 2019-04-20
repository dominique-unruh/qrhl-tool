theory O2H
  imports Programs
begin

(* TODO: correctly define type measurement, then define the following *)
(* TODO: move *)
axiomatization binary_measurement :: "('a,'a) bounded \<Rightarrow> (bit,'a) measurement"
  where binary_measurement_true[simp]: "isProjector P \<Longrightarrow> mproj (binary_measurement P) 1 = P"
    and binary_measurement_false[simp]: "isProjector P \<Longrightarrow> mproj (binary_measurement P) 0 = idOp-P"

(* TODO move (& rename?) *)
definition "projS S = Proj (span {ket s|s. s\<in>S})"

lemma o2h:
  fixes q :: nat and b :: "bit variable" and rho :: program_state and count :: "nat variable"
    and Find :: "bool variable" and distr :: "_ distr"
    and z :: "_ variable" and G H :: "('a::universe \<Rightarrow> 'b::{universe,xor_group}) variable" and S :: "'a set variable"
    and adv :: oracle_program and X :: "'a variable" and Y :: "'b variable"
    and in_S :: "bit variable" and Count :: "oracle_program"

  assumes "game_left == block [assign \<lbrakk>count\<rbrakk> Expr[0], sample \<lbrakk>S,G,H,z\<rbrakk> Expr[distr], instantiateOracles adv [instantiateOracles Count [queryG]]]"
  assumes "game_right == block [assign \<lbrakk>count\<rbrakk> Expr[0], sample \<lbrakk>S,G,H,z\<rbrakk> Expr[distr], instantiateOracles adv [instantiateOracles Count [queryH]]]"
  assumes "game_find == block [assign \<lbrakk>count\<rbrakk> Expr[0], sample \<lbrakk>S,G,H,z\<rbrakk> Expr[distr], assign \<lbrakk>Find\<rbrakk> Expr[False], instantiateOracles adv [instantiateOracles Count [queryGS]]]"

  assumes "\<forall>P. instantiateOracles Count [P] = block [P, assign \<lbrakk>count\<rbrakk> (expression \<lbrakk>count\<rbrakk> (\<lambda>count. count+1))]"

  assumes "queryG = block [qapply \<lbrakk>X,Y\<rbrakk> (expression \<lbrakk>G\<rbrakk> (\<lambda>G. Uoracle G))]"
  assumes "queryGS = block [measurement \<lbrakk>in_S\<rbrakk> \<lbrakk>X\<rbrakk> (expression \<lbrakk>S\<rbrakk> (\<lambda>S. binary_measurement (projS S))),
                            ifthenelse (expression \<lbrakk>in_S\<rbrakk> (\<lambda>in_S. in_S=1)) [assign \<lbrakk>Find\<rbrakk> Expr[True]] [],
                            queryG]"
  assumes "queryH = block [qapply \<lbrakk>X,Y\<rbrakk> (expression \<lbrakk>H\<rbrakk> (\<lambda>H. Uoracle H))]"

  assumes "distinct_qvars \<lbrakk>b,count,Find,z,G,H,S,in_S,X,Y\<rbrakk>"

  assumes "disjnt (fv_oracle_program adv) (set (variable_names \<lbrakk>count,Find,G,H,S,in_S\<rbrakk>))" (* adv can access b,z,X,Y *)

  assumes "probability (expression \<lbrakk>count\<rbrakk> (\<lambda>count. count\<le>q)) game_left rho = 1"
  assumes "probability (expression \<lbrakk>count\<rbrakk> (\<lambda>count. count\<le>q)) game_right rho = 1"
  assumes "probability (expression \<lbrakk>count\<rbrakk> (\<lambda>count. count\<le>q)) game_find rho = 1"

  defines "Pleft == probability (expression \<lbrakk>b\<rbrakk> (\<lambda>b. b=1)) game_left rho"
  defines "Pright == probability (expression \<lbrakk>b\<rbrakk> (\<lambda>b. b=1)) game_right rho"
  defines "Pfind == probability (expression \<lbrakk>Find\<rbrakk> (\<lambda>Find. Find)) game_find rho"

  shows "abs (Pleft - Pright) \<le> 2 * sqrt( (1 + real q)*Pfind )"
    by (cheat O2H)

end

