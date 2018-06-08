theory Test_Tactics
  imports UnitTest "../../main/isabelle/Tactics"
begin

(* TEST CASE: get_wp of "if true then skip else skip" *)
ML \<open>
local
val post = @{term "Expr[top::predicate]"}
val expected_wp = @{term "const_expression ((\<CC>\<ll>\<aa>[True] + top) \<sqinter> (\<CC>\<ll>\<aa>[\<not> True] + top))"}

val (wp,thm) = Tactics.get_wp true @{term "ifthenelse Expr[True] [] []"} post @{context}

val _ = assert_aconv expected_wp wp
val (A,_,_,B) = Encoding.dest_qrhl_goal (Thm.prop_of thm)
val _ = assert_aconv expected_wp A
val _ = assert_aconv post B
in end
\<close>


(* TODO remove *)
variables classical b :: bit and quantum q :: bit begin
lemma "qrhl
       Expr[\<CC>\<ll>\<aa>[b1 = z] \<sqinter> (quantum_equality_full idOp \<lbrakk>q1\<rbrakk> hadamard \<lbrakk>q2\<rbrakk> \<sqinter> \<CC>\<ll>\<aa>[b1 \<noteq> b2]) ]
       [ifthenelse Expr[b=1] [qapply \<lbrakk>q\<rbrakk> Expr[hadamard] ] [] ]
       []
       Expr[\<lbrakk>q1\<rbrakk> \<equiv>\<qq> \<lbrakk>q2\<rbrakk>]"
  apply (tactic  \<open>Tactics.wp_tac @{context} true 1\<close>)
  oops
ML \<open>
val t = @{term "qrhl
       Expr[\<CC>\<ll>\<aa>[b1 = z] \<sqinter> (quantum_equality_full idOp \<lbrakk>q1\<rbrakk> hadamard \<lbrakk>q2\<rbrakk> \<sqinter> \<CC>\<ll>\<aa>[b1 \<noteq> b2]) ]
       [ifthenelse Expr[b=1] [qapply \<lbrakk>q\<rbrakk> Expr[hadamard] ] [] ]
       []
       Expr[\<lbrakk>q1\<rbrakk> \<equiv>\<qq> \<lbrakk>q2\<rbrakk>]"}
;;
Tactics.wp_tac_on_term true @{context} t
\<close>
end

end