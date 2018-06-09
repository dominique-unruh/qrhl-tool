theory Test_Tactics
  imports UnitTest "../../main/isabelle/Tactics"
begin

(* TEST CASE: get_wp of "if true then skip else skip" *)
ML \<open>
local
val post = @{term "Expr[top::predicate]"}
val expected_wp = @{term "const_expression ((\<CC>\<ll>\<aa>[\<not> True] + top) \<sqinter> (\<CC>\<ll>\<aa>[True] + top))"}

val (wp,thm) = Tactics.get_wp true @{term "ifthenelse Expr[True] [] []"} post @{context}

val _ = assert_aconv expected_wp wp
val (A,_,_,B) = Encoding.dest_qrhl_goal (Thm.prop_of thm)
val _ = assert_aconv expected_wp A
val _ = assert_aconv post B
in end
\<close>


(* TEST CASE: get_wp of "measure a A computational_basis" *)
variables classical a :: bit and quantum A :: bit begin
ML \<open>
local
val prog = @{term "measurement var_a \<lbrakk>A\<rbrakk> (const_expression computational_basis)"}
val post = @{term "const_expression (top::predicate)"}
val expected_wp = @{term "const_expression (\<CC>\<ll>\<aa>[mtotal (computational_basis::(bit,_)measurement) ] \<sqinter>
            (INF z. top \<sqinter> (mproj computational_basis z\<guillemotright>\<lbrakk>A1\<rbrakk> \<cdot> top) +
                    ortho (mproj computational_basis z\<guillemotright>\<lbrakk>A1\<rbrakk> \<cdot> top)))"}

val (wp,thm) = Tactics.get_wp true prog post @{context}

val _ = assert_aconv expected_wp wp
val (A,_,_,B) = Encoding.dest_qrhl_goal (Thm.prop_of thm)
val _ = assert_aconv expected_wp A
val _ = assert_aconv post B
in end
\<close>
end


end
