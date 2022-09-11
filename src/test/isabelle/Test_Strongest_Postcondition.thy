theory Test_Strongest_Postcondition
  imports QRHL.Strongest_Postcondition UnitTest
begin


ML \<open>
fun test_get_sp ctxt left prog pre expected =
let val (sp,thm,side) = Strongest_Postcondition.get_sp left prog pre ctxt
    val _ = tracing ("Side conditions:\n" ^ String.concatWith "\n" (map (Syntax.string_of_term ctxt) side))
    val sp' = sp |> Thm.cterm_of ctxt |> Conv.try_conv (Expressions.clean_expression_conv ctxt)
                 |> Thm.rhs_of |> Thm.term_of |> Envir.beta_norm
    val _ = assert_aconv expected sp'
    val (A,_,_,B) = Relational_Hoare.dest_qrhl_goal (Thm.prop_of thm)
    val _ = assert_aconv sp B
    val _ = assert_aconv pre A
in () end
\<close>

declare [[show_consts, show_types]]

(* print_translation \<open>[(\<^const_syntax>\<open>expression\<close>, fn ctxt => fn [vars,t] => 
      Const(\<^const_syntax>\<open>undefined\<close>, dummyT) $ vars $ t)]\<close> *)

(* TEST CASE: assign *)
variables classical x :: nat and classical y :: nat begin
ML \<open>
test_get_sp \<^context> true
            \<^term>\<open>assign \<lbrakk>var_x\<rbrakk> Expr[5]\<close> (* program *)
            \<^term>\<open>Expr[Cla[x+x = y]]\<close> (* pre *)
            \<^term>\<open>expression \<lbrakk>var_x1::nat variable, var_x::nat variable, var_y::nat variable\<rbrakk>
                   (\<lambda>(var_x1::nat, var_x::nat, var_y::nat).
                   SUP z::nat. \<CC>\<ll>\<aa>[var_x1 = (5::nat)] \<sqinter> \<CC>\<ll>\<aa>[var_x + var_x = var_y])\<close> (* expected *)
\<close>
end

(* TEST CASE: qinit *)
variables quantum Q :: nat begin
ML \<open>
test_get_sp \<^context> false
            \<^term>\<open>qinit \<lbrakk>Q\<rbrakk> Expr[ket 0]\<close> (* program *)
            \<^term>\<open>Expr[Cla[(1::nat)=1]]\<close> (* pre *)
            \<^term>\<open>Expr[\<CC>\<ll>\<aa>[(1::nat) = 1] \<sqinter> \<lbrakk>Q2\<rbrakk> =\<^sub>\<qq> |0\<rangle>]\<close> (* expected *)
\<close>
end

(* TEST CASE: get_sp of "measure a A computational_basis" *)
variables classical a :: bit and quantum A :: bit begin
ML \<open>
test_get_sp \<^context> false 
            \<^term>\<open>measurement \<lbrakk>var_a\<rbrakk> \<lbrakk>A\<rbrakk> (const_expression computational_basis)\<close> (* program *)
            \<^term>\<open>const_expression (top::predicate)\<close> (* pre *)
            \<^term>\<open>Expr[SUP (z::bit) r::bit. \<CC>\<ll>\<aa>[a2 = r] \<sqinter> (mproj computational_basis r\<guillemotright>\<lbrakk>A2::bit variable\<rbrakk> *\<^sub>S \<top>)]\<close> (* expected *)
\<close>
end


(* TEST CASE: get_sp of a block *)
variables classical x :: nat begin
ML \<open>
test_get_sp \<^context> true
            \<^term>\<open>block [assign \<lbrakk>var_x\<rbrakk> Expr[x+1], assign \<lbrakk>var_x\<rbrakk> Expr[x+1]]\<close> (* program *)
            \<^term>\<open>Expr[Cla[x1 = 0]]\<close> (* pre *)
            \<^term>\<open>Expr[SUP z::nat. \<CC>\<ll>\<aa>[x1 = z + (1::nat)] \<sqinter> (SUP za::nat. \<CC>\<ll>\<aa>[z = za + (1::nat)] \<sqinter> \<CC>\<ll>\<aa>[za = (0::nat)])]\<close> (* expected *)
\<close>
end

(* TEST CASE: sample *)
variables classical x :: bit begin
ML \<open>
test_get_sp \<^context> true
            \<^term>\<open>sample \<lbrakk>var_x\<rbrakk> Expr[uniform UNIV]\<close> (* program *)
            \<^term>\<open>Expr[Cla[x1=0]]\<close> (* pre *)
            \<^term>\<open>Expr[SUP z::bit. \<CC>\<ll>\<aa>[x1 \<in> supp (uniform UNIV)] \<sqinter> \<CC>\<ll>\<aa>[z = (0::bit)]]\<close> (* expected *)
\<close>
end



(* TEST CASE: if *)
variables classical x :: bit begin
ML \<open>
test_get_sp \<^context> true
            \<^term>\<open>ifthenelse Expr[x=0] [assign \<lbrakk>var_x\<rbrakk> Expr[1]] [assign \<lbrakk>var_x\<rbrakk> Expr[0]]\<close> (* program *)
            \<^term>\<open>Expr[top :: predicate]\<close> (* pre *)
            \<^term>\<open>expression \<lbrakk>var_x1::bit variable, var_x1\<rbrakk>
                     (\<lambda>(var_x1::bit, var_x1a::bit).
                         (SUP z::bit. \<CC>\<ll>\<aa>[var_x1 = (1::bit)] \<sqinter> (\<CC>\<ll>\<aa>[z = (0::bit)] \<sqinter> \<top>)) \<squnion>
                         (SUP z::bit. \<CC>\<ll>\<aa>[var_x1a = (0::bit)] \<sqinter> (\<CC>\<ll>\<aa>[z \<noteq> (0::bit)] \<sqinter> \<top>)))\<close> (* expected *)
\<close>
end

(* TEST CASE: qapply *)
variables quantum q :: bit begin
ML \<open>
test_get_sp \<^context> true
            \<^term>\<open>qapply \<lbrakk>q\<rbrakk> Expr[hadamard]\<close> (* program *)
            \<^term>\<open>Expr[\<lbrakk>q1\<rbrakk> =\<^sub>q ket 0]\<close> (* pre *)
            \<^term>\<open>Expr[hadamard\<guillemotright>\<lbrakk>q1::bit variable\<rbrakk> *\<^sub>S \<lbrakk>q1\<rbrakk> =\<^sub>\<qq> |0::bit\<rangle>]\<close> (* expected *)
\<close>
end

end
