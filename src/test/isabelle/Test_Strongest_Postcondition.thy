theory Test_Strongest_Postcondition
  imports QRHL.Strongest_Postcondition UnitTest
begin


ML \<open>
fun test_get_sp ctxt left prog pre expected =
let val (sp,thm,side) = Strongest_Postcondition.get_sp left prog pre ctxt
    val _ = tracing ("Side conditions:\n" ^ String.concatWith "\n" (map (Syntax.string_of_term ctxt) side))
    val sp' = sp |> Thm.cterm_of ctxt |> Conv.try_conv (Expressions.clean_expression_conv ctxt)
                 |> Thm.rhs_of |> Thm.term_of |> Envir.beta_norm
    val _ = assert_aconv true expected sp'
    val (A,_,_,B) = Relational_Hoare.dest_qrhl_goal (Thm.prop_of thm)
    val _ = assert_aconv true sp B
    val _ = assert_aconv true pre A
in () end
\<close>

declare [[show_consts, show_types]]

experiment
  fixes x :: \<open>nat cvariable\<close> and y :: \<open>nat cvariable\<close> and Q :: \<open>nat qvariable\<close> 
    and a :: \<open>bit cvariable\<close> and A :: \<open>bit qvariable\<close>
  assumes [register]: \<open>cregister \<lbrakk>x,y,a\<rbrakk>\<^sub>c\<close>
  assumes [register]: \<open>qregister \<lbrakk>Q,A\<rbrakk>\<^sub>q\<close>
begin

(* print_translation \<open>[(\<^const_syntax>\<open>expression\<close>, fn ctxt => fn [vars,t] => 
      Const(\<^const_syntax>\<open>undefined\<close>, dummyT) $ vars $ t)]\<close> *)

(* TEST CASE: assign *)

ML \<open>
test_get_sp \<^context> true
            \<^term>\<open>assign x Expr[5]\<close> (* program *)
            \<^term>\<open>Expr[Cla[x1 + x1 = y1]] :: predicate expression2\<close> (* pre *)
            \<^term>\<open>Expr[\<Squnion>z::nat. \<CC>\<ll>\<aa>[x1 = 5] \<sqinter> \<CC>\<ll>\<aa>[z + z = y1]] :: predicate expression2\<close>
\<close>

(* TEST CASE: qinit *)
ML \<open>
test_get_sp \<^context> false
            \<^term>\<open>qinit Q Expr[ket 0]\<close> (* program *)
            \<^term>\<open>Expr[Cla[(1::nat)=1]] :: predicate expression2\<close> (* pre *)
            \<^term>\<open>Expr[\<CC>\<ll>\<aa>[(1::nat) = 1] \<sqinter> Q2 =\<^sub>\<qq> |0\<rangle>] :: predicate expression2\<close> (* expected *)
\<close>

(* TEST CASE: get_sp of "measure a A computational_basis" *)
ML \<open>
test_get_sp \<^context> false 
            \<^term>\<open>measurement a A Expr[computational_basis]\<close> (* program *)
            \<^term>\<open>Expr[top] :: predicate expression2\<close> (* pre *)
            \<^term>\<open>Expr[SUP (z::bit) r::bit. \<CC>\<ll>\<aa>[a2 = r] \<sqinter> (mproj computational_basis r\<guillemotright>\<lbrakk>A2\<rbrakk> *\<^sub>S \<top>)] :: _ expression2\<close> (* expected *)
\<close>


(* TEST CASE: get_sp of a block *)
ML \<open>
test_get_sp \<^context> true
            \<^term>\<open>block [assign x Expr[x+1], assign x Expr[x+1]]\<close> (* program *)
            \<^term>\<open>Expr[Cla[x1 = 0]] :: predicate expression2\<close> (* pre *)
            \<^term>\<open>Expr[SUP z::nat. \<CC>\<ll>\<aa>[x1 = z + (1::nat)] \<sqinter> (SUP za::nat. \<CC>\<ll>\<aa>[z = za + (1::nat)] \<sqinter> \<CC>\<ll>\<aa>[za = (0::nat)])] :: predicate expression2\<close> (* expected *)
\<close>

(* TEST CASE: sample *)
ML \<open>
test_get_sp \<^context> true
            \<^term>\<open>sample a Expr[uniform UNIV]\<close> (* program *)
            \<^term>\<open>Expr[Cla[a1=0]] :: predicate expression2\<close> (* pre *)
            \<^term>\<open>Expr[SUP z::bit. \<CC>\<ll>\<aa>[a1 \<in> supp (uniform UNIV)] \<sqinter> \<CC>\<ll>\<aa>[z = (0::bit)]] :: predicate expression2\<close> (* expected *)
\<close>


(* TEST CASE: if *)
ML \<open>
test_get_sp \<^context> true
            \<^term>\<open>ifthenelse Expr[a=0] [assign a Expr[1]] [assign a Expr[0]]\<close> (* program *)
            \<^term>\<open>Expr[top] :: predicate expression2\<close> (* pre *)
            \<^term>\<open>Expr[(SUP z::bit. \<CC>\<ll>\<aa>[a1 = (1::bit)] \<sqinter> (\<CC>\<ll>\<aa>[z = (0::bit)] \<sqinter> \<top>)) \<squnion>
                         (SUP z::bit. \<CC>\<ll>\<aa>[a1 = (0::bit)] \<sqinter> (\<CC>\<ll>\<aa>[z \<noteq> (0::bit)] \<sqinter> \<top>))] :: predicate expression2\<close> (* expected *)
\<close>

(* TEST CASE: qapply *)
ML \<open>
test_get_sp \<^context> true
            \<^term>\<open>qapply \<lbrakk>A\<rbrakk> Expr[hadamard]\<close> (* program *)
            \<^term>\<open>Expr[\<lbrakk>A1\<rbrakk> =\<^sub>q ket 0] :: predicate expression2\<close> (* pre *)
            \<^term>\<open>Expr[hadamard\<guillemotright>\<lbrakk>A1\<rbrakk> *\<^sub>S \<lbrakk>A1\<rbrakk> =\<^sub>\<qq> |0::bit\<rangle>] :: predicate expression2\<close> (* expected *)
\<close>

lemma \<open>qrhl top [assign x Expr[1]] [] top\<close>
  apply (tactic \<open>Strongest_Postcondition.sp_seq_tac 1 0 \<^context> 1\<close>)
  oops

end

end
