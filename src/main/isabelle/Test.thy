theory Test
  imports Tactics
begin


ML {*
*}

ML {*
*}

ML {*
*}


ML {*
*}

(*ML {*
  Outer_Syntax.command @{command_keyword variables2} "bla"
  (Scan.succeed (Toplevel.open_target (fn gthy =>
    let val lthy = Bundle.context [] [] gthy |> #2
        val lthy2 = QRHL.declare_variable lthy @{binding "a"} @{typ bool} QRHL.Classical
        val lthy3 = QRHL.declare_variable lthy2 @{binding "q"} @{typ nat} QRHL.Quantum
  in lthy3 end
  )))
*}*)

(* ML {*
fun variables2 vars gthy =
let val lthy = Bundle.context [] [] gthy |> #2
    val lthy2 = fold (fn (cq,bind,T) => fn lthy' => QRHL.declare_variable lthy' bind T cq) vars lthy
in lthy2 end
*}

ML {*
fun variables2_cmd vars gthy = 
  let val ctxt = Context.proof_of gthy
      val vars' = map (fn (a,b,c) => (a,b,Syntax.read_typ ctxt c)) vars
  in
    variables2 vars' gthy
  end
*}

ML {*
val parse_classical_quantum = (Parse.reserved "classical" >> K QRHL.Classical) || (Parse.reserved "quantum" >> K QRHL.Quantum)
val _ =
  Outer_Syntax.command @{command_keyword variables2} "declare quantum/classical variables"
    ((Parse.and_list (parse_classical_quantum -- Args.binding --| Parse.$$$ "::" -- Parse.typ >> (fn ((a,b),c) => (a,b,c))) >> 
      (fn vars => Toplevel.open_target (variables2_cmd vars)))
        --| Parse.begin)
*}
 *)
(* 
variables2 classical a :: int and quantum q :: nat begin
term a_var
term a
term q
thm a_varname

lemma l: "variable_name a_var = ''a''" by simp

end

lemma l: "variable_name a_var = ''a''" by simp
 *)

lemma tmp3[simp]: 
  fixes e :: "('a*'b)*'c \<Rightarrow> 'e"
  defines "f == (\<lambda>(a,b,c). e ((a,b),c))"
  shows "expression (qvariable_concat (qvariable_concat S Q) R) e
    = expression (qvariable_concat S (qvariable_concat Q R)) f"
  sorry

lemma tmp4[simp]: 
  fixes e :: "'a*unit \<Rightarrow> 'e"
  (* defines "f == (\<lambda>(a,b,c). e ((a,b),c))" *)
  shows "expression (qvariable_concat Q \<lbrakk>\<rbrakk>) e = expression Q (\<lambda>a. e (a,()))"
  sorry

(* context begin

lemma xxx[simp]: "1=2" sorry

declare[[method_error]]

local_setup {*
decl_var_hack "x" @{typ int} QRHL.Classical
*}

lemma "1=1" by auto
definition "q=1" 

ML {*
QRHL.VarTypes.get @{context} |> Symtab.dest
*}

end

ML {*
QRHL.VarTypes.get @{context} |> Symtab.dest
*}

lemma "1=2" by simp
ML {* Config.get @{context} Tactics.method_error *}

ML {* Config.get @{context} Tactics.method_error *}

ML Config.declare
 *)

variables
  classical x :: int and
  classical a :: int and
  classical b :: int and 
  classical c :: int
begin


lemma tmp[simp]: "subst_expression (substitute1 v (const_expression z)) (expression \<lbrakk>v\<rbrakk> f)
= const_expression (f z)" sorry

lemma tmp2[simp]: "index_var True x_var = x1_var" sorry


lemma "qrhl D [s1,sample x_var Expr[uniform {0..x}] ] [t1,t2,t3] Expr[ Cla[x1\<ge>0] ]"
  using [[method_error]]
  apply (tactic \<open>Tactics.wp1_tac @{context} 1\<close>)
  apply simp
  oops

term a_var
definition "p1 = [ assign a_var Expr[1], assign b_var Expr[2] ]"
term a_var
definition "p2 = [ assign a_var Expr[3], assign b_var Expr[4] ]"

ML {* Tactics.take_n_thm @{context} 2 *}

ML {* Type.constraint *}

lemma lem: "QRHL {Cla[True]} p1 p2 {Cla[True]}"
  unfolding p1_def p2_def
  using[[method_error=true]]
  apply (seq 1 1 "Cla[a1=b1]")
  sorry

ML {*
QRHL.VarTypes.get @{context} |> Symtab.dest
*}

lemma xx[simp]: "1=2" sorry

end

ML {*
QRHL.VarTypes.get @{context} |> Symtab.dest
*}


end
