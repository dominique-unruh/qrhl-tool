theory Test
  imports QRHL
  keywords "variables" :: thy_decl_block
  and "variables2" :: thy_decl_block
begin


ML {*
local 
fun declare_variable ctx v T typ =
  let val ctx = QRHL.VarTypes.map (Symtab.insert op= (v,typ)) ctx
      val ctx = QRHL.VarTypes.map (Symtab.insert op= (v^"1",typ)) ctx
      val ctx = QRHL.VarTypes.map (Symtab.insert op= (v^"2",typ)) ctx
  in
    ctx
  end

in

fun decl_var_hack name typ vartype = 
  Local_Theory.declaration {pervasive=true, syntax=false} (fn morph => Context.mapping (fn thy => thy)
   (fn ctx => (declare_variable ctx name (Morphism.typ morph typ) vartype)))

end
*}

ML {*
fun varname_assumption bind T = HOLogic.mk_eq 
  (Const(@{const_name variable_name}, QRHL.mk_qvariableT T --> @{typ string}) $ 
       Free(Binding.name_of bind ^ "_var", QRHL.mk_qvariableT T),
   HOLogic.mk_string (Binding.name_of bind)) |> HOLogic.mk_Trueprop
fun variables vars gthy = 
let fun elems0 idx = [
      Element.Fixes (map (fn (_,bind,T) => (Binding.suffix_name idx bind, SOME T, Mixfix.NoSyn)) vars),
      Element.Fixes (map (fn (_,bind,T) => (Binding.suffix_name (idx^"_var") bind, SOME (QRHL.mk_qvariableT T), Mixfix.NoSyn)) vars),
      Element.Assumes (map (fn (_,bind,T) => ((Binding.suffix_name (idx^"_varname") bind, @{attributes [simp]}),
                             [(varname_assumption (Binding.suffix_name idx bind) T, [])])) vars)]
    val elems = map elems0 ["", "1", "2"] |> List.concat
    val (_,lthy) = Bundle.context [] elems gthy
    val lthy2 = fold (fn (cq,bind,T) => fn lthy' => decl_var_hack (Binding.name_of bind) T cq lthy') vars lthy
in lthy2 end
*}

ML {*
fun variables_cmd vars gthy = 
  let val ctxt = Context.proof_of gthy
      val vars' = map (fn (a,b,c) => (a,b,Syntax.read_typ ctxt c)) vars
  in
    variables vars' gthy
  end
*}

ML {*
val parse_classical_quantum = (Parse.reserved "classical" >> K QRHL.Classical) || (Parse.reserved "quantum" >> K QRHL.Quantum)
val _ =
  Outer_Syntax.command @{command_keyword variables} "declare quantum/classical variables"
    ((Parse.and_list (parse_classical_quantum -- Args.binding --| Parse.$$$ "::" -- Parse.typ >> (fn ((a,b),c) => (a,b,c))) >> 
      (fn vars => Toplevel.open_target (variables_cmd vars)))
        --| Parse.begin)
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

ML {*
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


variables2 classical a :: int and quantum q :: nat begin
term a_var
term a
term q
thm a_varname

lemma l: "variable_name a_var = ''a''" by simp

end

ML {*
  Thm.cterm_of @{context} t1;
  Thm.cterm_of @{context} t2
*}

lemma l: "variable_name a_var \<equiv> ''a''" sorry

lemma "a_var=u" apply simp oops
ML {* 
@{thms a_varname}
*}
thm a_var
ML Variable.declare_constraints

variables
  quantum a :: int and
  classical b :: int and 
  classical c :: int begin

ML 1

definition "p1 = [ assign a_var Expr[1], assign b_var Expr[2] ]"
definition "p2 = [ assign a_var Expr[3], assign b_var Expr[4] ]"

ML {* Tactics.take_n_thm @{context} 2 *}

ML {* Type.constraint *}

lemma lem: "QRHL {Cla[True]} p1 p2 {Cla[True]}"
  unfolding p1_def p2_def
  using[[method_error=true]]
  apply (seq 1 1 "Cla[a1=b1]")
  sorry

end

variables classical a :: int and classical b :: int begin
thm lem

end
