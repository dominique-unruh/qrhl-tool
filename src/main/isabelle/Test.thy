theory Test
  imports Main
begin

lemma x: fixes c :: int assumes "c = d" shows "True" ..

context fixes a :: int begin

ML {*
val ctx = @{context}
val T = TFree(("a"),@{sort type}) (* Note the incorrect "a" instead of "'a" *)
val l = Free(("l"),T)
val prop = HOLogic.mk_Trueprop (HOLogic.mk_eq (l,l)) (* prop = "l=l" *)
fun tac {context=ctx, ...} = ALLGOALS (simp_tac ctx)
val thm = Goal.prove ctx ["l"] [] prop tac (* proving prop *)
val _ = @{thm x} OF [thm] (* Fails with "no unifiers". But succeeds if "fixes a" above is "fixes b" *)
*}




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
   (fn ctx => (@{print} morph; declare_variable ctx name (Morphism.typ morph typ) vartype)))

end
*}

context
  fixes a_var b_var c_var :: "int qvariable"
  assumes "variable_name a_var = ''a''"
  assumes "variable_name b_var = ''b''"
  assumes "variable_name c_var = ''c''"
  (* assumes [simp]: "distinct_qvars \<lbrakk>a,b,c\<rbrakk>" *)
begin

local_setup {* decl_var_hack "a" @{typ int} QRHL.Classical *}
local_setup {* decl_var_hack "b" @{typ int} QRHL.Classical *}
local_setup {* decl_var_hack "c" @{typ int} QRHL.Classical *}

definition "p1 = [ assign a_var Expr[1], assign b_var Expr[2] ]"
definition "p2 = [ assign a_var Expr[3], assign b_var Expr[4] ]"


lemma take1: "s#l = [s]@l" by auto
lemma take2: "s1#s2#l = [s1,s2]@l" by auto

ML {* List.tabulate (3,fn i => i) *}

ML {* List.tabulate (3, fn i => Var(("s"^string_of_int (i+1),0),@{typ int})) *}

ML Array.tabulate

ML {*
*}

ML {*
take_n_thm @{context} 2 (* |> Thm.cterm_of @{context} *)
*}

ML {*
val t = @{term "qrhl (expression qvariable_unit (\<lambda>x. \<CC>\<ll>\<aa>[True]))
     [assign a_var (expression qvariable_unit (\<lambda>x. 1)), assign b_var (expression qvariable_unit (\<lambda>x. 2)) ]
     [assign a_var (expression qvariable_unit (\<lambda>x. 3)), assign b_var (expression qvariable_unit (\<lambda>x. 4)) ]
     (expression \<lbrakk>a1_var, a2_var, b1_var, b2_var\<rbrakk> (\<lambda>(a1, a2, b1, b2). \<CC>\<ll>\<aa>[a1 < a2] \<sqinter> \<CC>\<ll>\<aa>[b1 < b2]))"}
*}




end
