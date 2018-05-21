theory Test
  imports QRHL
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

lemma seq[simplified]:
  assumes "c = c1@c2" and "d = d1@d2"
  assumes "qrhl A c1 d1 B"
  and "qrhl A c2 d2 B"
  shows "qrhl A c d B"
  sorry

lemma take1: "s#l = [s]@l" by auto
lemma take2: "s1#s2#l = [s1,s2]@l" by auto

ML {* List.tabulate (3,fn i => i) *}

ML {* List.tabulate (3, fn i => Var(("s"^string_of_int (i+1),0),@{typ int})) *}

ML Array.tabulate

ML {*
fun take_n_thm ctx n = 
  let val T = TFree(("a"),@{sort type})
      val Tlist = HOLogic.listT T
      val l = Free(("l"),Tlist)
      val ss = List.tabulate (n, fn i => Free(("s"^string_of_int (i+1)),T))
      val ss_names = map (fst o dest_Free) ss
      val lhs = fold_rev (fn s => fn l => HOLogic.cons_const T $ s $ l) ss l
      val rhs = Const(@{const_name append}, Tlist --> Tlist --> Tlist) $ HOLogic.mk_list T ss $ l
      val prop = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs,rhs))
      (* fun tac {context=ctx, ...} = ALLGOALS (Skip_Proof.cheat_tac ctx) *)
      fun tac {context=ctx, ...} = ALLGOALS (simp_tac ctx)
      (* fun tac {context=ctx, ...} = Method.NO_CONTEXT_TACTIC ctx (Method.sleep (seconds 5.0)) *)
      val thm = Goal.prove ctx ("l"::ss_names) [] prop tac
  in
    thm
  end;
*}

ML {*
take_n_thm @{context} 2 (* |> Thm.cterm_of @{context} *)
*}

ML {*
fun seq_tac i j ctx = 
  let val rule = @{thm seq} OF [take_n_thm ctx i, take_n_thm ctx j] 
      (* val _ = @{print} rule *)
  in
  resolve_tac ctx [rule] end
*}

thm seq[OF take1 take1]

lemma "QRHL {Cla[true]} p1 p2 {Cla[a1<a2] \<sqinter> Cla[b1<b2]}"
  unfolding p1_def p2_def
  apply (tactic \<open>seq_tac 1 1 @{context} 1\<close>)
  (* apply (rule seq[OF take1 take2]) *)
  oops

end



end
