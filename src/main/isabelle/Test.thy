theory Test
  imports Tactics
begin

(* TODO: to Encoding *)
lemma tmp3[simp]: 
  fixes e :: "('a*'b)*'c \<Rightarrow> 'e"
  defines "f == (\<lambda>(a,b,c). e ((a,b),c))"
  shows "expression (qvariable_concat (qvariable_concat S Q) R) e
    = expression (qvariable_concat S (qvariable_concat Q R)) f"
  sorry

(* TODO: to Encoding *)
lemma tmp4[simp]: 
  fixes e :: "'a*unit \<Rightarrow> 'e"
  shows "expression (qvariable_concat Q \<lbrakk>\<rbrakk>) e = expression Q (\<lambda>a. e (a,()))"
  sorry


variables
  classical x :: int and
  classical a :: int and
  classical b :: int and 
  classical c :: int
begin

(* TODO: generalize *)
lemma tmp[simp]: "subst_expression (substitute1 v (const_expression z)) (expression \<lbrakk>v\<rbrakk> f)
= const_expression (f z)" sorry


lemma qrhl_top: "qrhl A p1 p2 (expression Q (\<lambda>z. top))" sorry

lemma index_var_conv_helper1:
  assumes "variable_name v \<equiv> vname"
  assumes "variable_name v1 \<equiv> v1name"
  assumes "vname @ ''1'' \<equiv> v1name"
  shows "index_var True v \<equiv> v1"
  using assms index_var1I by smt

lemma index_var_conv_helper2:
  assumes "variable_name v \<equiv> vname"
  assumes "variable_name v2 \<equiv> v2name"
  assumes "vname @ ''2'' \<equiv> v2name"
  shows "index_var False v \<equiv> v2"
  using assms index_var2I by smt

ML {*
fun index_var_conv ctxt ct =
  let val (lrname,x,T) = case Thm.term_of ct of
        Const(@{const_name index_var},_) $ Const(lrname,_) $ Free(x,T) => (lrname,x,T)
      | _ => raise CTERM("index_var_conv: wrong shape",[ct])
      val lr = case lrname of 
          @{const_name True} => true
        | @{const_name False} => false
        | _ => raise CTERM("index_var_conv: wrong shape (expected True/False as first arg)",[ct])

      val suffix = (if lr then "1" else "2")
      val x1 = x ^ suffix

      val varname_x = Raw_Simplifier.rewrite_cterm (false,false,false) (fn _ => fn _ => NONE) ctxt (Thm.cterm_of ctxt 
        (Const(@{const_name variable_name}, T --> @{typ string}) $ Free(x,T)))

      val varname_x1 = Raw_Simplifier.rewrite_cterm (false,false,false) (fn _ => fn _ => NONE) ctxt (Thm.cterm_of ctxt 
        (Const(@{const_name variable_name}, T --> @{typ string}) $ Free(x1,T)))

      (* val _ = varname_x |> @{print} *)
      (* val _ = varname_x1 |> @{print} *)

      val helper_thm = if lr then @{thm index_var_conv_helper1} else  @{thm index_var_conv_helper2}
  
      val name_x = varname_x |> Thm.concl_of |> Logic.dest_equals |> snd
      val name_eq = Raw_Simplifier.rewrite_cterm (false,false,false) (fn _ => fn _ => NONE) ctxt
        (@{term "op@ :: string=>_=>_"} $ name_x $ HOLogic.mk_string suffix |> Thm.cterm_of ctxt)
  in
    helper_thm OF [varname_x, varname_x1, name_eq]
  end;;

index_var_conv @{context} @{cterm "index_var True var_x"}
*}


ML {*
  fun index_var_simproc _ ctxt ct = SOME (index_var_conv ctxt ct) handle CTERM _ => NONE
*}

simproc_setup index_var ("index_var lr v") = index_var_simproc

lemma
  assumes [simp]: "x\<ge>0"
  shows "qrhl D [s1,sample var_x Expr[uniform {0..max x 0}] ] [t1,t2,t3] Expr[ Cla[x1\<ge>0] ]"
  using [[method_error]]
  apply (tactic \<open>Tactics.wp1_tac @{context} 1\<close>)
  apply simp
  by (rule qrhl_top)


end

lemma "quantum_equality_full idOp \<lbrakk>q1\<rbrakk> hadamard \<lbrakk>q2\<rbrakk> \<le> (INF (b1, b2):supp (map_distr (\<lambda>b::bit. (b, b + 1)) (uniform UNIV)). 
case (va, va) of (b1, b2) \<Rightarrow> quantum_equality_full idOp \<lbrakk>q1\<rbrakk> hadamard \<lbrakk>q2\<rbrakk> \<sqinter> \<CC>\<ll>\<aa>[b1 \<noteq> b2])
"
  apply simp

end
