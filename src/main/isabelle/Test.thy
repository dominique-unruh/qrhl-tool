theory Test
  imports Tactics
begin

(* TODO: to Encoding *)
lemma tmp3[simp]: 
  fixes e :: "('a*'b)*'c \<Rightarrow> 'e"
  defines "f == (\<lambda>(a,b,c). e ((a,b),c))"
  shows "expression (variable_concat (variable_concat S Q) R) e
    = expression (variable_concat S (variable_concat Q R)) f"
  sorry

(* TODO: to Encoding *)
lemma tmp4[simp]: 
  fixes e :: "'a*unit \<Rightarrow> 'e"
  shows "expression (variable_concat Q \<lbrakk>\<rbrakk>) e = expression Q (\<lambda>a. e (a,()))"
  sorry

lemma subst_expression_unit_metaeq:
  "subst_expression (substitute1 x f) (expression \<lbrakk>\<rbrakk> e') \<equiv> (expression \<lbrakk>\<rbrakk> e')" sorry

lemma subst_expression_singleton_same_metaeq:
  "subst_expression (substitute1 x (expression R f')) (expression \<lbrakk>x\<rbrakk> e') \<equiv> (expression R (\<lambda>r. e' (f' r)))" sorry

lemma subst_expression_singleton_notsame_metaeq:
  assumes "variable_name x \<noteq> variable_name y"
  shows "subst_expression (substitute1 x f) (expression \<lbrakk>y\<rbrakk> e') \<equiv> expression \<lbrakk>y\<rbrakk> e'" sorry

lemma subst_expression_concat_id_meta:
  assumes "subst_expression (substitute1 x f) (expression Q1 (\<lambda>x. x)) \<equiv> expression Q1' e1"
  assumes "subst_expression (substitute1 x f) (expression Q2 (\<lambda>x. x)) \<equiv> expression Q2' e2"
  shows "subst_expression (substitute1 x f) (expression (variable_concat Q1 Q2) (\<lambda>x. x)) \<equiv>
    expression (variable_concat Q1' Q2') (\<lambda>(x1,x2). (e1 x1, e2 x2))"
  sorry

variables classical v :: int and classical w :: nat begin

ML {*
fun subst_expression_conv' ctxt t = let
  val (sub1,e) = case t of
    Const(@{const_name subst_expression},_) $ sub1 $ e => (sub1,e)
    | _ => raise TERM ("Not of the form subst_expression \<sigma> e",[t])
  val (x,f) = case sub1 of
    Const(@{const_name substitute1},_) $ x $ f => (x,f)
    | _ => raise TERM ("Not of the form subst_expression (substitute1 x f) e",[t])
  val (R,f') = case f of
    Const(@{const_name expression},_) $ R $ f' => (R,f')
    | _ => raise TERM ("Not of the form subst_expression (substitute1 x (expression R f')) e",[t])
  val (Q,e') = case e of
    Const(@{const_name expression},_) $ Q $ e' => (Q,e')
    | _ => raise TERM ("Not of the form subst_expression (substitute1 x f) (expression Q e')",[t])
(* val _ = @{print} x
val _ = @{print} (Thm.cterm_of @{context} f)
val _ = @{print} (Thm.cterm_of @{context} e)
val _ = @{print} ("R", Thm.cterm_of @{context} R)
val _ = @{print} ("f'", Thm.cterm_of @{context} f')
val _ = @{print} ("Q", Thm.cterm_of @{context} Q)
val _ = @{print} ("e'", Thm.cterm_of @{context} e') *)
  fun inst subst thm = infer_instantiate ctxt (map (fn (n,t) => ((n,0),Thm.cterm_of ctxt t)) subst) thm
  fun is_id (Abs(_,_,Bound 0)) = true
    | is_id _ = false
in
  case Q of
    Const(@{const_name variable_unit},_) => 
      inst [("x",x),("f",f),("e'",e')] @{thm subst_expression_unit_metaeq}
  | Const(@{const_name variable_singleton},_) $ v =>
      if v=x then
        inst [("x",x),("R",R),("f'",f'),("e'",e')] @{thm subst_expression_singleton_same_metaeq}
      else let
        val ineq_t = HOLogic.mk_eq (QRHL.mk_variable_name x, QRHL.mk_variable_name v)
                         |> HOLogic.mk_not |> HOLogic.mk_Trueprop
        val ineq = Goal.prove ctxt [] [] ineq_t
                   (fn {context,...} => simp_tac context 1) |> @{print}
      in
        (inst [("f",f),("e'",e')] @{thm subst_expression_singleton_notsame_metaeq})
            OF [ineq]
      end
  | Const(@{const_name variable_concat},_) $ Q1 $ Q2 =>
      if is_id e' then let
        val sub1T = fastype_of sub1
        val Q1T = fastype_of Q1
        val Q1T' = QRHL.dest_variablesT Q1T
        val Q2T = fastype_of Q2
        val Q2T' = QRHL.dest_variablesT Q2T
        val resultT = fastype_of t
        val Q1_thm = subst_expression_conv' ctxt 
          (Const(@{const_name subst_expression},sub1T --> Encoding.mk_expressionT Q1T' --> resultT) $ sub1 $
             (Const(@{const_name expression},Q1T --> (Q1T' --> Q1T') --> Encoding.mk_expressionT Q1T') $
                Q1 $ Abs("",Q1T',Bound 0)))
val _ = @{print} (Q1_thm)
        val Q2_thm = subst_expression_conv' ctxt 
          (Const(@{const_name subst_expression},sub1T --> Encoding.mk_expressionT Q2T' --> resultT) $ sub1 $
             (Const(@{const_name expression},Q2T --> (Q2T' --> Q2T') --> Encoding.mk_expressionT Q2T') $
                Q2 $ Abs("",Q2T',Bound 0)))
val _ = @{print} (Q2_thm)
      in                    
        (@{thm subst_expression_concat_id_meta} OF [Q1_thm, Q2_thm]) |> @{print}
(* Use: subst_expression_concat_id_meta OF Q1_thm Q2_thm *)
      end else
        error "nyi: not id"
  | _ =>
      raise TERM("Variables in second expression are not a variable tuple",[t])
end

fun subst_expression_conv ctxt ct = subst_expression_conv' ctxt (Thm.term_of ct)

;;
subst_expression_conv @{context} @{cterm "
  
subst_expression (substitute1 var_v (const_expression z)) (expression \<lbrakk>var_v,var_w\<rbrakk> e)

"
}
*}

ML {*
  fun subst_expression_simproc _ ctxt ct = SOME (subst_expression_conv ctxt ct) handle CTERM _ => NONE
*}

simproc_setup subst_expression ("subst_expression (substitute1 x (expression R f')) (expression Q e')") = subst_expression_simproc


variables
  classical x :: int and
  classical a :: int and
  classical b :: int and 
  classical c :: int
begin

(* (* TODO: generalize *)
lemma tmp[simp]: "subst_expression (substitute1 v (const_expression z)) (expression \<lbrakk>v\<rbrakk> f)
= const_expression (f z)" 
  by simp
  sorry
 *)


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
  end
*}


ML {*
  fun index_var_simproc _ ctxt ct = SOME (index_var_conv ctxt ct) handle CTERM _ => NONE
*}

simproc_setup index_var ("index_var lr v") = index_var_simproc

lemma
  assumes [simp]: "x\<ge>0"
  shows "qrhl D [s1,sample var_x Expr[ uniform {0..max x 0}] ] [t1,t2,t3] Expr[ Cla[x1\<ge>0] ]"
  using [[method_error]]
  apply (tactic \<open>Tactics.wp1_tac @{context} 1\<close>)
  apply simp
  by (rule qrhl_top)


end

end
