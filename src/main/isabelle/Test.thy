theory Test
  imports Encoding Tactics
begin


ML {*
fun is_explicit_expression (Const(@{const_name expression},_) $ Q $ _) =
  ((QRHL.parse_varterm Q; true) handle TERM _ => false)
  | is_explicit_expression _ = false
fun is_varlist_explicit_expression (Const(@{const_name expression},_) $ Q $ _) =
  ((QRHL.parse_varlist Q; true) handle TERM _ => false)
  |  is_varlist_explicit_expression _ = false
*}

ML {*
fun clean_expression_simproc _ ctxt ct = 
  let val t = Thm.term_of ct in
  if is_explicit_expression t andalso not (is_varlist_explicit_expression t) then
      SOME (Encoding.clean_expression_conv ctxt ct) handle CTERM _ => NONE
    else
      NONE
  end
*}

simproc_setup clean_expression ("expression Q e") = clean_expression_simproc

(* ML {* fun double ctx [e] = @{const plus(dummy)} $ e $ e *}

syntax "_double1" :: "'a \<Rightarrow> 'a" ("double1 _" [81] 80)
parse_translation {* [("_double1", double)] *}

(* Ctrl-click on double1 DOT NOT jump to definition *)
term "double1 2"


consts "double2_donotuse" :: "'a \<Rightarrow> 'a" ("double2 _" [81] 80)
parse_translation {* [(@{const_syntax double2_donotuse}, double)] *}

(* Ctrl-click on double1 DOES jump to definition
   but we define an extra constant that clutters the name space
   and is forbidden (meaningless) *)
term "double2 2"
(* Example: leads to valid looking pretty printing but is nonsense *)
term "double2_donotuse 2"


abbreviation (input) double3 ("double3 _" [81] 80) where
  "double3 x == x+x"

(* Ctrl-click on double1 DOES jump to definition, 
   but abbreviation mechanism too limited for more complex cases *)
term "double3 2"


syntax "_double4" :: "'a \<Rightarrow> 'a" ("TEMPORARY")
parse_translation {* [("_double4", double)] *}
abbreviation (input) double4_donotuse ("double4 _" [81] 80) where
  "double4_donotuse x == TEMPORARY x"
no_syntax "_double4" :: "'a \<Rightarrow> 'a" ("TEMPORARY")

(* Ctrl-click on double1 DOES jump to definition, 
   no "forbidden" constant defined,
   but it's complicated and feels like a hack. *)
term "double4 2"
 *)


instantiation expression :: (ord) ord begin
instance sorry
end




ML{*
Encoding.clean_expression_abs_pat_conv @{context} @{cterm "expression \<lbrakk>var_w, var_v, var_w\<rbrakk>
           (\<lambda>x. case case x of (x, q) \<Rightarrow> (x, case q of (x, q) \<Rightarrow> (x, (), q, ())) of (q, r, s) \<Rightarrow> e ((q, r), s)) 
"}
*}


ML {*
Encoding.clean_expression_conv @{context} @{cterm "expression (variable_concat \<lbrakk>var_w,var_w\<rbrakk>
 (variable_concat variable_unit (variable_concat \<lbrakk>var_w\<rbrakk> variable_unit))) e"}
*}

ML {*
Encoding.clean_expression_conv @{context} @{cterm "expression \<lbrakk>var_w, var_v, var_w\<rbrakk>
           (\<lambda>x. case case x of (x, q) \<Rightarrow> (x, case q of (x, q) \<Rightarrow> (x, (), q, ())) of (q, r, s) \<Rightarrow> e ((q, r), s)) 

"}
*}

(*
(* TODO: to Encoding *)
lemma tmp3[simp]: 
  fixes e :: "('a*'b)*'c \<Rightarrow> 'e"
  defines "f == (\<lambda>(a,b,c). e ((a,b),c))"
  shows "expression (variable_concat (variable_concat S Q) R) e
       = expression (variable_concat S (variable_concat Q R)) f"
  sorry
*)

(*
(* TODO: to Encoding *)
lemma tmp4[simp]: 
  fixes e :: "'a*unit \<Rightarrow> 'e"
  shows "expression (variable_concat Q \<lbrakk>\<rbrakk>) e = expression Q (\<lambda>a. e (a,()))"
  sorry
 *)

(* lemma subst_expression_concat_id:
  assumes "subst_expression (substitute1 x f) (expression Q1 (\<lambda>x. x)) = expression Q1' e1"
  assumes "subst_expression (substitute1 x f) (expression Q2 (\<lambda>x. x)) = expression Q2' e2"
  shows "subst_expression (substitute1 x f) (expression (variable_concat Q1 Q2) (\<lambda>x. x)) =
    expression (variable_concat Q1' Q2') (\<lambda>(x1,x2). (e1 x1, e2 x2))"
  sorry *)



(* lemma subst_expression_id_comp_aux:
  assumes "NO_MATCH e (\<lambda>x. x)"
  assumes "subst_expression (substitute1 x f) (expression Q (\<lambda>x. x)) \<equiv> expression Q' g"
  shows "subst_expression (substitute1 x f) (expression Q e) \<equiv> expression Q' (\<lambda>x. e (g x))"
  sorry *)

(*lemma subst_expression_cons_same_aux:
  assumes "subst_expression (substitute1 x f) (expression Q (\<lambda>x. x)) = expression Q'"
  shows "subst_expression (substitute1 x f) (expression (variable_concat \<lbrakk>x\<rbrakk> Q) (\<lambda>x. x)) \<equiv> xxxxx"*)

ML {*
*}

(* variables classical v :: int and classical w :: nat begin *)

ML {*


(* ;;
subst_expression_conv @{context} @{cterm "subst_expression (substitute1 var_v (const_expression z)) (expression \<lbrakk>var_v,var_w\<rbrakk> e)"} *)
*}

(* schematic_goal bla: "subst_expression (substitute1 var_v (const_expression z)) (expression \<lbrakk>var_v,var_w\<rbrakk> e) \<equiv> ?expression"
  (* apply (tactic \<open>REPEAT_DETERM (CHANGED (resolve_tac @{context} @{thms subst_expression_concat_id_meta subst_expression_singleton_same_metaeq subst_expression_id_comp_meta} 1))\<close>) *)
  by (tactic \<open>subst_expression_conv_tac @{context}\<close>)
  (* apply (rule subst_expression_id_comp_meta) *)
  (* apply (rule subst_expression_concat_id_meta) *)
  (* apply (rule subst_expression_singleton_same_metaeq) *)
  (* apply (tactic \<open>\<close>) *)
  (* apply (rule subst_expression_singleton_notsame_metaeq) *)
  (* by simp *) *)

(* lemma xxx: "f \<equiv> (\<lambda>(x,y,z). f (x,y,z))" by auto *)

schematic_goal blu: "expression (variable_concat \<lbrakk>var_w,var_w\<rbrakk> (variable_concat variable_unit (variable_concat \<lbrakk>var_w\<rbrakk> variable_unit))) (\<lambda>x. e (case x of (x1, x2) \<Rightarrow> (z, x2))) \<equiv> ?expression"
  apply (tactic \<open>Encoding.clean_expression_conv_varlist_tac @{context}\<close>)
  done


ML {*
  fun subst_expression_simproc _ ctxt ct = SOME (Encoding.subst_expression_conv ctxt ct) handle CTERM _ => NONE
*}

simproc_setup subst_expression ("subst_expression (substitute1 x (expression R f')) (expression Q e')") = subst_expression_simproc


variables
  classical x :: int and
  classical a :: int and
  classical b :: int and 
  classical c :: int and
  quantum q :: int
begin

lemma "qrhl Expr[top] [qinit \<lbrakk>q\<rbrakk> Expr[ket 0] ] [qinit \<lbrakk>q\<rbrakk> Expr[ket 0] ] Expr[top]"
  apply (tactic \<open>Tactics.wp_tac @{context} true 1\<close>)
  using[[method_error]]
  apply (tactic \<open>Tactics.wp_tac @{context} false 1\<close>)
  apply simp
  oops

lemma expression_clean_unit_cons_aux: -- \<open>Helper for ML function clean_expression_conv_varlist\<close>
  assumes "expression Q (\<lambda>q. e ((),q)) \<equiv> expression Q' e'"
  shows "expression (variable_concat variable_unit Q) e \<equiv> expression Q' e'"
  sorry

schematic_goal "expression (variable_concat variable_unit (variable_concat variable_unit variable_unit)) (\<lambda>(x1, x2). bot) \<equiv> ?xxx"
  apply (rule expression_clean_unit_cons_aux)+
  oops

thm map_expression2
ML {*
  Tactics.get_wp true @{term "qinit \<lbrakk>q\<rbrakk> (const_expression (ket 0))"} 
@{term "(expression (variable_concat variable_unit variable_unit) (\<lambda>(x1, x2). \<CC>\<ll>\<aa>[norm (ket 0) = 1] \<sqinter> top \<div> ket 0\<guillemotright>\<lbrakk>q\<rbrakk>))"} @{context}
|> snd
*}

ML \<open>
Tactics.wp_cleanup_conv @{context} @{cprop \<open>qrhl (expression (variable_concat variable_unit (variable_concat variable_unit variable_unit))
                 (\<lambda>(x1, x2). \<CC>\<ll>\<aa>[norm (ket 0) = 1] \<sqinter> (case x2 of (x1, x2) \<Rightarrow> \<CC>\<ll>\<aa>[norm (ket ...) = 1] \<sqinter> top \<div> ket 0\<guillemotright>\<lbrakk>q\<rbrakk>) \<div> ket 0\<guillemotright>\<lbrakk>q\<rbrakk>))
           [qinit \<lbrakk>q\<rbrakk> (const_expression (ket 0)) ] []
           (expression (variable_concat variable_unit variable_unit) (\<lambda>(x1, x2). \<CC>\<ll>\<aa>[norm (ket 0) = 1] \<sqinter> top \<div> ket 0\<guillemotright>\<lbrakk>q\<rbrakk>))\<close>}
\<close>

ML \<open>
Encoding.clean_expression_conv_varlist @{context} @{cterm "expression (variable_concat variable_unit (variable_concat variable_unit variable_unit))
                 (\<lambda>(x1, x2). True)"}
\<close>

schematic_goal "expression (variable_concat variable_unit (variable_concat variable_unit variable_unit))
                 (\<lambda>(x1, x2). True) == ?xx"
(* apply (rule expression_clean_unit_cons_aux) *)

apply (tactic  \<open>Encoding.clean_expression_conv_varlist_tac1 @{context}\<close>)
apply (tactic  \<open>Encoding.clean_expression_conv_varlist_tac1 @{context}\<close>)
apply (tactic  \<open>Encoding.clean_expression_conv_varlist_tac1 @{context}\<close>)
  oops

thm q1_varname
thm x1_varname

lemma qrhl_top: "qrhl A p1 p2 (expression Q (\<lambda>z. top))" sorry
lemma qrhl_top': "f \<ge> top \<Longrightarrow> qrhl A p1 p2 (expression Q f)" sorry



ML {*
Encoding.subst_expression_conv @{context} @{cterm "subst_expression (substitute1 var_x2 (const_expression 0))
 (expression \<lbrakk>var_x1, var_x2\<rbrakk> (\<lambda>(x1, x2). \<CC>\<ll>\<aa>[Ball {0..max x1 0} (op \<le> x2) ] ))"}
*}

lemma
  assumes [simp]: "x\<ge>0"
  shows "qrhl D [s1,sample var_x Expr[ uniform {0..max x 0}] ] [t1,t2,assign var_x Expr[0] ] Expr[ Cla[x1\<ge>x2] ]"
  using [[method_error,show_types]]
  apply (tactic \<open>Tactics.wp_tac @{context} true 1\<close>)
  apply (tactic \<open>Tactics.wp_tac @{context} false 1\<close>)
  apply simp
  by (rule qrhl_top)

lemma skip:
  assumes "A \<le> B"
  shows "qrhl A [] [] B"
  sorry

lemma expression_leq1:
  assumes "\<And>x. e x \<le> e' x"
  shows "expression \<lbrakk>v\<rbrakk> e \<le> expression \<lbrakk>v\<rbrakk> e'"
  sorry

lemma expression_leq2:
  assumes "\<And>x y. e x y \<le> e' x y"
  shows "expression \<lbrakk>v,w\<rbrakk> (\<lambda>(x,y). e x y) \<le> expression \<lbrakk>v,w\<rbrakk> (\<lambda>(x,y). e' x y)"
  sorry


schematic_goal
  assumes [simp]: "x\<ge>0"
  shows "qrhl Expr[ Cla[x1=0 \<and> x2=1] ] [qinit \<lbrakk>q\<rbrakk> Expr[ ket 0 ] ] [assign var_x Expr[x-1] ] Expr[ Cla[x1\<ge>x2] ]"
  using [[method_error,show_types]]
  apply (tactic \<open>Tactics.wp_tac @{context} true 1\<close>) 
  apply (tactic \<open>Tactics.wp_tac @{context} false 1\<close>)
  apply simp
  apply (rule skip)
  apply (rule expression_leq2)
  by simp

ML {*
  val (_,thm) = Tactics.get_wp true  @{term "sample var_x Expr[uniform{x}]"} @{term "Expr[ Cla[x1=1 \<and> True] ]"} @{context}
  val (pre,_,_,_) = Tactics.dest_qrhl_goal (Thm.prop_of thm)
  val cpre = Thm.cterm_of @{context} pre
*}                                                                                             

ML \<open>
@{const_name implies}
\<close>


ML {*
  Tactics.wp_cleanup_conv @{context} (Thm.cprop_of thm)
  |> Thm.rhs_of
*}


schematic_goal "qrhl ?pre [assign var_x Expr[x+2], assign var_x Expr[0], assign var_x Expr[x+1] ] [] Expr[ Cla[x1=1] ]"
  apply (tactic \<open>Tactics.wp_tac @{context} true 1\<close>)+
  (* apply (tactic \<open>CONVERSION (wp_cleanup_conv @{context}) 1\<close>) *)
  apply (rule qrhl_top')
  by (auto simp: le_fun_def) 




end

end
