theory Weakest_Precondition
  imports Cert_Codegen Encoding
begin

lemma seq:
  assumes "qrhl A c1 d1 B"
  and "qrhl B c2 d2 C"
  shows "qrhl A (c1@c2) (d1@d2) C"
  sorry



lemma seqREMOVE:
  assumes "c = c1@c2" and "d = d1@d2"
  assumes "qrhl A c1 d1 B"
    and "qrhl B c2 d2 C"
  shows "qrhl A c d C"
  using assms using seq by auto
  

lemma wp_skip:
  shows "qrhl B [] [] B"
  sorry

lemma wp1_assign:
  fixes A B x e
  defines "A \<equiv> subst_expression (substitute1 (index_var True x) (index_expression True e)) B"
  shows "qrhl A [assign x e] [] B"
  sorry

lemma wp2_assign:
  fixes A B x e
  defines "A \<equiv> subst_expression (substitute1 (index_var False x) (index_expression False e)) B"
  shows "qrhl A [] [assign x e] B"
  sorry

lemma wp1_sample:
  fixes A B x e
  defines "e' \<equiv> index_expression True e"
  defines "B' z \<equiv> subst_expression (substitute1 (index_var True x) (const_expression z)) B"
  defines "A \<equiv> map_expression2' (\<lambda>e' B'. Cla[weight e' = 1] \<sqinter> (INF z:supp e'. B' z)) e' B'"
  shows "qrhl A [sample x e] [] B"
  sorry

lemma wp2_sample:
  fixes A B x e
  defines "e' \<equiv> index_expression False e"
  defines "B' z \<equiv> subst_expression (substitute1 (index_var False x) (const_expression z)) B"
  defines "A \<equiv> map_expression2' (\<lambda>e' B'. Cla[weight e' = 1] \<sqinter> (INF z:supp e'. B' z)) e' B'"
  shows "qrhl A [] [sample x e] B"
  sorry

lemma wp1_qapply:
  fixes A B Q e
  defines "Q\<^sub>1 \<equiv> index_vars True Q"
  defines "A \<equiv> map_expression2 (\<lambda>e\<^sub>1 B. Cla[isometry e\<^sub>1] \<sqinter> (adjoint (e\<^sub>1\<guillemotright>Q\<^sub>1) \<cdot> (B \<sqinter> (e\<^sub>1\<guillemotright>Q\<^sub>1 \<cdot> top)))) (index_expression True e) B"
  shows "qrhl A [qapply Q e] [] B"
  sorry

lemma wp2_qapply:
  fixes A B Q e
  defines "Q\<^sub>2 \<equiv> index_vars False Q"
  defines "A \<equiv> map_expression2 (\<lambda>e\<^sub>2 B. Cla[isometry e\<^sub>2] \<sqinter> (adjoint (e\<^sub>2\<guillemotright>Q\<^sub>2) \<cdot> (B \<sqinter> (e\<^sub>2\<guillemotright>Q\<^sub>2 \<cdot> top)))) (index_expression False e) B"
  shows "qrhl A [] [qapply Q e] B"
  sorry

lemma wp1_measure:
  fixes A B x Q e
  defines "e\<^sub>1 \<equiv> index_expression True e"
  defines "B' z \<equiv> subst_expression (substitute1 (index_var True x) (const_expression z)) B"
  defines "\<And>e\<^sub>1 z. ebar e\<^sub>1 z \<equiv> ((mproj e\<^sub>1 z)\<guillemotright>(index_vars True Q)) \<cdot> top"
  defines "A \<equiv> map_expression2' (\<lambda>e\<^sub>1 B'. let M = e\<^sub>1 in Cla[mtotal M] \<sqinter> 
           (INF z. let P = ebar M z in ((B' z \<sqinter> P) + ortho P))) e\<^sub>1 B'"
  shows "qrhl A [measurement x Q e] [] B"
  sorry

lemma wp2_measure:
  fixes A B x Q e
  defines "e\<^sub>2 \<equiv> index_expression False e"
  defines "B' z \<equiv> subst_expression (substitute1 (index_var False x) (const_expression z)) B"
  defines "\<And>e\<^sub>2 z. ebar e\<^sub>2 z \<equiv> ((mproj e\<^sub>2 z)\<guillemotright>(index_vars False Q)) \<cdot> top"
  defines "A \<equiv> map_expression2' (\<lambda>e\<^sub>2 B'. let M = e\<^sub>2 in Cla[mtotal M] \<sqinter> 
           (INF z. let P = ebar M z in ((B' z \<sqinter> P) + ortho P))) e\<^sub>2 B'"
  shows "qrhl A [] [measurement x Q e] B"
  sorry

lemma wp1_qinit:
  fixes B e Q
  defines "A \<equiv> map_expression2 (\<lambda>e\<^sub>1 B. Cla[norm e\<^sub>1 = 1] \<sqinter> (B \<div> e\<^sub>1 \<guillemotright> (index_vars True Q)))
           (index_expression True e) B"
  shows "qrhl A [qinit Q e] [] B"
  sorry

lemma wp2_qinit:
  fixes B e Q
  defines "A \<equiv> map_expression2 (\<lambda>e\<^sub>2 B. Cla[norm e\<^sub>2 = 1] \<sqinter> (B \<div> e\<^sub>2 \<guillemotright> (index_vars False Q)))
           (index_expression False e) B"
  shows "qrhl A [] [qinit Q e] B"
  sorry

lemma wp1_if:
  fixes e p1 p2 B
  assumes "qrhl wp_true p1 [] B"
  assumes "qrhl wp_false p2 [] B"
  defines "A \<equiv> map_expression3 (\<lambda>e\<^sub>1 wp_true wp_false. (Cla[\<not>e\<^sub>1] + wp_true) \<sqinter> (Cla[e\<^sub>1] + wp_false))
           (index_expression True e) wp_true wp_false"
  shows "qrhl A [ifthenelse e p1 p2] [] B"
  sorry

lemma wp2_if:
  fixes e p1 p2 B
  assumes "qrhl wp_true [] p1 B"
  assumes "qrhl wp_false [] p2 B"
  defines "A \<equiv> map_expression3 (\<lambda>e\<^sub>2 wp_true wp_false. (Cla[\<not>e\<^sub>2] + wp_true) \<sqinter> (Cla[e\<^sub>2] + wp_false))
           (index_expression False e) wp_true wp_false"
  shows "qrhl A [] [ifthenelse e p1 p2] B"
  sorry

lemma wp1_block:
  assumes "qrhl A p [] B"
  shows "qrhl A [block p] [] B"
  sorry

lemma wp2_block:
  assumes "qrhl A [] p B"
  shows "qrhl A [] [block p] B"
  sorry

lemma wp1_cons:
  assumes "qrhl A [p] [] B'"
    and "qrhl B' ps [] B"
  shows "qrhl A (p#ps) [] B"
  sorry

lemma wp2_cons:
  assumes "qrhl A [] [p] B'"
    and "qrhl B' [] ps B"
  shows "qrhl A [] (p#ps) B"
  sorry

(* ML \<open>
fun get_variable_name_orig ctxt v = let
  val ct = Const(\<^const_name>\<open>variable_name\<close>, fastype_of v --> HOLogic.stringT) $ v |> Thm.cterm_of ctxt
  val thm = Raw_Simplifier.rewrite_cterm (false,false,false) (K (K NONE)) ctxt ct
  val rhs = Thm.rhs_of thm |> Thm.term_of
  val _ = HOLogic.dest_string rhs         
  in
    (rhs, fn () => thm RS @{thm meta_eq_to_obj_eq})
  end
\<close> *)

ML \<open>
fun get_variable_name ctxt (v as Free(n,T)) = let
  val vn = unprefix "var_" n handle Fail _ => n
  val varinfo = case Prog_Variables.lookup_variable ctxt vn of SOME vi => vi |
                  NONE => raise TERM("get_variable_name: unknown variable",[v])
  val thm = #name_thm varinfo
(*   val vn = unprefix "var_" n handle Fail _ => n
  val str = HOLogic.mk_string vn
  val _ = get_variable_name_count := (!get_variable_name_count) + 1
in (str, (fn _ => error "get_variable_name cert")) end
 *)
  val prop = Thm.prop_of thm
  val (n',T',str) = case prop of Const _ $ (Const _ $ (Const _ $ Free(n',T')) $ str) => (n',T',str)
  val _ = if n <> n' then raise TERM("get_variable_name: wrong name: "^n',[v]) else ()
  val _ = if T <> T' then raise TYPE("get_variable_name: wrong type",[T,T'],[v]) else ()
in (str, fn _ => thm) end
  | get_variable_name _ v = raise TERM("get_variable_name: not a variable",[v])
\<close>


(* TODO move non wp-stuff *)
ML \<open>
val get_variable_name_spec : Cert_Codegen.specf = {name="get_variable_name", inputs=["v"], outputs=["n"],
                                      pattern=\<^prop>\<open>variable_name v = n\<close> |> Cert_Codegen.free_to_var}
\<close>
setup \<open>Cert_Codegen.add_spec get_variable_name_spec\<close>


lemma index_var1_aux:
  assumes "variable_name v = vname"
  assumes "variable_name v1 = v1name"
  assumes "vname @ ''1'' = v1name'"
  assumes "assert_equals v1name v1name'"
  shows "index_var True v = v1"
  using assms unfolding assert_equals_def using index_var1I by smt

lemma index_var2_aux:
  assumes "variable_name v = vname"
  assumes "variable_name v2 = v2name"
  assumes "vname @ ''2'' = v2name'"
  assumes "assert_equals v2name v2name'"
  shows "index_var False v = v2"
  using assms unfolding assert_equals_def using index_var2I by smt


ML \<open>
fun index_var_func ctxt left (v as Free(n,T)) = let
  val left' = if left = \<^const>\<open>True\<close> then true else if left = \<^const>\<open>False\<close> then false else raise TERM("index_var_func",[left])
  fun lr x y = if left' then x else y
  val v1 = Free(n^lr "1" "2",T)
  val (vname,vname_cert) = get_variable_name ctxt v
  val (v1name,v1name_cert) = get_variable_name ctxt v1
  val (v1name',v1name'_cert) = Cert_Codegen.string_concat_func ctxt vname (lr \<^term>\<open>''1''\<close> \<^term>\<open>''2''\<close>)
  val ((),eq_cert) = Cert_Codegen.assert_equals_func ctxt v1name v1name'
  fun cert () = (lr @{thm index_var1_aux} @{thm index_var2_aux}) OF [vname_cert(), v1name_cert(), v1name'_cert(), eq_cert()]
  in (v1,cert) end
  | index_var_func _ _ v = raise TERM("index_var_func",[v])
;;
val index_var_func_spec = {name="index_var_func", inputs=["left","v"], outputs=["v1"], pattern=\<^prop>\<open>index_var left v = v1\<close> |> Cert_Codegen.free_to_var} : Cert_Codegen.specf
\<close>
setup \<open>Cert_Codegen.add_spec index_var_func_spec\<close>

lemma index_vars_unit_func:
  assumes "X \<equiv> variable_unit"
  assumes "variable_unit \<equiv> X'"
  shows "index_vars left X = X'"
  using assms index_vars_unit by metis

lemma index_vars_singleton_func:
  assumes "X \<equiv> variable_singleton x"
  assumes "index_var left x = x1"
  assumes "variable_singleton x1 \<equiv> X'"
  shows "index_vars left X = X'"
  using assms index_vars_singleton by metis

lemma index_vars_concat_func:
  assumes "X \<equiv> variable_concat Y Z"
  assumes "index_vars left Y = Y1"
  assumes "index_vars left Z = Z1"
  assumes "variable_concat Y1 Z1 \<equiv> X'"
  shows "index_vars left X = X'"
  using assms index_vars_concat by metis

ML \<open>
val index_vars_func_spec : Cert_Codegen.specfx = {name="index_vars", inputs=["left","X"], outputs=["X'"],
  thms= ["index_vars_unit_func","index_vars_singleton_func","index_vars_concat_func"],
  pattern=Thm.concl_of @{thm index_vars_singleton_func}, fallback="fn (left,X) => raise TERM(\"index_vars_concat_func\",[left,X])"}
\<close>
setup \<open>Cert_Codegen.thms_to_funs [index_vars_func_spec] "Autogen_Index_Vars" "index_vars.ML"\<close>


lemma index_expression_func:
  assumes "e \<equiv> expression Q E"
  assumes "index_vars left Q = Q1"
  assumes "expression Q1 E \<equiv> e'"
  shows "index_expression left e = e'"
  using assms index_expression by metis

ML \<open>
val index_expression_func_spec : Cert_Codegen.specfx = {name="index_expression_func", inputs=["left","e"], outputs=["e'"],
    pattern=Thm.concl_of @{thm index_expression_func}, thms=["index_expression_func"], 
    fallback="fn (left,e) => raise TERM(\"index_expression_func\",[left,e])"}
\<close>
setup \<open>Cert_Codegen.thms_to_funs [index_expression_func_spec] "Autogen_Index_Expression" "index_expression.ML"\<close>




lemma wp_skip_func:
  assumes "c == []" and "d == []" and "B == A"
  shows "qrhl A c d B"
  unfolding assms by (rule wp_skip)

lemma wp1_assign_func:
  fixes x e c d A B
  assumes "c == [assign x e]" and "d == []"
  assumes "index_var True x = x1"
  assumes "index_expression True e = e1"
  assumes "subst_expression (substitute1 x1 e1) B = A"
  shows "qrhl A c d B"
  using assms wp1_assign by metis

lemma wp2_assign_func:
  fixes x e c d A B
  assumes "d == [assign x e]" and "c == []"
  assumes "index_var False x = x1"
  assumes "index_expression False e = e1"
  assumes "subst_expression (substitute1 x1 e1) B = A"
  shows "qrhl A c d B"
  using assms wp2_assign by metis

definition "cleanup_expression_function Q f = f"
lemma cleanup_expression_functionI: "f == f' \<Longrightarrow> cleanup_expression_function Q f = f'"
  unfolding cleanup_expression_function_def by simp

ML \<open>
fun cleanup_expression_function ctxt Q f = let
  val vs = Prog_Variables.parse_varlist Q
  val (f',cert') = Cert_Codegen.mk_tupled_lambda ctxt vs f
  fun cert () = (infer_instantiate ctxt [(("Q",0),Q |> Thm.cterm_of ctxt)] @{thm cleanup_expression_functionI}) OF [cert' ()]
  in
    (f',cert)
  end;;
val cleanup_expression_function_spec : Cert_Codegen.specf = {
  name="cleanup_expression_function",
  pattern=\<^prop>\<open>cleanup_expression_function Q e = e'\<close> |> Cert_Codegen.free_to_var,
  inputs=["Q","e"], outputs=["e'"]
}
\<close>
setup \<open>Cert_Codegen.add_spec cleanup_expression_function_spec\<close>

(* ML \<open>
cleanup_expression_function \<^context> \<^term>\<open>variable_unit\<close> \<^term>\<open>undefined :: unit\<Rightarrow>unit\<close>
|> snd |> (fn x => x())
\<close> 
thm unit_abs_eta_conv[THEN eq_reflection, symmetric] *)

definition "cleanup_expression_concat' Q1 Q2 = expression (variable_concat Q1 Q2)"
definition "cleanup_expression_concat Q1 Q2 = expression (variable_concat Q1 Q2)"
(* definition "cleanup_expression_concat3' Q1 Q2 Q3 = expression (variable_concat Q1 (variable_concat Q2 Q3))" *)
(* definition "cleanup_expression_concat3 Q1 Q2 Q3 = expression (variable_concat Q1 (variable_concat Q2 Q3))" *)

lemma cleanup_expression_concat'_unit:
  assumes "Q1 \<equiv> \<lbrakk>\<rbrakk>"
  (* TODO: beta reduce f ((),q) if possible *)
  assumes "expression Q2 (\<lambda>q. f ((),q)) \<equiv> e"
  shows "cleanup_expression_concat' Q1 Q2 f = e"
  unfolding cleanup_expression_concat'_def using assms apply auto
  sorry

lemma cleanup_expression_concat'_cons:
  assumes "Q1 \<equiv> variable_concat \<lbrakk>q\<rbrakk> Q1'"
  (* TODO: beta reduce f ((),q) if possible *)
  assumes "expression (variable_concat Q1' (variable_concat \<lbrakk>q\<rbrakk> Q2)) (\<lambda>(x1',(x,x2)). f ((x,x1'),x2)) \<equiv> e"
  shows "cleanup_expression_concat' Q1 Q2 f = e"
  unfolding cleanup_expression_concat'_def using assms apply auto
  sorry

lemma cleanup_expression_concat'_right_unit:
  assumes "Q2 \<equiv> \<lbrakk>\<rbrakk>"
  (* TODO: beta reduce f ((),q) if possible *)
  assumes "expression Q1 (\<lambda>q. f (q,())) \<equiv> e"
  shows "cleanup_expression_concat' Q1 Q2 f = e"
  unfolding cleanup_expression_concat'_def assms(1) assms(2)[symmetric] 
  sorry

lemma cleanup_expression_concat'_single:
  assumes "Q1 \<equiv> \<lbrakk>q\<rbrakk>"
  assumes "expression (variable_concat Q1 Q2) f  \<equiv> e"
  shows "cleanup_expression_concat' Q1 Q2 f = e"
  unfolding cleanup_expression_concat'_def using assms by auto

lemma cleanup_expression_concat:
  assumes "cleanup_expression_concat' Q1 Q2 f = expression Q f'"
  assumes "cleanup_expression_function Q f' = f''"
  assumes "expression Q f'' == e"
  shows "cleanup_expression_concat Q1 Q2 f = e"
  using assms unfolding cleanup_expression_function_def cleanup_expression_concat'_def cleanup_expression_concat_def by simp


ML \<open>
val cleanup_expression_concat'_spec : Cert_Codegen.specfx = {
  name="cleanup_expression_concat'",
  pattern=\<^prop>\<open>cleanup_expression_concat' Q1 Q2 f = e\<close> |> Cert_Codegen.free_to_var,
  inputs=["Q1","Q2","f"], outputs=["e"],
  thms=["cleanup_expression_concat'_unit","cleanup_expression_concat'_right_unit",
        "cleanup_expression_concat'_cons","cleanup_expression_concat'_single"],
  fallback="fn (Q1,Q2,f) => raise TERM(\"cleanup_expression_concat'\",[Q1,Q2,f])"
}
val cleanup_expression_concat_spec : Cert_Codegen.specfx = {
  name="cleanup_expression_concat",
  pattern=\<^prop>\<open>cleanup_expression_concat Q1 Q2 f = e\<close> |> Cert_Codegen.free_to_var,
  inputs=["Q1","Q2","f"], outputs=["e"],
  thms=["cleanup_expression_concat"],
  fallback="fn (Q1,Q2,f) => raise TERM(\"cleanup_expression_concat\",[Q1,Q2,f])"
}\<close>
(* TODO: should remove duplicates in the varterm *)
setup \<open>Cert_Codegen.thms_to_funs [cleanup_expression_concat'_spec,cleanup_expression_concat_spec] "Autogen_Cleanup_Expression_Concat" "cleanup_expression_concat.ML"\<close>
(* ML_file "autogenerated/cleanup_expression_concat.ML" *)

lemma map_expression2_func:
  assumes "e1 == expression Q1 E1"
  assumes "e2 == expression Q2 E2"
  assumes "cleanup_expression_concat Q1 Q2 (\<lambda>(x1,x2). f (E1 x1) (E2 x2)) = e'"
  shows "map_expression2 f e1 e2 = e'"
  unfolding assms(1,2) assms(3)[symmetric]
  unfolding cleanup_expression_concat_def
  by simp

lemma map_expression2'_func:
  assumes "e1 == expression Q1 E1"
  assumes "\<And>z. e2 z == expression (Q2z z) (E2 z)"
  assumes "constant_function Q2z Q2"
  assumes "cleanup_expression_concat Q1 Q2 (\<lambda>(x1,x2). f (E1 x1) (\<lambda>z. E2 z x2)) = e'"
  shows "map_expression2' f e1 e2 = e'"
  unfolding assms(1,2) assms(4)[symmetric]
  using assms(3) unfolding constant_function_def cleanup_expression_concat_def
  by simp

lemma map_expression3_func:
  assumes "e1 == expression Q1 E1"
  assumes "e2 == expression Q2 E2"
  assumes "e3 == expression Q3 E3"
  assumes "cleanup_expression_concat Q2 Q3 (\<lambda>(x2,x3) z. f z (E2 x2) (E3 x3)) = expression Q23 E23" (is "?c23 = ?e23")
  assumes "cleanup_expression_concat Q1 Q23 (\<lambda>(x1,x2x3). (E23 x2x3) (E1 x1)) = e'" (is "?c123 = _")
  shows "map_expression3 f e1 e2 e3 = e'"
proof -
  have e23: "?e23 = expression (variable_concat Q2 Q3) (\<lambda>(x2,x3) z. f z (E2 x2) (E3 x3))" (is "_ = ?m23")
    unfolding assms(4)[symmetric] cleanup_expression_concat_def map_expression_def pair_expression_def by simp
  have "e' = map_expression (\<lambda>(x1,x2). x2 x1) (pair_expression (expression Q1 E1) ?e23)"
    unfolding assms(5)[symmetric]
    unfolding cleanup_expression_concat_def map_expression_def pair_expression apply simp
    apply (tactic \<open>cong_tac \<^context> 1\<close>) by auto
  also have "\<dots> = (expression (variable_concat Q1 (variable_concat Q2 Q3)) (\<lambda>(x1,(x2,x3)). (f (E1 x1) (E2 x2) (E3 x3))))"
    unfolding e23 apply simp
    apply (tactic \<open>cong_tac \<^context> 1\<close>) by auto
  also have "\<dots> = map_expression3 f e1 e2 e3"
    unfolding assms(1-3) by simp
  finally show ?thesis by simp
qed

ML \<open>
val map_expression2'_func_spec : Cert_Codegen.specfx = {
  name="map_expression2'",
  pattern=\<^prop>\<open>map_expression2' f e1 e2 = e'\<close> |> Cert_Codegen.free_to_var,
  inputs=["f","e1","e2"], outputs=["e'"],
  thms=["map_expression2'_func"],
  fallback="fn (f,e1,e2) => raise TERM(\"map_expression2'\",[f,e1,e2])"
}
val map_expression2_func_spec : Cert_Codegen.specfx = {
  name="map_expression2",
  pattern=\<^prop>\<open>map_expression2 f e1 e2 = e'\<close> |> Cert_Codegen.free_to_var,
  inputs=["f","e1","e2"], outputs=["e'"],
  thms=["map_expression2_func"],
  fallback="fn (f,e1,e2) => raise TERM(\"map_expression2\",[f,e1,e2])"
}
val map_expression3_func_spec : Cert_Codegen.specfx = {
  name="map_expression3",
  pattern=\<^prop>\<open>map_expression3 f e1 e2 e3 = e'\<close> |> Cert_Codegen.free_to_var,
  inputs=["f","e1","e2","e3"], outputs=["e'"],
  thms=["map_expression3_func"],
  fallback="fn (f,e1,e2,e3) => raise TERM(\"map_expression3\",[f,e1,e2,e3])"
}
\<close>
setup \<open>Cert_Codegen.thms_to_funs [map_expression2_func_spec,map_expression3_func_spec,map_expression2'_func_spec] "Autogen_Map_Expression" "map_expression.ML"\<close>
(* ML_file "autogenerated/map_expression.ML" *)

 
lemma subst_expression_func_unit:
  assumes "s == substitute1 x f"
  assumes "e == expression variable_unit E"
  assumes "expression variable_unit E == e'"
  shows "subst_expression s e = e'"
  using assms Encoding.subst_expression_unit_aux by metis

lemma subst_expression_func_singleton_same:
  assumes "s == substitute1 x (expression R F)"
  assumes "e == expression \<lbrakk>x\<rbrakk> E"
  assumes "expression R (\<lambda>r. E (F r)) == e'"
  shows "subst_expression s e = e'"
  using assms Encoding.subst_expression_singleton_same_aux by metis

lemma subst_expression_func_singleton_notsame:
  assumes "s == substitute1 x f"
  assumes "e == expression \<lbrakk>y\<rbrakk> E"
  assumes "variable_name x = xn"
  assumes "variable_name y = yn"
  assumes neq: "assert_string_neq xn yn"
  assumes "e == e'"
  shows "subst_expression s e = e'"
  using neq unfolding assms(1,2) assms(3,4,6)[symmetric] assert_string_neq_def
  using Encoding.subst_expression_singleton_notsame_aux by metis

lemma subst_expression_func_concat_id:
  assumes "s == substitute1 x f"
  assumes "e == expression (variable_concat Q1 Q2) (\<lambda>x. x)"
  assumes "subst_expression (substitute1 x f) (expression Q1 (\<lambda>x. x)) = expression Q1' e1"
  assumes "subst_expression (substitute1 x f) (expression Q2 (\<lambda>x. x)) = expression Q2' e2"
  assumes "cleanup_expression_concat Q1' Q2' (\<lambda>(x1,x2). (e1 x1, e2 x2)) = e'"
  shows "subst_expression s e = e'"
  using assms Encoding.subst_expression_concat_id_aux unfolding cleanup_expression_concat_def by metis

lemma subst_expression_func_id_comp:
  assumes "s == substitute1 x f"
  assumes "e == expression Q E"
  assumes "NO_MATCH (\<lambda>x::unit. x) E"
  assumes "subst_expression (substitute1 x f) (expression Q (\<lambda>x. x)) = expression Q' g"
  assumes "expression Q' (\<lambda>x. E (g x)) == e'"
  shows "subst_expression s e = e'"
  using assms(4) unfolding assms(1-2) assms(5)[symmetric]
  using Encoding.subst_expression_id_comp_aux by metis

ML \<open>
val subst_expression_func_spec : Cert_Codegen.specfx = {
  name="subst_expression_func",
  inputs=["s","e"], outputs=["e'"], pattern= @{thm subst_expression_func_id_comp} |> Thm.concl_of,
  thms= ["subst_expression_func_unit","subst_expression_func_concat_id",
               "subst_expression_func_singleton_same","subst_expression_func_singleton_notsame",
               "subst_expression_func_concat_id", "subst_expression_func_id_comp"],
  fallback="fn (s,e) => raise TERM(\"subst_expression_func\",[s,e])"}
\<close>
setup \<open>Cert_Codegen.thms_to_funs [subst_expression_func_spec] "Autogen_Subst_Expression" "subst_expression.ML"\<close>


lemma wp1_sample_func:
  fixes A B c d x e
  assumes "d == []" and "c == [sample x e]" 
  assumes "index_var True x = x1"
  assumes "index_expression True e = e1"
  assumes "\<And>z. subst_expression (substitute1 x1 (const_expression z)) B = B' z"
  assumes "map_expression2' (\<lambda>e' B'. Cla[weight e' = 1] \<sqinter> (INF z:supp e'. B' z)) e1 B' = A"
  shows "qrhl A c d B"
  unfolding assms(1-2) assms(3-6)[symmetric] by (rule wp1_sample)

lemma wp2_sample_func:
  fixes A B c d x e
  assumes "c == []" and "d == [sample x e]" 
  assumes "index_var False x = x1"
  assumes "index_expression False e = e1"
  assumes "\<And>z. subst_expression (substitute1 x1 (const_expression z)) B = B' z"
  assumes "map_expression2' (\<lambda>e' B'. Cla[weight e' = 1] \<sqinter> (INF z:supp e'. B' z)) e1 B' = A"
  shows "qrhl A c d B"
  unfolding assms(1-2) assms(3-6)[symmetric] by (rule wp2_sample)

lemma wp1_qapply_func:
  fixes A B Q e
  assumes "d == []" and "c == [qapply Q e]"
  assumes "index_vars True Q = Q\<^sub>1"
  assumes "index_expression True e = e\<^sub>1"
  assumes "map_expression2 (\<lambda>e\<^sub>1 B. Cla[isometry e\<^sub>1] \<sqinter> (adjoint (e\<^sub>1\<guillemotright>Q\<^sub>1) \<cdot> (B \<sqinter> (e\<^sub>1\<guillemotright>Q\<^sub>1 \<cdot> top)))) e\<^sub>1 B = A"
  shows "qrhl A c d B"
  unfolding assms(1-2) assms(3-5)[symmetric] by (rule wp1_qapply)

lemma wp2_qapply_func:
  fixes A B Q e
  assumes "c == []" and "d == [qapply Q e]"
  assumes "index_vars False Q = Q\<^sub>1"
  assumes "index_expression False e = e\<^sub>1"
  assumes "map_expression2 (\<lambda>e\<^sub>1 B. Cla[isometry e\<^sub>1] \<sqinter> (adjoint (e\<^sub>1\<guillemotright>Q\<^sub>1) \<cdot> (B \<sqinter> (e\<^sub>1\<guillemotright>Q\<^sub>1 \<cdot> top)))) e\<^sub>1 B = A"
  shows "qrhl A c d B"
  unfolding assms(1-2) assms(3-5)[symmetric] by (rule wp2_qapply)

lemma wp1_measure_func:
  fixes A B x Q e
  assumes "d == []" and "c == [measurement x Q e]"
  assumes "index_expression True e = e\<^sub>1"
  assumes "index_vars True Q = Q\<^sub>1"
  assumes "index_var True x = x\<^sub>1"
  assumes "\<And>z. subst_expression (substitute1 x\<^sub>1 (const_expression z)) B = B' z"
  assumes "map_expression2' (\<lambda>e\<^sub>1 B'. let meas=e\<^sub>1 in Cla[mtotal meas] \<sqinter> 
           (INF z. ((B' z \<sqinter> (((mproj meas z)\<guillemotright>Q\<^sub>1) \<cdot> top)) + ortho (((mproj meas z)\<guillemotright>Q\<^sub>1) \<cdot> top)))) e\<^sub>1 B' = A"
  shows "qrhl A c d B"
  unfolding assms(1,2) assms(3,4,5,6,7)[symmetric] Let_def by (rule wp1_measure[unfolded Let_def])

lemma wp2_measure_func:
  fixes A B x Q e
  assumes "c == []" and "d == [measurement x Q e]"
  assumes "index_expression False e = e\<^sub>1"
  assumes "index_vars False Q = Q\<^sub>1"
  assumes "index_var False x = x\<^sub>1"
  assumes "\<And>z. subst_expression (substitute1 x\<^sub>1 (const_expression z)) B = B' z"
  assumes "map_expression2' (\<lambda>e\<^sub>1 B'. let meas=e\<^sub>1 in Cla[mtotal meas] \<sqinter> 
           (INF z. ((B' z \<sqinter> (((mproj meas z)\<guillemotright>Q\<^sub>1) \<cdot> top)) + ortho (((mproj meas z)\<guillemotright>Q\<^sub>1) \<cdot> top)))) e\<^sub>1 B' = A"
  shows "qrhl A c d B"
  unfolding assms(1,2) assms(3,4,5,6,7)[symmetric] Let_def by (rule wp2_measure[unfolded Let_def])


lemma wp1_qinit_func:
  fixes A B e Q c d
  assumes "d==[]" and "c == [qinit Q e]"
  assumes "index_expression True e = e\<^sub>1"
  assumes "index_vars True Q = Q\<^sub>1"
  assumes "map_expression2 (\<lambda>e\<^sub>1 B. Cla[norm e\<^sub>1 = 1] \<sqinter> (B \<div> e\<^sub>1 \<guillemotright> Q\<^sub>1)) e\<^sub>1 B = A"
  shows "qrhl A c d B"
  unfolding assms(1-2) assms(3-5)[symmetric] by (rule wp1_qinit)

lemma wp2_qinit_func:
  fixes A B e Q c d
  assumes "c==[]" and "d == [qinit Q e]"
  assumes "index_expression False e = e\<^sub>1"
  assumes "index_vars False Q = Q\<^sub>1"
  assumes "map_expression2 (\<lambda>e\<^sub>1 B. Cla[norm e\<^sub>1 = 1] \<sqinter> (B \<div> e\<^sub>1 \<guillemotright> Q\<^sub>1)) e\<^sub>1 B = A"
  shows "qrhl A c d B"
  unfolding assms(1-2) assms(3-5)[symmetric] by (rule wp2_qinit)

lemma wp1_if_func:
  fixes e p1 p2 B
  assumes "d == []" and "c == [ifthenelse e p1 p2]"
  assumes "index_expression True e = e\<^sub>1"
  assumes "qrhl wp_true p1 [] B"
  assumes "qrhl wp_false p2 [] B"
  assumes "map_expression3 (\<lambda>e\<^sub>1 wp_true wp_false. (Cla[\<not>e\<^sub>1] + wp_true) \<sqinter> (Cla[e\<^sub>1] + wp_false))
                 e\<^sub>1 wp_true wp_false = A"
  shows "qrhl A c d B"
  unfolding assms(1-2) assms(3,6)[symmetric] using assms(4,5) by (rule wp1_if)

lemma wp2_if_func:
  fixes e p1 p2 B
  assumes "c == []" and "d == [ifthenelse e p1 p2]"
  assumes "index_expression False e = e\<^sub>1"
  assumes "qrhl wp_true [] p1 B"
  assumes "qrhl wp_false [] p2 B"
  assumes "map_expression3 (\<lambda>e\<^sub>1 wp_true wp_false. (Cla[\<not>e\<^sub>1] + wp_true) \<sqinter> (Cla[e\<^sub>1] + wp_false))
               e\<^sub>1 wp_true wp_false = A"
  shows "qrhl A c d B"
  unfolding assms(1-2) assms(3,6)[symmetric] using assms(4,5) by (rule wp2_if)

lemma wp1_block_func:
  assumes "d == []" and "c == [block p]"
  assumes "qrhl A p [] B"
  shows "qrhl A c d B"
  unfolding assms(1,2) using assms(3) by (rule wp1_block)

lemma wp2_block_func:
  assumes "c == []" and "d == [block p]"
  assumes "qrhl A [] p B"
  shows "qrhl A c d B"
  unfolding assms(1,2) using assms(3) by (rule wp2_block)

lemma wp1_cons_func:
  assumes "d == []" and "c == p#ps"
  assumes "NO_MATCH ([]::unit list) ps"
  assumes "qrhl B' ps [] B" and "qrhl A [p] [] B'"
  shows "qrhl A c d B"
  unfolding assms(1,2) using assms(4,5) by (rule wp1_cons[rotated])

lemma wp2_cons_func:
  assumes "c == []" and "d == p#ps"
  assumes "NO_MATCH ([]::unit list) ps"
  assumes "qrhl B' [] ps B"
    and "qrhl A [] [p] B'"
  shows "qrhl A c d B"
  unfolding assms(1,2) using assms(4,5) by (rule wp2_cons[rotated])




definition "wp1_tac left qrhl_in qrhl_out =
  (qrhl_out \<longrightarrow> qrhl_in)" 

lemma wp1_tac_func_left:
  assumes "left == True"
  assumes "qrhl_in == qrhl A c d B"
  assumes "list_last c c' s"
  assumes "qrhl B' [s] [] B"
  assumes "qrhl A c' d B' == qrhl_out"
  shows "wp1_tac left qrhl_in qrhl_out"
  unfolding wp1_tac_def assms(1,2) assms(5)[symmetric] assms(3)[unfolded list_last_def, symmetric]
  using assms(4) apply auto
  apply (rule seqREMOVE) by auto  


lemma wp1_tac_func_right:
  assumes "left == False"
  assumes "qrhl_in == qrhl A c d B"
  assumes "list_last d d' s"
  assumes "qrhl B' [] [s] B"
  assumes "qrhl A c d' B' == qrhl_out"
  shows "wp1_tac left qrhl_in qrhl_out"
  unfolding wp1_tac_def assms(1,2) assms(5)[symmetric] assms(3)[unfolded list_last_def, symmetric]
  using assms(4) apply auto
  apply (rule seqREMOVE) by auto

setup \<open>Cert_Codegen.thms_to_funs [

{name="wp", thms= 
["wp_skip_func","wp1_assign_func","wp2_assign_func", "wp1_sample_func", "wp2_sample_func",
  "wp1_qapply_func", "wp2_qapply_func", "wp1_measure_func", "wp2_measure_func", 
  "wp1_qinit_func", "wp2_qinit_func", "wp1_if_func", "wp2_if_func",
  "wp1_block_func", "wp2_block_func", "wp1_cons_func", "wp2_cons_func"],
inputs=["c","d","B"], outputs=["A"], fallback="fn (c,d,B) => raise TERM(\"wp\",[c,d,B])", 
pattern=Thm.concl_of @{thm wp_skip_func}},

{name="wp1_tac", inputs=["left","qrhl_in"], outputs=["qrhl_out"],
  pattern= @{thm wp1_tac_func_left} |> Thm.concl_of, thms=["wp1_tac_func_left","wp1_tac_func_right"],
  fallback="fn (left,qrhl_in) => raise TERM(\"wp1_tac\",[left,qrhl_in])"}

] "Autogen_WP" "wp.ML"\<close>


end
