theory Test
  imports 
 (* CryptHOL.Cyclic_Group QRHL.QRHL "HOL-Eisbach.Eisbach_Tools"  *)
QRHL.QRHL
     (* QRHL.QRHL_Core  Multi_Transfer  *)
(* QRHL.Prog_Variables *)
(*   keywords
    "relift_definition" :: thy_goal
 *)
begin

text nothing

no_notation "Order.bottom" ("\<bottom>\<index>")
no_notation "Order.top" ("\<top>\<index>")
no_notation "Lattice.meet" (infixl "\<sqinter>\<index>" 70)
no_notation "Lattice.join" (infixl "\<squnion>\<index>" 65)
hide_const (open) Order.bottom Order.top

term Order.bottom
term \<bottom>
term "a \<sqinter> b"
term Lattice.meet

definition "assert_equals a b = (a=b)"
lemma assert_equals_refl: "assert_equals a a" unfolding assert_equals_def by simp
definition [simp]: "assert_string_neq (a::string) b = (a \<noteq> b)"
lemma NO_MATCH_I: "NO_MATCH x y" by simp

ML_file "cert_codegen.ML"

(* variables classical xxx :: int begin *)

(* lemma [simp]: "variable_name var_xxx = ''x''" sorry
lemma [simp]: "variable_name var_xxx = ''x''" *)

(* lemma "variable_name var_xxx = undefined" apply simp oops *)

ML \<open>open Cert_Codegen\<close>

ML \<open>
fun get_variable_name ctxt v = let
  val ct = Const(\<^const_name>\<open>variable_name\<close>, fastype_of v --> HOLogic.stringT) $ v |> Thm.cterm_of ctxt
  val thm = Raw_Simplifier.rewrite_cterm (false,false,false) (K (K NONE)) ctxt ct
  val rhs = Thm.rhs_of thm |> Thm.term_of
  val _ = HOLogic.dest_string rhs         
  in
    (rhs, fn () => thm RS @{thm meta_eq_to_obj_eq})
  end
val get_variable_name_spec : specf = {name="get_variable_name", inputs=["v"], outputs=["n"],
                                      pattern=\<^prop>\<open>variable_name v = n\<close> |> free_to_var}
;;
(* get_variable_name \<^context> @{term var_xxx} *)
\<close>

ML \<open>
@{ml_term "string_concat_func a b c"}
\<close>

ML \<open>
fun check_func (t,cert) = let
  val thm = cert ()
  (* val _ = if Thm.term_of (Thm.rhs_of thm) <> t then raise TERM("check_func",[Thm.prop_of thm, t]) else () *)
  in (Thm.global_cterm_of (Thm.theory_of_thm thm) t, thm) end
\<close>


(* definition string_concat_func[simp]: "string_concat_func a b c = (a@b = c)" *)
ML \<open> 
;;
string_concat_func \<^context> \<^term>\<open>''hello''\<close> \<^term>\<open>''there''\<close> |> check_func 
;;
fun get_variable_name_spec ctxt v = let
  val ct = Thm.cterm_of ctxt v
  val thm = Raw_Simplifier.rewrite_cterm (false,false,false) (K (K NONE)) ctxt ct
  val rhs = Thm.rhs_of thm |> Thm.term_of
  val _ = HOLogic.dest_string rhs
  in
    (rhs, fn () => thm)
  end
;;
val get_variable_name_spec : specf = {name="get_variable_name", inputs=["v"], outputs=["n"],
                                      pattern=\<^prop>\<open>variable_name v = n\<close> |> free_to_var}
;;
(* get_variable_name \<^context> @{term var_xxx} |> check_func *)
\<close>


ML \<open>
;;
assert_equals_func \<^context> @{term 123} @{term 123} |> snd |> (fn c => c())
\<close>


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
  val (v1name',v1name'_cert) = string_concat_func ctxt vname (lr \<^term>\<open>''1''\<close> \<^term>\<open>''2''\<close>)
  val ((),eq_cert) = assert_equals_func ctxt v1name v1name'
  fun cert () = (lr @{thm index_var1_aux} @{thm index_var2_aux}) OF [vname_cert(), v1name_cert(), v1name'_cert(), eq_cert()]
  in (v1,cert) end
  | index_var_func _ _ v = raise TERM("index_var_func",[v])
;;
val index_var_func_spec = {name="index_var_func", inputs=["left","v"], outputs=["v1"], pattern=\<^prop>\<open>index_var left v = v1\<close> |> free_to_var} : specf
\<close>

variables classical x :: int begin
ML \<open>
index_var_func \<^context> @{term False} @{term "var_x"} |> check_func
\<close>
end

lemma index_expression_func:
  assumes "e \<equiv> expression Q E"
  assumes "index_vars left Q = Q1"
  assumes "expression Q1 E \<equiv> e'"
  shows "index_expression left e = e'"
  using assms index_expression_def by metis

ML \<open>
val index_expression_func_spec : specfx = {name="index_expression_func", inputs=["left","e"], outputs=["e'"],
    pattern=Thm.concl_of @{thm index_expression_func}, thms=["index_expression_func"], 
    fallback="fn (left,e) => raise TERM(\"index_expression_func\",[left,e])"}
\<close>


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
val index_vars_func_spec : specfx = {name="index_vars", inputs=["left","X"], outputs=["X'"],
  thms= ["index_vars_unit_func","index_vars_singleton_func","index_vars_concat_func"],
  pattern=Thm.concl_of @{thm index_vars_singleton_func}, fallback="fn (left,X) => raise TERM(\"index_vars_concat_func\",[left,X])"}
\<close>

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
  assumes "expression (variable_concat Q1' Q2') (\<lambda>(x1,x2). (e1 x1, e2 x2)) == e'"
  shows "subst_expression s e = e'"
  using assms Encoding.subst_expression_concat_id_aux by metis

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
val subst_expression_func_spec : specfx = {
  name="subst_expression_func",
  inputs=["s","e"], outputs=["e'"], pattern= @{thm subst_expression_func_id_comp} |> Thm.concl_of,
  thms= ["subst_expression_func_unit","subst_expression_func_concat_id",
               "subst_expression_func_singleton_same","subst_expression_func_singleton_notsame",
               "subst_expression_func_concat_id", "subst_expression_func_id_comp"],
  fallback="fn (s,e) => raise TERM(\"subst_expression_func\",[s,e])"}
\<close>



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

lemma wp1_sample_func:
  fixes A B c d x e
  assumes "d == []" and "c == [sample x e]" 
  assumes "index_var True x = x1"
  assumes "index_expression True e = e1"
(* TODO: all-quants probably don't work! *)
  assumes "\<And>z. subst_expression (substitute1 x1 (const_expression z)) B = B' z"
(* TODO: implement map_expression2 *)
  assumes "map_expression2' (\<lambda>e' B'. Cla[weight e' = 1] \<sqinter> (INF z:supp e'. B' z)) e1 B' == A"
  shows "qrhl A c d B"
  unfolding assms(1-2) assms(3-6)[symmetric] by (rule wp1_sample)

lemma wp2_sample_func:
(*TODO*)
  fixes A B c d x e
  assumes "c == []" and "d == [sample x e]" 
  defines "e' \<equiv> index_expression False e"
  defines "B' z \<equiv> subst_expression (substitute1 (index_var False x) (const_expression z)) B"
  assumes "map_expression2' (\<lambda>e' B'. Cla[weight e' = 1] \<sqinter> (INF z:supp e'. B' z)) e' B' == A"
  shows "qrhl A c d B"
  unfolding assms(1-4) assms(5)[symmetric] by (rule wp2_sample)

lemma wp1_qapply_func:
(*TODO*)
  fixes A B Q e
  assumes "d == []" and "c == [qapply Q e]"
  defines "Q\<^sub>1 \<equiv> index_vars True Q"
  assumes "map_expression2 (\<lambda>e\<^sub>1 B. Cla[isometry e\<^sub>1] \<sqinter> (adjoint (e\<^sub>1\<guillemotright>Q\<^sub>1) \<cdot> (B \<sqinter> (e\<^sub>1\<guillemotright>Q\<^sub>1 \<cdot> top)))) (index_expression True e) B \<equiv> A"
  shows "qrhl A c d B"
  unfolding assms(1-3) assms(4)[symmetric] by (rule wp1_qapply)

lemma wp2_qapply_func:
(*TODO*)
  fixes A B Q e
  assumes "c == []" and "d == [qapply Q e]"
  defines "Q\<^sub>1 \<equiv> index_vars False Q"
  assumes "map_expression2 (\<lambda>e\<^sub>1 B. Cla[isometry e\<^sub>1] \<sqinter> (adjoint (e\<^sub>1\<guillemotright>Q\<^sub>1) \<cdot> (B \<sqinter> (e\<^sub>1\<guillemotright>Q\<^sub>1 \<cdot> top)))) (index_expression False e) B \<equiv> A"
  shows "qrhl A c d B"
  unfolding assms(1-3) assms(4)[symmetric] by (rule wp2_qapply)

lemma wp1_measure_func:
(*TODO*)
  fixes A B x Q e
  assumes "d == []" and "c == [measurement x Q e]"
  defines "e\<^sub>1 \<equiv> index_expression True e"
  defines "B' z \<equiv> subst_expression (substitute1 (index_var True x) (const_expression z)) B"
  defines "\<And>e\<^sub>1 z. ebar e\<^sub>1 z \<equiv> ((mproj e\<^sub>1 z)\<guillemotright>(index_vars True Q)) \<cdot> top"
  assumes "map_expression2' (\<lambda>e\<^sub>1 B'. Cla[mtotal e\<^sub>1] \<sqinter> 
           (INF z. ((B' z \<sqinter> ebar e\<^sub>1 z) + ortho (ebar e\<^sub>1 z)))) e\<^sub>1 B' == A"
  shows "qrhl A c d B"
  unfolding assms(1-5) assms(6)[symmetric] by (rule wp1_measure)

lemma wp2_measure_func:
(*TODO*)
  fixes A B x Q e
  assumes "c == []" and "d == [measurement x Q e]"
  defines "e\<^sub>1 \<equiv> index_expression False e"
  defines "B' z \<equiv> subst_expression (substitute1 (index_var False x) (const_expression z)) B"
  defines "\<And>e\<^sub>1 z. ebar e\<^sub>1 z \<equiv> ((mproj e\<^sub>1 z)\<guillemotright>(index_vars False Q)) \<cdot> top"
  assumes "map_expression2' (\<lambda>e\<^sub>1 B'. Cla[mtotal e\<^sub>1] \<sqinter> 
           (INF z. ((B' z \<sqinter> ebar e\<^sub>1 z) + ortho (ebar e\<^sub>1 z)))) e\<^sub>1 B' == A"
  shows "qrhl A c d B"
  unfolding assms(1-5) assms(6)[symmetric] by (rule wp2_measure)

lemma wp1_qinit_func:
(*TODO*)
  fixes A B e Q
  assumes "d==[]" and "c == [qinit Q e]"
  assumes "map_expression2 (\<lambda>e\<^sub>1 B. Cla[norm e\<^sub>1 = 1] \<sqinter> (B \<div> e\<^sub>1 \<guillemotright> (index_vars True Q)))
           (index_expression True e) B == A"
  shows "qrhl A c d B"
  unfolding assms(1-2) assms(3)[symmetric] by (rule wp1_qinit)

lemma wp2_qinit_func:
(*TODO*)
  fixes A B e Q
  assumes "c == []" and "d == [qinit Q e]"
  assumes "map_expression2 (\<lambda>e\<^sub>1 B. Cla[norm e\<^sub>1 = 1] \<sqinter> (B \<div> e\<^sub>1 \<guillemotright> (index_vars False Q)))
           (index_expression False e) B == A"
  shows "qrhl A c d B"
  unfolding assms(1-2) assms(3)[symmetric] by (rule wp2_qinit)

lemma wp1_if_func:
(*TODO*)
  fixes e p1 p2 B
  assumes "d == []" and "c == [ifthenelse e p1 p2]"
  assumes "qrhl wp_true p1 [] B"
  assumes "qrhl wp_false p2 [] B"
  assumes "map_expression3 (\<lambda>e\<^sub>1 wp_true wp_false. (Cla[\<not>e\<^sub>1] + wp_true) \<sqinter> (Cla[e\<^sub>1] + wp_false))
           (index_expression True e) wp_true wp_false == A"
  shows "qrhl A c d B"
  unfolding assms(1-2) assms(5)[symmetric] using assms(3,4) by (rule wp1_if)

lemma wp2_if_func:
(*TODO*)
  fixes e p1 p2 B
  assumes "c == []" and "d == [ifthenelse e p1 p2]"
  assumes "qrhl wp_true [] p1 B"
  assumes "qrhl wp_false [] p2 B"
  assumes "map_expression3 (\<lambda>e\<^sub>1 wp_true wp_false. (Cla[\<not>e\<^sub>1] + wp_true) \<sqinter> (Cla[e\<^sub>1] + wp_false))
           (index_expression False e) wp_true wp_false == A"
  shows "qrhl A c d B"
  unfolding assms(1-2) assms(5)[symmetric] using assms(3,4) by (rule wp2_if)

lemma wp1_block_func:
(*TODO*)
  assumes "d == []" and "c == [block p]"
  assumes "qrhl A p [] B"
  shows "qrhl A c d B"
  unfolding assms(1,2) using assms(3) by (rule wp1_block)

lemma wp2_block_func:
(*TODO*)
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




(* lemmas wp_func = wp_skip_func wp1_assign_func wp2_assign_func (* wp1_sample_func TODO *) wp2_sample_func
  wp1_qapply_func wp2_qapply_func wp1_measure_func wp2_measure_func wp1_if_func wp2_if_func
  wp1_block_func wp2_block_func wp1_cons_func wp2_cons_func *)




(* ML \<open>
val thm_by_id = Synchronized.var "thm_by_id" Inttab.empty : thm Inttab.table Synchronized.var
fun store_thm thm = let val id = serial () 
                        val _ = Synchronized.change thm_by_id (Inttab.update_new (id,thm))
                    in id end
fun get_thm_by_id id = Inttab.lookup (Synchronized.value thm_by_id) id |> the
\<close>
 *)

(* ML \<open>
structure Data = Theory_Data (
  type T = thm Inttab.table
  (* fun init _ = Inttab.empty *)
  val empty = Inttab.empty
  fun merge _ = Inttab.empty
  val extend = I
)
fun get_thm ctxt id = Inttab.lookup (Data.get ctxt) id |> the
fun thm_antiq (conf:conf) thm =
  let val id = serial ()
      val ctxt = Data.map (Inttab.update_new (id,thm)) (!(#ctxt conf))
      val (var,ctxt) = ML_Context.variant "thm" ctxt
      val prepare = "val " ^ var ^ " = get_thm \<^context> " ^ ML_Syntax.print_int id
      val retrieve = (* ML_Context.struct_name ctxt ^ "." ^ *) var
      val _ = #ctxt conf := ctxt
  in
    (prepare,retrieve)
  end
\<close> *)


ML \<open>
fun specf_to_specfx ({name,inputs,outputs,pattern} : specf) = {name=name,fallback="",inputs=inputs,outputs=outputs,pattern=pattern,thms=[]} : specfx
\<close>


ML \<open>
val spec_wp = 
{name="wp", thms= 
["wp_skip_func","wp1_assign_func","wp2_assign_func", (* "wp1_sample_func", *) "wp2_sample_func",
  "wp1_qapply_func", "wp2_qapply_func", "wp1_measure_func", "wp2_measure_func", "wp1_if_func", "wp2_if_func",
  "wp1_block_func", "wp2_block_func", "wp1_cons_func", "wp2_cons_func"],
inputs=["c","d","B"], outputs=["A"], fallback="fn (c,d,B) => raise TERM(\"wp\",[c,d,B])", pattern=Thm.concl_of @{thm wp_skip_func}} : specfx
val spec = [
  spec_wp,
  specf_to_specfx index_var_func_spec,
  specf_to_specfx get_variable_name_spec,
  specf_to_specfx assert_string_neq_func_spec,
  specf_to_specfx NO_MATCH_func_spec,
  index_expression_func_spec,
  index_vars_func_spec,
  subst_expression_func_spec
]
\<close>



ML \<open>
;;
print_comment "This (* is *) cool (******)"
\<close>






ML \<open>
(* TODO make work *)
thm_to_fun \<^context> (empty_conf (hd spec)) spec "wp1_sample_func" "f" ["c","d","B"] ["A"] |> writeln
\<close>


ML \<open>
;;
val _ = thms_to_fun \<^context> spec spec_wp |> tracing
\<close>

ML \<open>
\<close>



ML \<open>
(* val path = Path.append (Resources.master_directory \<^theory>) (Path.make ["test.ML"]) *)
val code = thms_to_funs \<^context> spec "Test" "test.ML"
(* val code = "val x = 1;;" *)
(* val written = File.write path code *)
(* val _ = ML_Context.eval_file ML_Compiler.flags path *)
(* val pos = Path.position path *)
(* val lex = ML_Lex.read_pos pos code *)
(* val res = ML_Context.eval_in (SOME ctxt) ML_Compiler.flags pos lex *)
(* val res = ML_Context.eval_file ML_Compiler.flags path *)
\<close>

ML_file "test.ML"

(* declare[[show_brackets]] *)
(* print_attributes *)

declare[[show_abbrevs=false,eta_contract=false]]
ML \<open>
\<^term>\<open>(%x::bool. x)\<close> $ \<^term>\<open>True\<close> |> Thm.cterm_of \<^context> 
\<close>

term "(%x. x) x"
term "(%x. f x)"

ML \<open>
fun rewrite_thm_as thm ct = let
val eq = Thm.transitive (Thm.beta_conversion true (Thm.cprop_of thm)) (Thm.beta_conversion true ct |> Thm.symmetric)
val thm' = Thm.equal_elim eq thm
in thm' end
\<close>

ML \<open>
local
val ctxt = \<^context>
val assm = @{prop "\<And>z. subst_expression (substitute1 x1 (const_expression z)) B = B' z"} |> free_to_var
val termvars = Symtab.make(map(fn n=>(n,n))["B","t_b","t_a","x1","z"])
val conf = (empty_conf (hd spec))

val _ = assm |> Thm.cterm_of ctxt
val ((z,T),assm') = Logic.dest_all assm
(* val _ = (z,T) |> @{print} *)
val _ = assm' |> Thm.cterm_of ctxt
val vars = Term.add_vars assm [] |> map (fst o fst)
val outputs = vars |> filter (not o Symtab.defined termvars)
val outputs_z = Name.variant_list vars (outputs |> map (fn n => n ^ "_" ^ z))
val subst = outputs ~~ outputs_z |> Symtab.make
fun s (t as Var((n,0),T') $ Free z') =
    (case (Symtab.lookup subst n, z'=(z,T)) of
      (SOME nz, true) => Var((nz,0),T' |> dest_funT |> snd)
    | _ => t)
  | s (t1 $ t2) = s t1 $ s t2
  | s (Abs(n,T,t)) = Abs(n,T,s t)
  | s t = t
val assm'' = s assm'
val _ = assm'' |> Thm.cterm_of ctxt

val ((code,cert'),(termvars,ctxt)) = code_for_assumption ctxt termvars conf spec assm''
val code = "local" :: map indent' code
(* val _ = @{print} termvars *)
(* val _ = @{print} termvars *)
(* val _ = @{print} cert' *)

val comment = print_comment "TODO: comment"
fun abscode1 (v,vz) (ctxt,termvars,checks) = let 
  val (v',(ctxt,termvars,checks)) = print_var_pattern v (ctxt,termvars,checks)
  val T' = print_typ termvars T
  val vz' = print_var termvars vz
  in ("val "^v'^" = absfree ("^ML_Syntax.print_string z^","^T'^") "^vz', (* SHouldn't z be quoted in some way? TODO *)
      (ctxt,termvars,checks)) end
val (abscode,(ctxt,termvars,checks)) = fold_map abscode1 (Symtab.dest subst) (ctxt,termvars,[])
val _ = if null checks then () else error "checks not empty"
val (certvar,ctxt) = ML_Context.variant "cert" ctxt
val certcode = "fun "^certvar^" () = generalize_thm_to ctxt " ^ ML_Syntax.atomic cert' ^ " " ^ ML_Syntax.atomic (print_term termvars assm)
  ^ " TODO: (" ^ "\"z\",t_a)"
val code = code @ ["in", comment] @ abscode @ [certcode,"end"]

val termvars = fold Symtab.delete outputs_z termvars

val _ = code |> String.concatWith "\n" |> tracing

(* Generate: cert *)

in end
\<close>

ML \<open>
fun generalize_thm_to ctxt thm prop (v,T) = let
  val thm' = thm |> Thm.generalize ([],["v"]) 0 |> Thm.forall_intr (Thm.cterm_of ctxt (Free(v,T)))
  val thm'' = rewrite_thm_as thm' (Thm.cterm_of ctxt prop)
  in thm'' end
\<close>



variables classical x :: nat begin
ML \<open>
local
val ctxt = \<^context>
val t_a = @{typ "nat"}
val t_b = @{typ "nat"}
val x1 = @{term "var_x1"}
val B = @{term "Expr[Suc x1]"}
open Test
in

local
  (* Assumption: subst_expression (substitute1 ?x1.0 (expression variable_unit (\<lambda>_. z))) ?B = ?B'_z
     Handled using function subst_expression_func *)
  val (((b_z)), cert)
           = subst_expression_func ctxt (Term.$ (Term.$ (Term.Const ("Expressions.substitute1", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [t_a]), Term.Type ("fun", [Term.Type ("Expressions.expression", [t_a]), Term.Type ("Expressions.substitution", [])])])), x1), Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.unit", [])]), Term.Type ("fun", [Term.Type ("fun", [Term.Type ("Product_Type.unit", []), t_a]), Term.Type ("Expressions.expression", [t_a])])])), Term.Const ("Prog_Variables.variable_unit", Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.unit", [])]))), Term.Abs ("uu_", Term.Type ("Product_Type.unit", []), Term.Free ("z", t_a))))) (B)
in
(* TODO: comment *)
val b = absfree ("z",t_a) b_z
fun certa () = generalize_thm_to ctxt (cert ()) (Term.$ (Term.Const ("Pure.all", Term.Type ("fun", [Term.Type ("fun", [t_a, Term.Type ("prop", [])]), Term.Type ("prop", [])])), Term.Abs ("z", t_a, Term.$ (Term.Const ("HOL.Trueprop", Term.Type ("fun", [Term.Type ("HOL.bool", []), Term.Type ("prop", [])])), Term.$ (Term.$ (Term.Const ("HOL.eq", Term.Type ("fun", [Term.Type ("Expressions.expression", [t_b]), Term.Type ("fun", [Term.Type ("Expressions.expression", [t_b]), Term.Type ("HOL.bool", [])])])), Term.$ (Term.$ (Term.Const ("Expressions.subst_expression", Term.Type ("fun", [Term.Type ("Expressions.substitution", []), Term.Type ("fun", [Term.Type ("Expressions.expression", [t_b]), Term.Type ("Expressions.expression", [t_b])])])), Term.$ (Term.$ (Term.Const ("Expressions.substitute1", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [t_a]), Term.Type ("fun", [Term.Type ("Expressions.expression", [t_a]), Term.Type ("Expressions.substitution", [])])])), x1), Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.unit", [])]), Term.Type ("fun", [Term.Type ("fun", [Term.Type ("Product_Type.unit", []), t_a]), Term.Type ("Expressions.expression", [t_a])])])), Term.Const ("Prog_Variables.variable_unit", Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.unit", [])]))), Term.Abs ("uu_", Term.Type ("Product_Type.unit", []), Term.Bound 1)))), B)), Term.$ (b, Term.Bound 0))))))
  ("z",t_a)
end 


end
;;
b |> Thm.cterm_of \<^context>
;;
certa ()
;;
certa () 
|> Thm.prop_of
(* |> Term.dest_comb |> snd *)
(* |> (fn (Abs(_,_,body)) => body) *)
|> Logic.dest_all |> snd
|> HOLogic.dest_Trueprop
|> Term.dest_comb |> snd
 (* |>Thm.cterm_of \<^context> *)
\<close>

ML \<open>
val ctxt = \<^context>
val t_b = @{typ "nat"}
val x1 = @{term "var_x1"}
val z = @{term "z::nat"}
val B = @{term "Expr[Suc x1]"}

(* Assumption: subst_expression (substitute1 ?x1.0 (const_expression ?z)) ?B = ?B'z
   Handled using function subst_expression_func *)

val (((b_z)), cert)
         = Test.subst_expression_func ctxt (Term.$ (Term.$ (Term.Const ("Expressions.substitute1", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [t_b]), Term.Type ("fun", [Term.Type ("Expressions.expression", [t_b]), Term.Type ("Expressions.substitution", [])])])), x1), Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.unit", [])]), Term.Type ("fun", [Term.Type ("fun", [Term.Type ("Product_Type.unit", []), t_b]), Term.Type ("Expressions.expression", [t_b])])])), Term.Const ("Prog_Variables.variable_unit", Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.unit", [])]))), Term.Abs ("uu_", Term.Type ("Product_Type.unit", []), z)))) (B) 
val B' = absfree ("z",@{typ int}) b_z
val thm = cert()
val prop = @{cprop "\<And>z. subst_expression (substitute1 var_x1 (const_expression z)) (expression \<lbrakk>var_x1\<rbrakk> (%x. Suc x)) = (\<lambda>z. const_expression (Suc z)) z"}
val thm' = thm |> Thm.generalize ([],["z"]) 0 |> Thm.forall_intr (Thm.cterm_of \<^context> (Var(("z",0),@{typ nat})))
val thm'' = rewrite_thm_as thm' prop
\<close>
end

(* ML \<open>
val _ = Theory.setup (ML_Antiquotation.declaration \<^binding>\<open>lemma_to_fun\<close>
(Scan.succeed()) (fn _ => fn _ => fn ctxt => (lemma_to_fun ctxt spec |> apfst K)))
\<close> *)

variables classical x :: bool and classical y :: bool begin
(* declare [[show_types,show_consts]] *)
ML \<open>
Test.index_vars \<^context> @{term True} @{term "\<lbrakk>var_x,var_y\<rbrakk>"} |> check_func
\<close>

ML \<open>
Test.wp \<^context> @{term "[assign var_x Expr[undefined]]"} @{term "[] :: program list"} @{term "Expr[top::predicate]"}
|> check_func
\<close>


ML \<open>
(* TODO should simplif the nested prod-case's *)
Test.subst_expression_func \<^context> @{term "substitute1 (var_x1::bool variable) (const_expression True)"}
@{term "Expr[Cla[x1=x2]]"}
|> check_func
\<close>
end


variables classical x :: int begin
ML \<open>
wp \<^context> @{term "[assign var_x Expr[x*x], assign var_x Expr[x*x]]"} @{term "[] :: program list"} @{term "Expr[Cla[x1=x2]]"}
|> check_func
\<close>
end



(* value "0 = (1::bit)"

typedef stuff = "UNIV :: nat set" by simp

locale stuff1
setup_lifting (in stuff1) type_definition_stuff

locale stuff2 begin
lemma type_definition_stuff': "type_definition (\<lambda>x. Rep_stuff x + 1) (\<lambda>x. Abs_stuff (x - 1)) {0<..}"
  apply (rule type_definition.intro)
  using Rep_stuff_inverse Abs_stuff_inverse by auto
setup_lifting type_definition_stuff'
end

lift_definition (in stuff1) all :: "stuff set" is UNIV .

lift_definition (in stuff2) all :: "stuff set" is "{0<..}" by simp
lemma (in stuff2) all: "all = stuff1.all"
  unfolding stuff1.all_def all_def apply auto
  using greaterThan_0 image_iff
  by fastforce
lemma (in stuff2) all_UNIV: "all = UNIV"
  unfolding all_def apply auto
  by (metis (no_types, lifting) Abs_stuff_cases diff_Suc_Suc diff_zero greaterThan_0 image_iff)


lemmas (in stuff2) [transfer_rule] = all.transfer[unfolded all]
lemmas (in stuff2) [transfer_rule] = all.transfer[unfolded all_UNIV]

save_transfer_rules stuff1
save_transfer_rules stuff2

lemma "card (UNIV :: stuff set) = 0"
  using [[transfer_import stuff1]]
  apply transfer
  by auto

lemma "stuff1.all = stuff2.all"
  using [[transfer_import stuff1]]
  using [[transfer_import stuff2]]
  apply transfer
  by simp
  
 *)


ML \<open>
type sorry_location = { position : Position.T, comment : string }
val sorry_table = Synchronized.var "sorry" (Inttab.empty : sorry_location Inttab.table)
\<close>

definition sorry_marker :: "int \<Rightarrow> prop \<Rightarrow> prop" where "sorry_marker n P == P"

ML \<open>
Proofterm.proofs := 1
\<close>


oracle sorry_marker_oracle = \<open>fn (ctxt, (loc:sorry_location), t) => let
  val ser = serial ()
  val _ = Synchronized.change sorry_table (Inttab.update (ser, loc))
  val t' = \<^const>\<open>sorry_marker\<close> $ HOLogic.mk_number \<^typ>\<open>int\<close> ser $ t
  val ct = Thm.cterm_of ctxt t'
  in
    ct
  end
\<close>

ML \<open>
fun marked_sorry ctxt loc t = 
  sorry_marker_oracle (ctxt,loc,t) |> Conv.fconv_rule (Conv.rewr_conv @{thm sorry_marker_def});;
(* val thm1 = marked_sorry @{context} {position= @{here}} @{prop "1==1"}
val thm2 = marked_sorry @{context} {position= @{here}} @{prop "1==1"}
val thm = Thm.transitive thm1 thm2 *)
\<close>


ML \<open>
fun marked_sorry_tac ctxt loc = SUBGOAL (fn (goal,i) => let
  val thm = marked_sorry ctxt loc goal
  in
    solve_tac ctxt [thm] i
  end
) 
\<close>


ML \<open>
fun show_oracles thm = let
  val known_oracles = thm |> Thm.theory_of_thm |> Proof_Context.init_global
                          |> Thm.extern_oracles false |> map (fn (m as (_,props),name) => 
                              (Properties.get props "name" |> the,
                               Markup.markup m name))
                          |> Symtab.make
  val oracles = thm |> Thm.proof_body_of |> Proofterm.all_oracles_of
  fun show ("Test.sorry_marker_oracle",t) = let
        val ser = case t of \<^const>\<open>sorry_marker\<close> $ n $ _ => HOLogic.dest_number n |> snd
                          | t => raise (TERM ("show_oracles", [t]))
        val loc = Inttab.lookup (Synchronized.value sorry_table) ser |> the
        val pos = #position loc
        val comment = #comment loc
      in "\n  cheat method: " ^ comment ^ Position.here pos  end
    | show (name,_) = "\n  " ^ (Symtab.lookup known_oracles name |> the)
  in
    "Oracles used in theorem:" :: (map show oracles) |> Output.writelns
  end
\<close>


method_setup cheat = \<open>Scan.lift (Parse.position Parse.text) >> (fn (txt,pos) => fn _ => CONTEXT_METHOD (fn _ => fn (ctxt, st) =>
    Method.CONTEXT ctxt (marked_sorry_tac ctxt {position=pos, comment=txt} 1 st)))\<close>

declare[[smt_oracle=true]]

lemma theo: "1=1"
  (* apply (rule trans[of _ 1]) *)
   (* apply (cheat 1) *)
  by smt

ML \<open>
val _ = show_oracles @{thm theo}
\<close>





(* 
ML \<open>
val (func,fut) = Active.dialog_text ()
val _ = func "hello" |> writeln
val _ = func "hullo" |> writeln
val _ = Future.join fut
\<close>
 *)

hide_const (open) Order.top Polynomial.order
hide_const (open) List_Fusion.generator.generator


(* 
lemma "hadamard\<guillemotright>\<lbrakk>q1\<rbrakk> \<cdot> Qeq[q1=q2] = hadamard\<guillemotright>\<lbrakk>q2\<rbrakk> \<cdot> Qeq[q1=q2]"
  apply (auto simp: prepare_for_code)
  apply eval
  done

 *)  
  
  
  
(* lemma "space_div (span{ket 0}\<guillemotright>\<lbrakk>q\<rbrakk>) (ket 1) \<lbrakk>r\<rbrakk> = span{ket 0}\<guillemotright>\<lbrakk>q\<rbrakk>"
  apply (auto simp: prepare_for_code)
  by eval

lemma "space_div (span{ket (0,0), ket(1,1)}\<guillemotright>\<lbrakk>q,r\<rbrakk>) (ket 0) \<lbrakk>r\<rbrakk> = span{ket 0}\<guillemotright>\<lbrakk>q\<rbrakk>"
  apply (auto simp: prepare_for_code)
  by eval
 *)

(* TODO move *)
setup_lifting type_definition_variable_raw
setup_lifting type_definition_variable
setup_lifting type_definition_mem2

(* thm type_definition_mem2
lemma type_definition_universe_class: 
  fixes embed
  defines "embed \<equiv> embedding::'a::universe\<Rightarrow>_"
  shows "type_definition embed (inv embed) (range embed)"
  apply (rule type_definition.intro)
  by (auto simp: embed_def)
setup_lifting type_definition_universe_class *)

lift_definition eval_variable :: "'a::universe variable \<Rightarrow> mem2 \<Rightarrow> 'a"
  is "\<lambda>v m. Hilbert_Choice.inv embedding (m v)" .
print_theorems

axiomatization eval_variables :: "'a variables \<Rightarrow> mem2 \<Rightarrow> 'a"

lemma eval_variables_unit: "eval_variables \<lbrakk>\<rbrakk> m = ()" sorry
lemma eval_variables_singleton: "eval_variables \<lbrakk>q\<rbrakk> m = eval_variable q m" sorry
lemma eval_variables_concat: "eval_variables (variable_concat Q R) m = (eval_variables Q m, eval_variables R m)" sorry


instantiation expression :: (ord) ord begin
definition "less_eq_expression e f \<longleftrightarrow> expression_eval e \<le> expression_eval f"
definition "less_expression e f \<longleftrightarrow> expression_eval e \<le> expression_eval f \<and> \<not> (expression_eval f \<le> expression_eval e)"
instance by intro_classes                   
end

axiomatization where expression_eval: "expression_eval (expression X e) m = e (eval_variables X m)"
  for X :: "'x variables" and e :: "'x \<Rightarrow> 'e" and m :: mem2

instantiation expression :: (preorder) preorder begin
instance apply intro_classes
  unfolding less_expression_def less_eq_expression_def 
  using order_trans by auto
end

(* ML {*
  fun subst_expression_simproc _ ctxt ct = SOME (Encoding.subst_expression_conv ctxt ct) handle CTERM _ => NONE
*} *)

(* simproc_setup subst_expression ("subst_expression (substitute1 x (expression R f')) (expression Q e')") = subst_expression_simproc *)



lemma qrhl_top: "qrhl A p1 p2 (expression Q (\<lambda>z. top))" sorry
lemma qrhl_top': "f \<ge> top \<Longrightarrow> qrhl A p1 p2 (expression Q f)" sorry

lemma skip:
  assumes "A \<le> B"
  shows "qrhl A [] [] B"
  sorry

ML \<open>
fun rename_tac_variant names = SUBGOAL (fn (goal,i) =>
  let val used = Term.add_free_names goal []
      val fresh = Name.variant_list used names
  in
    rename_tac fresh i
  end)
\<close>

method_setup rename_tac_eisbach = \<open>
  Args.term >> (fn name => fn ctxt => 
    case name of Free(name',_) => SIMPLE_METHOD' (rename_tac_variant [name'])
               | _ => (warning ("Could not convert "^Syntax.string_of_term ctxt name^" into a variable name. Not renaming."); Method.succeed)
    )\<close>

(* Converts a goal of the form "expression Q e \<le> expression R f :: 'a expression" 
   with Q,R explicit variable terms into "\<And>x1...xn. C x1...xn \<le> D x1...xn :: 'a" for some C,D. *)
method intro_expression_leq = 
  (rule less_eq_expression_def[THEN iffD2],
   rule le_fun_def[THEN iffD2],
   match conclusion in "\<forall>mem::mem2. C mem" for C \<Rightarrow>
      \<open>rule allI, rename_tac mem, 
       match conclusion in "C mem" for mem \<Rightarrow> 
         \<open>unfold expression_eval[where m=mem],
          (unfold eval_variables_concat[where m=mem] eval_variables_unit[where m=mem] eval_variables_singleton[where m=mem])?,
          (unfold case_prod_conv)?,
          ((match conclusion in "PROP (D (eval_variable v mem))" for D v \<Rightarrow> 
              \<open>rule meta_spec[where x="eval_variable v mem" and P=D], rename_tac_eisbach v\<close>)+)?
         \<close>
      \<close>
  )[1]

method print_goal = match conclusion in goal for goal \<Rightarrow> \<open>print_term goal\<close>

method skip = (rule skip, intro_expression_leq)

variables
  classical x :: int and
  classical a :: int and
  classical b :: int and 
  classical c :: int and
  quantum q :: int
begin

lemma
  assumes [simp]: "x\<ge>0"
  shows "qrhl D [s1,sample var_x Expr[uniform {0..max x 0}]] [t1,t2,assign var_x Expr[0]] Expr[Cla[x1\<ge>x2]]"
  using [[method_error,show_types]]
  apply (tactic \<open>Tactics.wp_tac \<^context> true 1\<close>)
  apply (tactic \<open>Tactics.wp_tac \<^context> false 1\<close>)
  apply simp
  by (rule qrhl_top)

lemma test:
  (* assumes "\<And>x y. e x \<le> e' x y" *)
  (* fixes z::"_::preorder" *)
  shows "Expr[z] \<le> Expr[z+0*a]"
  (* apply (insert assms)   *)
  apply intro_expression_leq 
  by auto

lemma
  assumes [simp]: "x\<ge>0"
  shows "qrhl Expr[ Cla[x1=0 \<and> x2=1] ] [qinit \<lbrakk>q\<rbrakk> Expr[ ket 0 ]] [assign var_x Expr[x-1]] Expr[Cla[x1\<ge>x2]]"
  using [[method_error]]
  apply (tactic \<open>Tactics.wp_tac \<^context> true 1\<close>) 
  apply (tactic \<open>Tactics.wp_tac \<^context> false 1\<close>)
  apply simp
  apply skip
  by simp

end

declare_variable_type G :: "{power,ab_semigroup_mult,inverse}"

axiomatization G::"G cyclic_group" and g::G

(* term "(^^)" *)
axiomatization powG :: "G \<Rightarrow> int \<Rightarrow> G" (infixr "\<^sup>^" 80)
(* locale group_G = cyclic_group G  *)
(* axiomatization where group_G: group_G *)
(* abbreviation "g == generator G" *)

thm cyclic_group.carrier_conv_generator

(* Add to CryptHOL? *)
lemma (in cyclic_group) "finite (carrier G)"
proof -
  from generator obtain n::nat where "\<^bold>g [^] n = inv \<^bold>g" 
    apply atomize_elim by (metis generatorE generator_closed inv_closed)
  then have g1: "\<^bold>g [^] (Suc n) = \<one>"
    by auto
  then have mod: "\<^bold>g [^] m = \<^bold>g [^] (m mod Suc n)" for m
  proof -
    obtain k where "m mod Suc n + Suc n * k = m" apply atomize_elim
      by (metis mod_less_eq_dividend mod_mod_trivial nat_mod_eq_lemma)
    then have "\<^bold>g [^] m = \<^bold>g [^] (m mod Suc n + Suc n * k)" by simp
    also have "\<dots> = \<^bold>g [^] (m mod Suc n)" 
      apply (subst nat_pow_mult[symmetric], rule)
      apply (subst nat_pow_pow[symmetric], rule)
      unfolding g1 by simp
    finally show ?thesis .
  qed
  have "range ((([^])::_\<Rightarrow>nat\<Rightarrow>_) \<^bold>g) \<subseteq> (([^]) \<^bold>g) ` {..<Suc n}"
  proof -
    have "\<^bold>g [^] x \<in> ([^]) \<^bold>g ` {..<Suc n}" for x::nat
      apply (subst mod) by auto
    then show ?thesis by auto
  qed
  then have "finite (range ((([^])::_\<Rightarrow>nat\<Rightarrow>_) \<^bold>g))"
    using finite_surj by auto
  with generator show "finite (carrier G)"
    using finite_subset by blast
qed

lemma (in cyclic_group) m_comm:
  assumes "x : carrier G" and "y : carrier G"
  shows "x \<otimes> y = y \<otimes> x"
proof -
  from generator assms obtain n m :: nat where x:"x=\<^bold>g [^] n" and y:"y=\<^bold>g [^] m" 
    apply atomize_elim by auto
  show ?thesis
    unfolding x y by (simp add: add.commute nat_pow_mult)
qed

interpretation G_group: cyclic_group G
  rewrites "x [^]\<^bsub>G\<^esub> n = x \<^sup>^ (n::int)" and "x \<otimes>\<^bsub>G\<^esub> y = x*y" and "\<one>\<^bsub>G\<^esub> = 1" and "generator G = g" 
    and "m_inv G = inverse" and "carrier G = UNIV"
  sorry


definition "keygen = uniform {(g \<^sup>^ x, x) | x::int. x\<in>{0..order G-1}}"
definition "enc h x = uniform {(g\<^sup>^r, h\<^sup>^r * x) | r::int. r\<in>{0..order G-1}}"
definition "dec x c = (let (c1,c2) = c in c2 * c1 \<^sup>^ (-x))"

lemma weight_enc: "weight (enc var_pk1 var_m1) = 1"
  unfolding enc_def
  apply (rule weight_uniform)
  by auto

lemma supp_enc: "supp (enc pk m) = {(g \<^sup>^ r, pk \<^sup>^ r * m) |r::int. r \<in> {0..order G-1}}"
  unfolding enc_def apply (rule supp_uniform) by auto
  (* find_theorems intro supp uniform *)

lemma weight_keygen: "weight keygen = 1"
  unfolding keygen_def
  apply (rule weight_uniform)
  by auto

lemma supp_keygen: "supp keygen = {(g \<^sup>^ x, x) |x::int. x \<in> {0..order G - 1}}"
  unfolding keygen_def apply (rule supp_uniform) by auto

lemma (in monoid) nat_pow_Suc_left: 
  assumes "x \<in> carrier G"
  shows "x [^] Suc n = x \<otimes> (x [^] n)"
  apply (induction n)
  using assms apply simp
  subgoal premises prems for n
    apply (subst nat_pow_Suc)
    apply (subst prems)
    apply (subst nat_pow_Suc)
    apply (subst m_assoc)
    using assms by auto
  done

lemma (in group) inv_nat_pow:
  assumes "x \<in> carrier G"
  shows "inv x [^] (n::nat) = inv (x [^] n)"
  apply (induction n) 
   apply simp
  apply (subst nat_pow_Suc)
  apply (subst nat_pow_Suc_left)
  using assms by (auto simp: inv_mult_group)

lemma (in group) inv_int_pow:
  assumes "x \<in> carrier G"
  shows "inv x [^] (n::int) = inv (x [^] n)"
  apply (cases n; hypsubst_thin)
   apply (subst int_pow_int)+
  using assms apply (rule inv_nat_pow)
  using assms apply (subst int_pow_neg, simp)+
  apply (subst int_pow_int)+
  by (subst inv_nat_pow, simp_all)


lemma (in cyclic_group) "(\<^bold>g [^] r) [^] -x = (\<^bold>g [^] (-r*x))" for r x :: int
  apply (subst int_pow_pow)
   apply (simp add: nat_pow_pow)
  by auto

(* lemma correct: "(g [^] x) [^] r \oti* m * (g \<^sup>^ r) \<^sup>^ -x = m"  *)

lemma correct: "(g \<^sup>^ x) \<^sup>^ r * m * (g \<^sup>^ r) \<^sup>^ -x = m" 
  apply (subst G_group.int_pow_pow) apply simp
  apply (subst G_group.int_pow_pow) apply simp
  apply (subst G_group.m_comm) 
    apply (auto simp: G_group.inv_int_pow )
  by (metis G_group.int_pow_neg G_group.inv_solve_left UNIV_I mult.commute)

variables classical c :: "G*G" and classical m :: G and classical pksk :: "G*int"
and classical pk :: G and classical sk :: int begin

definition "ElGamal = [sample var_pksk Expr[keygen],
           assign var_pk Expr[fst pksk],
           assign var_sk Expr[snd pksk],
           sample var_c Expr[enc pk m],
           assign var_m Expr[dec sk c]
          ]"

lemma elgamal_correct [simp]:
  fixes z
  shows "qrhl Expr[Cla[m1=z]] 
          ElGamal
         [] Expr[Cla[m1=z]]"
  unfolding ElGamal_def
  apply (tactic  \<open>Tactics.wp_tac \<^context> true 1\<close>)
  apply (simp add: dec_def)
  apply (tactic  \<open>Tactics.wp_tac \<^context> true 1\<close>)
  (* unfolding enc_def *)
  (* unfolding  *)
  apply (simp add: weight_enc supp_enc)
  apply (tactic  \<open>Tactics.wp_tac \<^context> true 1\<close>)
  apply (tactic  \<open>Tactics.wp_tac \<^context> true 1\<close>)
  apply (tactic  \<open>Tactics.wp_tac \<^context> true 1\<close>)
  apply (simp add: weight_keygen supp_keygen)
  apply skip
  by (auto simp: correct)

term "Pr[x:y(z)]"

lemma elgamal_correct2 [simp]:
  fixes z
  shows "qrhl Expr[Cla[m1=m2]] 
          ElGamal
         [] Expr[Cla[m1=m2]]"
  unfolding ElGamal_def
  apply (tactic  \<open>Tactics.wp_tac \<^context> true 1\<close>)
  apply (simp add: dec_def)
  apply (tactic  \<open>Tactics.wp_tac \<^context> true 1\<close>)
  (* unfolding enc_def *)
  (* unfolding  *)
  apply (simp add: weight_enc supp_enc)
  apply (tactic  \<open>Tactics.wp_tac \<^context> true 1\<close>)
  apply (tactic  \<open>Tactics.wp_tac \<^context> true 1\<close>)
  apply (tactic  \<open>Tactics.wp_tac \<^context> true 1\<close>)
  apply (simp add: weight_keygen supp_keygen)
  apply skip
  by (auto simp: correct)

end
