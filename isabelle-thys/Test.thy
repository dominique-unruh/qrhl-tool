theory Test
  imports 
 (* CryptHOL.Cyclic_Group QRHL.QRHL "HOL-Eisbach.Eisbach_Tools"  *)
(* Cert_Codegen *)
QRHL.QRHL QRHL.QRHL_Operations
Hashed_Terms Extended_Sorry
     (* QRHL.QRHL_Core  Multi_Transfer  *)
(* QRHL.Prog_Variables *)
(*   keywords
    "relift_definition" :: thy_goal
 *)
begin

variables classical c :: bit and quantum q :: bit begin
ML \<open>
local
fun p t = (@{print} (Thm.cterm_of \<^context> t); t)
val goal = @{term "qrhl (expression \<lbrakk>var_c1, var_c2\<rbrakk> (\<lambda>(c1, c2). \<CC>\<ll>\<aa>[c1 = c2] \<sqinter> \<lbrakk>q1\<rbrakk> \<equiv>\<qq> \<lbrakk>q2\<rbrakk>)) [measurement var_c \<lbrakk>q\<rbrakk> (const_expression computational_basis)] [measurement var_c \<lbrakk>q\<rbrakk> (const_expression computational_basis)] (expression \<lbrakk>var_c1, var_c2\<rbrakk> (\<lambda>(c1, c2). \<CC>\<ll>\<aa>[c1 = c2] \<sqinter> \<lbrakk>q1\<rbrakk> \<equiv>\<qq> \<lbrakk>q2\<rbrakk>))"}
val ctxt = \<^context>
val res = Tactics.tac_on_term_concl (Joint_Measure.joint_measure_simple_seq_tac ctxt 1) ctxt goal |> the |> the_single
val B = res |> dest_comb |> snd |> p
val res2 = Expressions.expression_to_term \<^context> B |> p
in
end
\<close>
lemma "qrhl (expression \<lbrakk>var_c1, var_c2\<rbrakk> (\<lambda>(c1, c2). \<CC>\<ll>\<aa>[c1 = c2] \<sqinter> \<lbrakk>q1\<rbrakk> \<equiv>\<qq> \<lbrakk>q2\<rbrakk>)) [measurement var_c \<lbrakk>q\<rbrakk> (const_expression computational_basis)] [measurement var_c \<lbrakk>q\<rbrakk> (const_expression computational_basis)] (expression \<lbrakk>var_c1, var_c2\<rbrakk> (\<lambda>(c1, c2). \<CC>\<ll>\<aa>[c1 = c2] \<sqinter> \<lbrakk>q1\<rbrakk> \<equiv>\<qq> \<lbrakk>q2\<rbrakk>))"
  apply (tactic \<open>Joint_Measure.joint_measure_simple_seq_tac \<^context> 1\<close>)
  oops
end


thm wp1_measure

term map_expression3

lemma index_expression_tac:
  assumes "Q1 = index_vars left Q"
  shows "(expression Q1 E) = index_expression left (expression Q E)"
  using assms index_expression_def by metis

lemma index_vars_unit_tac:
  shows "variable_unit = index_vars left variable_unit"
  using index_vars_unit by metis

lemma index_vars_singleton_tac:
  assumes "x1 = index_var left x"
  shows "variable_singleton x1 = index_vars left (variable_singleton x)"
  using assms index_vars_singleton by metis

lemma index_vars_concat_tac:
  assumes "Y1 = index_vars left Y"
  assumes "Z1 = index_vars left Z"
  shows "variable_concat Y1 Z1 = index_vars left (variable_concat Y Z)"
  using assms index_vars_concat by metis

lemma map_expression3'_tac:
  shows "expression (variable_concat Q1 (variable_concat Q2 Q3)) (\<lambda>(x1,x2,x3). f (e1 x1) (e2 x2) (\<lambda>z. e3 z x3))
   = map_expression3' f (expression Q1 e1) (expression Q2 e2) (\<lambda>z. expression Q3 (e3 z))"
  using map_expression3' by metis

ML \<open>
fun print_conv ct = (\<^print> ct; Conv.all_conv ct)
\<close>

ML \<open>
(* Subgoals of the form ?x = index_var True/False x *)
fun index_var_tac ctxt = 
  CONVERSION (Conv.arg_conv (Conv.arg_conv (Prog_Variables.index_var_conv ctxt)))
  THEN'
  SUBGOAL (fn (t,i) =>
    case t of Const(\<^const_name>\<open>Trueprop\<close>,_) $ (Const(\<^const_name>\<open>HOL.eq\<close>,_) $ _ $ Free _) => resolve_tac ctxt @{thms refl} i
            | _ => raise TERM("index_var_tac",[t]))
\<close>

ML \<open>
\<close>


ML \<open>
(* Subgoals of the form ?x = index_vars True/False vs
   where vs is an explicit varterm *)
fun index_vars_tac ctxt = SUBGOAL (fn (t,i) =>
  case t of Const(\<^const_name>\<open>Trueprop\<close>,_) $ 
        (Const(\<^const_name>\<open>HOL.eq\<close>,_) $ _ $ (Const(\<^const_name>\<open>index_vars\<close>,_) $ _ $ vars)) =>
    (case vars of Const(\<^const_name>\<open>variable_unit\<close>, _) => 
                    resolve_tac ctxt @{thms index_vars_unit_tac} i
                | Const(\<^const_name>\<open>variable_singleton\<close>, _) $ _ => 
                    resolve_tac ctxt @{thms index_vars_singleton_tac} i
                    THEN index_var_tac ctxt i
                | Const(\<^const_name>\<open>variable_concat\<close>, _) $ _ $ _ => 
                    resolve_tac ctxt @{thms index_vars_concat_tac} i
                    THEN index_vars_tac ctxt i THEN index_vars_tac ctxt i
                | _ => raise TERM("index_vars_tac: not a varterm",[t,vars]))
  | _ => raise TERM("index_vars_tac",[t]))
\<close>

ML \<open>
(* Subgoals of the form ?x = index_expression True/False e
   where e is an explicit expression *)
fun index_expression_tac ctxt = 
  resolve_tac ctxt @{thms index_expression_tac}
  THEN' index_vars_tac ctxt
\<close>

ML \<open>
fun print_tac_n ctxt msg = SUBGOAL (fn (t,i) =>
 (tracing (msg ^ Position.here \<^here> ^ "\n" ^ Syntax.string_of_term ctxt t); all_tac))
\<close>



ML \<open>
\<close>

ML \<open>
\<close>

ML \<open>
\<close>


variables classical x :: "int*int" and classical y :: "int*int" and quantum q :: "int*int" and quantum r :: "int" and quantum s :: int begin
schematic_goal 
  shows "qrhl ?A [measurement var_x \<lbrakk>q\<rbrakk> Expr[computational_basis]]  [measurement var_y \<lbrakk>r,s\<rbrakk> Expr[computational_basis]] Expr[Cla[x1=y2]] \<and> undefined ?A"
  apply rule
  apply (tactic \<open>joint_measure_simple_tac \<^context> 1\<close>)


  sorry (* TODO *)

ML \<open>
;;
Hashed_Terms.hash_term \<^term>\<open>%x. x+2\<close>
\<close>

ML \<open>
;;
Hashed_Terms.hash_and_store_term \<^term>\<open>%x. 2+x+2*2\<close> |> \<^print>
;;
Hashed_Terms.hash_and_store_term \<^term>\<open>%x. 2*3\<close> |> \<^print>
\<close>


ML \<open>
1000*1000*1000*1000*1000*1000*1000*1000*1000*1000*1000*1000*1000*1000*1000*1000*1000*1000
\<close>


ML \<open>
fun check_func (t,cert) = let
  val thm = cert ()
  (* val _ = if Thm.term_of (Thm.rhs_of thm) <> t then raise TERM("check_func",[Thm.prop_of thm, t]) else () *)
  in (Thm.global_cterm_of (Thm.theory_of_thm thm) t, thm) end
\<close>


ML \<open>
Cert_Codegen.list_last \<^context> \<^term>\<open>[1,2,3]\<close>
|> (fn ((x,x'),y) => (Thm.cterm_of \<^context> x, Thm.cterm_of \<^context> x', y ()))
\<close>

(* ML \<open>
val t = \<^term>\<open>\<CC>\<ll>\<aa>[uniform UNIV = uniform UNIV] \<sqinter> (\<Sqinter>z\<in>supp (uniform UNIV). (\<Sqinter>m12 m11. \<CC>\<ll>\<aa>[m11 \<noteq> m12] + (\<CC>\<ll>\<aa>[\<not> True] + \<top>) \<sqinter> \<CC>\<ll>\<aa>[enc (z, m11) = G z + m12 \<and> b1 = b2]) \<sqinter> \<CC>\<ll>\<aa>[m11 = m12 \<and> m21 = m22 \<and> cglobA1 = cglobA2] \<sqinter> \<lbrakk>qglobA1\<rbrakk> \<equiv>\<qq> \<lbrakk>qglobA2\<rbrakk>)\<close>
val _ = Autogen_WP.wp \<^context> 
\<close> *)



variables classical x :: int begin
ML \<open>
Autogen_WP.wp1_tac \<^context> \<^term>\<open>False\<close>
\<^term>\<open>qrhl Expr[Cla[False]] [assign var_x Expr[1], assign var_x Expr[2]]
[assign var_x Expr[1], assign var_x Expr[2]] Expr[Cla[True]]\<close>
|> snd |> (fn x => x())
\<close>
end


(* eta_proc bug *)
lemma "(\<lambda>(i, b, s). t (i, b, s)) == x"
  apply simp (* Becomes t = x *)
  oops
schematic_goal x: " (\<lambda>(i, b, s). ?t (i, b, s)) = xxx"
  (* apply simp *)
  oops


ML \<open>
fun test_wp ctxt c d B = let
  val (A,cert) = Autogen_WP.wp ctxt c d B
  val thm = cert ()
  val prop = Thm.prop_of thm |> HOLogic.dest_Trueprop
  val Const(\<^const_name>\<open>qrhl\<close>,_) $ A' $ c' $ d' $ B' = prop
  fun err s t t' = raise CTERM("test_wp: "^s,[Thm.cterm_of ctxt t,Thm.cterm_of ctxt t'])
  val _ = if c' = c then () else err "c" c c'
  val _ = if d' = d then () else err "d" d d'
  val _ = if B' = B then () else err "B" B B'
  val _ = if Envir.beta_norm A' = Envir.beta_norm A then () else err "A" A A'
in Thm.global_cterm_of (Thm.theory_of_thm thm) A end
\<close>


variables classical x :: int and classical y :: int and classical u :: unit and quantum q :: int and classical b :: bool begin
ML \<open>
  test_wp \<^context> \<^term>\<open>[ifthenelse Expr[b] [assign var_b Expr[\<not>b], assign var_b Expr[\<not>b]] [] ]\<close> \<^term>\<open>[]::program list\<close>   @{term "Expr[Cla[b1]]"}
     |> Simplifier.rewrite \<^context> |> Thm.rhs_of
\<close>
ML \<open>
  test_wp \<^context> \<^term>\<open>[]::program list\<close> @{term "[measurement var_x \<lbrakk>q\<rbrakk> Expr[computational_basis]]"} @{term "Expr[Cla[x2=x1]]"}
\<close>
ML \<open>
  test_wp \<^context> @{term "[measurement var_x \<lbrakk>q\<rbrakk> Expr[computational_basis]]"} @{term "[] :: program list"} @{term "Expr[Cla[x2=x1]]"}
\<close>
ML \<open>
  test_wp \<^context> @{term "[sample var_x Expr[uniform {y<..<x}]]"} @{term "[] :: program list"} @{term "Expr[Cla[x1=x2]]"}
\<close>
ML \<open>
  test_wp \<^context> @{term "[qapply \<lbrakk>q\<rbrakk> Expr[undefined]]"} @{term "[] :: program list"} @{term "Expr[top \<guillemotright> \<lbrakk>q\<rbrakk>]"}
\<close>
ML \<open>
Autogen_Cleanup_Expression_Concat.cleanup_expression_concat \<^context> \<^term>\<open>variable_unit\<close> \<^term>\<open>variable_unit\<close> \<^term>\<open>\<lambda>(x1::unit, x2::unit). ()\<close>
|> check_func
\<close>
ML \<open>
cleanup_expression_function \<^context> \<^term>\<open>variable_unit\<close> \<^term>\<open>undefined :: unit\<Rightarrow>unit\<close>
|> check_func
\<close>
end

declare[[show_abbrevs=false,eta_contract=false]]

text nothing



ML \<open>open Cert_Codegen\<close>

ML \<open>
;;
(* get_variable_name \<^context> @{term var_xxx} *)
\<close>

(* (* TODO remove *)
lemma func: (* TODO remove *)
  assumes "e1 == expression Q1 E1"
  assumes "\<And>z. e2 z == expression (Q2 z) (E2 z)"
  assumes "expression (variable_concat Q1 (Q2 undefined)) (\<lambda>(x1,x2). f (E1 x1) (\<lambda>z. E2 z x2)) \<equiv> e'"
  (* assumes "undefined \<equiv> e'" *)
  shows "map_expression2' f e1 e2 = e'"
  sorry 



ML \<open>
val func_spec : specfx = {
  name="func", pattern=\<^prop>\<open>map_expression2' f e1 e2 = e'\<close> |> free_to_var,
  inputs=["f","e1","e2"], outputs=["e'"],
  thms=["func"], fallback="fn (f,e1,e2) => raise TERM(\"func\",[f,e1,e2])"} \<close>

ML \<open>
val code = thms_to_funs \<^context> [func_spec] "Test" "test0.ML"
\<close>
ML\<open>fun prt t = (@{print} (Thm.cterm_of \<^context> t); ())
\<close>

ML_file "test0.ML"


ML \<open>
local
val t = @{term "map_expression2' f (const_expression ()) (%_. const_expression ())"}
val (Const _ $ f $ e1 $ e2) = t
in
val res = Test.func \<^context> f e1 e2 |> check_func
end
\<close>                                                      

(* END remove *)
 *)

ML \<open>
@{ml_term "string_concat_func a b c"}
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




ML \<open>
\<close>

declare[[show_types]]

ML \<open>
constant_function \<^context> @{term "%z::nat. 1+(2::int)"} |> check_func
\<close>


variables classical x :: int begin
ML \<open>
index_var_func \<^context> @{term False} @{term "var_x"} |> check_func
\<close>
end





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


ML ML_File.ML
ML Toplevel.generic_theory

(* ML_file "test_index_vars.ML" *)
(* ML "open Index_Vars" *)

(* ML_file "test_index_expression.ML" *)
(* ML "open Index_Expression" *)

(* ML_file "test_map_expression.ML" *)
(* ML "open Map_Expression" *)

(* ML_file "test_subst_expression.ML" *)
(* ML "open Subst_Expression" *)


(* ML \<open>                           
val _ = thms_to_fun \<^context> spec map_expression2'_func_spec
|> (fn c => "fun " ^ c)
|> (fn c => (tracing c; c))
|> (fn c => ML_Context.eval ML_Compiler.flags Position.none (ML_Lex.read_pos Position.none c))
\<close> 


ML \<open>
local
val t = @{term "map_expression2' f (const_expression ()) (%_. const_expression ())"}
in
val (Const _ $ f $ e1 $ e2) = t
val _ =
map_expression2' \<^context> f e1 e2
end
\<close>                                                      
*)





(* ML \<open>
(* TODO make work *)
thm_to_fun \<^context> (empty_conf (hd spec)) spec "wp1_sample_func" "f" ["c","d","B"] ["A"] |> writeln
\<close>
 

ML \<open>
;;
val _ = thms_to_fun \<^context> spec spec_wp |> tracing
\<close>
*)

(* ML_file "test_wp.ML" *)
(* ML "open WP" *)





(* ML \<open>
val _ = Theory.setup (ML_Antiquotation.declaration \<^binding>\<open>lemma_to_fun\<close>
(Scan.succeed()) (fn _ => fn _ => fn ctxt => (lemma_to_fun ctxt spec |> apfst K)))
\<close> *)

variables classical x :: bool and classical y :: bool begin
(* declare [[show_types,show_consts]] *)
ML \<open>
Autogen_Index_Vars.index_vars \<^context> @{term True} @{term "\<lbrakk>var_x,var_y\<rbrakk>"} |> check_func
\<close>

(* ML \<open>
fun check_func1 pattern [input] (t,cert) = let
  val thm = cert ()
  val thy = Thm.theory_of_thm thm
  val pattern = free_to_var pattern
  val (_,tenv) = Pattern.first_order_match thy (pattern,Thm.prop_of thm) (Vartab.empty,Vartab.empty)
  val _ = if input aconv (Vartab.lookup tenv ("input",0) |> the |> snd) then () else error "mismatch"
  in (Thm.global_cterm_of thy t) end
  | check_func1  _ _ _ = error "meh"
\<close> *)



ML \<open>
(* TODO should simplif the nested prod-case's *)
Autogen_Subst_Expression.subst_expression_func \<^context> @{term "substitute1 (var_x1::bool variable) (const_expression True)"}
@{term "Expr[Cla[x1=x2]]"}
|> check_func
\<close>
end


variables classical x :: int begin
ML \<open>
Autogen_WP.wp \<^context> @{term "[assign var_x Expr[x*x], assign var_x Expr[x*x]]"} @{term "[] :: program list"} @{term "Expr[Cla[x1=x2]]"}
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
(* fun marked_sorry ctxt loc t = 
  sorry_marker_oracle (ctxt,loc,t) |> Conv.fconv_rule (Conv.rewr_conv @{thm sorry_marker_def});;
 *)(* val thm1 = marked_sorry @{context} {position= @{here}} @{prop "1==1"}
val thm2 = marked_sorry @{context} {position= @{here}} @{prop "1==1"}
val thm = Thm.transitive thm1 thm2 *)
\<close>


ML \<open>
(* fun marked_sorry_tac ctxt loc = SUBGOAL (fn (goal,i) => let
  val thm = marked_sorry ctxt loc goal
  in
    solve_tac ctxt [thm] i
  end
) 
 *)\<close>



declare[[smt_oracle=true]]

lemma theo: "1=1"
  (* apply (rule trans[of _ 1]) *)
   (* apply (cheat 1) *)
  by smt

ML \<open>
Extended_Sorry.show_oracles_lines @{thm theo}
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

consts eval_variables :: "'a variables \<Rightarrow> mem2 \<Rightarrow> 'a"

lemma eval_variables_unit: "eval_variables \<lbrakk>\<rbrakk> m = ()" sorry
lemma eval_variables_singleton: "eval_variables \<lbrakk>q\<rbrakk> m = eval_variable q m" sorry
lemma eval_variables_concat: "eval_variables (variable_concat Q R) m = (eval_variables Q m, eval_variables R m)" sorry


instantiation expression :: (ord) ord begin
definition "less_eq_expression e f \<longleftrightarrow> expression_eval e \<le> expression_eval f"
definition "less_expression e f \<longleftrightarrow> expression_eval e \<le> expression_eval f \<and> \<not> (expression_eval f \<le> expression_eval e)"
instance by intro_classes                   
end

(* lemma expression_eval: "expression_eval (expression X e) m = e (eval_variables X m)"
  for X :: "'x variables" and e :: "'x \<Rightarrow> 'e" and m :: mem2
 *)

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

consts G::"G cyclic_group" and g::G

(* term "(^^)" *)
consts powG :: "G \<Rightarrow> int \<Rightarrow> G" (infixr "\<^sup>^" 80)
(* locale group_G = cyclic_group G  *)
(* lemma group_G: group_G *)
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
