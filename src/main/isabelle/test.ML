structure Test =
struct

fun wp ctxt c d b = let
  (* wp_skip_func: ?c \<equiv> [] \<Longrightarrow> ?d \<equiv> [] \<Longrightarrow> ?B \<equiv> ?A \<Longrightarrow> qrhl ?A ?c ?d ?B *)
  fun wp_skip_func ca da ba = let
    val Term.Type ("List.list", [Term.Type ("Encoding.program", [])]) = fastype_of ca
    val Term.Type ("List.list", [Term.Type ("Encoding.program", [])]) = fastype_of da
    val Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]) = fastype_of ba
    (* Assumption: ?c \<equiv> []
       Handled using pattern matching *)
    val Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])])) = ca
    (* Assumption: ?d \<equiv> []
       Handled using pattern matching *)
    val Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])])) = da
    (* Assumption: ?B \<equiv> ?A
       Handled using pattern matching *)
    val a = ba
    fun mkcert () = Cert_Codegen.implies_elim_multi_beta (infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [ca, da, ba, a]) @{thm "wp_skip_func"}) [infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])]))) |> SOME] reflexive_thm, infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])]))) |> SOME] reflexive_thm, infer_instantiate' ctxt [Thm.cterm_of ctxt (a) |> SOME] reflexive_thm]
  in (a, mkcert) end
  
  (* wp1_assign_func: ?c \<equiv> [assign ?x ?e] \<Longrightarrow> ?d \<equiv> [] \<Longrightarrow> index_var True ?x = ?x1.0 \<Longrightarrow> index_expression True ?e = ?e1.0 \<Longrightarrow> subst_expression (substitute1 ?x1.0 ?e1.0) ?B = ?A \<Longrightarrow> qrhl ?A ?c ?d ?B *)
  fun wp1_assign_func ca da ba = let
    val Term.Type ("List.list", [Term.Type ("Encoding.program", [])]) = fastype_of ca
    val Term.Type ("List.list", [Term.Type ("Encoding.program", [])]) = fastype_of da
    val Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]) = fastype_of ba
    (* Assumption: ?c \<equiv> [assign ?x ?e]
       Handled using pattern matching *)
    val Term.$ (Term.$ (Term.Const ("List.list.Cons", Term.Type ("fun", [Term.Type ("Encoding.program", []), Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("List.list", [Term.Type ("Encoding.program", [])])])])), Term.$ (Term.$ (Term.Const ("Encoding.assign", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("fun", [Term.Type ("Expressions.expression", [x_aa]), Term.Type ("Encoding.program", [])])])), x), e)), Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])]))) = ca
    val _ = if (x_aa=x_a) then () else raise Bind
    (* Assumption: ?d \<equiv> []
       Handled using pattern matching *)
    val Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])])) = da
    (* Assumption: index_var True ?x = ?x1.0
       Handled using function index_var_func *)
    val (((x1)), cert)
             = index_var_func ctxt (Term.Const ("HOL.True", Term.Type ("HOL.bool", []))) (x)
    (* Assumption: index_expression True ?e = ?e1.0
       Handled using function index_expression_func *)
    val (((e1)), certa)
             = index_expression_func ctxt (Term.Const ("HOL.True", Term.Type ("HOL.bool", []))) (e)
    (* Assumption: subst_expression (substitute1 ?x1.0 ?e1.0) ?B = ?A
       Handled using function subst_expression_func *)
    val (((a)), certb)
             = subst_expression_func ctxt (Term.$ (Term.$ (Term.Const ("Expressions.substitute1", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("fun", [Term.Type ("Expressions.expression", [x_a]), Term.Type ("Expressions.substitution", [])])])), x1), e1)) (ba)
    fun mkcert () = Cert_Codegen.implies_elim_multi_beta (infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [ca, x, e, da, x1, e1, ba, a]) @{thm "wp1_assign_func"}) [infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.$ (Term.$ (Term.Const ("List.list.Cons", Term.Type ("fun", [Term.Type ("Encoding.program", []), Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("List.list", [Term.Type ("Encoding.program", [])])])])), Term.$ (Term.$ (Term.Const ("Encoding.assign", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("fun", [Term.Type ("Expressions.expression", [x_aa]), Term.Type ("Encoding.program", [])])])), x), e)), Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])])))) |> SOME] reflexive_thm, infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])]))) |> SOME] reflexive_thm, cert (), certa (), certb ()]
  in (a, mkcert) end
  
  (* wp2_assign_func: ?d \<equiv> [assign ?x ?e] \<Longrightarrow> ?c \<equiv> [] \<Longrightarrow> index_var False ?x = ?x1.0 \<Longrightarrow> index_expression False ?e = ?e1.0 \<Longrightarrow> subst_expression (substitute1 ?x1.0 ?e1.0) ?B = ?A \<Longrightarrow> qrhl ?A ?c ?d ?B *)
  fun wp2_assign_func ca da ba = let
    val Term.Type ("List.list", [Term.Type ("Encoding.program", [])]) = fastype_of ca
    val Term.Type ("List.list", [Term.Type ("Encoding.program", [])]) = fastype_of da
    val Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]) = fastype_of ba
    (* Assumption: ?d \<equiv> [assign ?x ?e]
       Handled using pattern matching *)
    val Term.$ (Term.$ (Term.Const ("List.list.Cons", Term.Type ("fun", [Term.Type ("Encoding.program", []), Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("List.list", [Term.Type ("Encoding.program", [])])])])), Term.$ (Term.$ (Term.Const ("Encoding.assign", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("fun", [Term.Type ("Expressions.expression", [x_aa]), Term.Type ("Encoding.program", [])])])), x), e)), Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])]))) = da
    val _ = if (x_aa=x_a) then () else raise Bind
    (* Assumption: ?c \<equiv> []
       Handled using pattern matching *)
    val Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])])) = ca
    (* Assumption: index_var False ?x = ?x1.0
       Handled using function index_var_func *)
    val (((x1)), cert)
             = index_var_func ctxt (Term.Const ("HOL.False", Term.Type ("HOL.bool", []))) (x)
    (* Assumption: index_expression False ?e = ?e1.0
       Handled using function index_expression_func *)
    val (((e1)), certa)
             = index_expression_func ctxt (Term.Const ("HOL.False", Term.Type ("HOL.bool", []))) (e)
    (* Assumption: subst_expression (substitute1 ?x1.0 ?e1.0) ?B = ?A
       Handled using function subst_expression_func *)
    val (((a)), certb)
             = subst_expression_func ctxt (Term.$ (Term.$ (Term.Const ("Expressions.substitute1", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("fun", [Term.Type ("Expressions.expression", [x_a]), Term.Type ("Expressions.substitution", [])])])), x1), e1)) (ba)
    fun mkcert () = Cert_Codegen.implies_elim_multi_beta (infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [da, x, e, ca, x1, e1, ba, a]) @{thm "wp2_assign_func"}) [infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.$ (Term.$ (Term.Const ("List.list.Cons", Term.Type ("fun", [Term.Type ("Encoding.program", []), Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("List.list", [Term.Type ("Encoding.program", [])])])])), Term.$ (Term.$ (Term.Const ("Encoding.assign", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("fun", [Term.Type ("Expressions.expression", [x_aa]), Term.Type ("Encoding.program", [])])])), x), e)), Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])])))) |> SOME] reflexive_thm, infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])]))) |> SOME] reflexive_thm, cert (), certa (), certb ()]
  in (a, mkcert) end
  
  (* wp1_sample_func: ?d \<equiv> [] \<Longrightarrow> ?c \<equiv> [sample ?x ?e] \<Longrightarrow> index_var True ?x = ?x1.0 \<Longrightarrow> index_expression True ?e = ?e1.0 \<Longrightarrow> (\<And>z. subst_expression (substitute1 ?x1.0 (const_expression z)) ?B = ?B' z) \<Longrightarrow> map_expression2' (\<lambda>e' B'. \<CC>\<ll>\<aa>[weight e' = 1] \<sqinter> (\<Sqinter>z\<in>supp e'. B' z)) ?e1.0 ?B' = ?A \<Longrightarrow> qrhl ?A ?c ?d ?B *)
  fun wp1_sample_func ca da ba = let
    val Term.Type ("List.list", [Term.Type ("Encoding.program", [])]) = fastype_of ca
    val Term.Type ("List.list", [Term.Type ("Encoding.program", [])]) = fastype_of da
    val Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]) = fastype_of ba
    (* Assumption: ?d \<equiv> []
       Handled using pattern matching *)
    val Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])])) = da
    (* Assumption: ?c \<equiv> [sample ?x ?e]
       Handled using pattern matching *)
    val Term.$ (Term.$ (Term.Const ("List.list.Cons", Term.Type ("fun", [Term.Type ("Encoding.program", []), Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("List.list", [Term.Type ("Encoding.program", [])])])])), Term.$ (Term.$ (Term.Const ("Encoding.sample", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("Discrete_Distributions.distr", [x_aa])]), Term.Type ("Encoding.program", [])])])), x), e)), Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])]))) = ca
    val _ = if (x_aa=x_a) then () else raise Bind
    (* Assumption: index_var True ?x = ?x1.0
       Handled using function index_var_func *)
    val (((x1)), cert)
             = index_var_func ctxt (Term.Const ("HOL.True", Term.Type ("HOL.bool", []))) (x)
    (* Assumption: index_expression True ?e = ?e1.0
       Handled using function index_expression_func *)
    val (((e1)), certa)
             = index_expression_func ctxt (Term.Const ("HOL.True", Term.Type ("HOL.bool", []))) (e)
    val z = Free("z_" ^ serial_string(), x_a)
    val b_z = betapply (ba,z)
    val x1_z = betapply (x1,z)
    (* Assumption: subst_expression (substitute1 ?x1.0 (const_expression ?z)) ?B = ?B'_z
       Handled using function subst_expression_func *)
    val (((b_za)), certb)
             = subst_expression_func ctxt (Term.$ (Term.$ (Term.Const ("Expressions.substitute1", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("fun", [Term.Type ("Expressions.expression", [x_a]), Term.Type ("Expressions.substitution", [])])])), x1), Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.unit", [])]), Term.Type ("fun", [Term.Type ("fun", [Term.Type ("Product_Type.unit", []), x_a]), Term.Type ("Expressions.expression", [x_a])])])), Term.Const ("Prog_Variables.variable_unit", Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.unit", [])]))), Term.Abs ("uu_", Term.Type ("Product_Type.unit", []), z)))) (ba)
    (* Assumption: \<And>z. subst_expression (substitute1 ?x1.0 (const_expression z)) ?B = ?B' z
       Handled by stripping all-quantifier *)
    val bb = Cert_Codegen.absfree' "z" (dest_Free z) b_za
    fun certc () = Cert_Codegen.generalize_thm_to ctxt (certb ()) (dest_Free z)
                   (Term.$ (Term.Const ("Pure.all", Term.Type ("fun", [Term.Type ("fun", [x_a, Term.Type ("prop", [])]), Term.Type ("prop", [])])), Term.Abs ("z", x_a, Term.$ (Term.Const ("HOL.Trueprop", Term.Type ("fun", [Term.Type ("HOL.bool", []), Term.Type ("prop", [])])), Term.$ (Term.$ (Term.Const ("HOL.eq", Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]), Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]), Term.Type ("HOL.bool", [])])])), Term.$ (Term.$ (Term.Const ("Expressions.subst_expression", Term.Type ("fun", [Term.Type ("Expressions.substitution", []), Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]), Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])])), Term.$ (Term.$ (Term.Const ("Expressions.substitute1", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("fun", [Term.Type ("Expressions.expression", [x_a]), Term.Type ("Expressions.substitution", [])])])), x1), Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.unit", [])]), Term.Type ("fun", [Term.Type ("fun", [Term.Type ("Product_Type.unit", []), x_a]), Term.Type ("Expressions.expression", [x_a])])])), Term.Const ("Prog_Variables.variable_unit", Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.unit", [])]))), Term.Abs ("uu_", Term.Type ("Product_Type.unit", []), Term.Bound 1)))), ba)), Term.$ (bb, Term.Bound 0))))))
    (* Assumption: map_expression2' (\<lambda>e' B'. \<CC>\<ll>\<aa>[weight e' = 1] \<sqinter> (\<Sqinter>z\<in>supp e'. B' z)) ?e1.0 ?B' = ?A
       Handled using function map_expression2' *)
    val (((a)), certd)
             = map_expression2' ctxt (Term.Abs ("e'", Term.Type ("Discrete_Distributions.distr", [x_a]), Term.Abs ("B'", Term.Type ("fun", [x_a, Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]), Term.$ (Term.$ (Term.Const ("Lattices.inf_class.inf", Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])), Term.$ (Term.Const ("QRHL_Core.classical_subspace", Term.Type ("fun", [Term.Type ("HOL.bool", []), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])), Term.$ (Term.$ (Term.Const ("HOL.eq", Term.Type ("fun", [Term.Type ("Real.real", []), Term.Type ("fun", [Term.Type ("Real.real", []), Term.Type ("HOL.bool", [])])])), Term.$ (Term.Const ("Discrete_Distributions.weight", Term.Type ("fun", [Term.Type ("Discrete_Distributions.distr", [x_a]), Term.Type ("Real.real", [])])), Term.Bound 1)), Term.Const ("Groups.one_class.one", Term.Type ("Real.real", []))))), Term.$ (Term.Const ("Complete_Lattices.Inf_class.Inf", Term.Type ("fun", [Term.Type ("Set.set", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])), Term.$ (Term.$ (Term.Const ("Set.image", Term.Type ("fun", [Term.Type ("fun", [x_a, Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]), Term.Type ("fun", [Term.Type ("Set.set", [x_a]), Term.Type ("Set.set", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])])), Term.Abs ("z", x_a, Term.$ (Term.Bound 1, Term.Bound 0))), Term.$ (Term.Const ("Discrete_Distributions.supp", Term.Type ("fun", [Term.Type ("Discrete_Distributions.distr", [x_a]), Term.Type ("Set.set", [x_a])])), Term.Bound 1))))))) (e1) (bb)
    fun mkcert () = Cert_Codegen.implies_elim_multi_beta (infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [da, ca, x, e, x1, e1, ba, bb, a]) @{thm "wp1_sample_func"}) [infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])]))) |> SOME] reflexive_thm, infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.$ (Term.$ (Term.Const ("List.list.Cons", Term.Type ("fun", [Term.Type ("Encoding.program", []), Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("List.list", [Term.Type ("Encoding.program", [])])])])), Term.$ (Term.$ (Term.Const ("Encoding.sample", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("Discrete_Distributions.distr", [x_aa])]), Term.Type ("Encoding.program", [])])])), x), e)), Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])])))) |> SOME] reflexive_thm, cert (), certa (), certc (), certd ()]
  in (a, mkcert) end
  
  (* wp2_sample_func: ?c \<equiv> [] \<Longrightarrow> ?d \<equiv> [sample ?x ?e] \<Longrightarrow> map_expression2' (\<lambda>e' B'. \<CC>\<ll>\<aa>[weight e' = 1] \<sqinter> (\<Sqinter>z\<in>supp e'. B' z)) (index_expression False ?e) (\<lambda>z. subst_expression (substitute1 (index_var False ?x) (const_expression z)) ?B) \<equiv> ?A \<Longrightarrow> qrhl ?A ?c ?d ?B *)
  fun wp2_sample_func ca da ba = let
    val Term.Type ("List.list", [Term.Type ("Encoding.program", [])]) = fastype_of ca
    val Term.Type ("List.list", [Term.Type ("Encoding.program", [])]) = fastype_of da
    val Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]) = fastype_of ba
    (* Assumption: ?c \<equiv> []
       Handled using pattern matching *)
    val Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])])) = ca
    (* Assumption: ?d \<equiv> [sample ?x ?e]
       Handled using pattern matching *)
    val Term.$ (Term.$ (Term.Const ("List.list.Cons", Term.Type ("fun", [Term.Type ("Encoding.program", []), Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("List.list", [Term.Type ("Encoding.program", [])])])])), Term.$ (Term.$ (Term.Const ("Encoding.sample", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("Discrete_Distributions.distr", [x_aa])]), Term.Type ("Encoding.program", [])])])), x), e)), Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])]))) = da
    val _ = if (x_aa=x_a) then () else raise Bind
    (* Assumption: map_expression2' (\<lambda>e' B'. \<CC>\<ll>\<aa>[weight e' = 1] \<sqinter> (\<Sqinter>z\<in>supp e'. B' z)) (index_expression False ?e) (\<lambda>z. subst_expression (substitute1 (index_var False ?x) (const_expression z)) ?B) \<equiv> ?A
       Handled using pattern matching *)
    val a = Term.$ (Term.$ (Term.$ (Term.Const ("Expressions.map_expression2'", Term.Type ("fun", [Term.Type ("fun", [Term.Type ("Discrete_Distributions.distr", [x_a]), Term.Type ("fun", [Term.Type ("fun", [x_a, Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])]), Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("Discrete_Distributions.distr", [x_a])]), Term.Type ("fun", [Term.Type ("fun", [x_a, Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])]), Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])])])), Term.Abs ("e'", Term.Type ("Discrete_Distributions.distr", [x_a]), Term.Abs ("B'", Term.Type ("fun", [x_a, Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]), Term.$ (Term.$ (Term.Const ("Lattices.inf_class.inf", Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])), Term.$ (Term.Const ("QRHL_Core.classical_subspace", Term.Type ("fun", [Term.Type ("HOL.bool", []), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])), Term.$ (Term.$ (Term.Const ("HOL.eq", Term.Type ("fun", [Term.Type ("Real.real", []), Term.Type ("fun", [Term.Type ("Real.real", []), Term.Type ("HOL.bool", [])])])), Term.$ (Term.Const ("Discrete_Distributions.weight", Term.Type ("fun", [Term.Type ("Discrete_Distributions.distr", [x_a]), Term.Type ("Real.real", [])])), Term.Bound 1)), Term.Const ("Groups.one_class.one", Term.Type ("Real.real", []))))), Term.$ (Term.Const ("Complete_Lattices.Inf_class.Inf", Term.Type ("fun", [Term.Type ("Set.set", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])), Term.$ (Term.$ (Term.Const ("Set.image", Term.Type ("fun", [Term.Type ("fun", [x_a, Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]), Term.Type ("fun", [Term.Type ("Set.set", [x_a]), Term.Type ("Set.set", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])])), Term.Abs ("z", x_a, Term.$ (Term.Bound 1, Term.Bound 0))), Term.$ (Term.Const ("Discrete_Distributions.supp", Term.Type ("fun", [Term.Type ("Discrete_Distributions.distr", [x_a]), Term.Type ("Set.set", [x_a])])), Term.Bound 1))))))), Term.$ (Term.$ (Term.Const ("Expressions.index_expression", Term.Type ("fun", [Term.Type ("HOL.bool", []), Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("Discrete_Distributions.distr", [x_a])]), Term.Type ("Expressions.expression", [Term.Type ("Discrete_Distributions.distr", [x_a])])])])), Term.Const ("HOL.False", Term.Type ("HOL.bool", []))), e)), Term.Abs ("z", x_a, Term.$ (Term.$ (Term.Const ("Expressions.subst_expression", Term.Type ("fun", [Term.Type ("Expressions.substitution", []), Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]), Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])])), Term.$ (Term.$ (Term.Const ("Expressions.substitute1", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("fun", [Term.Type ("Expressions.expression", [x_a]), Term.Type ("Expressions.substitution", [])])])), Term.$ (Term.$ (Term.Const ("Prog_Variables.index_var", Term.Type ("fun", [Term.Type ("HOL.bool", []), Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("Prog_Variables.variable", [x_a])])])), Term.Const ("HOL.False", Term.Type ("HOL.bool", []))), x)), Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.unit", [])]), Term.Type ("fun", [Term.Type ("fun", [Term.Type ("Product_Type.unit", []), x_a]), Term.Type ("Expressions.expression", [x_a])])])), Term.Const ("Prog_Variables.variable_unit", Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.unit", [])]))), Term.Abs ("uu_", Term.Type ("Product_Type.unit", []), Term.Bound 1)))), ba)))
    fun mkcert () = Cert_Codegen.implies_elim_multi_beta (infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [ca, da, x, e, ba, a]) @{thm "wp2_sample_func"}) [infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])]))) |> SOME] reflexive_thm, infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.$ (Term.$ (Term.Const ("List.list.Cons", Term.Type ("fun", [Term.Type ("Encoding.program", []), Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("List.list", [Term.Type ("Encoding.program", [])])])])), Term.$ (Term.$ (Term.Const ("Encoding.sample", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("Discrete_Distributions.distr", [x_aa])]), Term.Type ("Encoding.program", [])])])), x), e)), Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])])))) |> SOME] reflexive_thm, infer_instantiate' ctxt [Thm.cterm_of ctxt (a) |> SOME] reflexive_thm]
  in (a, mkcert) end
  
  (* wp1_qapply_func: ?d \<equiv> [] \<Longrightarrow> ?c \<equiv> [qapply ?Q ?e] \<Longrightarrow> map_expression2 (\<lambda>e\<^sub>1 B. \<CC>\<ll>\<aa>[isometry e\<^sub>1] \<sqinter> ((e\<^sub>1\<guillemotright>index_vars True ?Q)* \<cdot> (B \<sqinter> (e\<^sub>1\<guillemotright>index_vars True ?Q \<cdot> \<top>)))) (index_expression True ?e) ?B \<equiv> ?A \<Longrightarrow> qrhl ?A ?c ?d ?B *)
  fun wp1_qapply_func ca da ba = let
    val Term.Type ("List.list", [Term.Type ("Encoding.program", [])]) = fastype_of ca
    val Term.Type ("List.list", [Term.Type ("Encoding.program", [])]) = fastype_of da
    val Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]) = fastype_of ba
    (* Assumption: ?d \<equiv> []
       Handled using pattern matching *)
    val Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])])) = da
    (* Assumption: ?c \<equiv> [qapply ?Q ?e]
       Handled using pattern matching *)
    val Term.$ (Term.$ (Term.Const ("List.list.Cons", Term.Type ("fun", [Term.Type ("Encoding.program", []), Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("List.list", [Term.Type ("Encoding.program", [])])])])), Term.$ (Term.$ (Term.Const ("Encoding.qapply", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_a]), Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("Bounded_Operators.bounded", [x_aa, x_ab])]), Term.Type ("Encoding.program", [])])])), q), e)), Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])]))) = ca
    val _ = if (x_ab=x_a) then () else raise Bind
    val _ = if (x_aa=x_a) then () else raise Bind
    (* Assumption: map_expression2 (\<lambda>e\<^sub>1 B. \<CC>\<ll>\<aa>[isometry e\<^sub>1] \<sqinter> ((e\<^sub>1\<guillemotright>index_vars True ?Q)* \<cdot> (B \<sqinter> (e\<^sub>1\<guillemotright>index_vars True ?Q \<cdot> \<top>)))) (index_expression True ?e) ?B \<equiv> ?A
       Handled using pattern matching *)
    val a = Term.$ (Term.$ (Term.$ (Term.Const ("Expressions.map_expression2", Term.Type ("fun", [Term.Type ("fun", [Term.Type ("Bounded_Operators.bounded", [x_a, x_a]), Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])]), Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("Bounded_Operators.bounded", [x_a, x_a])]), Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]), Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])])])), Term.Abs ("e\<^sub>1", Term.Type ("Bounded_Operators.bounded", [x_a, x_a]), Term.Abs ("B", Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.$ (Term.$ (Term.Const ("Lattices.inf_class.inf", Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])), Term.$ (Term.Const ("QRHL_Core.classical_subspace", Term.Type ("fun", [Term.Type ("HOL.bool", []), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])), Term.$ (Term.Const ("Bounded_Operators.isometry", Term.Type ("fun", [Term.Type ("Bounded_Operators.bounded", [x_a, x_a]), Term.Type ("HOL.bool", [])])), Term.Bound 1))), Term.$ (Term.$ (Term.Const ("Bounded_Operators.applyOpSpace", Term.Type ("fun", [Term.Type ("Bounded_Operators.bounded", [Term.Type ("Prog_Variables.mem2", []), Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])), Term.$ (Term.Const ("Bounded_Operators.adjoint", Term.Type ("fun", [Term.Type ("Bounded_Operators.bounded", [Term.Type ("Prog_Variables.mem2", []), Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("Bounded_Operators.bounded", [Term.Type ("Prog_Variables.mem2", []), Term.Type ("Prog_Variables.mem2", [])])])), Term.$ (Term.$ (Term.Const ("QRHL_Core.liftOp", Term.Type ("fun", [Term.Type ("Bounded_Operators.bounded", [x_a, x_a]), Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_a]), Term.Type ("Bounded_Operators.bounded", [Term.Type ("Prog_Variables.mem2", []), Term.Type ("Prog_Variables.mem2", [])])])])), Term.Bound 1), Term.$ (Term.$ (Term.Const ("Prog_Variables.index_vars", Term.Type ("fun", [Term.Type ("HOL.bool", []), Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_a]), Term.Type ("Prog_Variables.variables", [x_a])])])), Term.Const ("HOL.True", Term.Type ("HOL.bool", []))), q)))), Term.$ (Term.$ (Term.Const ("Lattices.inf_class.inf", Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])), Term.Bound 0), Term.$ (Term.$ (Term.Const ("Bounded_Operators.applyOpSpace", Term.Type ("fun", [Term.Type ("Bounded_Operators.bounded", [Term.Type ("Prog_Variables.mem2", []), Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])), Term.$ (Term.$ (Term.Const ("QRHL_Core.liftOp", Term.Type ("fun", [Term.Type ("Bounded_Operators.bounded", [x_a, x_a]), Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_a]), Term.Type ("Bounded_Operators.bounded", [Term.Type ("Prog_Variables.mem2", []), Term.Type ("Prog_Variables.mem2", [])])])])), Term.Bound 1), Term.$ (Term.$ (Term.Const ("Prog_Variables.index_vars", Term.Type ("fun", [Term.Type ("HOL.bool", []), Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_a]), Term.Type ("Prog_Variables.variables", [x_a])])])), Term.Const ("HOL.True", Term.Type ("HOL.bool", []))), q))), Term.Const ("Orderings.top_class.top", Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]))))))))), Term.$ (Term.$ (Term.Const ("Expressions.index_expression", Term.Type ("fun", [Term.Type ("HOL.bool", []), Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("Bounded_Operators.bounded", [x_a, x_a])]), Term.Type ("Expressions.expression", [Term.Type ("Bounded_Operators.bounded", [x_a, x_a])])])])), Term.Const ("HOL.True", Term.Type ("HOL.bool", []))), e)), ba)
    fun mkcert () = Cert_Codegen.implies_elim_multi_beta (infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [da, ca, q, e, ba, a]) @{thm "wp1_qapply_func"}) [infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])]))) |> SOME] reflexive_thm, infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.$ (Term.$ (Term.Const ("List.list.Cons", Term.Type ("fun", [Term.Type ("Encoding.program", []), Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("List.list", [Term.Type ("Encoding.program", [])])])])), Term.$ (Term.$ (Term.Const ("Encoding.qapply", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_a]), Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("Bounded_Operators.bounded", [x_aa, x_ab])]), Term.Type ("Encoding.program", [])])])), q), e)), Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])])))) |> SOME] reflexive_thm, infer_instantiate' ctxt [Thm.cterm_of ctxt (a) |> SOME] reflexive_thm]
  in (a, mkcert) end
  
  (* wp2_qapply_func: ?c \<equiv> [] \<Longrightarrow> ?d \<equiv> [qapply ?Q ?e] \<Longrightarrow> map_expression2 (\<lambda>e\<^sub>1 B. \<CC>\<ll>\<aa>[isometry e\<^sub>1] \<sqinter> ((e\<^sub>1\<guillemotright>index_vars False ?Q)* \<cdot> (B \<sqinter> (e\<^sub>1\<guillemotright>index_vars False ?Q \<cdot> \<top>)))) (index_expression False ?e) ?B \<equiv> ?A \<Longrightarrow> qrhl ?A ?c ?d ?B *)
  fun wp2_qapply_func ca da ba = let
    val Term.Type ("List.list", [Term.Type ("Encoding.program", [])]) = fastype_of ca
    val Term.Type ("List.list", [Term.Type ("Encoding.program", [])]) = fastype_of da
    val Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]) = fastype_of ba
    (* Assumption: ?c \<equiv> []
       Handled using pattern matching *)
    val Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])])) = ca
    (* Assumption: ?d \<equiv> [qapply ?Q ?e]
       Handled using pattern matching *)
    val Term.$ (Term.$ (Term.Const ("List.list.Cons", Term.Type ("fun", [Term.Type ("Encoding.program", []), Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("List.list", [Term.Type ("Encoding.program", [])])])])), Term.$ (Term.$ (Term.Const ("Encoding.qapply", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_a]), Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("Bounded_Operators.bounded", [x_aa, x_ab])]), Term.Type ("Encoding.program", [])])])), q), e)), Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])]))) = da
    val _ = if (x_ab=x_a) then () else raise Bind
    val _ = if (x_aa=x_a) then () else raise Bind
    (* Assumption: map_expression2 (\<lambda>e\<^sub>1 B. \<CC>\<ll>\<aa>[isometry e\<^sub>1] \<sqinter> ((e\<^sub>1\<guillemotright>index_vars False ?Q)* \<cdot> (B \<sqinter> (e\<^sub>1\<guillemotright>index_vars False ?Q \<cdot> \<top>)))) (index_expression False ?e) ?B \<equiv> ?A
       Handled using pattern matching *)
    val a = Term.$ (Term.$ (Term.$ (Term.Const ("Expressions.map_expression2", Term.Type ("fun", [Term.Type ("fun", [Term.Type ("Bounded_Operators.bounded", [x_a, x_a]), Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])]), Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("Bounded_Operators.bounded", [x_a, x_a])]), Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]), Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])])])), Term.Abs ("e\<^sub>1", Term.Type ("Bounded_Operators.bounded", [x_a, x_a]), Term.Abs ("B", Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.$ (Term.$ (Term.Const ("Lattices.inf_class.inf", Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])), Term.$ (Term.Const ("QRHL_Core.classical_subspace", Term.Type ("fun", [Term.Type ("HOL.bool", []), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])), Term.$ (Term.Const ("Bounded_Operators.isometry", Term.Type ("fun", [Term.Type ("Bounded_Operators.bounded", [x_a, x_a]), Term.Type ("HOL.bool", [])])), Term.Bound 1))), Term.$ (Term.$ (Term.Const ("Bounded_Operators.applyOpSpace", Term.Type ("fun", [Term.Type ("Bounded_Operators.bounded", [Term.Type ("Prog_Variables.mem2", []), Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])), Term.$ (Term.Const ("Bounded_Operators.adjoint", Term.Type ("fun", [Term.Type ("Bounded_Operators.bounded", [Term.Type ("Prog_Variables.mem2", []), Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("Bounded_Operators.bounded", [Term.Type ("Prog_Variables.mem2", []), Term.Type ("Prog_Variables.mem2", [])])])), Term.$ (Term.$ (Term.Const ("QRHL_Core.liftOp", Term.Type ("fun", [Term.Type ("Bounded_Operators.bounded", [x_a, x_a]), Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_a]), Term.Type ("Bounded_Operators.bounded", [Term.Type ("Prog_Variables.mem2", []), Term.Type ("Prog_Variables.mem2", [])])])])), Term.Bound 1), Term.$ (Term.$ (Term.Const ("Prog_Variables.index_vars", Term.Type ("fun", [Term.Type ("HOL.bool", []), Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_a]), Term.Type ("Prog_Variables.variables", [x_a])])])), Term.Const ("HOL.False", Term.Type ("HOL.bool", []))), q)))), Term.$ (Term.$ (Term.Const ("Lattices.inf_class.inf", Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])), Term.Bound 0), Term.$ (Term.$ (Term.Const ("Bounded_Operators.applyOpSpace", Term.Type ("fun", [Term.Type ("Bounded_Operators.bounded", [Term.Type ("Prog_Variables.mem2", []), Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])), Term.$ (Term.$ (Term.Const ("QRHL_Core.liftOp", Term.Type ("fun", [Term.Type ("Bounded_Operators.bounded", [x_a, x_a]), Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_a]), Term.Type ("Bounded_Operators.bounded", [Term.Type ("Prog_Variables.mem2", []), Term.Type ("Prog_Variables.mem2", [])])])])), Term.Bound 1), Term.$ (Term.$ (Term.Const ("Prog_Variables.index_vars", Term.Type ("fun", [Term.Type ("HOL.bool", []), Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_a]), Term.Type ("Prog_Variables.variables", [x_a])])])), Term.Const ("HOL.False", Term.Type ("HOL.bool", []))), q))), Term.Const ("Orderings.top_class.top", Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]))))))))), Term.$ (Term.$ (Term.Const ("Expressions.index_expression", Term.Type ("fun", [Term.Type ("HOL.bool", []), Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("Bounded_Operators.bounded", [x_a, x_a])]), Term.Type ("Expressions.expression", [Term.Type ("Bounded_Operators.bounded", [x_a, x_a])])])])), Term.Const ("HOL.False", Term.Type ("HOL.bool", []))), e)), ba)
    fun mkcert () = Cert_Codegen.implies_elim_multi_beta (infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [ca, da, q, e, ba, a]) @{thm "wp2_qapply_func"}) [infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])]))) |> SOME] reflexive_thm, infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.$ (Term.$ (Term.Const ("List.list.Cons", Term.Type ("fun", [Term.Type ("Encoding.program", []), Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("List.list", [Term.Type ("Encoding.program", [])])])])), Term.$ (Term.$ (Term.Const ("Encoding.qapply", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_a]), Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("Bounded_Operators.bounded", [x_aa, x_ab])]), Term.Type ("Encoding.program", [])])])), q), e)), Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])])))) |> SOME] reflexive_thm, infer_instantiate' ctxt [Thm.cterm_of ctxt (a) |> SOME] reflexive_thm]
  in (a, mkcert) end
  
  (* wp1_measure_func: ?d \<equiv> [] \<Longrightarrow> ?c \<equiv> [measurement ?x ?Q ?e] \<Longrightarrow> map_expression2' (\<lambda>e\<^sub>1 B'. \<CC>\<ll>\<aa>[mtotal e\<^sub>1] \<sqinter> (\<Sqinter>z. B' z \<sqinter> (mproj e\<^sub>1 z\<guillemotright>index_vars True ?Q \<cdot> \<top>) + ortho (mproj e\<^sub>1 z\<guillemotright>index_vars True ?Q \<cdot> \<top>))) (index_expression True ?e) (\<lambda>z. subst_expression (substitute1 (index_var True ?x) (const_expression z)) ?B) \<equiv> ?A \<Longrightarrow> qrhl ?A ?c ?d ?B *)
  fun wp1_measure_func ca da ba = let
    val Term.Type ("List.list", [Term.Type ("Encoding.program", [])]) = fastype_of ca
    val Term.Type ("List.list", [Term.Type ("Encoding.program", [])]) = fastype_of da
    val Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]) = fastype_of ba
    (* Assumption: ?d \<equiv> []
       Handled using pattern matching *)
    val Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])])) = da
    (* Assumption: ?c \<equiv> [measurement ?x ?Q ?e]
       Handled using pattern matching *)
    val Term.$ (Term.$ (Term.Const ("List.list.Cons", Term.Type ("fun", [Term.Type ("Encoding.program", []), Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("List.list", [Term.Type ("Encoding.program", [])])])])), Term.$ (Term.$ (Term.$ (Term.Const ("Encoding.measurement", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_b]), Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("QRHL_Core.measurement", [x_aa, x_ba])]), Term.Type ("Encoding.program", [])])])])), x), q), e)), Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])]))) = ca
    val _ = if (x_ba=x_b) then () else raise Bind
    val _ = if (x_aa=x_a) then () else raise Bind
    (* Assumption: map_expression2' (\<lambda>e\<^sub>1 B'. \<CC>\<ll>\<aa>[mtotal e\<^sub>1] \<sqinter> (\<Sqinter>z. B' z \<sqinter> (mproj e\<^sub>1 z\<guillemotright>index_vars True ?Q \<cdot> \<top>) + ortho (mproj e\<^sub>1 z\<guillemotright>index_vars True ?Q \<cdot> \<top>))) (index_expression True ?e) (\<lambda>z. subst_expression (substitute1 (index_var True ?x) (const_expression z)) ?B) \<equiv> ?A
       Handled using pattern matching *)
    val a = Term.$ (Term.$ (Term.$ (Term.Const ("Expressions.map_expression2'", Term.Type ("fun", [Term.Type ("fun", [Term.Type ("QRHL_Core.measurement", [x_a, x_b]), Term.Type ("fun", [Term.Type ("fun", [x_a, Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])]), Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("QRHL_Core.measurement", [x_a, x_b])]), Term.Type ("fun", [Term.Type ("fun", [x_a, Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])]), Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])])])), Term.Abs ("e\<^sub>1", Term.Type ("QRHL_Core.measurement", [x_a, x_b]), Term.Abs ("B'", Term.Type ("fun", [x_a, Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]), Term.$ (Term.$ (Term.Const ("Lattices.inf_class.inf", Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])), Term.$ (Term.Const ("QRHL_Core.classical_subspace", Term.Type ("fun", [Term.Type ("HOL.bool", []), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])), Term.$ (Term.Const ("QRHL_Core.mtotal", Term.Type ("fun", [Term.Type ("QRHL_Core.measurement", [x_a, x_b]), Term.Type ("HOL.bool", [])])), Term.Bound 1))), Term.$ (Term.Const ("Complete_Lattices.Inf_class.Inf", Term.Type ("fun", [Term.Type ("Set.set", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])), Term.$ (Term.$ (Term.Const ("Set.image", Term.Type ("fun", [Term.Type ("fun", [x_a, Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]), Term.Type ("fun", [Term.Type ("Set.set", [x_a]), Term.Type ("Set.set", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])])), Term.Abs ("z", x_a, Term.$ (Term.$ (Term.Const ("Groups.plus_class.plus", Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])), Term.$ (Term.$ (Term.Const ("Lattices.inf_class.inf", Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])), Term.$ (Term.Bound 1, Term.Bound 0)), Term.$ (Term.$ (Term.Const ("Bounded_Operators.applyOpSpace", Term.Type ("fun", [Term.Type ("Bounded_Operators.bounded", [Term.Type ("Prog_Variables.mem2", []), Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])), Term.$ (Term.$ (Term.Const ("QRHL_Core.liftOp", Term.Type ("fun", [Term.Type ("Bounded_Operators.bounded", [x_b, x_b]), Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_b]), Term.Type ("Bounded_Operators.bounded", [Term.Type ("Prog_Variables.mem2", []), Term.Type ("Prog_Variables.mem2", [])])])])), Term.$ (Term.$ (Term.Const ("QRHL_Core.mproj", Term.Type ("fun", [Term.Type ("QRHL_Core.measurement", [x_a, x_b]), Term.Type ("fun", [x_a, Term.Type ("Bounded_Operators.bounded", [x_b, x_b])])])), Term.Bound 2), Term.Bound 0)), Term.$ (Term.$ (Term.Const ("Prog_Variables.index_vars", Term.Type ("fun", [Term.Type ("HOL.bool", []), Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_b]), Term.Type ("Prog_Variables.variables", [x_b])])])), Term.Const ("HOL.True", Term.Type ("HOL.bool", []))), q))), Term.Const ("Orderings.top_class.top", Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]))))), Term.$ (Term.Const ("Complex_L2.ortho", Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])), Term.$ (Term.$ (Term.Const ("Bounded_Operators.applyOpSpace", Term.Type ("fun", [Term.Type ("Bounded_Operators.bounded", [Term.Type ("Prog_Variables.mem2", []), Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])), Term.$ (Term.$ (Term.Const ("QRHL_Core.liftOp", Term.Type ("fun", [Term.Type ("Bounded_Operators.bounded", [x_b, x_b]), Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_b]), Term.Type ("Bounded_Operators.bounded", [Term.Type ("Prog_Variables.mem2", []), Term.Type ("Prog_Variables.mem2", [])])])])), Term.$ (Term.$ (Term.Const ("QRHL_Core.mproj", Term.Type ("fun", [Term.Type ("QRHL_Core.measurement", [x_a, x_b]), Term.Type ("fun", [x_a, Term.Type ("Bounded_Operators.bounded", [x_b, x_b])])])), Term.Bound 2), Term.Bound 0)), Term.$ (Term.$ (Term.Const ("Prog_Variables.index_vars", Term.Type ("fun", [Term.Type ("HOL.bool", []), Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_b]), Term.Type ("Prog_Variables.variables", [x_b])])])), Term.Const ("HOL.True", Term.Type ("HOL.bool", []))), q))), Term.Const ("Orderings.top_class.top", Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]))))))), Term.Const ("Orderings.top_class.top", Term.Type ("Set.set", [x_a])))))))), Term.$ (Term.$ (Term.Const ("Expressions.index_expression", Term.Type ("fun", [Term.Type ("HOL.bool", []), Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("QRHL_Core.measurement", [x_a, x_b])]), Term.Type ("Expressions.expression", [Term.Type ("QRHL_Core.measurement", [x_a, x_b])])])])), Term.Const ("HOL.True", Term.Type ("HOL.bool", []))), e)), Term.Abs ("z", x_a, Term.$ (Term.$ (Term.Const ("Expressions.subst_expression", Term.Type ("fun", [Term.Type ("Expressions.substitution", []), Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]), Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])])), Term.$ (Term.$ (Term.Const ("Expressions.substitute1", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("fun", [Term.Type ("Expressions.expression", [x_a]), Term.Type ("Expressions.substitution", [])])])), Term.$ (Term.$ (Term.Const ("Prog_Variables.index_var", Term.Type ("fun", [Term.Type ("HOL.bool", []), Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("Prog_Variables.variable", [x_a])])])), Term.Const ("HOL.True", Term.Type ("HOL.bool", []))), x)), Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.unit", [])]), Term.Type ("fun", [Term.Type ("fun", [Term.Type ("Product_Type.unit", []), x_a]), Term.Type ("Expressions.expression", [x_a])])])), Term.Const ("Prog_Variables.variable_unit", Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.unit", [])]))), Term.Abs ("uu_", Term.Type ("Product_Type.unit", []), Term.Bound 1)))), ba)))
    fun mkcert () = Cert_Codegen.implies_elim_multi_beta (infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [da, ca, x, q, e, ba, a]) @{thm "wp1_measure_func"}) [infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])]))) |> SOME] reflexive_thm, infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.$ (Term.$ (Term.Const ("List.list.Cons", Term.Type ("fun", [Term.Type ("Encoding.program", []), Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("List.list", [Term.Type ("Encoding.program", [])])])])), Term.$ (Term.$ (Term.$ (Term.Const ("Encoding.measurement", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_b]), Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("QRHL_Core.measurement", [x_aa, x_ba])]), Term.Type ("Encoding.program", [])])])])), x), q), e)), Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])])))) |> SOME] reflexive_thm, infer_instantiate' ctxt [Thm.cterm_of ctxt (a) |> SOME] reflexive_thm]
  in (a, mkcert) end
  
  (* wp2_measure_func: ?c \<equiv> [] \<Longrightarrow> ?d \<equiv> [measurement ?x ?Q ?e] \<Longrightarrow> map_expression2' (\<lambda>e\<^sub>1 B'. \<CC>\<ll>\<aa>[mtotal e\<^sub>1] \<sqinter> (\<Sqinter>z. B' z \<sqinter> (mproj e\<^sub>1 z\<guillemotright>index_vars False ?Q \<cdot> \<top>) + ortho (mproj e\<^sub>1 z\<guillemotright>index_vars False ?Q \<cdot> \<top>))) (index_expression False ?e) (\<lambda>z. subst_expression (substitute1 (index_var False ?x) (const_expression z)) ?B) \<equiv> ?A \<Longrightarrow> qrhl ?A ?c ?d ?B *)
  fun wp2_measure_func ca da ba = let
    val Term.Type ("List.list", [Term.Type ("Encoding.program", [])]) = fastype_of ca
    val Term.Type ("List.list", [Term.Type ("Encoding.program", [])]) = fastype_of da
    val Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]) = fastype_of ba
    (* Assumption: ?c \<equiv> []
       Handled using pattern matching *)
    val Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])])) = ca
    (* Assumption: ?d \<equiv> [measurement ?x ?Q ?e]
       Handled using pattern matching *)
    val Term.$ (Term.$ (Term.Const ("List.list.Cons", Term.Type ("fun", [Term.Type ("Encoding.program", []), Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("List.list", [Term.Type ("Encoding.program", [])])])])), Term.$ (Term.$ (Term.$ (Term.Const ("Encoding.measurement", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_b]), Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("QRHL_Core.measurement", [x_aa, x_ba])]), Term.Type ("Encoding.program", [])])])])), x), q), e)), Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])]))) = da
    val _ = if (x_ba=x_b) then () else raise Bind
    val _ = if (x_aa=x_a) then () else raise Bind
    (* Assumption: map_expression2' (\<lambda>e\<^sub>1 B'. \<CC>\<ll>\<aa>[mtotal e\<^sub>1] \<sqinter> (\<Sqinter>z. B' z \<sqinter> (mproj e\<^sub>1 z\<guillemotright>index_vars False ?Q \<cdot> \<top>) + ortho (mproj e\<^sub>1 z\<guillemotright>index_vars False ?Q \<cdot> \<top>))) (index_expression False ?e) (\<lambda>z. subst_expression (substitute1 (index_var False ?x) (const_expression z)) ?B) \<equiv> ?A
       Handled using pattern matching *)
    val a = Term.$ (Term.$ (Term.$ (Term.Const ("Expressions.map_expression2'", Term.Type ("fun", [Term.Type ("fun", [Term.Type ("QRHL_Core.measurement", [x_a, x_b]), Term.Type ("fun", [Term.Type ("fun", [x_a, Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])]), Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("QRHL_Core.measurement", [x_a, x_b])]), Term.Type ("fun", [Term.Type ("fun", [x_a, Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])]), Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])])])), Term.Abs ("e\<^sub>1", Term.Type ("QRHL_Core.measurement", [x_a, x_b]), Term.Abs ("B'", Term.Type ("fun", [x_a, Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]), Term.$ (Term.$ (Term.Const ("Lattices.inf_class.inf", Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])), Term.$ (Term.Const ("QRHL_Core.classical_subspace", Term.Type ("fun", [Term.Type ("HOL.bool", []), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])), Term.$ (Term.Const ("QRHL_Core.mtotal", Term.Type ("fun", [Term.Type ("QRHL_Core.measurement", [x_a, x_b]), Term.Type ("HOL.bool", [])])), Term.Bound 1))), Term.$ (Term.Const ("Complete_Lattices.Inf_class.Inf", Term.Type ("fun", [Term.Type ("Set.set", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])), Term.$ (Term.$ (Term.Const ("Set.image", Term.Type ("fun", [Term.Type ("fun", [x_a, Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]), Term.Type ("fun", [Term.Type ("Set.set", [x_a]), Term.Type ("Set.set", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])])), Term.Abs ("z", x_a, Term.$ (Term.$ (Term.Const ("Groups.plus_class.plus", Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])), Term.$ (Term.$ (Term.Const ("Lattices.inf_class.inf", Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])), Term.$ (Term.Bound 1, Term.Bound 0)), Term.$ (Term.$ (Term.Const ("Bounded_Operators.applyOpSpace", Term.Type ("fun", [Term.Type ("Bounded_Operators.bounded", [Term.Type ("Prog_Variables.mem2", []), Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])), Term.$ (Term.$ (Term.Const ("QRHL_Core.liftOp", Term.Type ("fun", [Term.Type ("Bounded_Operators.bounded", [x_b, x_b]), Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_b]), Term.Type ("Bounded_Operators.bounded", [Term.Type ("Prog_Variables.mem2", []), Term.Type ("Prog_Variables.mem2", [])])])])), Term.$ (Term.$ (Term.Const ("QRHL_Core.mproj", Term.Type ("fun", [Term.Type ("QRHL_Core.measurement", [x_a, x_b]), Term.Type ("fun", [x_a, Term.Type ("Bounded_Operators.bounded", [x_b, x_b])])])), Term.Bound 2), Term.Bound 0)), Term.$ (Term.$ (Term.Const ("Prog_Variables.index_vars", Term.Type ("fun", [Term.Type ("HOL.bool", []), Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_b]), Term.Type ("Prog_Variables.variables", [x_b])])])), Term.Const ("HOL.False", Term.Type ("HOL.bool", []))), q))), Term.Const ("Orderings.top_class.top", Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]))))), Term.$ (Term.Const ("Complex_L2.ortho", Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])), Term.$ (Term.$ (Term.Const ("Bounded_Operators.applyOpSpace", Term.Type ("fun", [Term.Type ("Bounded_Operators.bounded", [Term.Type ("Prog_Variables.mem2", []), Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])), Term.$ (Term.$ (Term.Const ("QRHL_Core.liftOp", Term.Type ("fun", [Term.Type ("Bounded_Operators.bounded", [x_b, x_b]), Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_b]), Term.Type ("Bounded_Operators.bounded", [Term.Type ("Prog_Variables.mem2", []), Term.Type ("Prog_Variables.mem2", [])])])])), Term.$ (Term.$ (Term.Const ("QRHL_Core.mproj", Term.Type ("fun", [Term.Type ("QRHL_Core.measurement", [x_a, x_b]), Term.Type ("fun", [x_a, Term.Type ("Bounded_Operators.bounded", [x_b, x_b])])])), Term.Bound 2), Term.Bound 0)), Term.$ (Term.$ (Term.Const ("Prog_Variables.index_vars", Term.Type ("fun", [Term.Type ("HOL.bool", []), Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_b]), Term.Type ("Prog_Variables.variables", [x_b])])])), Term.Const ("HOL.False", Term.Type ("HOL.bool", []))), q))), Term.Const ("Orderings.top_class.top", Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]))))))), Term.Const ("Orderings.top_class.top", Term.Type ("Set.set", [x_a])))))))), Term.$ (Term.$ (Term.Const ("Expressions.index_expression", Term.Type ("fun", [Term.Type ("HOL.bool", []), Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("QRHL_Core.measurement", [x_a, x_b])]), Term.Type ("Expressions.expression", [Term.Type ("QRHL_Core.measurement", [x_a, x_b])])])])), Term.Const ("HOL.False", Term.Type ("HOL.bool", []))), e)), Term.Abs ("z", x_a, Term.$ (Term.$ (Term.Const ("Expressions.subst_expression", Term.Type ("fun", [Term.Type ("Expressions.substitution", []), Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]), Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])])), Term.$ (Term.$ (Term.Const ("Expressions.substitute1", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("fun", [Term.Type ("Expressions.expression", [x_a]), Term.Type ("Expressions.substitution", [])])])), Term.$ (Term.$ (Term.Const ("Prog_Variables.index_var", Term.Type ("fun", [Term.Type ("HOL.bool", []), Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("Prog_Variables.variable", [x_a])])])), Term.Const ("HOL.False", Term.Type ("HOL.bool", []))), x)), Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.unit", [])]), Term.Type ("fun", [Term.Type ("fun", [Term.Type ("Product_Type.unit", []), x_a]), Term.Type ("Expressions.expression", [x_a])])])), Term.Const ("Prog_Variables.variable_unit", Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.unit", [])]))), Term.Abs ("uu_", Term.Type ("Product_Type.unit", []), Term.Bound 1)))), ba)))
    fun mkcert () = Cert_Codegen.implies_elim_multi_beta (infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [ca, da, x, q, e, ba, a]) @{thm "wp2_measure_func"}) [infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])]))) |> SOME] reflexive_thm, infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.$ (Term.$ (Term.Const ("List.list.Cons", Term.Type ("fun", [Term.Type ("Encoding.program", []), Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("List.list", [Term.Type ("Encoding.program", [])])])])), Term.$ (Term.$ (Term.$ (Term.Const ("Encoding.measurement", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_b]), Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("QRHL_Core.measurement", [x_aa, x_ba])]), Term.Type ("Encoding.program", [])])])])), x), q), e)), Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])])))) |> SOME] reflexive_thm, infer_instantiate' ctxt [Thm.cterm_of ctxt (a) |> SOME] reflexive_thm]
  in (a, mkcert) end
  
  (* wp1_if_func: ?d \<equiv> [] \<Longrightarrow> ?c \<equiv> [ifthenelse ?e ?p1.0 ?p2.0] \<Longrightarrow> qrhl ?wp_true ?p1.0 [] ?B \<Longrightarrow> qrhl ?wp_false ?p2.0 [] ?B \<Longrightarrow> map_expression3 (\<lambda>e\<^sub>1 wp_true wp_false. (\<CC>\<ll>\<aa>[\<not> e\<^sub>1] + wp_true) \<sqinter> (\<CC>\<ll>\<aa>[e\<^sub>1] + wp_false)) (index_expression True ?e) ?wp_true ?wp_false \<equiv> ?A \<Longrightarrow> qrhl ?A ?c ?d ?B *)
  fun wp1_if_func ca da ba = let
    val Term.Type ("List.list", [Term.Type ("Encoding.program", [])]) = fastype_of ca
    val Term.Type ("List.list", [Term.Type ("Encoding.program", [])]) = fastype_of da
    val Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]) = fastype_of ba
    (* Assumption: ?d \<equiv> []
       Handled using pattern matching *)
    val Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])])) = da
    (* Assumption: ?c \<equiv> [ifthenelse ?e ?p1.0 ?p2.0]
       Handled using pattern matching *)
    val Term.$ (Term.$ (Term.Const ("List.list.Cons", Term.Type ("fun", [Term.Type ("Encoding.program", []), Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("List.list", [Term.Type ("Encoding.program", [])])])])), Term.$ (Term.$ (Term.$ (Term.Const ("Encoding.ifthenelse", Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("HOL.bool", [])]), Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("Encoding.program", [])])])])), e), p1), p2)), Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])]))) = ca
    (* Assumption: qrhl ?wp_true ?p1.0 [] ?B
       Handled using function wp *)
    val (((wp_true)), cert)
             = wp ctxt (p1) (Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])]))) (ba)
    (* Assumption: qrhl ?wp_false ?p2.0 [] ?B
       Handled using function wp *)
    val (((wp_false)), certa)
             = wp ctxt (p2) (Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])]))) (ba)
    (* Assumption: map_expression3 (\<lambda>e\<^sub>1 wp_true wp_false. (\<CC>\<ll>\<aa>[\<not> e\<^sub>1] + wp_true) \<sqinter> (\<CC>\<ll>\<aa>[e\<^sub>1] + wp_false)) (index_expression True ?e) ?wp_true ?wp_false \<equiv> ?A
       Handled using pattern matching *)
    val a = Term.$ (Term.$ (Term.$ (Term.$ (Term.Const ("Expressions.map_expression3", Term.Type ("fun", [Term.Type ("fun", [Term.Type ("HOL.bool", []), Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])]), Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("HOL.bool", [])]), Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]), Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]), Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])])])])), Term.Abs ("e\<^sub>1", Term.Type ("HOL.bool", []), Term.Abs ("wp_true", Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Abs ("wp_false", Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.$ (Term.$ (Term.Const ("Lattices.inf_class.inf", Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])), Term.$ (Term.$ (Term.Const ("Groups.plus_class.plus", Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])), Term.$ (Term.Const ("QRHL_Core.classical_subspace", Term.Type ("fun", [Term.Type ("HOL.bool", []), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])), Term.$ (Term.Const ("HOL.Not", Term.Type ("fun", [Term.Type ("HOL.bool", []), Term.Type ("HOL.bool", [])])), Term.Bound 2))), Term.Bound 1)), Term.$ (Term.$ (Term.Const ("Groups.plus_class.plus", Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])), Term.$ (Term.Const ("QRHL_Core.classical_subspace", Term.Type ("fun", [Term.Type ("HOL.bool", []), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])), Term.Bound 2)), Term.Bound 0)))))), Term.$ (Term.$ (Term.Const ("Expressions.index_expression", Term.Type ("fun", [Term.Type ("HOL.bool", []), Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("HOL.bool", [])]), Term.Type ("Expressions.expression", [Term.Type ("HOL.bool", [])])])])), Term.Const ("HOL.True", Term.Type ("HOL.bool", []))), e)), wp_true), wp_false)
    fun mkcert () = Cert_Codegen.implies_elim_multi_beta (infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [da, ca, e, p1, p2, wp_true, ba, wp_false, a]) @{thm "wp1_if_func"}) [infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])]))) |> SOME] reflexive_thm, infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.$ (Term.$ (Term.Const ("List.list.Cons", Term.Type ("fun", [Term.Type ("Encoding.program", []), Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("List.list", [Term.Type ("Encoding.program", [])])])])), Term.$ (Term.$ (Term.$ (Term.Const ("Encoding.ifthenelse", Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("HOL.bool", [])]), Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("Encoding.program", [])])])])), e), p1), p2)), Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])])))) |> SOME] reflexive_thm, cert (), certa (), infer_instantiate' ctxt [Thm.cterm_of ctxt (a) |> SOME] reflexive_thm]
  in (a, mkcert) end
  
  (* wp2_if_func: ?c \<equiv> [] \<Longrightarrow> ?d \<equiv> [ifthenelse ?e ?p1.0 ?p2.0] \<Longrightarrow> qrhl ?wp_true [] ?p1.0 ?B \<Longrightarrow> qrhl ?wp_false [] ?p2.0 ?B \<Longrightarrow> map_expression3 (\<lambda>e\<^sub>1 wp_true wp_false. (\<CC>\<ll>\<aa>[\<not> e\<^sub>1] + wp_true) \<sqinter> (\<CC>\<ll>\<aa>[e\<^sub>1] + wp_false)) (index_expression False ?e) ?wp_true ?wp_false \<equiv> ?A \<Longrightarrow> qrhl ?A ?c ?d ?B *)
  fun wp2_if_func ca da ba = let
    val Term.Type ("List.list", [Term.Type ("Encoding.program", [])]) = fastype_of ca
    val Term.Type ("List.list", [Term.Type ("Encoding.program", [])]) = fastype_of da
    val Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]) = fastype_of ba
    (* Assumption: ?c \<equiv> []
       Handled using pattern matching *)
    val Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])])) = ca
    (* Assumption: ?d \<equiv> [ifthenelse ?e ?p1.0 ?p2.0]
       Handled using pattern matching *)
    val Term.$ (Term.$ (Term.Const ("List.list.Cons", Term.Type ("fun", [Term.Type ("Encoding.program", []), Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("List.list", [Term.Type ("Encoding.program", [])])])])), Term.$ (Term.$ (Term.$ (Term.Const ("Encoding.ifthenelse", Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("HOL.bool", [])]), Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("Encoding.program", [])])])])), e), p1), p2)), Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])]))) = da
    (* Assumption: qrhl ?wp_true [] ?p1.0 ?B
       Handled using function wp *)
    val (((wp_true)), cert)
             = wp ctxt (Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])]))) (p1) (ba)
    (* Assumption: qrhl ?wp_false [] ?p2.0 ?B
       Handled using function wp *)
    val (((wp_false)), certa)
             = wp ctxt (Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])]))) (p2) (ba)
    (* Assumption: map_expression3 (\<lambda>e\<^sub>1 wp_true wp_false. (\<CC>\<ll>\<aa>[\<not> e\<^sub>1] + wp_true) \<sqinter> (\<CC>\<ll>\<aa>[e\<^sub>1] + wp_false)) (index_expression False ?e) ?wp_true ?wp_false \<equiv> ?A
       Handled using pattern matching *)
    val a = Term.$ (Term.$ (Term.$ (Term.$ (Term.Const ("Expressions.map_expression3", Term.Type ("fun", [Term.Type ("fun", [Term.Type ("HOL.bool", []), Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])]), Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("HOL.bool", [])]), Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]), Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]), Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])])])])), Term.Abs ("e\<^sub>1", Term.Type ("HOL.bool", []), Term.Abs ("wp_true", Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Abs ("wp_false", Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.$ (Term.$ (Term.Const ("Lattices.inf_class.inf", Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])), Term.$ (Term.$ (Term.Const ("Groups.plus_class.plus", Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])), Term.$ (Term.Const ("QRHL_Core.classical_subspace", Term.Type ("fun", [Term.Type ("HOL.bool", []), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])), Term.$ (Term.Const ("HOL.Not", Term.Type ("fun", [Term.Type ("HOL.bool", []), Term.Type ("HOL.bool", [])])), Term.Bound 2))), Term.Bound 1)), Term.$ (Term.$ (Term.Const ("Groups.plus_class.plus", Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("fun", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])]), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])])), Term.$ (Term.Const ("QRHL_Core.classical_subspace", Term.Type ("fun", [Term.Type ("HOL.bool", []), Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])])), Term.Bound 2)), Term.Bound 0)))))), Term.$ (Term.$ (Term.Const ("Expressions.index_expression", Term.Type ("fun", [Term.Type ("HOL.bool", []), Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("HOL.bool", [])]), Term.Type ("Expressions.expression", [Term.Type ("HOL.bool", [])])])])), Term.Const ("HOL.False", Term.Type ("HOL.bool", []))), e)), wp_true), wp_false)
    fun mkcert () = Cert_Codegen.implies_elim_multi_beta (infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [ca, da, e, p1, p2, wp_true, ba, wp_false, a]) @{thm "wp2_if_func"}) [infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])]))) |> SOME] reflexive_thm, infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.$ (Term.$ (Term.Const ("List.list.Cons", Term.Type ("fun", [Term.Type ("Encoding.program", []), Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("List.list", [Term.Type ("Encoding.program", [])])])])), Term.$ (Term.$ (Term.$ (Term.Const ("Encoding.ifthenelse", Term.Type ("fun", [Term.Type ("Expressions.expression", [Term.Type ("HOL.bool", [])]), Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("Encoding.program", [])])])])), e), p1), p2)), Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])])))) |> SOME] reflexive_thm, cert (), certa (), infer_instantiate' ctxt [Thm.cterm_of ctxt (a) |> SOME] reflexive_thm]
  in (a, mkcert) end
  
  (* wp1_block_func: ?d \<equiv> [] \<Longrightarrow> ?c \<equiv> [block ?p] \<Longrightarrow> qrhl ?A ?p [] ?B \<Longrightarrow> qrhl ?A ?c ?d ?B *)
  fun wp1_block_func ca da ba = let
    val Term.Type ("List.list", [Term.Type ("Encoding.program", [])]) = fastype_of ca
    val Term.Type ("List.list", [Term.Type ("Encoding.program", [])]) = fastype_of da
    val Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]) = fastype_of ba
    (* Assumption: ?d \<equiv> []
       Handled using pattern matching *)
    val Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])])) = da
    (* Assumption: ?c \<equiv> [block ?p]
       Handled using pattern matching *)
    val Term.$ (Term.$ (Term.Const ("List.list.Cons", Term.Type ("fun", [Term.Type ("Encoding.program", []), Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("List.list", [Term.Type ("Encoding.program", [])])])])), Term.$ (Term.Const ("Encoding.block", Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("Encoding.program", [])])), p)), Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])]))) = ca
    (* Assumption: qrhl ?A ?p [] ?B
       Handled using function wp *)
    val (((a)), cert)
             = wp ctxt (p) (Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])]))) (ba)
    fun mkcert () = Cert_Codegen.implies_elim_multi_beta (infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [da, ca, p, a, ba]) @{thm "wp1_block_func"}) [infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])]))) |> SOME] reflexive_thm, infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.$ (Term.$ (Term.Const ("List.list.Cons", Term.Type ("fun", [Term.Type ("Encoding.program", []), Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("List.list", [Term.Type ("Encoding.program", [])])])])), Term.$ (Term.Const ("Encoding.block", Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("Encoding.program", [])])), p)), Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])])))) |> SOME] reflexive_thm, cert ()]
  in (a, mkcert) end
  
  (* wp2_block_func: ?c \<equiv> [] \<Longrightarrow> ?d \<equiv> [block ?p] \<Longrightarrow> qrhl ?A [] ?p ?B \<Longrightarrow> qrhl ?A ?c ?d ?B *)
  fun wp2_block_func ca da ba = let
    val Term.Type ("List.list", [Term.Type ("Encoding.program", [])]) = fastype_of ca
    val Term.Type ("List.list", [Term.Type ("Encoding.program", [])]) = fastype_of da
    val Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]) = fastype_of ba
    (* Assumption: ?c \<equiv> []
       Handled using pattern matching *)
    val Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])])) = ca
    (* Assumption: ?d \<equiv> [block ?p]
       Handled using pattern matching *)
    val Term.$ (Term.$ (Term.Const ("List.list.Cons", Term.Type ("fun", [Term.Type ("Encoding.program", []), Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("List.list", [Term.Type ("Encoding.program", [])])])])), Term.$ (Term.Const ("Encoding.block", Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("Encoding.program", [])])), p)), Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])]))) = da
    (* Assumption: qrhl ?A [] ?p ?B
       Handled using function wp *)
    val (((a)), cert)
             = wp ctxt (Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])]))) (p) (ba)
    fun mkcert () = Cert_Codegen.implies_elim_multi_beta (infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [ca, da, p, a, ba]) @{thm "wp2_block_func"}) [infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])]))) |> SOME] reflexive_thm, infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.$ (Term.$ (Term.Const ("List.list.Cons", Term.Type ("fun", [Term.Type ("Encoding.program", []), Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("List.list", [Term.Type ("Encoding.program", [])])])])), Term.$ (Term.Const ("Encoding.block", Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("Encoding.program", [])])), p)), Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])])))) |> SOME] reflexive_thm, cert ()]
  in (a, mkcert) end
  
  (* wp1_cons_func: ?d \<equiv> [] \<Longrightarrow> ?c \<equiv> ?p # ?ps \<Longrightarrow> NO_MATCH [] ?ps \<Longrightarrow> qrhl ?B' ?ps [] ?B \<Longrightarrow> qrhl ?A [?p] [] ?B' \<Longrightarrow> qrhl ?A ?c ?d ?B *)
  fun wp1_cons_func ca da ba = let
    val Term.Type ("List.list", [Term.Type ("Encoding.program", [])]) = fastype_of ca
    val Term.Type ("List.list", [Term.Type ("Encoding.program", [])]) = fastype_of da
    val Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]) = fastype_of ba
    (* Assumption: ?d \<equiv> []
       Handled using pattern matching *)
    val Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])])) = da
    (* Assumption: ?c \<equiv> ?p # ?ps
       Handled using pattern matching *)
    val Term.$ (Term.$ (Term.Const ("List.list.Cons", Term.Type ("fun", [Term.Type ("Encoding.program", []), Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("List.list", [Term.Type ("Encoding.program", [])])])])), p), ps) = ca
    (* Assumption: NO_MATCH [] ?ps
       Handled using function NO_MATCH_func *)
    val ((), cert)
             = NO_MATCH_func ctxt (Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Product_Type.unit", [])]))) (ps)
    (* Assumption: qrhl ?B' ?ps [] ?B
       Handled using function wp *)
    val (((bb)), certa)
             = wp ctxt (ps) (Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])]))) (ba)
    (* Assumption: qrhl ?A [?p] [] ?B'
       Handled using function wp *)
    val (((a)), certb)
             = wp ctxt (Term.$ (Term.$ (Term.Const ("List.list.Cons", Term.Type ("fun", [Term.Type ("Encoding.program", []), Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("List.list", [Term.Type ("Encoding.program", [])])])])), p), Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])])))) (Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])]))) (bb)
    fun mkcert () = Cert_Codegen.implies_elim_multi_beta (infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [da, ca, p, ps, bb, ba, a]) @{thm "wp1_cons_func"}) [infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])]))) |> SOME] reflexive_thm, infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.$ (Term.$ (Term.Const ("List.list.Cons", Term.Type ("fun", [Term.Type ("Encoding.program", []), Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("List.list", [Term.Type ("Encoding.program", [])])])])), p), ps)) |> SOME] reflexive_thm, cert (), certa (), certb ()]
  in (a, mkcert) end
  
  (* wp2_cons_func: ?c \<equiv> [] \<Longrightarrow> ?d \<equiv> ?p # ?ps \<Longrightarrow> NO_MATCH [] ?ps \<Longrightarrow> qrhl ?B' [] ?ps ?B \<Longrightarrow> qrhl ?A [] [?p] ?B' \<Longrightarrow> qrhl ?A ?c ?d ?B *)
  fun wp2_cons_func ca da ba = let
    val Term.Type ("List.list", [Term.Type ("Encoding.program", [])]) = fastype_of ca
    val Term.Type ("List.list", [Term.Type ("Encoding.program", [])]) = fastype_of da
    val Term.Type ("Expressions.expression", [Term.Type ("Complex_L2.subspace", [Term.Type ("Prog_Variables.mem2", [])])]) = fastype_of ba
    (* Assumption: ?c \<equiv> []
       Handled using pattern matching *)
    val Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])])) = ca
    (* Assumption: ?d \<equiv> ?p # ?ps
       Handled using pattern matching *)
    val Term.$ (Term.$ (Term.Const ("List.list.Cons", Term.Type ("fun", [Term.Type ("Encoding.program", []), Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("List.list", [Term.Type ("Encoding.program", [])])])])), p), ps) = da
    (* Assumption: NO_MATCH [] ?ps
       Handled using function NO_MATCH_func *)
    val ((), cert)
             = NO_MATCH_func ctxt (Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Product_Type.unit", [])]))) (ps)
    (* Assumption: qrhl ?B' [] ?ps ?B
       Handled using function wp *)
    val (((bb)), certa)
             = wp ctxt (Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])]))) (ps) (ba)
    (* Assumption: qrhl ?A [] [?p] ?B'
       Handled using function wp *)
    val (((a)), certb)
             = wp ctxt (Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])]))) (Term.$ (Term.$ (Term.Const ("List.list.Cons", Term.Type ("fun", [Term.Type ("Encoding.program", []), Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("List.list", [Term.Type ("Encoding.program", [])])])])), p), Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])])))) (bb)
    fun mkcert () = Cert_Codegen.implies_elim_multi_beta (infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [ca, da, p, ps, bb, ba, a]) @{thm "wp2_cons_func"}) [infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.Const ("List.list.Nil", Term.Type ("List.list", [Term.Type ("Encoding.program", [])]))) |> SOME] reflexive_thm, infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.$ (Term.$ (Term.Const ("List.list.Cons", Term.Type ("fun", [Term.Type ("Encoding.program", []), Term.Type ("fun", [Term.Type ("List.list", [Term.Type ("Encoding.program", [])]), Term.Type ("List.list", [Term.Type ("Encoding.program", [])])])])), p), ps)) |> SOME] reflexive_thm, cert (), certa (), certb ()]
  in (a, mkcert) end
  
  val _ = "Invoking: wp " ^ ("\<open>" ^ Syntax.string_of_term ctxt c ^ "\<close>") ^" "^ ("\<open>" ^ Syntax.string_of_term ctxt d ^ "\<close>") ^" "^ ("\<open>" ^ Syntax.string_of_term ctxt b ^ "\<close>") |> tracing
in
wp_skip_func c d b handle Bind => wp1_assign_func c d b handle Bind => wp2_assign_func c d b handle Bind => wp1_sample_func c d b handle Bind => wp2_sample_func c d b handle Bind => wp1_qapply_func c d b handle Bind => wp2_qapply_func c d b handle Bind => wp1_measure_func c d b handle Bind => wp2_measure_func c d b handle Bind => wp1_if_func c d b handle Bind => wp2_if_func c d b handle Bind => wp1_block_func c d b handle Bind => wp2_block_func c d b handle Bind => wp1_cons_func c d b handle Bind => wp2_cons_func c d b handle Bind => (fn (c,d,B) => raise TERM("wp",[c,d,B])) (c, d, b)
end


and index_expression_func ctxt left e = let
  (* index_expression_func: ?e \<equiv> expression ?Q ?E \<Longrightarrow> index_vars ?left ?Q = ?Q1.0 \<Longrightarrow> expression ?Q1.0 ?E \<equiv> ?e' \<Longrightarrow> index_expression ?left ?e = ?e' *)
  fun index_expression_funca lefta ea = let
    val Term.Type ("HOL.bool", []) = fastype_of lefta
    val Term.Type ("Expressions.expression", [x_a]) = fastype_of ea
    (* Assumption: ?e \<equiv> expression ?Q ?E
       Handled using pattern matching *)
    val Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_b]), Term.Type ("fun", [Term.Type ("fun", [x_ba, x_aa]), Term.Type ("Expressions.expression", [x_ab])])])), q), eb) = ea
    val _ = if (x_ab=x_a) then () else raise Bind
    val _ = if (x_aa=x_a) then () else raise Bind
    val _ = if (x_ba=x_b) then () else raise Bind
    (* Assumption: index_vars ?left ?Q = ?Q1.0
       Handled using function index_vars *)
    val (((q1)), cert)
             = index_vars ctxt (lefta) (q)
    (* Assumption: expression ?Q1.0 ?E \<equiv> ?e'
       Handled using pattern matching *)
    val ec = Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_b]), Term.Type ("fun", [Term.Type ("fun", [x_b, x_a]), Term.Type ("Expressions.expression", [x_a])])])), q1), eb)
    fun mkcert () = Cert_Codegen.implies_elim_multi_beta (infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [ea, q, eb, lefta, q1, ec]) @{thm "index_expression_func"}) [infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_b]), Term.Type ("fun", [Term.Type ("fun", [x_ba, x_aa]), Term.Type ("Expressions.expression", [x_ab])])])), q), eb)) |> SOME] reflexive_thm, cert (), infer_instantiate' ctxt [Thm.cterm_of ctxt (ec) |> SOME] reflexive_thm]
  in (ec, mkcert) end
  
  val _ = "Invoking: index_expression_func " ^ ("\<open>" ^ Syntax.string_of_term ctxt left ^ "\<close>") ^" "^ ("\<open>" ^ Syntax.string_of_term ctxt e ^ "\<close>") |> tracing
in
index_expression_funca left e handle Bind => (fn (left,e) => raise TERM("index_expression_func",[left,e])) (left, e)
end


and index_vars ctxt left x = let
  (* index_vars_unit_func: ?X \<equiv> variable_unit \<Longrightarrow> variable_unit \<equiv> ?X' \<Longrightarrow> index_vars ?left ?X = ?X' *)
  fun index_vars_unit_func lefta xa = let
    val Term.Type ("HOL.bool", []) = fastype_of lefta
    val Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.unit", [])]) = fastype_of xa
    (* Assumption: ?X \<equiv> variable_unit
       Handled using pattern matching *)
    val Term.Const ("Prog_Variables.variable_unit", Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.unit", [])])) = xa
    (* Assumption: variable_unit \<equiv> ?X'
       Handled using pattern matching *)
    val xb = Term.Const ("Prog_Variables.variable_unit", Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.unit", [])]))
    fun mkcert () = Cert_Codegen.implies_elim_multi_beta (infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [xa, xb, lefta]) @{thm "index_vars_unit_func"}) [infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.Const ("Prog_Variables.variable_unit", Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.unit", [])]))) |> SOME] reflexive_thm, infer_instantiate' ctxt [Thm.cterm_of ctxt (xb) |> SOME] reflexive_thm]
  in (xb, mkcert) end
  
  (* index_vars_singleton_func: ?X \<equiv> \<lbrakk>?x\<rbrakk> \<Longrightarrow> index_var ?left ?x = ?x1.0 \<Longrightarrow> \<lbrakk>?x1.0\<rbrakk> \<equiv> ?X' \<Longrightarrow> index_vars ?left ?X = ?X' *)
  fun index_vars_singleton_func lefta xa = let
    val Term.Type ("HOL.bool", []) = fastype_of lefta
    val Term.Type ("Prog_Variables.variables", [x_a]) = fastype_of xa
    (* Assumption: ?X \<equiv> \<lbrakk>?x\<rbrakk>
       Handled using pattern matching *)
    val Term.$ (Term.Const ("Prog_Variables.variable_singleton", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_aa]), Term.Type ("Prog_Variables.variables", [x_ab])])), xb) = xa
    val _ = if (x_ab=x_a) then () else raise Bind
    val _ = if (x_aa=x_a) then () else raise Bind
    (* Assumption: index_var ?left ?x = ?x1.0
       Handled using function index_var_func *)
    val (((x1)), cert)
             = index_var_func ctxt (lefta) (xb)
    (* Assumption: \<lbrakk>?x1.0\<rbrakk> \<equiv> ?X'
       Handled using pattern matching *)
    val xc = Term.$ (Term.Const ("Prog_Variables.variable_singleton", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("Prog_Variables.variables", [x_a])])), x1)
    fun mkcert () = Cert_Codegen.implies_elim_multi_beta (infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [xa, xb, lefta, x1, xc]) @{thm "index_vars_singleton_func"}) [infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.$ (Term.Const ("Prog_Variables.variable_singleton", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_aa]), Term.Type ("Prog_Variables.variables", [x_ab])])), xb)) |> SOME] reflexive_thm, cert (), infer_instantiate' ctxt [Thm.cterm_of ctxt (xc) |> SOME] reflexive_thm]
  in (xc, mkcert) end
  
  (* index_vars_concat_func: ?X \<equiv> variable_concat ?Y ?Z \<Longrightarrow> index_vars ?left ?Y = ?Y1.0 \<Longrightarrow> index_vars ?left ?Z = ?Z1.0 \<Longrightarrow> variable_concat ?Y1.0 ?Z1.0 \<equiv> ?X' \<Longrightarrow> index_vars ?left ?X = ?X' *)
  fun index_vars_concat_func lefta xa = let
    val Term.Type ("HOL.bool", []) = fastype_of lefta
    val Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.prod", [x_a, x_b])]) = fastype_of xa
    (* Assumption: ?X \<equiv> variable_concat ?Y ?Z
       Handled using pattern matching *)
    val Term.$ (Term.$ (Term.Const ("Prog_Variables.variable_concat", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_aa]), Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_ba]), Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.prod", [x_ab, x_bb])])])])), y), z) = xa
    val _ = if (x_bb=x_b) then () else raise Bind
    val _ = if (x_ab=x_a) then () else raise Bind
    val _ = if (x_ba=x_b) then () else raise Bind
    val _ = if (x_aa=x_a) then () else raise Bind
    (* Assumption: index_vars ?left ?Y = ?Y1.0
       Handled using function index_vars *)
    val (((y1)), cert)
             = index_vars ctxt (lefta) (y)
    (* Assumption: index_vars ?left ?Z = ?Z1.0
       Handled using function index_vars *)
    val (((z1)), certa)
             = index_vars ctxt (lefta) (z)
    (* Assumption: variable_concat ?Y1.0 ?Z1.0 \<equiv> ?X'
       Handled using pattern matching *)
    val xb = Term.$ (Term.$ (Term.Const ("Prog_Variables.variable_concat", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_a]), Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_b]), Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.prod", [x_a, x_b])])])])), y1), z1)
    fun mkcert () = Cert_Codegen.implies_elim_multi_beta (infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [xa, y, z, lefta, y1, z1, xb]) @{thm "index_vars_concat_func"}) [infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.$ (Term.$ (Term.Const ("Prog_Variables.variable_concat", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_aa]), Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_ba]), Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.prod", [x_ab, x_bb])])])])), y), z)) |> SOME] reflexive_thm, cert (), certa (), infer_instantiate' ctxt [Thm.cterm_of ctxt (xb) |> SOME] reflexive_thm]
  in (xb, mkcert) end
  
  val _ = "Invoking: index_vars " ^ ("\<open>" ^ Syntax.string_of_term ctxt left ^ "\<close>") ^" "^ ("\<open>" ^ Syntax.string_of_term ctxt x ^ "\<close>") |> tracing
in
index_vars_unit_func left x handle Bind => index_vars_singleton_func left x handle Bind => index_vars_concat_func left x handle Bind => (fn (left,X) => raise TERM("index_vars_concat_func",[left,X])) (left, x)
end


and subst_expression_func ctxt s e = let
  (* subst_expression_func_unit: ?s \<equiv> substitute1 ?x ?f \<Longrightarrow> ?e \<equiv> expression variable_unit ?E \<Longrightarrow> expression variable_unit ?E \<equiv> ?e' \<Longrightarrow> subst_expression ?s ?e = ?e' *)
  fun subst_expression_func_unit sa ea = let
    val Term.Type ("Expressions.substitution", []) = fastype_of sa
    val Term.Type ("Expressions.expression", [x_b]) = fastype_of ea
    (* Assumption: ?s \<equiv> substitute1 ?x ?f
       Handled using pattern matching *)
    val Term.$ (Term.$ (Term.Const ("Expressions.substitute1", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("fun", [Term.Type ("Expressions.expression", [x_aa]), Term.Type ("Expressions.substitution", [])])])), x), f) = sa
    val _ = if (x_aa=x_a) then () else raise Bind
    (* Assumption: ?e \<equiv> expression variable_unit ?E
       Handled using pattern matching *)
    val Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.unit", [])]), Term.Type ("fun", [Term.Type ("fun", [Term.Type ("Product_Type.unit", []), x_ba]), Term.Type ("Expressions.expression", [x_bb])])])), Term.Const ("Prog_Variables.variable_unit", Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.unit", [])]))), eb) = ea
    val _ = if (x_bb=x_b) then () else raise Bind
    val _ = if (x_ba=x_b) then () else raise Bind
    (* Assumption: expression variable_unit ?E \<equiv> ?e'
       Handled using pattern matching *)
    val ec = Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.unit", [])]), Term.Type ("fun", [Term.Type ("fun", [Term.Type ("Product_Type.unit", []), x_b]), Term.Type ("Expressions.expression", [x_b])])])), Term.Const ("Prog_Variables.variable_unit", Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.unit", [])]))), eb)
    fun mkcert () = Cert_Codegen.implies_elim_multi_beta (infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [sa, x, f, ea, eb, ec]) @{thm "subst_expression_func_unit"}) [infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.$ (Term.$ (Term.Const ("Expressions.substitute1", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("fun", [Term.Type ("Expressions.expression", [x_aa]), Term.Type ("Expressions.substitution", [])])])), x), f)) |> SOME] reflexive_thm, infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.unit", [])]), Term.Type ("fun", [Term.Type ("fun", [Term.Type ("Product_Type.unit", []), x_ba]), Term.Type ("Expressions.expression", [x_bb])])])), Term.Const ("Prog_Variables.variable_unit", Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.unit", [])]))), eb)) |> SOME] reflexive_thm, infer_instantiate' ctxt [Thm.cterm_of ctxt (ec) |> SOME] reflexive_thm]
  in (ec, mkcert) end
  
  (* subst_expression_func_concat_id: ?s \<equiv> substitute1 ?x ?f \<Longrightarrow> ?e \<equiv> expression (variable_concat ?Q1.0 ?Q2.0) (\<lambda>x. x) \<Longrightarrow> subst_expression (substitute1 ?x ?f) (expression ?Q1.0 (\<lambda>x. x)) = expression ?Q1' ?e1.0 \<Longrightarrow> subst_expression (substitute1 ?x ?f) (expression ?Q2.0 (\<lambda>x. x)) = expression ?Q2' ?e2.0 \<Longrightarrow> expression (variable_concat ?Q1' ?Q2') (\<lambda>(x1, x2). (?e1.0 x1, ?e2.0 x2)) \<equiv> ?e' \<Longrightarrow> subst_expression ?s ?e = ?e' *)
  fun subst_expression_func_concat_id sa ea = let
    val Term.Type ("Expressions.substitution", []) = fastype_of sa
    val Term.Type ("Expressions.expression", [Term.Type ("Product_Type.prod", [x_b, x_c])]) = fastype_of ea
    (* Assumption: ?s \<equiv> substitute1 ?x ?f
       Handled using pattern matching *)
    val Term.$ (Term.$ (Term.Const ("Expressions.substitute1", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("fun", [Term.Type ("Expressions.expression", [x_aa]), Term.Type ("Expressions.substitution", [])])])), x), f) = sa
    val _ = if (x_aa=x_a) then () else raise Bind
    (* Assumption: ?e \<equiv> expression (variable_concat ?Q1.0 ?Q2.0) (\<lambda>x. x)
       Handled using pattern matching *)
    val Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.prod", [x_ba, x_ca])]), Term.Type ("fun", [Term.Type ("fun", [Term.Type ("Product_Type.prod", [x_bb, x_cb]), Term.Type ("Product_Type.prod", [x_bc, x_cc])]), Term.Type ("Expressions.expression", [Term.Type ("Product_Type.prod", [x_bd, x_cd])])])])), Term.$ (Term.$ (Term.Const ("Prog_Variables.variable_concat", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_be]), Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_ce]), Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.prod", [x_bf, x_cf])])])])), q1), q2)), Term.Abs ("x", Term.Type ("Product_Type.prod", [x_bg, x_cg]), Term.Bound 0)) = ea
    val _ = if (x_cg=x_c) then () else raise Bind
    val _ = if (x_bg=x_b) then () else raise Bind
    val _ = if (x_cf=x_c) then () else raise Bind
    val _ = if (x_bf=x_b) then () else raise Bind
    val _ = if (x_ce=x_c) then () else raise Bind
    val _ = if (x_be=x_b) then () else raise Bind
    val _ = if (x_cd=x_c) then () else raise Bind
    val _ = if (x_bd=x_b) then () else raise Bind
    val _ = if (x_cc=x_c) then () else raise Bind
    val _ = if (x_bc=x_b) then () else raise Bind
    val _ = if (x_cb=x_c) then () else raise Bind
    val _ = if (x_bb=x_b) then () else raise Bind
    val _ = if (x_ca=x_c) then () else raise Bind
    val _ = if (x_ba=x_b) then () else raise Bind
    (* Assumption: subst_expression (substitute1 ?x ?f) (expression ?Q1.0 (\<lambda>x. x)) = expression ?Q1' ?e1.0
       Handled using function subst_expression_func *)
    val (((Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_d]), Term.Type ("fun", [Term.Type ("fun", [x_da, x_bh]), Term.Type ("Expressions.expression", [x_bi])])])), q1a), e1))), cert)
             = subst_expression_func ctxt (Term.$ (Term.$ (Term.Const ("Expressions.substitute1", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("fun", [Term.Type ("Expressions.expression", [x_a]), Term.Type ("Expressions.substitution", [])])])), x), f)) (Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_b]), Term.Type ("fun", [Term.Type ("fun", [x_b, x_b]), Term.Type ("Expressions.expression", [x_b])])])), q1), Term.Abs ("x", x_b, Term.Bound 0)))
    val _ = if (x_bi=x_b) then () else raise Bind
    val _ = if (x_bh=x_b) then () else raise Bind
    val _ = if (x_da=x_d) then () else raise Bind
    (* Assumption: subst_expression (substitute1 ?x ?f) (expression ?Q2.0 (\<lambda>x. x)) = expression ?Q2' ?e2.0
       Handled using function subst_expression_func *)
    val (((Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_e]), Term.Type ("fun", [Term.Type ("fun", [x_ea, x_ch]), Term.Type ("Expressions.expression", [x_ci])])])), q2a), e2))), certa)
             = subst_expression_func ctxt (Term.$ (Term.$ (Term.Const ("Expressions.substitute1", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("fun", [Term.Type ("Expressions.expression", [x_a]), Term.Type ("Expressions.substitution", [])])])), x), f)) (Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_c]), Term.Type ("fun", [Term.Type ("fun", [x_c, x_c]), Term.Type ("Expressions.expression", [x_c])])])), q2), Term.Abs ("x", x_c, Term.Bound 0)))
    val _ = if (x_ci=x_c) then () else raise Bind
    val _ = if (x_ch=x_c) then () else raise Bind
    val _ = if (x_ea=x_e) then () else raise Bind
    (* Assumption: expression (variable_concat ?Q1' ?Q2') (\<lambda>(x1, x2). (?e1.0 x1, ?e2.0 x2)) \<equiv> ?e'
       Handled using pattern matching *)
    val eb = Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.prod", [x_d, x_e])]), Term.Type ("fun", [Term.Type ("fun", [Term.Type ("Product_Type.prod", [x_d, x_e]), Term.Type ("Product_Type.prod", [x_b, x_c])]), Term.Type ("Expressions.expression", [Term.Type ("Product_Type.prod", [x_b, x_c])])])])), Term.$ (Term.$ (Term.Const ("Prog_Variables.variable_concat", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_d]), Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_e]), Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.prod", [x_d, x_e])])])])), q1a), q2a)), Term.$ (Term.Const ("Product_Type.prod.case_prod", Term.Type ("fun", [Term.Type ("fun", [x_d, Term.Type ("fun", [x_e, Term.Type ("Product_Type.prod", [x_b, x_c])])]), Term.Type ("fun", [Term.Type ("Product_Type.prod", [x_d, x_e]), Term.Type ("Product_Type.prod", [x_b, x_c])])])), Term.Abs ("x1", x_d, Term.Abs ("x2", x_e, Term.$ (Term.$ (Term.Const ("Product_Type.Pair", Term.Type ("fun", [x_b, Term.Type ("fun", [x_c, Term.Type ("Product_Type.prod", [x_b, x_c])])])), Term.$ (e1, Term.Bound 1)), Term.$ (e2, Term.Bound 0))))))
    fun mkcert () = Cert_Codegen.implies_elim_multi_beta (infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [sa, x, f, ea, q1, q2, q1a, e1, q2a, e2, eb]) @{thm "subst_expression_func_concat_id"}) [infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.$ (Term.$ (Term.Const ("Expressions.substitute1", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("fun", [Term.Type ("Expressions.expression", [x_aa]), Term.Type ("Expressions.substitution", [])])])), x), f)) |> SOME] reflexive_thm, infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.prod", [x_ba, x_ca])]), Term.Type ("fun", [Term.Type ("fun", [Term.Type ("Product_Type.prod", [x_bb, x_cb]), Term.Type ("Product_Type.prod", [x_bc, x_cc])]), Term.Type ("Expressions.expression", [Term.Type ("Product_Type.prod", [x_bd, x_cd])])])])), Term.$ (Term.$ (Term.Const ("Prog_Variables.variable_concat", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_be]), Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_ce]), Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.prod", [x_bf, x_cf])])])])), q1), q2)), Term.Abs ("x", Term.Type ("Product_Type.prod", [x_bg, x_cg]), Term.Bound 0))) |> SOME] reflexive_thm, cert (), certa (), infer_instantiate' ctxt [Thm.cterm_of ctxt (eb) |> SOME] reflexive_thm]
  in (eb, mkcert) end
  
  (* subst_expression_func_singleton_same: ?s \<equiv> substitute1 ?x (expression ?R ?F) \<Longrightarrow> ?e \<equiv> expression \<lbrakk>?x\<rbrakk> ?E \<Longrightarrow> expression ?R (\<lambda>r. ?E (?F r)) \<equiv> ?e' \<Longrightarrow> subst_expression ?s ?e = ?e' *)
  fun subst_expression_func_singleton_same sa ea = let
    val Term.Type ("Expressions.substitution", []) = fastype_of sa
    val Term.Type ("Expressions.expression", [x_c]) = fastype_of ea
    (* Assumption: ?s \<equiv> substitute1 ?x (expression ?R ?F)
       Handled using pattern matching *)
    val Term.$ (Term.$ (Term.Const ("Expressions.substitute1", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("fun", [Term.Type ("Expressions.expression", [x_aa]), Term.Type ("Expressions.substitution", [])])])), x), Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_b]), Term.Type ("fun", [Term.Type ("fun", [x_ba, x_ab]), Term.Type ("Expressions.expression", [x_ac])])])), r), f)) = sa
    val _ = if (x_ac=x_a) then () else raise Bind
    val _ = if (x_ab=x_a) then () else raise Bind
    val _ = if (x_ba=x_b) then () else raise Bind
    val _ = if (x_aa=x_a) then () else raise Bind
    (* Assumption: ?e \<equiv> expression \<lbrakk>?x\<rbrakk> ?E
       Handled using pattern matching *)
    val Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_ad]), Term.Type ("fun", [Term.Type ("fun", [x_ae, x_ca]), Term.Type ("Expressions.expression", [x_cb])])])), Term.$ (Term.Const ("Prog_Variables.variable_singleton", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_af]), Term.Type ("Prog_Variables.variables", [x_ag])])), xa)), eb) = ea
    val _ = if (xa=x) then () else raise Bind
    val _ = if (x_ag=x_a) then () else raise Bind
    val _ = if (x_af=x_a) then () else raise Bind
    val _ = if (x_cb=x_c) then () else raise Bind
    val _ = if (x_ca=x_c) then () else raise Bind
    val _ = if (x_ae=x_a) then () else raise Bind
    val _ = if (x_ad=x_a) then () else raise Bind
    (* Assumption: expression ?R (\<lambda>r. ?E (?F r)) \<equiv> ?e'
       Handled using pattern matching *)
    val ec = Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_b]), Term.Type ("fun", [Term.Type ("fun", [x_b, x_c]), Term.Type ("Expressions.expression", [x_c])])])), r), Term.Abs ("r", x_b, Term.$ (eb, Term.$ (f, Term.Bound 0))))
    fun mkcert () = Cert_Codegen.implies_elim_multi_beta (infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [sa, x, r, f, ea, eb, ec]) @{thm "subst_expression_func_singleton_same"}) [infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.$ (Term.$ (Term.Const ("Expressions.substitute1", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("fun", [Term.Type ("Expressions.expression", [x_aa]), Term.Type ("Expressions.substitution", [])])])), x), Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_b]), Term.Type ("fun", [Term.Type ("fun", [x_ba, x_ab]), Term.Type ("Expressions.expression", [x_ac])])])), r), f))) |> SOME] reflexive_thm, infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_ad]), Term.Type ("fun", [Term.Type ("fun", [x_ae, x_ca]), Term.Type ("Expressions.expression", [x_cb])])])), Term.$ (Term.Const ("Prog_Variables.variable_singleton", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_af]), Term.Type ("Prog_Variables.variables", [x_ag])])), xa)), eb)) |> SOME] reflexive_thm, infer_instantiate' ctxt [Thm.cterm_of ctxt (ec) |> SOME] reflexive_thm]
  in (ec, mkcert) end
  
  (* subst_expression_func_singleton_notsame: ?s \<equiv> substitute1 ?x ?f \<Longrightarrow> ?e \<equiv> expression \<lbrakk>?y\<rbrakk> ?E \<Longrightarrow> variable_name ?x = ?xn \<Longrightarrow> variable_name ?y = ?yn \<Longrightarrow> assert_string_neq ?xn ?yn \<Longrightarrow> ?e \<equiv> ?e' \<Longrightarrow> subst_expression ?s ?e = ?e' *)
  fun subst_expression_func_singleton_notsame sa ea = let
    val Term.Type ("Expressions.substitution", []) = fastype_of sa
    val Term.Type ("Expressions.expression", [x_b]) = fastype_of ea
    (* Assumption: ?s \<equiv> substitute1 ?x ?f
       Handled using pattern matching *)
    val Term.$ (Term.$ (Term.Const ("Expressions.substitute1", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("fun", [Term.Type ("Expressions.expression", [x_aa]), Term.Type ("Expressions.substitution", [])])])), x), f) = sa
    val _ = if (x_aa=x_a) then () else raise Bind
    (* Assumption: ?e \<equiv> expression \<lbrakk>?y\<rbrakk> ?E
       Handled using pattern matching *)
    val Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_c]), Term.Type ("fun", [Term.Type ("fun", [x_ca, x_ba]), Term.Type ("Expressions.expression", [x_bb])])])), Term.$ (Term.Const ("Prog_Variables.variable_singleton", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_cb]), Term.Type ("Prog_Variables.variables", [x_cc])])), y)), eb) = ea
    val _ = if (x_cc=x_c) then () else raise Bind
    val _ = if (x_cb=x_c) then () else raise Bind
    val _ = if (x_bb=x_b) then () else raise Bind
    val _ = if (x_ba=x_b) then () else raise Bind
    val _ = if (x_ca=x_c) then () else raise Bind
    (* Assumption: variable_name ?x = ?xn
       Handled using function get_variable_name *)
    val (((xn)), cert)
             = get_variable_name ctxt (x)
    (* Assumption: variable_name ?y = ?yn
       Handled using function get_variable_name *)
    val (((yn)), certa)
             = get_variable_name ctxt (y)
    (* Assumption: assert_string_neq ?xn ?yn
       Handled using function assert_string_neq_func *)
    val ((), certb)
             = assert_string_neq_func ctxt (xn) (yn)
    (* Assumption: ?e \<equiv> ?e'
       Handled using pattern matching *)
    val ec = ea
    fun mkcert () = Cert_Codegen.implies_elim_multi_beta (infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [sa, x, f, ea, y, eb, xn, yn, ec]) @{thm "subst_expression_func_singleton_notsame"}) [infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.$ (Term.$ (Term.Const ("Expressions.substitute1", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("fun", [Term.Type ("Expressions.expression", [x_aa]), Term.Type ("Expressions.substitution", [])])])), x), f)) |> SOME] reflexive_thm, infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_c]), Term.Type ("fun", [Term.Type ("fun", [x_ca, x_ba]), Term.Type ("Expressions.expression", [x_bb])])])), Term.$ (Term.Const ("Prog_Variables.variable_singleton", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_cb]), Term.Type ("Prog_Variables.variables", [x_cc])])), y)), eb)) |> SOME] reflexive_thm, cert (), certa (), certb (), infer_instantiate' ctxt [Thm.cterm_of ctxt (ec) |> SOME] reflexive_thm]
  in (ec, mkcert) end
  
  (* subst_expression_func_concat_id: ?s \<equiv> substitute1 ?x ?f \<Longrightarrow> ?e \<equiv> expression (variable_concat ?Q1.0 ?Q2.0) (\<lambda>x. x) \<Longrightarrow> subst_expression (substitute1 ?x ?f) (expression ?Q1.0 (\<lambda>x. x)) = expression ?Q1' ?e1.0 \<Longrightarrow> subst_expression (substitute1 ?x ?f) (expression ?Q2.0 (\<lambda>x. x)) = expression ?Q2' ?e2.0 \<Longrightarrow> expression (variable_concat ?Q1' ?Q2') (\<lambda>(x1, x2). (?e1.0 x1, ?e2.0 x2)) \<equiv> ?e' \<Longrightarrow> subst_expression ?s ?e = ?e' *)
  fun subst_expression_func_concat_ida sa ea = let
    val Term.Type ("Expressions.substitution", []) = fastype_of sa
    val Term.Type ("Expressions.expression", [Term.Type ("Product_Type.prod", [x_b, x_c])]) = fastype_of ea
    (* Assumption: ?s \<equiv> substitute1 ?x ?f
       Handled using pattern matching *)
    val Term.$ (Term.$ (Term.Const ("Expressions.substitute1", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("fun", [Term.Type ("Expressions.expression", [x_aa]), Term.Type ("Expressions.substitution", [])])])), x), f) = sa
    val _ = if (x_aa=x_a) then () else raise Bind
    (* Assumption: ?e \<equiv> expression (variable_concat ?Q1.0 ?Q2.0) (\<lambda>x. x)
       Handled using pattern matching *)
    val Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.prod", [x_ba, x_ca])]), Term.Type ("fun", [Term.Type ("fun", [Term.Type ("Product_Type.prod", [x_bb, x_cb]), Term.Type ("Product_Type.prod", [x_bc, x_cc])]), Term.Type ("Expressions.expression", [Term.Type ("Product_Type.prod", [x_bd, x_cd])])])])), Term.$ (Term.$ (Term.Const ("Prog_Variables.variable_concat", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_be]), Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_ce]), Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.prod", [x_bf, x_cf])])])])), q1), q2)), Term.Abs ("x", Term.Type ("Product_Type.prod", [x_bg, x_cg]), Term.Bound 0)) = ea
    val _ = if (x_cg=x_c) then () else raise Bind
    val _ = if (x_bg=x_b) then () else raise Bind
    val _ = if (x_cf=x_c) then () else raise Bind
    val _ = if (x_bf=x_b) then () else raise Bind
    val _ = if (x_ce=x_c) then () else raise Bind
    val _ = if (x_be=x_b) then () else raise Bind
    val _ = if (x_cd=x_c) then () else raise Bind
    val _ = if (x_bd=x_b) then () else raise Bind
    val _ = if (x_cc=x_c) then () else raise Bind
    val _ = if (x_bc=x_b) then () else raise Bind
    val _ = if (x_cb=x_c) then () else raise Bind
    val _ = if (x_bb=x_b) then () else raise Bind
    val _ = if (x_ca=x_c) then () else raise Bind
    val _ = if (x_ba=x_b) then () else raise Bind
    (* Assumption: subst_expression (substitute1 ?x ?f) (expression ?Q1.0 (\<lambda>x. x)) = expression ?Q1' ?e1.0
       Handled using function subst_expression_func *)
    val (((Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_d]), Term.Type ("fun", [Term.Type ("fun", [x_da, x_bh]), Term.Type ("Expressions.expression", [x_bi])])])), q1a), e1))), cert)
             = subst_expression_func ctxt (Term.$ (Term.$ (Term.Const ("Expressions.substitute1", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("fun", [Term.Type ("Expressions.expression", [x_a]), Term.Type ("Expressions.substitution", [])])])), x), f)) (Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_b]), Term.Type ("fun", [Term.Type ("fun", [x_b, x_b]), Term.Type ("Expressions.expression", [x_b])])])), q1), Term.Abs ("x", x_b, Term.Bound 0)))
    val _ = if (x_bi=x_b) then () else raise Bind
    val _ = if (x_bh=x_b) then () else raise Bind
    val _ = if (x_da=x_d) then () else raise Bind
    (* Assumption: subst_expression (substitute1 ?x ?f) (expression ?Q2.0 (\<lambda>x. x)) = expression ?Q2' ?e2.0
       Handled using function subst_expression_func *)
    val (((Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_e]), Term.Type ("fun", [Term.Type ("fun", [x_ea, x_ch]), Term.Type ("Expressions.expression", [x_ci])])])), q2a), e2))), certa)
             = subst_expression_func ctxt (Term.$ (Term.$ (Term.Const ("Expressions.substitute1", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("fun", [Term.Type ("Expressions.expression", [x_a]), Term.Type ("Expressions.substitution", [])])])), x), f)) (Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_c]), Term.Type ("fun", [Term.Type ("fun", [x_c, x_c]), Term.Type ("Expressions.expression", [x_c])])])), q2), Term.Abs ("x", x_c, Term.Bound 0)))
    val _ = if (x_ci=x_c) then () else raise Bind
    val _ = if (x_ch=x_c) then () else raise Bind
    val _ = if (x_ea=x_e) then () else raise Bind
    (* Assumption: expression (variable_concat ?Q1' ?Q2') (\<lambda>(x1, x2). (?e1.0 x1, ?e2.0 x2)) \<equiv> ?e'
       Handled using pattern matching *)
    val eb = Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.prod", [x_d, x_e])]), Term.Type ("fun", [Term.Type ("fun", [Term.Type ("Product_Type.prod", [x_d, x_e]), Term.Type ("Product_Type.prod", [x_b, x_c])]), Term.Type ("Expressions.expression", [Term.Type ("Product_Type.prod", [x_b, x_c])])])])), Term.$ (Term.$ (Term.Const ("Prog_Variables.variable_concat", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_d]), Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_e]), Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.prod", [x_d, x_e])])])])), q1a), q2a)), Term.$ (Term.Const ("Product_Type.prod.case_prod", Term.Type ("fun", [Term.Type ("fun", [x_d, Term.Type ("fun", [x_e, Term.Type ("Product_Type.prod", [x_b, x_c])])]), Term.Type ("fun", [Term.Type ("Product_Type.prod", [x_d, x_e]), Term.Type ("Product_Type.prod", [x_b, x_c])])])), Term.Abs ("x1", x_d, Term.Abs ("x2", x_e, Term.$ (Term.$ (Term.Const ("Product_Type.Pair", Term.Type ("fun", [x_b, Term.Type ("fun", [x_c, Term.Type ("Product_Type.prod", [x_b, x_c])])])), Term.$ (e1, Term.Bound 1)), Term.$ (e2, Term.Bound 0))))))
    fun mkcert () = Cert_Codegen.implies_elim_multi_beta (infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [sa, x, f, ea, q1, q2, q1a, e1, q2a, e2, eb]) @{thm "subst_expression_func_concat_id"}) [infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.$ (Term.$ (Term.Const ("Expressions.substitute1", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("fun", [Term.Type ("Expressions.expression", [x_aa]), Term.Type ("Expressions.substitution", [])])])), x), f)) |> SOME] reflexive_thm, infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.prod", [x_ba, x_ca])]), Term.Type ("fun", [Term.Type ("fun", [Term.Type ("Product_Type.prod", [x_bb, x_cb]), Term.Type ("Product_Type.prod", [x_bc, x_cc])]), Term.Type ("Expressions.expression", [Term.Type ("Product_Type.prod", [x_bd, x_cd])])])])), Term.$ (Term.$ (Term.Const ("Prog_Variables.variable_concat", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_be]), Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_ce]), Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.prod", [x_bf, x_cf])])])])), q1), q2)), Term.Abs ("x", Term.Type ("Product_Type.prod", [x_bg, x_cg]), Term.Bound 0))) |> SOME] reflexive_thm, cert (), certa (), infer_instantiate' ctxt [Thm.cterm_of ctxt (eb) |> SOME] reflexive_thm]
  in (eb, mkcert) end
  
  (* subst_expression_func_id_comp: ?s \<equiv> substitute1 ?x ?f \<Longrightarrow> ?e \<equiv> expression ?Q ?E \<Longrightarrow> NO_MATCH (\<lambda>x. x) ?E \<Longrightarrow> subst_expression (substitute1 ?x ?f) (expression ?Q (\<lambda>x. x)) = expression ?Q' ?g \<Longrightarrow> expression ?Q' (\<lambda>x. ?E (?g x)) \<equiv> ?e' \<Longrightarrow> subst_expression ?s ?e = ?e' *)
  fun subst_expression_func_id_comp sa ea = let
    val Term.Type ("Expressions.substitution", []) = fastype_of sa
    val Term.Type ("Expressions.expression", [x_b]) = fastype_of ea
    (* Assumption: ?s \<equiv> substitute1 ?x ?f
       Handled using pattern matching *)
    val Term.$ (Term.$ (Term.Const ("Expressions.substitute1", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("fun", [Term.Type ("Expressions.expression", [x_aa]), Term.Type ("Expressions.substitution", [])])])), x), f) = sa
    val _ = if (x_aa=x_a) then () else raise Bind
    (* Assumption: ?e \<equiv> expression ?Q ?E
       Handled using pattern matching *)
    val Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_c]), Term.Type ("fun", [Term.Type ("fun", [x_ca, x_ba]), Term.Type ("Expressions.expression", [x_bb])])])), q), eb) = ea
    val _ = if (x_bb=x_b) then () else raise Bind
    val _ = if (x_ba=x_b) then () else raise Bind
    val _ = if (x_ca=x_c) then () else raise Bind
    (* Assumption: NO_MATCH (\<lambda>x. x) ?E
       Handled using function NO_MATCH_func *)
    val ((), cert)
             = NO_MATCH_func ctxt (Term.Abs ("x", Term.Type ("Product_Type.unit", []), Term.Bound 0)) (eb)
    (* Assumption: subst_expression (substitute1 ?x ?f) (expression ?Q (\<lambda>x. x)) = expression ?Q' ?g
       Handled using function subst_expression_func *)
    val (((Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_d]), Term.Type ("fun", [Term.Type ("fun", [x_da, x_cb]), Term.Type ("Expressions.expression", [x_cc])])])), qa), g))), certa)
             = subst_expression_func ctxt (Term.$ (Term.$ (Term.Const ("Expressions.substitute1", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("fun", [Term.Type ("Expressions.expression", [x_a]), Term.Type ("Expressions.substitution", [])])])), x), f)) (Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_c]), Term.Type ("fun", [Term.Type ("fun", [x_c, x_c]), Term.Type ("Expressions.expression", [x_c])])])), q), Term.Abs ("x", x_c, Term.Bound 0)))
    val _ = if (x_cc=x_c) then () else raise Bind
    val _ = if (x_cb=x_c) then () else raise Bind
    val _ = if (x_da=x_d) then () else raise Bind
    (* Assumption: expression ?Q' (\<lambda>x. ?E (?g x)) \<equiv> ?e'
       Handled using pattern matching *)
    val ec = Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_d]), Term.Type ("fun", [Term.Type ("fun", [x_d, x_b]), Term.Type ("Expressions.expression", [x_b])])])), qa), Term.Abs ("x", x_d, Term.$ (eb, Term.$ (g, Term.Bound 0))))
    fun mkcert () = Cert_Codegen.implies_elim_multi_beta (infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [sa, x, f, ea, q, eb, qa, g, ec]) @{thm "subst_expression_func_id_comp"}) [infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.$ (Term.$ (Term.Const ("Expressions.substitute1", Term.Type ("fun", [Term.Type ("Prog_Variables.variable", [x_a]), Term.Type ("fun", [Term.Type ("Expressions.expression", [x_aa]), Term.Type ("Expressions.substitution", [])])])), x), f)) |> SOME] reflexive_thm, infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_c]), Term.Type ("fun", [Term.Type ("fun", [x_ca, x_ba]), Term.Type ("Expressions.expression", [x_bb])])])), q), eb)) |> SOME] reflexive_thm, cert (), certa (), infer_instantiate' ctxt [Thm.cterm_of ctxt (ec) |> SOME] reflexive_thm]
  in (ec, mkcert) end
  
  val _ = "Invoking: subst_expression_func " ^ ("\<open>" ^ Syntax.string_of_term ctxt s ^ "\<close>") ^" "^ ("\<open>" ^ Syntax.string_of_term ctxt e ^ "\<close>") |> tracing
in
subst_expression_func_unit s e handle Bind => subst_expression_func_concat_id s e handle Bind => subst_expression_func_singleton_same s e handle Bind => subst_expression_func_singleton_notsame s e handle Bind => subst_expression_func_concat_ida s e handle Bind => subst_expression_func_id_comp s e handle Bind => (fn (s,e) => raise TERM("subst_expression_func",[s,e])) (s, e)
end


and map_expression2' ctxt f e1 e2 = let
  (* map_expression2'_func: ?e1.0 \<equiv> expression ?Q1.0 ?E1.0 \<Longrightarrow> (\<And>z. ?e2.0 z \<equiv> expression (?Q2.0 z) (?E2.0 z)) \<Longrightarrow> expression (variable_concat ?Q1.0 (?Q2.0 undefined)) (\<lambda>(x1, x2). ?f (?E1.0 x1) (\<lambda>z. ?E2.0 z x2)) \<equiv> ?e' \<Longrightarrow> map_expression2' ?f ?e1.0 ?e2.0 = ?e' *)
  fun map_expression2_func fa e1a e2a = let
    val Term.Type ("fun", [x_a, Term.Type ("fun", [Term.Type ("fun", [x_c, x_d]), x_f])]) = fastype_of fa
    val Term.Type ("Expressions.expression", [x_aa]) = fastype_of e1a
    val Term.Type ("fun", [x_ca, Term.Type ("Expressions.expression", [x_da])]) = fastype_of e2a
    val _ = if (x_da=x_d) then () else raise Bind
    val _ = if (x_ca=x_c) then () else raise Bind
    val _ = if (x_aa=x_a) then () else raise Bind
    (* Assumption: ?e1.0 \<equiv> expression ?Q1.0 ?E1.0
       Handled using pattern matching *)
    val Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_b]), Term.Type ("fun", [Term.Type ("fun", [x_ba, x_ab]), Term.Type ("Expressions.expression", [x_ac])])])), q1), e1b) = e1a
    val _ = if (x_ac=x_a) then () else raise Bind
    val _ = if (x_ab=x_a) then () else raise Bind
    val _ = if (x_ba=x_b) then () else raise Bind
    val z = Free("z_" ^ serial_string(), x_c)
    val e2_z = betapply (e2a,z)
    (* Assumption: ?e2_z \<equiv> expression ?Q2_z ?E2_z
       Handled using pattern matching *)
    val Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_e]), Term.Type ("fun", [Term.Type ("fun", [x_ea, x_db]), Term.Type ("Expressions.expression", [x_dc])])])), q2_z), e2_za) = e2_z
    val _ = if (x_dc=x_d) then () else raise Bind
    val _ = if (x_db=x_d) then () else raise Bind
    val _ = if (x_ea=x_e) then () else raise Bind
    (* Assumption: \<And>z. ?e2.0 z \<equiv> expression (?Q2.0 z) (?E2.0 z)
       Handled by stripping all-quantifier *)
    val e2b = Cert_Codegen.absfree' "z" (dest_Free z) e2_za
    val q2 = Cert_Codegen.absfree' "z" (dest_Free z) q2_z
    fun cert () = Cert_Codegen.generalize_thm_to ctxt (infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_e]), Term.Type ("fun", [Term.Type ("fun", [x_ea, x_db]), Term.Type ("Expressions.expression", [x_dc])])])), q2_z), e2_za)) |> SOME] reflexive_thm) (dest_Free z)
                   (Term.$ (Term.Const ("Pure.all", Term.Type ("fun", [Term.Type ("fun", [x_c, Term.Type ("prop", [])]), Term.Type ("prop", [])])), Term.Abs ("z", x_c, Term.$ (Term.$ (Term.Const ("Pure.eq", Term.Type ("fun", [Term.Type ("Expressions.expression", [x_d]), Term.Type ("fun", [Term.Type ("Expressions.expression", [x_d]), Term.Type ("prop", [])])])), Term.$ (e2a, Term.Bound 0)), Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_e]), Term.Type ("fun", [Term.Type ("fun", [x_e, x_d]), Term.Type ("Expressions.expression", [x_d])])])), Term.$ (q2, Term.Bound 0)), Term.$ (e2b, Term.Bound 0))))))
    (* Assumption: expression (variable_concat ?Q1.0 (?Q2.0 undefined)) (\<lambda>(x1, x2). ?f (?E1.0 x1) (\<lambda>z. ?E2.0 z x2)) \<equiv> ?e'
       Handled using pattern matching *)
    val e = Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.prod", [x_b, x_e])]), Term.Type ("fun", [Term.Type ("fun", [Term.Type ("Product_Type.prod", [x_b, x_e]), x_f]), Term.Type ("Expressions.expression", [x_f])])])), Term.$ (Term.$ (Term.Const ("Prog_Variables.variable_concat", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_b]), Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_e]), Term.Type ("Prog_Variables.variables", [Term.Type ("Product_Type.prod", [x_b, x_e])])])])), q1), Term.$ (q2, Term.Const ("HOL.undefined", x_c)))), Term.$ (Term.Const ("Product_Type.prod.case_prod", Term.Type ("fun", [Term.Type ("fun", [x_b, Term.Type ("fun", [x_e, x_f])]), Term.Type ("fun", [Term.Type ("Product_Type.prod", [x_b, x_e]), x_f])])), Term.Abs ("x1", x_b, Term.Abs ("x2", x_e, Term.$ (Term.$ (fa, Term.$ (e1b, Term.Bound 1)), Term.Abs ("z", x_c, Term.$ (Term.$ (e2b, Term.Bound 0), Term.Bound 1)))))))
    fun mkcert () = Cert_Codegen.implies_elim_multi_beta (infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [e1a, q1, e1b, e2a, q2, e2b, fa, e]) @{thm "map_expression2'_func"}) [infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_b]), Term.Type ("fun", [Term.Type ("fun", [x_ba, x_ab]), Term.Type ("Expressions.expression", [x_ac])])])), q1), e1b)) |> SOME] reflexive_thm, cert (), infer_instantiate' ctxt [Thm.cterm_of ctxt (e) |> SOME] reflexive_thm]
  in (e, mkcert) end
  
  val _ = "Invoking: map_expression2' " ^ ("\<open>" ^ Syntax.string_of_term ctxt f ^ "\<close>") ^" "^ ("\<open>" ^ Syntax.string_of_term ctxt e1 ^ "\<close>") ^" "^ ("\<open>" ^ Syntax.string_of_term ctxt e2 ^ "\<close>") |> tracing
in
map_expression2_func f e1 e2 handle Bind => (fn (f,e1,e2) => raise TERM("map_expression2'",[f,e1,e2])) (f, e1, e2)
end


end
