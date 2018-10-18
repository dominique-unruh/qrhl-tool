structure Test =
struct

fun func ctxt f e1 e2 = let
  (* func: ?e1.0 \<equiv> expression ?Q1.0 ?E1.0 \<Longrightarrow> (\<And>z. ?e2.0 z \<equiv> expression (?Q2.0 z) (?E2.0 z)) \<Longrightarrow> expression (variable_concat ?Q1.0 (?Q2.0 undefined)) (\<lambda>(x1, x2). ?f (?E1.0 x1) (\<lambda>z. ?E2.0 z x2)) \<equiv> ?e' \<Longrightarrow> map_expression2' ?f ?e1.0 ?e2.0 = ?e' *)
  fun funca fa e1a e2a = let
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
    fun mkcert () = Cert_Codegen.implies_elim_multi_beta (infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) [e1a, q1, e1b, e2a, q2, e2b, fa, e]) @{thm "func"}) [infer_instantiate' ctxt [Thm.cterm_of ctxt (Term.$ (Term.$ (Term.Const ("Expressions.expression", Term.Type ("fun", [Term.Type ("Prog_Variables.variables", [x_b]), Term.Type ("fun", [Term.Type ("fun", [x_ba, x_ab]), Term.Type ("Expressions.expression", [x_ac])])])), q1), e1b)) |> SOME] reflexive_thm, cert (), infer_instantiate' ctxt [Thm.cterm_of ctxt (e) |> SOME] reflexive_thm]
  in (e, mkcert) end
  
  val _ = "Invoking: func " ^ ("\<open>" ^ Syntax.string_of_term ctxt f ^ "\<close>") ^" "^ ("\<open>" ^ Syntax.string_of_term ctxt e1 ^ "\<close>") ^" "^ ("\<open>" ^ Syntax.string_of_term ctxt e2 ^ "\<close>") |> tracing
in
funca f e1 e2 handle Bind => (fn (f,e1,e2) => raise TERM("func",[f,e1,e2])) (f, e1, e2)
end


end
