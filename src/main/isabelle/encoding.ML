structure Encoding = 
struct

fun mk_expressionT T = Type(@{type_name expression}, [T])

(* val expression_to_term_simpset = clear_simpset @{context} addsimps @{thms case_prod_conv} *)

fun expression_to_term t =
  let val (vs,e) = case t of Const(@{const_name expression},_) $ vs $ e => (vs,e) | _ => raise (TERM("expression_to_term",[t]))
      val vars = QRHL.parse_varterm vs |> QRHL.vars_in_varterm 
          |> map (fn (x,T) => Free (String.extract (x,4,NONE),T)) (* unsafe, not checking whether the var name is wellformed *)
          (* |> @{print} *)
      val e' = e $ HOLogic.mk_tuple vars
      val e'' = Raw_Simplifier.rewrite_term @{theory} @{thms case_prod_conv[THEN eq_reflection]} [] e'
  in
    e''
  end

(* val _ = expression_to_term @{term "expression \<lbrakk>var_x,var_y\<rbrakk> (\<lambda>(x,y). x+y)"} |> (fn t => (t,Thm.cterm_of @{context} t)) |> @{print} *)

fun expression_to_term_typ t =
  let val t2 = expression_to_term t in (t2, fastype_of t2) end

fun add_index_to_expression t left =
  let val suffix = if left then "1" else "2"
      fun rename (Free(x,T)) =  Free(x^suffix,T)
        | rename t = t
      val (vs,e,T) = case t of Const(@{const_name expression},T) $ vs $ e => (vs,e,T) | _ => 
            raise (TERM("add_index_to_expression",[t]))
      val vs = Term.map_aterms rename vs
  in
    Const(@{const_name expression},T) $ vs $ e
  end
    
fun term_to_expression ctx t =
  let val is_classical = QRHL.is_classical_variable ctx
      val frees = Term.add_frees t [] |> filter (fn (v,_) => is_classical v) |> rev
      val (vars,varsT) = 
        frees |> map (fn (v,T) => ("var_"^v,T)) |> QRHL.varterm_from_list |> QRHL.mk_varterm
      val pattern = HOLogic.mk_tuple (map Free frees)
      val e = HOLogic.tupled_lambda pattern t |> @{print}
      val T = fastype_of t
  in
    Const(@{const_name expression}, QRHL.mk_qvariablesT varsT --> (varsT --> T) --> mk_expressionT T)
      $ vars $ e
  end

fun lambda_name_untyped (x, v) t =
  Abs (if x = "" then Term.term_name v else x, dummyT, abstract_over (v, t));

fun lambda_untyped v t = lambda_name_untyped ("", v) t;

fun mk_case_prod_untyped t =
      @{const Product_Type.prod.case_prod(dummy,dummy,dummy)} $ t

fun tupled_lambda_untyped (x as Free _) b = lambda_untyped x b
  | tupled_lambda_untyped (x as Var _) b = lambda_untyped x b
  | tupled_lambda_untyped (Const ("Product_Type.Pair", _) $ u $ v) b =
      mk_case_prod_untyped (tupled_lambda_untyped u (tupled_lambda_untyped v b))
  | tupled_lambda_untyped (Const ("Product_Type.Unity", _)) b =
      Abs ("x", HOLogic.unitT, b)
  | tupled_lambda_untyped t _ = raise TERM ("tupled_lambda_untyped: bad tuple", [t]);

fun mk_prod_untyped (t1, t2) = @{const Pair(dummy,dummy)} $ t1 $ t2

fun mk_tuple_untyped [] = HOLogic.unit
  | mk_tuple_untyped ts = foldr1 mk_prod_untyped ts;

fun term_to_expression_untyped ctx t =
  let val lookup_var = QRHL.lookup_variable ctx
      val frees = Term.add_frees t [] |> filter (fn (v,_) => lookup_var v = SOME QRHL.Classical) |> rev
      val (vars,varsT) = 
        frees |> map (fn (v,T) => ("var_"^v,T)) |> QRHL.varterm_from_list |> QRHL.mk_varterm
      val pattern = mk_tuple_untyped (map Free frees)
      val e = tupled_lambda_untyped pattern t
  in
    Const(@{const_name expression}, QRHL.mk_qvariablesT varsT --> (varsT --> dummyT) --> @{typ "dummy expression"})
      $ vars $ e
  end

fun read_expression ctx str =
  let val t = Syntax.read_term ctx str
  in term_to_expression ctx t end

fun read_predicate ctx str =
  let val preterm = Syntax.parse_term ctx str
      val t = Syntax.check_term ctx (Type.constraint @{typ "predicate"} preterm)
  in term_to_expression ctx t end

end
