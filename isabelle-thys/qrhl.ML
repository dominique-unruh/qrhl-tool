structure QRHL =
struct

val mk_qvariableT = Prog_Variables.mk_qvariableT
val mk_conjs = Prog_Variables.mk_conjs
fun mk_measurementT T T' = Type(\<^type_name>\<open>measurement\<close>, [T,T'])
fun dest_measurementT (Type(\<^type_name>\<open>measurement\<close>, [T,T'])) = (T,T')
  | dest_measurementT T = raise TYPE("dest_measurementT",[T],[])

(* val parse_varterm = Prog_Variables.parse_varterm *)
val missing_in_varterm = Prog_Variables.missing_in_varterm
val vars_in_varterm = Prog_Variables.vars_in_varterm
(* val mk_varterm = Prog_Variables.mk_varterm *)
val type_of_varterm = Prog_Variables.type_of_varterm
datatype varterm = datatype Prog_Variables.varterm
datatype tree = datatype Prog_Variables.tree


fun mk_INFIMUM A f = 
  let val AT = fastype_of A
      val fT = fastype_of f
      val (_,infT) = dest_funT fT 
      val infsetT = HOLogic.mk_setT infT
  in
    Const(\<^const_name>\<open>Inf\<close>, infsetT --> infT) $ (Const(\<^const_name>\<open>image\<close>, fT --> AT --> infsetT) $ f $ A)
  end


fun dest_All (Const("HOL.All",_) $ Abs(_,T,body)) = (T,body)
  | dest_All t = raise TERM("dest_All",[t])

(* (* TODO: superseeded by mk_varterm ? *)
fun variables [] = (\<^const>\<open>variable_unit\<close>,\<^typ>\<open>unit\<close>)
  | variables [v] = 
        let val vT = fastype_of v
            val vT' = case vT of Type(\<^type_name>\<open>variable\<close>,[vT']) => vT' | _ => raise TYPE("expecting a variable",[vT],[v])
        in
          (Const(\<^const_name>\<open>variable_singleton\<close>, vT --> Type(\<^type_name>\<open>variables\<close>, [vT'])) $ v,
           vT')
        end
  | variables (v::vs) = 
        let val (vs',vsT) = variables vs
            (* val (v',vT) = variables [v] *)
            val vT = fastype_of v
            val vT' = case vT of Type(\<^type_name>\<open>variable\<close>,[vT']) => vT' | _ => raise TYPE("expecting a variable",[vT],[v])
            val prodT = HOLogic.mk_prodT (vT',vsT)
        in
          (Const(\<^const_name>\<open>variable_concat\<close>, 
              mk_variablesT vT' --> mk_variablesT vsT --> mk_variablesT prodT) $
            (Const(\<^const_name>\<open>variable_singleton\<close>, vT --> mk_variablesT vT') $ v) $ vs',
            prodT)
        end
*)

(* Transforms "\<lbrakk>\<dots>\<rbrakk> \<Longrightarrow> A==B" into "A==B" if all the premises can be solved by simp_tac *) 
fun simp_conv_premises ctxt thm =
  let val res = thm |> ALLGOALS (fn i => TRY (Simplifier.simp_tac ctxt i)) |> Seq.hd
      val _ = if Thm.nprems_of res > 0 then raise TERM("Unresolved premises. Perhaps increase simp_depth_limit?",Thm.prems_of res) else ()
  in res end

(* Given a term of the form "A\<guillemotright>Q", returns (lift,A,Q) where "lift x y" evaluates 
   to x/y if \<guillemotright> is a lifting of subspace/bounded, respectively.  *)
fun dest_lift (t as (Const(lift,_) $ S $ Q)) = 
  (case lift of \<^const_name>\<open>apply_qregister_space\<close> => ((fn x => fn _ => x), Q, S)
                             | \<^const_name>\<open>apply_qregister\<close> => ((fn _ => fn y => y), Q, S)
                             | _ => raise TERM("dest_lift: lift is "^lift, [t]))
  | dest_lift t = raise TERM("dest_lift",[t])

(* (* Converts "A >> Q" into "A' >> (Q\<otimes>R)" for some A' *)
fun extend_lift_conv ctxt vtR ct = let
  val (lift_kind,S,Q) = dest_lift (Thm.term_of ct)
  val extend_thm = infer_instantiate ctxt [(("Q",0),Thm.cterm_of ctxt Q),
                                           (("R",0),Thm.cterm_of ctxt vtR),
                                           (("S",0),Thm.cterm_of ctxt S)]
                        (lift_kind @{thm extend_space_lift_aux} @{thm extend_l2bounded_lift_aux})
  val extend_thm' = extend_thm |> simp_conv_premises ctxt
in
  extend_thm'
end
 *)

(*
(* TODO remove *)
fun qinitWp post e Q =
  let val (vs,vsT) = variables Q 
      val qpre = Const(\<^const_name>\<open>space_div\<close>, \<^typ>\<open>predicate\<close> --> mk_ell2T vsT --> mk_variablesT vsT --> \<^typ>\<open>predicate\<close>) $
                    post $ e $ vs
      val isunit = \<^const>\<open>classical_subspace\<close> $ HOLogic.mk_eq 
              (Const(\<^const_name>\<open>norm\<close>, mk_ell2T vsT --> \<^typ>\<open>real\<close>) $ e, \<^term>\<open>1::real\<close>)
  in
    @{const inf(predicate)} $ isunit $ qpre
  end
 *)
        
        (*
(* TODO remove *)
fun qapplyWp post e Q =
  let val (vs,vsT) = variables Q 
      val unitary = \<^const>\<open>classical_subspace\<close> $ 
          (Const(\<^const_name>\<open>isometry\<close>, mk_bounded2T vsT --> HOLogic.boolT) $ e)
      val e' = Const(\<^const_name>\<open>liftOp\<close>, mk_bounded2T vsT --> mk_variablesT vsT --> \<^typ>\<open>(mem2,mem2) bounded\<close>)
                $ e $ vs
      val im_e' = @{const applyOpSpace(mem2,mem2)} $ e' $ @{const top(predicate)}
      val adj_e' = @{const adjoint(mem2,mem2)} $ e'
      val post_im_e' = @{const inf(predicate)} $ post $ im_e'
      val apply_e' = @{const applyOpSpace(mem2,mem2)} $ adj_e' $ post_im_e'
      val unitary_etc = @{const inf(predicate)} $ unitary $ apply_e'
  in
    unitary_etc
  end
         *)

        (*
(* TODO remove *)
fun measureWp B x e Q =
  let val B_z = abstract_over(x,B)
      val (_,resT) = dest_Free x
      val (vs,vsT) = variables Q
      val measT = mk_measurementT resT vsT
      val e_z = Const(\<^const_name>\<open>mproj\<close>, measT --> resT --> mk_bounded2T vsT)
                  $ e $ Bound(0)
      val lift_e_z = Const(\<^const_name>\<open>liftOp\<close>, mk_bounded2T vsT --> mk_variablesT vsT --> \<^typ>\<open>(mem2,mem2) bounded\<close>)
                    $ e_z $ vs
      val im_e_z = @{const applyOpSpace(mem2,mem2)} $ lift_e_z $ @{const top(predicate)}
      val Be = @{const plus(predicate)} $ (@{const inf(predicate)} $ B_z $ im_e_z) $ (@{const ortho(mem2)} $ im_e_z)
      val Inf_Be = mk_INFIMUM (Const(\<^const_name>\<open>top\<close>, HOLogic.mk_setT resT)) (Abs("z",resT,Be))
      val total = @{const classical_subspace} $ (Const(\<^const_name>\<open>mtotal\<close>, measT --> HOLogic.boolT) $ e)
  in
  @{const inf(predicate)} $ total $ Inf_Be
  end
         *)

(*
(* TODO remove *)
fun ifWp e thenWp elseWp =
  let val Cla_e = \<^const>\<open>classical_subspace\<close> $ e
      val Cla_not_e = \<^const>\<open>classical_subspace\<close> $ (\<^const>\<open>Not\<close> $ e)
      val then' = @{const plus(predicate)} $ Cla_not_e $ thenWp
      val else' = @{const plus(predicate)} $ Cla_e $ elseWp
  in
    @{const inf(predicate)} $ then' $ else'
  end
 *)
        
(*
(* TODO remove *)
fun sampleWp v T e B =
    let val distrT = Type(\<^type_name>\<open>distr\<close>,[T])
        val _ = if fastype_of e = distrT then ()
                else raise(TYPE("variable and expression, type mismatch",[T,fastype_of e],[e]))
        val _ = if fastype_of B = \<^typ>\<open>predicate\<close> then ()
                else raise(TYPE("predicate has wrong type",[fastype_of B],[B]))
        val setT = Type(\<^type_name>\<open>set\<close>,[T])
        val supp = Const(\<^const_name>\<open>supp\<close>, distrT --> setT) $ e
        val absB = Term.absfree (v,T) B
        val B2 = @{const Inf(predicate)} $
                 (Const(\<^const_name>\<open>image\<close>, (T --> \<^typ>\<open>predicate\<close>) --> setT -->  \<^typ>\<open>predicate set\<close>)
                  $ absB $ supp)
        val total = \<^const>\<open>classical_subspace\<close> $
             HOLogic.mk_eq (Const(\<^const_name>\<open>weight\<close>, distrT --> \<^typ>\<open>real\<close>) $ e, \<^term>\<open>1::real\<close>)
    in
      @{const inf(predicate)} $ total $ B2
    end
 *)


fun rndWp v1 e1 v2 e2 T B =
    let val distrT = Type(\<^type_name>\<open>distr\<close>,[T])
        val _ = if fastype_of e1 = distrT then ()
                else raise(TYPE("variable and expression, type mismatch",[T,fastype_of e1],[e1]))
        val _ = if fastype_of e2 = distrT then ()
                else raise(TYPE("variable and expression, type mismatch",[T,fastype_of e2],[e2]))
        val _ = if fastype_of B = \<^typ>\<open>predicate\<close> then ()
                else raise(TYPE("predicate has wrong type",[fastype_of B],[B]))
        val setT = Type(\<^type_name>\<open>set\<close>,[T])
        val supp = Const(\<^const_name>\<open>supp\<close>, distrT --> setT) $ e1
        val absB = Term.abstract_over (Free(v1,T),B) |> (fn t => Term.abstract_over (Free(v2,T),t)) |> (fn t => Abs("z",T,t))
        val B2 = @{const Inf(predicate)} $
                      (Const(\<^const_name>\<open>image\<close>, (T --> \<^typ>\<open>predicate\<close>) --> setT -->  \<^typ>\<open>predicate set\<close>)
                         $ absB $ supp)
        val sameDistr = \<^Const>\<open>classical_subspace \<^typ>\<open>qu2\<close>\<close> $ HOLogic.mk_eq (e1,e2)
    in
      @{const inf(predicate)} $ sameDistr $ B2
    end
   
(* TODO remove *)
fun rndWp2 v1 T1 e1 v2 T2 e2 f B =
  let val distrT1 = Type(\<^type_name>\<open>distr\<close>,[T1])
      val distrT2 = Type(\<^type_name>\<open>distr\<close>,[T2])
      val T12 = HOLogic.mk_prodT (T1,T2)
      val distrT12 = Type(\<^type_name>\<open>distr\<close>,[T12])
      val setT12 = HOLogic.mk_setT T12
      val _ = if fastype_of e1 = distrT1 then ()
              else raise(TYPE("variable and expression, type mismatch",[T1,fastype_of e1],[e1]))
      val _ = if fastype_of e2 = distrT2 then ()
              else raise(TYPE("variable and expression, type mismatch",[T2,fastype_of e2],[e2]))
      val _ = if fastype_of B = \<^typ>\<open>predicate\<close> then ()
              else raise(TYPE("predicate has wrong type",[fastype_of B],[B]))
      val supp = Const(\<^const_name>\<open>supp\<close>, distrT12 --> setT12) $ f
      val absB = B |> absfree (v2,T2) |> absfree (v1,T1)
      val marginal1 = HOLogic.mk_eq (Const(\<^const_name>\<open>map_distr\<close>, (T12-->T1) --> distrT12 --> distrT1) $
          Const(\<^const_name>\<open>fst\<close>, T12-->T1) $ f, e1)
      val marginal2 = HOLogic.mk_eq (Const(\<^const_name>\<open>map_distr\<close>, (T12-->T2) --> distrT12 --> distrT2) $
          Const(\<^const_name>\<open>snd\<close>, T12-->T2) $ f, e2)
      val marginals = \<^Const>\<open>classical_subspace \<^typ>\<open>qu2\<close>\<close> $ (HOLogic.mk_conj (marginal1,marginal2))
      val B2 = @{const Inf(predicate)} $
               (Const(\<^const_name>\<open>image\<close>, (T12 --> \<^typ>\<open>predicate\<close>) --> setT12 -->  \<^typ>\<open>predicate set\<close>) $
                 (Const(\<^const_name>\<open>case_prod\<close>, (T1-->T2--> \<^typ>\<open>predicate\<close>) --> (T12-->\<^typ>\<open>predicate\<close>)) $
                  absB) $ supp)
  in
    @{const inf(predicate)} $ marginals $ B2
  end

(* val _ = rndWp2 "x1" @{typ int} @{term "uniform {x1::int}"} "x2" @{typ bool} @{term "uniform {x2::bool}"} 
@{term "uniform UNIV :: (int*bool)distr"} @{term "Cla[(x1::int)=0 \<and> x2]"}
|> Thm.cterm_of @{context} |> @{print} *)


fun mk_quantum_equality Q1 Q2 T =
  let val opT = Prog_Variables.mk_bounded2T T
      val qvT = Prog_Variables.mk_q2variableT T
  in
  Const(\<^const_name>\<open>quantum_equality_full\<close>, opT --> qvT --> opT --> qvT --> \<^typ>\<open>predicate\<close>) $
    Const(\<^const_name>\<open>id_cblinfun\<close>, opT) $ Q1 $ Const(\<^const_name>\<open>id_cblinfun\<close>, opT) $ Q2
  end

(* returns a term t' such that t'\<and>remove = t\<and>remove is true *)
fun removeAnd (remove:term) (t:term) = 
  if t=remove then \<^const>\<open>True\<close> else
  case t of
    (c as Const(\<^const_name>\<open>conj\<close>,_)) $ a $ b => c $ removeAnd remove a $ removeAnd remove b
  | (c as Const(\<^const_name>\<open>inf\<close>,_)) $ a $ b => c $ removeAnd remove a $ removeAnd remove b
  | (c as Const(\<^const_name>\<open>classical_subspace\<close>,_)) $ a => c $ removeAnd remove a
  | _ => t

(* returns a term t' such that t'\<sqinter>remove = t\<sqinter>remove is true *)
fun removeInf (remove:term) (t:term) = 
  if t=remove then Const(\<^const_name>\<open>top\<close>, fastype_of t) else
  case t of
    (c as Const(\<^const_name>\<open>inf\<close>,_)) $ a $ b => c $ removeInf remove a $ removeInf remove b
  | _ => t

fun tidyTrueTop' (Const(\<^const_name>\<open>inf\<close>,_) $ Const(\<^const_name>\<open>top\<close>,_) $ t) = tidyTrueTop' t
  | tidyTrueTop' (Const(\<^const_name>\<open>inf\<close>,_) $ t $ Const(\<^const_name>\<open>top\<close>,_)) = tidyTrueTop' t
  | tidyTrueTop' (Const(\<^const_name>\<open>conj\<close>,_) $ Const(\<^const_name>\<open>True\<close>,_) $ t) = tidyTrueTop' t
  | tidyTrueTop' (Const(\<^const_name>\<open>conj\<close>,_) $ t $ Const(\<^const_name>\<open>True\<close>,_)) = tidyTrueTop' t
  | tidyTrueTop' (Const(\<^const_name>\<open>classical_subspace\<close>,_) $ Const(\<^const_name>\<open>True\<close>,_)) = @{const top(predicate)}
  | tidyTrueTop' (t$u) = tidyTrueTop' t $ tidyTrueTop' u
  | tidyTrueTop' (Abs(v,T,body)) = Abs(v,T,tidyTrueTop' body)
  | tidyTrueTop' t = t

fun tidyTrueTop t =
  let val t' = tidyTrueTop' t
  in
    if t=t' then t else tidyTrueTop t'
  end

fun mk_equals_wp R cvars1 cvars2 qvars1 qvars2 = let
      val cvarEqs = ListPair.zip (cvars1,cvars2) |> map HOLogic.mk_eq
      val claCvarsEq = \<^Const>\<open>classical_subspace \<^typ>\<open>qu2\<close>\<close> $ mk_conjs cvarEqs
      val (qvars1',qvars1T) = (* variables qvars1 *) error "mk_equals_wp: nyi"
      val (qvars2',qvars2T) = (* variables qvars2 *) error "mk_equals_wp: nyi"
      val _ = if qvars1T <> qvars2T then raise TYPE("mismatch",[qvars1T,qvars2T],[]) else ()
      val qvarsEq = if qvars1=[] then @{const top(predicate)} else mk_quantum_equality qvars1' qvars2' qvars1T
      val wp = @{const inf(predicate)} $ (@{const inf(predicate)} $ R $ claCvarsEq) $ qvarsEq
      (* val wp = tidyTrueTop wp *)
in wp end

(* fun equal_get_R B cvars1 cvars2 qvars1 qvars2 overwritten_classical =
  let val (qvars1',qvars1T) = variables qvars1
      val (qvars2',qvars2T) = variables qvars2
      val _ = if qvars1T <> qvars2T then raise TYPE("mismatch",[qvars1T,qvars2T],[]) else ()
      val qvarsEq = if qvars1=[] then @{const top(predicate)} else mk_quantum_equality qvars1' qvars2' qvars1T
      val B0 = B |> removeInf qvarsEq (* invariant: post \<sqinter> qvarsEq \<Longrightarrow> original post *)

      val cwvarEqs = ListPair.zip (cvars1,cvars2) |> map HOLogic.mk_eq
      val B' = fold (fn eq => fn post => removeAnd eq post) cwvarEqs B0
             (* post \<sqinter> qvarsEq \<sqinter> claCvarsEq ==> original post *)
      val freeCWVars = Term.add_frees B' [] |> inter (op=) (overwritten_classical |> map Term.dest_Free) |> rev
      fun inf_over (v,T) p = mk_INFIMUM (HOLogic.mk_UNIV T) (Term.absfree (v,T) p)
      val usedEqs = filter (fn (v1,v2) => member op= freeCWVars (dest_Free v1) andalso member op= freeCWVars (dest_Free v2))
                    (ListPair.zip (cvars1,cvars2)) |> map HOLogic.mk_eq |> mk_conjs 
      val B'' = @{const plus(predicate)} $ (\<^const>\<open>classical_subspace\<close> $ HOLogic.mk_not usedEqs) $ B'
             (* post \<sqinter> qvarsEq \<sqinter> claCvarsEq ==> original post *)
      val B''' = fold inf_over freeCWVars B''
             (* post \<sqinter> qvarsEq \<sqinter> claCvarsEq ==> original post *)

  in
    tidyTrueTop B'''
  end *)



(* fun simp t facts ctx =
  let val ct = Thm.cterm_of ctx t
      val ctx'  = fold (fn name => fn ctx => ctx addsimps (Proof_Context.get_thms ctx name)) facts ctx
      val ct_eq = Simplifier.rewrite ctx' ct |> Thm.prop_of
      val (lhs,rhs) = Logic.dest_equals ct_eq
      val _ = if lhs<>t then raise TERM("conversion returned wrong lhs\n",[t,lhs,rhs]) else ()
  in
    rhs
  end *)

(* fun dest_numeral_syntax (Const (\<^const_syntax>\<open>Num.num.One\<close>, _)) = 1
  | dest_numeral_syntax (Const (\<^const_syntax>\<open>Num.num.Bit0\<close>, _) $ bs) = 2 * dest_numeral_syntax bs
  | dest_numeral_syntax (Const (\<^const_syntax>\<open>Num.num.Bit1\<close>, _) $ bs) = 2 * dest_numeral_syntax bs + 1
  | dest_numeral_syntax t = raise TERM ("dest_num_syntax", [t]); *)

fun dest_bit_syntax (Const (\<^const_syntax>\<open>False\<close>,_)) = 0
  | dest_bit_syntax (Const (\<^const_syntax>\<open>True\<close>,_)) = 1
  | dest_bit_syntax _ = raise TERM ("dest_bit_syntax", []);

val dest_bits_syntax = Integer.eval_radix 2 o map dest_bit_syntax;

fun dest_char_syntax (Const (\<^const_syntax>\<open>String.char.Char\<close>, _) $ b0 $ b1 $ b2 $ b3 $ b4 $ b5 $ b6 $ b7) =
      dest_bits_syntax [b0, b1, b2, b3, b4, b5, b6, b7]
  | dest_char_syntax t = raise TERM ("dest_char_syntax", [t]);

fun dest_list_syntax (Const (\<^const_syntax>\<open>Nil\<close>, _)) = []
  | dest_list_syntax (Const (\<^const_syntax>\<open>Cons\<close>, _) $ t $ u) = t :: dest_list_syntax u
  | dest_list_syntax t = raise TERM ("dest_list_syntax", [t])
val dest_string_syntax = implode o map (chr o dest_char_syntax) o dest_list_syntax;


fun checkType ctx term =
  let val ct = Thm.cterm_of ctx term
  in
    Thm.typ_of_cterm ct
  end

fun fixTac (term, var) =
  let val (typ,body) = dest_All term
      val res = Term.subst_bound (Free(var,typ), body)
  in
  (res,typ)
  end

fun declare_variable_type args sort a mx lthy = 
  let val sort' = Sign.minimize_sort (Proof_Context.theory_of lthy) ((* @{class universe}:: *)sort)
      val is_base_sort = Sign.subsort (Proof_Context.theory_of lthy) (Object_Logic.get_base_sort lthy |> the_default [], sort)
      (* val _ = Sign.witness_sorts (Proof_Context.theory_of lthy) [] [sort'] |> @{print} *)
      val _ = if null (Sign.witness_sorts (Proof_Context.theory_of lthy) [] [sort']) then
                warning ("Assuming the existence of a type of sort "^Syntax.string_of_sort lthy sort'^".\n"^
                         "To show that this is not an inconsistency, define an arbitrary type of that sort first!")
              else ()
      val (T,lthy) = Typedecl.typedecl {final = true} (a, args, mx) lthy
      val (typname,_) = dest_Type T
      val lthy = if is_base_sort then lthy else
                     Local_Theory.background_theory (Axclass.arity_axiomatization (typname, map snd args, sort)) lthy
(*       val lthy = Local_Theory.background_theory (Axclass.arity_axiomatization 
                      (typname, map (fn (_,sort) => @{class universe}::sort) args, @{sort universe})) lthy *)
  in lthy end

fun declare_variable_type_cmd args sort a mx lthy = let
  val default_sort = Type.defaultS (Proof_Context.tsig_of lthy)
  fun read_constraint lthy c = case Typedecl.read_constraint lthy c of [""] => default_sort | s => s
  val args' = map (apsnd (read_constraint lthy)) args
  val sort' = case sort of NONE => default_sort | SOME s => Syntax.read_sort lthy s
  in declare_variable_type args' sort' a mx lthy end

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>declare_variable_type\<close> "type declaration for qRHL programs"
    (Parse.type_args_constrained -- Parse.binding -- Parse.opt_mixfix -- Scan.option (Parse.$$$ "::" |-- Parse.!!! Parse.sort)
      >> (fn (((args, a), mx), sort) => declare_variable_type_cmd args sort a mx))

(* fun swap_variables_conv ctxt = 
  Raw_Simplifier.rewrite_cterm (false,false,false)
  (SINGLE o (K (ALLGOALS (simp_tac ctxt))))
   (Raw_Simplifier.init_simpset @{thms
        swap_variables_subspace_lift[THEN eq_reflection]
        swap_variables_subspace_top[THEN eq_reflection]
        swap_variables_subspace_bot[THEN eq_reflection]
        swap_variables_subspace_zero[THEN eq_reflection]
        swap_variables_subspace_inf[THEN eq_reflection]
        swap_variables_subspace_plus[THEN eq_reflection]
        swap_variables_subspace_Cla[THEN eq_reflection]
        swap_variables_subspace_quantum_equality[THEN eq_reflection]
        swap_variables_vars_concat[THEN eq_reflection]
        swap_variables_vars_singleton1[THEN eq_reflection]
        swap_variables_vars_singleton2[THEN eq_reflection]
        swap_variables_vars_singleton3[THEN eq_reflection]
  } ctxt) *)

fun distinct_qvars_guard_simproc _ _ ct = let
  fun qvariables_in_term (t$u) found = qvariables_in_term t (qvariables_in_term u found)
    | qvariables_in_term (Abs(_,_,t)) found = qvariables_in_term t found
    | qvariables_in_term (Free(v,Type(\<^type_name>\<open>qregister\<close>,_))) found = v :: found
    | qvariables_in_term _ found = found
  val t = case Thm.term_of ct of \<^Const_>\<open>DISTINCT_QVARS_GUARD\<close> $ t => t
  val (vars1, vars2) = case t of
     \<^Const_>\<open>distinct_qvars_pred_vars _ _\<close> $ P $ Q => (qvariables_in_term P [], qvariables_in_term Q [])
   | \<^Const_>\<open>distinct_qvars_op_pred\<close> $ P $ Q => (qvariables_in_term P [], qvariables_in_term Q [])
   | \<^Const_>\<open>distinct_qvars_op_vars _ _\<close> $ P $ Q => (qvariables_in_term P [], qvariables_in_term Q [])
   | _ => ([],[])
  val inter = Ord_List.inter string_ord (Ord_List.make string_ord vars1) (Ord_List.make string_ord vars2)
  val disjoint = null inter
  in if disjoint then SOME @{lemma \<open>DISTINCT_QVARS_GUARD x \<equiv> x\<close> by (simp add: DISTINCT_QVARS_GUARD_def)} else NONE end

fun distinct_qvars_tac ctxt : int -> tactic =
  resolve_tac ctxt [@{lemma \<open>DISTINCT_QVARS_GUARD (distinct_qvars Q) \<Longrightarrow> distinct_qvars Q\<close> 
                      by (simp add: DISTINCT_QVARS_GUARD_def)}]
  THEN' simp_tac ctxt

(* Given a subgoal of the form "liftOp (?trafo U) Q = liftOp U R", solves it by instantiating
   ?trafo suitably. *)
(* TODO needed? *)
fun extend_op_vars_tac ctxt = let
  in
    (* FIRST' [special_case_tac1, special_case_tac2, maintac] *)
    error "fix me! (extend_op_vars_tac)"
  end

(* Given a subgoal of the form "liftOp (?trafoU U) ?QR = liftOp U Q \<and> liftOp (?trafoV V) ?QR = liftOp V R",
   solves it by instantiating ?trafoU, ?trafoV, and ?QR suitably. *)
(* TODO needed? *)
fun extend_2op_vars_tac ctxt = let
(*   val subtac = CONVERSION ((Simplifier.rewrite |> Misc.mk_ctxt_conv Conv.arg1_conv 
                    |> Misc.mk_ctxt_conv HOLogic.Trueprop_conv |> Conv.params_conv ~1) ctxt)
               THEN' resolve_tac ctxt @{thms refl}
  val maintac = 
    resolve_tac ctxt [@{lemma
      \<open>(\<And>U. join_variables_hint (liftOp U Q) R = liftOp (trafoU U) QR)
     \<Longrightarrow> (\<And>V. reorder_variables_hint (liftOp V R) QR = liftOp (trafoV V) QR)
     \<Longrightarrow> liftOp (trafoU U) QR = liftOp U Q \<and> liftOp (trafoV V) QR = liftOp V R\<close>
      by (simp add: reorder_variables_hint_def join_variables_hint_def)}]
    THEN' subtac THEN' subtac
  val special_case_tac1 = resolve_tac ctxt [@{lemma
      \<open>liftOp U Q = liftOp U Q \<and> liftOp V Q = liftOp V Q\<close>
      by auto}]
  val special_case_tac2 = resolve_tac ctxt [@{lemma
      \<open>liftOp (trafoV V) Q = liftOp V R
       \<Longrightarrow> liftOp U Q = liftOp U Q \<and> liftOp (trafoV V) Q = liftOp V R\<close>
      by auto}]
    THEN' extend_op_vars_tac ctxt
  val special_case_tac3 = resolve_tac ctxt [@{lemma
      \<open>liftOp (trafoU U) R = liftOp U Q
       \<Longrightarrow> liftOp (trafoU U) R = liftOp U Q \<and> liftOp V R = liftOp V R\<close>
      by auto}]
    THEN' extend_op_vars_tac ctxt *)
  in
    (* FIRST' [special_case_tac1, special_case_tac2, special_case_tac3, maintac] *)
    error "fix me! (extend_2op_vars_tac)"
  end
end
