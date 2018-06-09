structure QRHL =
struct

fun mk_variablesT T = Type(@{type_name variables}, [T])
fun mk_distrT T = Type(@{type_name distr}, [T])
fun mk_variableT T = Type(@{type_name variable}, [T])
fun dest_variableT (Type(@{type_name variable}, [T])) = T
  | dest_variableT T = raise TYPE("dest_variableT", [T], [])
fun dest_variablesT (Type(@{type_name variables}, [T])) = T
  | dest_variablesT T = raise TYPE("dest_variablesT", [T], [])
fun mk_vectorT T = Type(@{type_name vector}, [T])
fun mk_boundedT T T' = Type(@{type_name bounded}, [T,T'])
fun dest_boundedT (Type(@{type_name bounded}, [T,T'])) = (T,T')
  | dest_boundedT T = raise TYPE("dest_boundedT",[T],[])
fun mk_bounded2T T = mk_boundedT T T
fun mk_measurementT T T' = Type(@{type_name measurement}, [T,T'])
(* fun mk_projectorT T = Type(@{type_name projector}, [T]) *)
fun mk_conjs [] = @{const True}
  | mk_conjs [t] = t
  | mk_conjs (t::ts) = @{const conj} $ t $ mk_conjs ts
fun mk_variable_name v = 
  Const(@{const_name variable_name}, fastype_of v --> @{typ string}) $ v

fun mk_INFIMUM A f = 
  let val AT = fastype_of A
      val fT = fastype_of f
      (* val idxT = case AT of Type(@{type_name set}, [T]) => T *)
      val (_,infT) = dest_funT fT 
      val infsetT = HOLogic.mk_setT infT
  in
    Const(@{const_name Inf}, infsetT --> infT) $ (Const(@{const_name image}, fT --> AT --> infsetT) $ f $ A)
  end


fun dest_All (Const("HOL.All",_) $ Abs(_,T,body)) = (T,body)
  | dest_All t = raise TERM("dest_All",[t])

fun variables [] = (@{const variable_unit},@{typ unit})
  | variables [v] = 
        let val vT = fastype_of v
            val vT' = case vT of Type(@{type_name variable},[vT']) => vT' | _ => raise TYPE("expecting a variable",[vT],[v])
        in
          (Const(@{const_name variable_singleton}, vT --> Type(@{type_name variables}, [vT'])) $ v,
           vT')
        end
  | variables (v::vs) = 
        let val (vs',vsT) = variables vs
            (* val (v',vT) = variables [v] *)
            val vT = fastype_of v
            val vT' = case vT of Type(@{type_name variable},[vT']) => vT' | _ => raise TYPE("expecting a variable",[vT],[v])
            val prodT = HOLogic.mk_prodT (vT',vsT)
        in
          (Const(@{const_name variable_concat}, 
              mk_variablesT vT' --> mk_variablesT vsT --> mk_variablesT prodT) $
            (Const(@{const_name variable_singleton}, vT --> mk_variablesT vT') $ v) $ vs',
            prodT)
        end
  
fun qinitWp post e Q =
  let val (vs,vsT) = variables Q 
      val qpre = Const(@{const_name space_div}, @{typ predicate} --> mk_vectorT vsT --> mk_variablesT vsT --> @{typ predicate}) $
                    post $ e $ vs
      val isunit = @{const classical_subspace} $ HOLogic.mk_eq 
              (Const(@{const_name norm}, mk_vectorT vsT --> @{typ real}) $ e, @{term "1::real"})
  in
    @{const inf(predicate)} $ isunit $ qpre
  end

fun qapplyWp post e Q =
  let val (vs,vsT) = variables Q 
      val unitary = @{const classical_subspace} $ 
          (Const(@{const_name isometry}, mk_bounded2T vsT --> HOLogic.boolT) $ e)
      val e' = Const(@{const_name liftOp}, mk_bounded2T vsT --> mk_variablesT vsT --> @{typ "(mem2,mem2) bounded"})
                $ e $ vs
      val im_e' = @{const applyOpSpace(mem2,mem2)} $ e' $ @{const top(predicate)}
      val adj_e' = @{const adjoint(mem2,mem2)} $ e'
      val post_im_e' = @{const inf(predicate)} $ post $ im_e'
      val apply_e' = @{const applyOpSpace(mem2,mem2)} $ adj_e' $ post_im_e'
      val unitary_etc = @{const inf(predicate)} $ unitary $ apply_e'
  in
    unitary_etc
  end

fun measureWp B x e Q =
  let val B_z = abstract_over(x,B)
      val (_,resT) = dest_Free x
      val (vs,vsT) = variables Q
      val measT = mk_measurementT resT vsT
      val e_z = Const(@{const_name mproj}, measT --> resT --> mk_bounded2T vsT)
                  $ e $ Bound(0)
      val lift_e_z = Const(@{const_name liftOp}, mk_bounded2T vsT --> mk_variablesT vsT --> @{typ "(mem2,mem2) bounded"})
                    $ e_z $ vs
      val im_e_z = @{const applyOpSpace(mem2,mem2)} $ lift_e_z $ @{const top(predicate)}
      val Be = @{const plus(predicate)} $ (@{const inf(predicate)} $ B_z $ im_e_z) $ (@{const ortho(mem2)} $ im_e_z)
      val Inf_Be = mk_INFIMUM (Const(@{const_name top}, HOLogic.mk_setT resT)) (Abs("z",resT,Be))
      val total = @{const classical_subspace} $ (Const(@{const_name mtotal}, measT --> HOLogic.boolT) $ e)
  in
  @{const inf(predicate)} $ total $ Inf_Be
  end


fun ifWp e thenWp elseWp =
  let val Cla_e = @{const classical_subspace} $ e
      val Cla_not_e = @{const classical_subspace} $ (@{const Not} $ e)
      val then' = @{const plus(predicate)} $ Cla_not_e $ thenWp
      val else' = @{const plus(predicate)} $ Cla_e $ elseWp
  in
    @{const inf(predicate)} $ then' $ else'
  end

fun sampleWp v T e B =
    let val distrT = Type(@{type_name distr},[T])
        val _ = if fastype_of e = distrT then ()
                else raise(TYPE("variable and expression, type mismatch",[T,fastype_of e],[e]))
        val _ = if fastype_of B = @{typ predicate} then ()
                else raise(TYPE("predicate has wrong type",[fastype_of B],[B]))
        val setT = Type(@{type_name set},[T])
        val supp = Const(@{const_name supp}, distrT --> setT) $ e
        val absB = Term.absfree (v,T) B
        val B2 = @{const Inf(predicate)} $
                 (Const(@{const_name image}, (T --> @{typ predicate}) --> setT -->  @{typ "predicate set"})
                  $ absB $ supp)
        val total = @{const classical_subspace} $
             HOLogic.mk_eq (Const(@{const_name weight}, distrT --> @{typ real}) $ e, @{term "1::real"})
    in
      @{const inf(predicate)} $ total $ B2
    end



fun rndWp v1 e1 v2 e2 T B =
    let val distrT = Type(@{type_name distr},[T])
        val _ = if fastype_of e1 = distrT then ()
                else raise(TYPE("variable and expression, type mismatch",[T,fastype_of e1],[e1]))
        val _ = if fastype_of e2 = distrT then ()
                else raise(TYPE("variable and expression, type mismatch",[T,fastype_of e2],[e2]))
        val _ = if fastype_of B = @{typ predicate} then ()
                else raise(TYPE("predicate has wrong type",[fastype_of B],[B]))
        val setT = Type(@{type_name set},[T])
        val supp = Const(@{const_name supp}, distrT --> setT) $ e1
        val absB = Term.abstract_over (Free(v1,T),B) |> (fn t => Term.abstract_over (Free(v2,T),t)) |> (fn t => Abs("z",T,t))
        val B2 = @{const Inf(predicate)} $
                      (Const(@{const_name image}, (T --> @{typ predicate}) --> setT -->  @{typ "predicate set"})
                         $ absB $ supp)
        val sameDistr = @{const classical_subspace} $ HOLogic.mk_eq (e1,e2)
    in
      @{const inf(predicate)} $ sameDistr $ B2
    end
   
fun rndWp2 v1 T1 e1 v2 T2 e2 f B =
  let val distrT1 = Type(@{type_name distr},[T1])
      val distrT2 = Type(@{type_name distr},[T2])
      val T12 = HOLogic.mk_prodT (T1,T2)
      val distrT12 = Type(@{type_name distr},[T12])
      val setT12 = HOLogic.mk_setT T12
      val _ = if fastype_of e1 = distrT1 then ()
              else raise(TYPE("variable and expression, type mismatch",[T1,fastype_of e1],[e1]))
      val _ = if fastype_of e2 = distrT2 then ()
              else raise(TYPE("variable and expression, type mismatch",[T2,fastype_of e2],[e2]))
      val _ = if fastype_of B = @{typ predicate} then ()
              else raise(TYPE("predicate has wrong type",[fastype_of B],[B]))
      val supp = Const(@{const_name supp}, distrT12 --> setT12) $ f
      val absB = B |> absfree (v2,T2) |> absfree (v1,T1)
      val marginal1 = HOLogic.mk_eq (Const(@{const_name map_distr}, (T12-->T1) --> distrT12 --> distrT1) $
          Const(@{const_name fst}, T12-->T1) $ f, e1)
      val marginal2 = HOLogic.mk_eq (Const(@{const_name map_distr}, (T12-->T2) --> distrT12 --> distrT2) $
          Const(@{const_name snd}, T12-->T2) $ f, e2)
      val marginals = @{const classical_subspace} $ (HOLogic.mk_conj (marginal1,marginal2))
      val B2 = @{const Inf(predicate)} $
               (Const(@{const_name image}, (T12 --> @{typ predicate}) --> setT12 -->  @{typ "predicate set"}) $
                 (Const(@{const_name case_prod}, (T1-->T2--> @{typ predicate}) --> (T12--> @{typ predicate})) $
                  absB) $ supp)
  in
    @{const inf(predicate)} $ marginals $ B2
  end

(* val _ = rndWp2 "x1" @{typ int} @{term "uniform {x1::int}"} "x2" @{typ bool} @{term "uniform {x2::bool}"} 
@{term "uniform UNIV :: (int*bool)distr"} @{term "Cla[(x1::int)=0 \<and> x2]"}
|> Thm.cterm_of @{context} |> @{print} *)


fun mk_quantum_equality Q1 Q2 T =
  let val opT = mk_bounded2T T
      val qvT = mk_variablesT T                                        
  in
  Const(@{const_name quantum_equality_full}, opT --> qvT --> opT --> qvT --> @{typ predicate}) $
    Const(@{const_name idOp}, opT) $ Q1 $ Const(@{const_name idOp}, opT) $ Q2
  end

(* returns a term t' such that t'\<and>remove = t\<and>remove is true *)
fun removeAnd (remove:term) (t:term) = 
  if t=remove then @{const True} else
  case t of
    (c as Const(@{const_name conj},_)) $ a $ b => c $ removeAnd remove a $ removeAnd remove b
  | (c as Const(@{const_name inf},_)) $ a $ b => c $ removeAnd remove a $ removeAnd remove b
  | (c as Const(@{const_name classical_subspace},_)) $ a => c $ removeAnd remove a
  | _ => t

(* returns a term t' such that t'\<sqinter>remove = t\<sqinter>remove is true *)
fun removeInf (remove:term) (t:term) = 
  if t=remove then Const(@{const_name top}, fastype_of t) else
  case t of
    (c as Const(@{const_name inf},_)) $ a $ b => c $ removeInf remove a $ removeInf remove b
(*  | Const(@{const_name classical_subspace},_) $ a =>
      (case remove of
        Const(@{const_name classical_subspace},_) $ r => @{const classical_subspace} $ removeAnd r a
      | _ => t) *)
  | _ => t

fun tidyTrueTop' (Const(@{const_name inf},_) $ Const(@{const_name top},_) $ t) = tidyTrueTop' t
  | tidyTrueTop' (Const(@{const_name inf},_) $ t $ Const(@{const_name top},_)) = tidyTrueTop' t
  | tidyTrueTop' (Const(@{const_name conj},_) $ Const(@{const_name True},_) $ t) = tidyTrueTop' t
  | tidyTrueTop' (Const(@{const_name conj},_) $ t $ Const(@{const_name True},_)) = tidyTrueTop' t
  | tidyTrueTop' (Const(@{const_name classical_subspace},_) $ Const(@{const_name True},_)) = @{const top(predicate)}
  | tidyTrueTop' (t$u) = tidyTrueTop' t $ tidyTrueTop' u
  | tidyTrueTop' (Abs(v,T,body)) = Abs(v,T,tidyTrueTop' body)
  | tidyTrueTop' t = t

fun tidyTrueTop t =
  let val t' = tidyTrueTop' t
  in
    if t=t' then t else tidyTrueTop t'
  end

(* open List *)

fun callWp cvars1 cvars2 qvars1 qvars2 B =
  let (* val cvarsEq = HOLogic.mk_eq (HOLogic.mk_tuple cvars1, HOLogic.mk_tuple cvars2)
      val claCvarsEq = @{const classical_subspace} $ cvarsEq *)
      val (qvars1',qvars1T) = variables qvars1
      val (qvars2',qvars2T) = variables qvars2
      val (qvars12',qvars12T) = variables (qvars1 @ qvars2)
      val _ = if qvars1T <> qvars2T then raise TYPE("mismatch",[qvars1T,qvars2T],[]) else ()
      val qvarsEq = if qvars1=[] then @{const top(predicate)} else mk_quantum_equality qvars1' qvars2' qvars1T
      val B0 = B |> removeInf qvarsEq (* invariant: post \<sqinter> qvarsEq \<Longrightarrow> original post *)

      val cvarEqs = ListPair.zip (cvars1,cvars2) |> map HOLogic.mk_eq
      val claCvarsEq = @{const classical_subspace} $ mk_conjs cvarEqs
      val B' = fold (fn eq => fn post => removeAnd eq post) cvarEqs B0
             (* post \<sqinter> qvarsEq \<sqinter> claCvarsEq ==> original post *)
      
      val freeCVars = Term.add_frees B' [] |> inter (op=) (cvars1 @ cvars2 |> map Term.dest_Free) |> rev
      fun inf_over (v,T) p = mk_INFIMUM (HOLogic.mk_UNIV T) (Term.absfree (v,T) p)
      val usedEqs = filter (fn (v1,v2) => member op= freeCVars (dest_Free v1) andalso member op= freeCVars (dest_Free v2))
                    (ListPair.zip (cvars1,cvars2)) |> map HOLogic.mk_eq |> mk_conjs 
      val B'' = @{const plus(predicate)} $ (@{const classical_subspace} $ HOLogic.mk_not usedEqs) $ B'
             (* post \<sqinter> qvarsEq \<sqinter> claCvarsEq ==> original post *)
      val B''' = fold inf_over freeCVars B''
             (* post \<sqinter> qvarsEq \<sqinter> claCvarsEq ==> original post *)

      val wp = @{const inf(predicate)} $ (@{const inf(predicate)} $ B''' $ claCvarsEq) $ qvarsEq
      val wp = tidyTrueTop wp

      val colocality = Const(@{const_name colocal_pred_qvars},
            @{typ predicate} --> mk_variablesT qvars12T --> HOLogic.boolT)
          $ B' $ qvars12'
  in
    (wp, colocality)
  end


fun simp_any t ctx =
  let val ct = Thm.cterm_of ctx t
      val ct_eq = Simplifier.asm_full_rewrite ctx ct |> Thm.prop_of
      val (lhs,rhs) = Logic.dest_equals ct_eq
      val _ = if lhs<>t then raise TERM("conversion returned wrong lhs\n",[t,lhs,rhs]) else ()
  in
    rhs
  end

fun simp_prop t ctx = 
  let val ct = Thm.cterm_of ctx t
      val goal = Goal.init ct
      val result = SINGLE (asm_full_simp_tac ctx 1) goal
  in
    case result of
      NONE => raise TERM("asm_full_simp_tac failed",[t])
    | SOME thm => case Thm.prems_of thm of
                    [t'] => t'
                  | [] => @{prop True}
                  | _ => raise THM("asm_full_simp_tac produced multiple subgoals",0,[thm])
  end       

fun simp_bool t ctx =
  let val prop = HOLogic.mk_Trueprop t
      val res = simp_prop prop ctx
  in
    case res of
      (Const (@{const_name Trueprop}, _) $ P) => P
    | _ => raise TERM("simp_prop did not return a term starting with Trueprop",[t,res])
  end

fun simp t facts ctx =
  let val ctx'  = fold (fn name => fn ctx => ctx addsimps (Proof_Context.get_thms ctx name)) facts ctx
  in case fastype_of t of
        Type(@{type_name prop},_) => simp_prop t ctx'
      | Type(@{type_name bool},_) => simp_bool t ctx'
      | _ => simp_any t ctx'
  end

(* fun simp t facts ctx =
  let val ct = Thm.cterm_of ctx t
      val ctx'  = fold (fn name => fn ctx => ctx addsimps (Proof_Context.get_thms ctx name)) facts ctx
      val ct_eq = Simplifier.rewrite ctx' ct |> Thm.prop_of
      val (lhs,rhs) = Logic.dest_equals ct_eq
      val _ = if lhs<>t then raise TERM("conversion returned wrong lhs\n",[t,lhs,rhs]) else ()
  in
    rhs
  end *)

fun dest_numeral_syntax (Const (@{const_syntax "Num.num.One"}, _)) = 1
  | dest_numeral_syntax (Const (@{const_syntax "Num.num.Bit0"}, _) $ bs) = 2 * dest_numeral_syntax bs
  | dest_numeral_syntax (Const (@{const_syntax "Num.num.Bit1"}, _) $ bs) = 2 * dest_numeral_syntax bs + 1
  | dest_numeral_syntax t = raise TERM ("dest_num_syntax", [t]);
fun dest_char_syntax t =
  case t of
      Const (@{const_syntax Groups.zero_class.zero}, _) => 0
    | (Const (@{const_syntax String.Char}, _) $ t) => dest_numeral_syntax t
    | _ => raise TERM ("dest_char_syntax", [t]);
fun dest_list_syntax (Const (@{const_syntax Nil}, _)) = []
  | dest_list_syntax (Const (@{const_syntax Cons}, _) $ t $ u) = t :: dest_list_syntax u
  | dest_list_syntax t = raise TERM ("dest_list_syntax", [t])
val dest_string_syntax = implode o map (chr o dest_char_syntax) o dest_list_syntax;


fun byQRHLPre cvars qvars =
  let val cEqs = map (fn (v1,v2,T) => HOLogic.mk_eq (Free(v1,T), Free(v2,T))) cvars
      val cEqs' = @{const classical_subspace} $ mk_conjs cEqs
      val (qvars1',qvars1T) = variables (map (fn (v1,_ ,T) => Free(v1,mk_variableT T)) qvars)
      val (qvars2',qvars2T) = variables (map (fn (_ ,v2,T) => Free(v2,mk_variableT T)) qvars)
      val _ = if qvars1T <> qvars2T then raise TYPE("mismatch",[qvars1T,qvars2T],[]) else () (* Shouldn't happen *)
      val qvarsEq = if qvars=[] then @{const top(predicate)} else mk_quantum_equality qvars1' qvars2' qvars1T
  in
    @{const inf(predicate)} $ cEqs' $ qvarsEq
  end

fun addAssumption name term ctx =
  let val _ = if fastype_of term = HOLogic.boolT then ()
              else raise (TYPE("expected a boolean expression",[fastype_of term],[term]))
      val prop = HOLogic.mk_Trueprop term
      val (_,ctx) = Proof_Context.add_assms Assumption.assume_export
                               [((Binding.name name,[]), [(prop,[])])] ctx
  in
    ctx
  end

fun checkType ctx term =
  let val ct = Thm.cterm_of ctx term
  in
    Thm.typ_of_cterm ct
  end

fun fixTac term var =
  let val (typ,body) = dest_All term
      val res = Term.subst_bound (Free(var,typ), body)
  in
  (res,typ)
  end

fun applyRule name goal ctx =
  let val thms = Proof_Context.get_thms ctx name
      val cgoal = Thm.cterm_of ctx (HOLogic.mk_Trueprop goal)
      val goal' = Goal.init cgoal
      val goal'' = case SINGLE (resolve_tac ctx thms 1) goal' of
                    NONE => raise TERM("rule "^name^" could not be applied", [goal])
                   | SOME x => x
      val subgoals = Thm.prems_of goal''
      val subgoals' = map HOLogic.dest_Trueprop subgoals
  in
    (* subgoals' |> map (Thm.cterm_of ctx) |> @{make_string} |> error *)
    subgoals'
  end


datatype varterm = VTCons of varterm * varterm | VTSingle of string*typ | VTUnit

fun parse_varterm (Const(@{const_name variable_concat},_) $ a $ b) = VTCons (parse_varterm a, parse_varterm b)
  | parse_varterm (Const(@{const_name variable_singleton},_) $ Free(n,Type(@{type_name variable},[T]))) = VTSingle (n,T)
  | parse_varterm (Const(@{const_name variable_unit},_)) = VTUnit
  | parse_varterm t = raise TERM("not a variables expression",[t])

fun mk_varterm (VTUnit) = (@{const variable_unit}, @{typ unit})
  | mk_varterm (VTCons(a,b)) = let
      val (vta,Ta) = mk_varterm a
      val (vtb,Tb) = mk_varterm b
    in
      (Const(@{const_name variable_concat}, 
        mk_variablesT Ta --> mk_variablesT Tb --> mk_variablesT (HOLogic.mk_prodT(Ta,Tb))) $ vta $ vtb,
       HOLogic.mk_prodT(Ta,Tb))
    end
  | mk_varterm (VTSingle(n,T)) = 
      (Const(@{const_name variable_singleton}, mk_variableT T --> mk_variablesT T) $ 
          Free(n,Type(@{type_name variable},[T])),T)

fun type_of_varterm (VTUnit) = @{typ unit}
  | type_of_varterm (VTCons(a,b)) = HOLogic.mk_prodT(type_of_varterm a, type_of_varterm b)
  | type_of_varterm (VTSingle(_,T)) = T

fun varterm_from_list [] = VTUnit
  | varterm_from_list [nT] = VTSingle nT
  | varterm_from_list (nT::xs) = VTCons (VTSingle nT, varterm_from_list xs)

fun vars_in_varterm (VTCons(a,b)) = vars_in_varterm a @ vars_in_varterm b
  | vars_in_varterm (VTSingle nT) = [nT]
  | vars_in_varterm VTUnit = []

fun parse_varlist t =
  let val vt = parse_varterm t
      fun tol (VTSingle nT) = [nT]
        | tol VTUnit = []
        | tol (VTCons (VTSingle _, VTUnit)) = raise TERM("not an explicit variable list",[t])
        | tol (VTCons (VTSingle nT, rest)) = nT :: tol rest
        | tol (VTCons _) = raise TERM("not an explicit variable list",[t])
  in
    tol vt
  end

(* Checks if term is a (not necessarily explict) variable list *)
fun is_varlist (Const(@{const_name variable_unit},_)) = true
  | is_varlist (Const(@{const_name variable_singleton},_) $ _) = true
  | is_varlist (Const(@{const_name variable_concat},_) $ _ $ Const(@{const_name variable_unit},_)) = false
  | is_varlist (Const(@{const_name variable_concat},_) $ Const(@{const_name variable_singleton},_) $ rest) = is_varlist rest
  | is_varlist _ = false

fun nameq ((x:string,_:typ), (y,_:typ)) = x=y

fun missing_in_varterm vt1 vt2 = let
  val v1 = vars_in_varterm vt1
  val v2 = vars_in_varterm vt2
  val miss = subtract nameq v1 v2
in
  varterm_from_list miss |> mk_varterm |> fst
end

fun variable_extension_hint_conv ctx ct = let
val (lift,S,Q,R) = case Thm.term_of ct of
    (Const(@{const_name join_variables_hint},_)) $ (Const(lift,_) $ S $ Q) $ R => (lift,S,Q,R)
    | _ => raise CTERM("variable_extension_hint_conv: wrong shape",[ct])
val conv_rule = case lift of @{const_name liftSpace} => @{thm join_variables_hint_subspace_conv_aux}
                           | @{const_name liftOp} => @{thm join_variables_hint_bounded_conv_aux}
                           | _ => raise CTERM("variable_extension_hint_conv: lift is "^lift, [ct])
val vtQ = parse_varterm Q
val vtR = parse_varterm R
val miss = missing_in_varterm vtQ vtR |> Thm.cterm_of ctx
val rule = infer_instantiate ctx 
  [(("S",0),Thm.cterm_of ctx S),
   (("R",0),Thm.cterm_of ctx R),
   (("R'",0),miss),
   (("Q",0),Thm.cterm_of ctx Q)]
  conv_rule 
in
rule
end

fun sort_variables_step (VTSingle _) = NONE
  | sort_variables_step (VTCons (v1 as VTSingle(n1,T1), v2 as VTSingle(n2,T2))) =
      if n1<=n2 then NONE
      else SOME(Const(@{const_name comm_op}, 
            mk_boundedT (HOLogic.mk_prodT(T1,T2)) (HOLogic.mk_prodT(T2,T1))), 
          VTCons (v2,v1))
  | sort_variables_step (vt as (VTCons (v1 as VTSingle(n1,T1), VTCons (v2 as VTSingle(n2,T2), rest)))) =
      if n1<=n2 then sort_variables_step_in vt
      else let val restT = type_of_varterm rest in
        SOME(Const(@{const_name comm_op_pfx},
            mk_boundedT (HOLogic.mk_prodT (T1, HOLogic.mk_prodT (T2,restT))) (HOLogic.mk_prodT (T2, HOLogic.mk_prodT (T1,restT)))),
          VTCons(v2, VTCons(v1,rest)))
      end
  | sort_variables_step (VTCons (VTCons(vt1,vt2), vt3)) =
      let val T1 = type_of_varterm vt1
          val T2 = type_of_varterm vt2
          val T3 = type_of_varterm vt3
      in
        SOME(Const(@{const_name assoc_op_adj},
            mk_boundedT (HOLogic.mk_prodT (HOLogic.mk_prodT(T1,T2), T3)) (HOLogic.mk_prodT (T1, HOLogic.mk_prodT(T2,T3)))),
          VTCons(vt1, VTCons(vt2, vt3)))
      end
  | sort_variables_step (vt as VTCons (VTSingle _, _)) = sort_variables_step_in vt
  | sort_variables_step VTUnit = NONE
  | sort_variables_step (VTCons (vt, VTUnit)) =
      let val T = type_of_varterm vt in
        SOME(Const(@{const_name remove_qvar_unit_op},
          mk_boundedT (HOLogic.mk_prodT(T,HOLogic.unitT)) T),
          vt) end
  | sort_variables_step (VTCons (VTUnit, vt)) =
      let val T = type_of_varterm vt in
        SOME(Const(@{const_name remove_qvar_unit_op2},
          mk_boundedT (HOLogic.mk_prodT(HOLogic.unitT,T)) T),
          vt) end

(* sort_variables_step_in must be called on term "variable_concat [[q]] rest" *)
and sort_variables_step_in (VTCons(v1 as VTSingle(_,T1), rest)) =
  (case sort_variables_step rest of
    NONE => NONE
  | SOME(rest_op, rest_vt) =>
    let val rest_opT = fastype_of rest_op
        val (rest_op_inT,rest_op_outT) = dest_boundedT rest_opT
    in
      SOME(Const(@{const_name id_tensor}, 
          rest_opT --> mk_boundedT (HOLogic.mk_prodT(T1,rest_op_inT)) (HOLogic.mk_prodT(T1,rest_op_outT))) $
          rest_op,
        VTCons(v1, rest_vt))
    end)
  | sort_variables_step_in vt = raise TERM("sort_variables_step_in", [mk_varterm vt |> fst])

fun sort_variables vt =
  case sort_variables_step vt of
    NONE => NONE
  | SOME(A,vt') =>
      case sort_variables vt' of
        NONE => SOME(A,vt')
      | SOME(A',vt'') => (* A'\<cdot>A *)
          let val AT = fastype_of A
              val A'T = fastype_of A'
              val (inT,_) = dest_boundedT AT
              val (_,outT) = dest_boundedT A'T
              val (vt't,vt'T) = mk_varterm vt'
          in
            SOME(Const(@{const_name qvar_trafo_mult}, mk_variablesT vt'T --> A'T --> AT --> mk_boundedT inT outT) $
              vt't $ A' $ A,
              vt'')
          end
        
(* Expects: ct = sort_variables_hint (x>>Q) *)
fun sort_variables_hint_conv ctx ct = let
val (lift,S,Q) = case Thm.term_of ct of
    (Const(@{const_name sort_variables_hint},_)) $ (Const(lift,_) $ S $ Q) => (lift,S,Q)
    | _ => raise CTERM("sort_variables_hint_hint_conv: wrong shape",[ct])
val conv_rule = case lift of @{const_name liftSpace} => @{thm sort_variables_hint_subspace_conv_aux}
                           | @{const_name liftOp} => @{thm sort_variables_hint_bounded_conv_aux}
                           | _ => raise CTERM("sort_variables_hint_hint_conv: lift is "^lift, [ct])
val vtQ = parse_varterm Q
in
  case sort_variables vtQ of
    NONE => Conv.rewr_conv @{thm sort_variables_hint_remove_aux} ct
  | SOME(A,vt) =>
        infer_instantiate ctx 
          [(("S",0),Thm.cterm_of ctx S),
           (("A",0),Thm.cterm_of ctx A),
           (("R'",0),mk_varterm vt |> fst |> Thm.cterm_of ctx),
           (("Q",0),Thm.cterm_of ctx Q)] conv_rule
end

fun variable_rewriting_simproc _ ctx ct =
  SOME (variable_extension_hint_conv ctx ct)
  handle CTERM _ => 
    SOME (sort_variables_hint_conv ctx ct)
    handle CTERM _ => NONE


(* fun warn_colocal_simproc _ _ ct = 
  let 
      val Q = Thm.term_of ct |> Term.dest_comb |> snd
      val vs = parse_varterm Q |> vars_in_varterm
      val _ = if not (has_duplicates nameq vs) 
              then warning ("Please add to simplifier: "^ @{make_string} ct^
                      " (or remove simproc warn_colocal to remove these warnings)")
              else ()
  in
    NONE
  end 
  handle TERM _ => NONE *)


local
  fun mk_var_eq (v as Const ("_constrain", _) $ Free (n, _) $ Free _) =
      @{const HOL.eq("char list")} $ (Const (@{const_name variable_name}, dummyT) $ v) $ HOLogic.mk_string n
    | mk_var_eq t = raise (TERM("the argument to declared_qvars must contain only free variables",[t]))

  fun declared_qvars_parse_tr' (Const (@{syntax_const "_variable_list_args"}, _) $ v $ vs)
    = mk_var_eq v :: declared_qvars_parse_tr' vs
    | declared_qvars_parse_tr' (Const (@{syntax_const "_variable_list_arg"}, _) $ v)
    = [mk_var_eq v]
| declared_qvars_parse_tr' t = raise (TERM("declared_qvars_parse_tr'",[t]))
in
  fun declared_qvars_parse_tr _ [vs] = mk_conjs (declared_qvars_parse_tr' vs)
    | declared_qvars_parse_tr _ ts = raise (TERM("declared_qvars_parse_tr", ts))
end

structure WarnDeclaredQvarsData = Proof_Data
(
  type T = bool (* Within a nested call to the simproc *)
  fun init _ = false
)

fun warn_declared_qvars_simproc _ ctx ct = 
  if WarnDeclaredQvarsData.get ctx then NONE
  else case Thm.term_of ct of
      Const(@{const_name variable_name}, _) $ Free (n,_) =>
        let val eq = Raw_Simplifier.rewrite_cterm (false,false,false) (fn _ => fn _ => NONE) (WarnDeclaredQvarsData.put true ctx) ct 
            val rhs = eq |> Thm.prop_of |> Logic.dest_equals |> snd
        in
            case rhs of Const(@{const_name variable_name}, _) $ _ => 
                            (warning ("Please add to simplifier: declared_qvars \<lbrakk>"^n
                                        ^"\<rbrakk> (or remove simproc warn_declared_qvars to remove these warnings)");
                            NONE)
                      | _ => SOME eq
        end
    | _ => NONE


datatype vartype = Classical | Quantum
structure VarTypes = Proof_Data
(
  type T = vartype Symtab.table
  fun init _ = Symtab.empty
)


fun varname_assumption cq bind T = 
  let val qT = mk_variableT T
      val name = Binding.name_of bind
      val name' = if cq=Classical then "var_"^name else name
      val lhs = Const(@{const_name variable_name}, qT --> HOLogic.stringT) $ Free(name',qT)
      val rhs = HOLogic.mk_string name
  in HOLogic.mk_eq (lhs,rhs) |> HOLogic.mk_Trueprop end

fun addQVariableNameAssumption cq bind T ctxt =
  let val assm = varname_assumption cq bind T
      val ctxt1 = Variable.declare_term assm ctxt
      val (_,ctxt2) = Proof_Context.add_assms Assumption.assume_export
                  [((Binding.suffix_name "_varname" bind,[Simplifier.simp_add]), [(assm,[])])] ctxt1
  in
    ctxt2
  end

fun declare_variable ctx bind T cq =
  let val qT = mk_variableT T
      val v = Binding.name_of bind
      val vars = if cq=Classical then [(bind,T),(Binding.suffix_name "1" bind,T),(Binding.suffix_name "2" bind,T),
                                       (bind |> Binding.prefix_name "var_",qT),(bind |> Binding.suffix_name "1" |> Binding.prefix_name "var_",qT),(bind |> Binding.suffix_name "2" |> Binding.prefix_name "var_",qT)]
                                  else [(bind,qT),(Binding.suffix_name "1" bind,qT),(Binding.suffix_name "2" bind,qT)]
      val (_,ctx) = Variable.add_fixes_binding (map fst vars) ctx
      val ctx = fold (fn (v,T) => Variable.declare_term (Free(Binding.name_of v,T))) vars ctx
      val ctx = addQVariableNameAssumption cq bind T ctx
      val ctx = addQVariableNameAssumption cq (Binding.suffix_name "1" bind) T ctx
      val ctx = addQVariableNameAssumption cq (Binding.suffix_name "2" bind) T ctx
      val ctx = VarTypes.map (Symtab.insert op= (v,cq)) ctx
      val ctx = VarTypes.map (Symtab.insert op= (v^"1",cq)) ctx
      val ctx = VarTypes.map (Symtab.insert op= (v^"2",cq)) ctx
  in
    ctx
  end

fun lookup_variable ctx = Symtab.lookup (VarTypes.get ctx)
fun is_classical_variable ctx name = case Symtab.lookup (VarTypes.get ctx) name of
  SOME Classical => true
  | _ => false

fun declare_variable_lthy name vartype = 
  Local_Theory.declaration {pervasive=true, syntax=false} (fn _ => 
    Context.mapping I (
      VarTypes.map (Symtab.insert op= (name,vartype)) #>
      VarTypes.map (Symtab.insert op= (name^"1",vartype)) #>
      VarTypes.map (Symtab.insert op= (name^"2",vartype))))

fun variables vars gthy = 
let fun elems0 idx = [
      Element.Fixes (map_filter (fn (cq,bind,T) => 
           case cq of Classical => SOME (bind |> Binding.suffix_name idx, SOME T, Mixfix.NoSyn) | Quantum => NONE) vars),
      Element.Fixes (map (fn (cq,bind,T) => (bind |> (case cq of Classical => Binding.prefix_name "var_" | Quantum => I)
                                                  |> Binding.suffix_name idx, SOME (mk_variableT T), Mixfix.NoSyn)) vars),
      Element.Assumes (map (fn (cq,bind,T) => ((Binding.suffix_name (idx^"_varname") bind, @{attributes [simp]}),
                             [(varname_assumption cq (Binding.suffix_name idx bind) T, [])])) vars)]
    val elems = map elems0 ["", "1", "2"] |> List.concat
    (* val (_,lthy) = Bundle.context [] elems gthy *)
    val (_,lthy) = Expression.add_locale (Binding.name ("variables_"^string_of_int(serial()))) Binding.empty ([],[]) elems gthy
    val lthy2 = fold (fn (cq,bind,_) => fn lthy' => declare_variable_lthy (Binding.name_of bind) cq lthy') vars lthy
in lthy2 end

fun variables_cmd vars thy = 
  let (* val ctxt = Context.proof_of gthy *)
      val vars' = map (fn (a,b,c) => (a,b,Syntax.read_typ_global thy c)) vars
  in
    variables vars' thy
  end

val parse_classical_quantum = (Parse.reserved "classical" >> K Classical) || (Parse.reserved "quantum" >> K Quantum)
val _ =
  Outer_Syntax.command @{command_keyword variables} "declare quantum/classical variables"
    ((Parse.and_list (parse_classical_quantum -- Args.binding --| Parse.$$$ "::" -- Parse.typ >> (fn ((a,b),c) => (a,b,c))) >> 
      (fn vars => Toplevel.begin_local_theory true (variables_cmd vars)))
        --| Parse.begin)

end
