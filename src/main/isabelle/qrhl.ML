structure QRHL =
struct

fun mk_qvariablesT T = Type(@{type_name qvariables}, [T])
fun mk_qvariableT T = Type(@{type_name qvariable}, [T])
fun mk_stateT T = Type(@{type_name state}, [T])
fun mk_boundedT T T' = Type(@{type_name bounded}, [T,T'])
fun mk_bounded2T T = mk_boundedT T T
fun mk_measurementT T T' = Type(@{type_name measurement}, [T,T'])
(* fun mk_projectorT T = Type(@{type_name projector}, [T]) *)
fun mk_conjs [] = @{const True}
  | mk_conjs [t] = t
  | mk_conjs (t::ts) = @{const conj} $ t $ mk_conjs ts

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

fun qvariables [] = (@{const qvariable_unit},@{typ unit})
  | qvariables [v] = 
        let val vT = fastype_of v
            val vT' = case vT of Type(@{type_name qvariable},[vT']) => vT' | _ => raise TYPE("expecting a qvariable",[vT],[v])
        in
          (Const(@{const_name qvariable_singleton}, vT --> Type(@{type_name qvariables}, [vT'])) $ v,
           vT')
        end
  | qvariables (v::vs) = 
        let val (vs',vsT) = qvariables vs
            (* val (v',vT) = qvariables [v] *)
            val vT = fastype_of v
            val vT' = case vT of Type(@{type_name qvariable},[vT']) => vT' | _ => raise TYPE("expecting a qvariable",[vT],[v])
            val prodT = HOLogic.mk_prodT (vT',vsT)
        in
          (Const(@{const_name qvariable_concat}, 
              mk_qvariablesT vT' --> mk_qvariablesT vsT --> mk_qvariablesT prodT) $
            (Const(@{const_name qvariable_singleton}, vT --> mk_qvariablesT vT') $ v) $ vs',
            prodT)
        end
  
fun qinitWp post e Q =
  let val (vs,vsT) = qvariables Q in
    Const(@{const_name space_div}, @{typ predicate} --> mk_stateT vsT --> mk_qvariablesT vsT --> @{typ predicate}) $
      post $ e $ vs
  end

fun qapplyWp post e Q =
  let val (vs,vsT) = qvariables Q 
      val unitary = @{const classical_subspace} $ 
          (Const(@{const_name isometry}, mk_bounded2T vsT --> HOLogic.boolT) $ e)
      val e' = Const(@{const_name liftOp}, mk_bounded2T vsT --> mk_qvariablesT vsT --> @{typ "(mem2,mem2) bounded"}) $ e $ vs
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
      val (vs,vsT) = qvariables Q
      val measT = mk_measurementT resT vsT
      val e_z = Const(@{const_name mproj}, measT --> resT --> mk_bounded2T vsT)
                  $ e $ Bound(0)
      val lift_e_z = Const(@{const_name liftOp}, mk_bounded2T vsT --> mk_qvariablesT vsT --> @{typ "(mem2,mem2) bounded"})
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


fun addQVariableNameAssumption name T ctx =
  let val qT = mk_qvariableT T
      val lhs = Const(@{const_name variable_name}, qT --> HOLogic.stringT) $ Free(name,qT)
      val rhs = HOLogic.mk_string name
      val assm = Logic.mk_equals (lhs,rhs)
      val (_,ctx) = Proof_Context.add_assms Assumption.assume_export
                    [((Binding.name name,[Simplifier.simp_add]), [(assm,[])])] ctx
  in
    ctx
  end

fun mk_quantum_equality Q1 Q2 T =
  let val opT = mk_bounded2T T
      val qvT = mk_qvariablesT T                                        
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
      val (qvars1',qvars1T) = qvariables qvars1
      val (qvars2',qvars2T) = qvariables qvars2
      val (qvars12',qvars12T) = qvariables (qvars1 @ qvars2)
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

      val colocality = Const(@{const_name colocal_ass_qvars},
            @{typ predicate} --> mk_qvariablesT qvars12T --> HOLogic.boolT)
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
      val (qvars1',qvars1T) = qvariables (map (fn (v1,_ ,T) => Free(v1,mk_qvariableT T)) qvars)
      val (qvars2',qvars2T) = qvariables (map (fn (_ ,v2,T) => Free(v2,mk_qvariableT T)) qvars)
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



end
