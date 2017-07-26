structure QRHL =
struct

fun mk_qvariablesT T = Type(@{type_name qvariables}, [T])
fun mk_qvariableT T = Type(@{type_name qvariable}, [T])
fun mk_stateT T = Type(@{type_name state}, [T])
fun mk_isometryT T T' = Type(@{type_name isometry}, [T,T'])
fun mk_isometry2T T = mk_isometryT T T
fun mk_measurementT T T' = Type(@{type_name measurement}, [T,T'])
fun mk_projectorT T = Type(@{type_name projector}, [T])
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


fun qvariables [] = (@{term "qvariable_unit"},@{typ unit})
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
          (Const(@{const_name qvariable_cons}, vT --> mk_qvariablesT vsT --> 
              mk_qvariablesT prodT) $ v $ vs',
            prodT)
        end
  
fun qinitWp post e Q =
  let val (vs,vsT) = qvariables Q in
    Const(@{const_name space_div}, @{typ assertion} --> mk_stateT vsT --> mk_qvariablesT vsT --> @{typ assertion}) $
      post $ e $ vs
  end

fun qapplyWp post e Q =
  let val (vs,vsT) = qvariables Q 
      val e' = Const(@{const_name liftIso}, mk_isometry2T vsT --> mk_qvariablesT vsT --> @{typ "mem2 isometry2"}) $ e $ vs
      val im_e' = @{const imageIso(mem2,mem2)} $ e'
      val adj_e' = @{term "adjoint :: _ \<Rightarrow> mem2 isometry2"} $ e'
      val post_im_e' = @{const inf(assertion)} $ post $ im_e'
  in
    @{term "applyIsoSpace :: mem2 isometry2 \<Rightarrow> _ \<Rightarrow> _"} $ adj_e' $ post_im_e'
  end

fun measureWp B x e Q =
  let val B_z = abstract_over(x,B)
      val (_,resT) = dest_Free x
      val (vs,vsT) = qvariables Q
      val measT = mk_measurementT resT vsT
      val e_z = Const(@{const_name mproj}, measT --> resT --> mk_projectorT vsT)
                  $ e $ Bound(0)
      val lift_e_z = Const(@{const_name liftProj}, mk_projectorT vsT --> mk_qvariablesT vsT --> @{typ "mem2 projector"})
                    $ e_z $ vs
      val im_e_z = @{const imProj(mem2)} $ lift_e_z
      val Be = @{const plus(assertion)} $ (@{const inf(assertion)} $ B_z $ im_e_z) $ (@{const ortho(mem2)} $ im_e_z)
      val Inf_Be = mk_INFIMUM (Const(@{const_name top}, HOLogic.mk_setT resT)) (Abs("z",resT,Be))
      val total = @{const classical_subspace} $ (Const(@{const_name mtotal}, measT --> HOLogic.boolT) $ e)
  in
  @{const inf(assertion)} $ total $ Inf_Be
  end


fun ifWp e thenWp elseWp =
  let val Cla_e = @{const classical_subspace} $ e
      val Cla_not_e = @{const classical_subspace} $ (@{const Not} $ e)
      val then' = @{const plus(assertion)} $ Cla_not_e $ thenWp
      val else' = @{const plus(assertion)} $ Cla_e $ elseWp
  in
    @{const inf(assertion)} $ then' $ else'
  end

fun sampleWp v T e B =
    let val distrT = Type(@{type_name distr},[T])
        val _ = if fastype_of e = distrT then ()
                else raise(TYPE("variable and expression, type mismatch",[T,fastype_of e],[e]))
        val _ = if fastype_of B = @{typ assertion} then ()
                else raise(TYPE("assertion has wrong type",[fastype_of B],[B]))
        val setT = Type(@{type_name set},[T])
        val supp = Const(@{const_name supp}, distrT --> setT) $ e
        val absB = Term.absfree (v,T) B
        val B2 = @{const Inf(assertion)} $
                      (Const(@{const_name image}, (T --> @{typ assertion}) --> setT -->  @{typ "assertion set"})
                         $ absB $ supp)
        val total = @{const classical_subspace} $
             HOLogic.mk_eq (Const(@{const_name weight}, distrT --> @{typ real}) $ e, @{term "1::real"})
    in
      @{term "inf::assertion=>assertion=>assertion"} $ total $ B2
    end
   
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
  let val isoT = mk_isometry2T T
      val qvT = mk_qvariablesT T
  in
  Const(@{const_name quantum_equality_full}, isoT --> qvT --> isoT --> qvT --> @{typ assertion}) $
    Const(@{const_name idIso}, isoT) $ Q1 $ Const(@{const_name idIso}, isoT) $ Q2
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
  | tidyTrueTop' (Const(@{const_name classical_subspace},_) $ Const(@{const_name True},_)) = @{const top(assertion)}
  | tidyTrueTop' (t$u) = tidyTrueTop' t $ tidyTrueTop' u
  | tidyTrueTop' (Abs(v,T,body)) = Abs(v,T,tidyTrueTop' body)
  | tidyTrueTop' t = t

fun tidyTrueTop t =
  let val t' = tidyTrueTop' t
  in
    if t=t' then t else tidyTrueTop t'
  end

(* open List *)

fun callWp cvars1 cvars2 qvars1 qvars2 post =
  let (* val cvarsEq = HOLogic.mk_eq (HOLogic.mk_tuple cvars1, HOLogic.mk_tuple cvars2)
      val claCvarsEq = @{const classical_subspace} $ cvarsEq *)
      val (qvars1',qvars1T) = qvariables qvars1
      val (qvars2',qvars2T) = qvariables qvars2
      val _ = if qvars1T <> qvars2T then raise TYPE("mismatch",[qvars1T,qvars2T],[]) else ()
      val qvarsEq = if qvars1=[] then @{const top(assertion)} else mk_quantum_equality qvars1' qvars2' qvars1T
      val post = post |> removeInf qvarsEq (* invariant: post \<sqinter> qvarsEq \<Longrightarrow> original post *)

      val cvarEqs = ListPair.zip (cvars1,cvars2) |> map HOLogic.mk_eq
      val claCvarsEq = @{const classical_subspace} $ mk_conjs cvarEqs
      val post = fold (fn eq => fn post => removeAnd eq post) cvarEqs post
             (* post \<sqinter> qvarsEq \<sqinter> claCvarsEq ==> original post *)
      
      val freeCVars = Term.add_frees post [] |> inter (op=) (cvars1 @ cvars2 |> map Term.dest_Free) |> rev
      fun inf_over (v,T) p = mk_INFIMUM (HOLogic.mk_UNIV T) (Term.absfree (v,T) p)
      val usedEqs = filter (fn (v1,v2) => member op= freeCVars (dest_Free v1) andalso member op= freeCVars (dest_Free v2))
                    (ListPair.zip (cvars1,cvars2)) |> map HOLogic.mk_eq |> mk_conjs |> @{print}
      val post = @{const plus(assertion)} $ (@{const classical_subspace} $ HOLogic.mk_not usedEqs) $ post
             (* post \<sqinter> qvarsEq \<sqinter> claCvarsEq ==> original post *)
      val post = fold inf_over freeCVars post
             (* post \<sqinter> qvarsEq \<sqinter> claCvarsEq ==> original post *)

      (* TODO: add "cvarEqs ==> " in post *)

      val wp = @{const inf(assertion)} $ (@{const inf(assertion)} $ post $ claCvarsEq) $ qvarsEq
      val wp = tidyTrueTop wp
  in
    ((wp, Term.add_free_names post []), qvarsEq)
    (* wp *)
  end

val _ = callWp [@{term "a1::int"},@{term "b1::int"},@{term "c1::int"}] [@{term "a2::int"},@{term "b2::int"},@{term "c2::int"}] 
               [] [] @{term "Cla[(a1::int)=a2 \<and> (a1\<le>a2) \<and> ((b1::int)=0) \<and> ((b2::int)=0)]"}
|> #1 |> #1
(* |> callWp [@{term "a1::int"},@{term "b1::int"},@{term "c1::int"}] [@{term "a2::int"},@{term "b2::int"},@{term "c2::int"}] 
               [] [] 
|> #1 |> #1 *)
|> Thm.cterm_of @{context}
|> @{print}

end
