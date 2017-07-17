structure QRHL =
struct

fun mk_qvariablesT T = Type(@{type_name qvariables}, [T])
fun mk_qvariableT T = Type(@{type_name qvariable}, [T])
fun mk_stateT T = Type(@{type_name state}, [T])
fun mk_isometryT T T' = Type(@{type_name isometry}, [T,T'])
fun mk_isometry2T T = mk_isometryT T T
fun mk_measurementT T T' = Type(@{type_name measurement}, [T,T'])
fun mk_projectorT T = Type(@{type_name projector}, [T])


fun qvariables [] = (@{term "()"},@{typ unit})
  | qvariables [v] = 
        let val vT = fastype_of v
            val vT' = case vT of Type(@{type_name qvariable},[vT']) => vT' | _ => raise TYPE("expecting a qvariable",[vT],[v])
        in
          (Const(@{const_name qvariable_singleton}, vT --> Type(@{type_name qvariables}, [vT'])) $ v,
           vT')
        end
  | qvariables (v::vs) = 
        let val (vs',vsT) = qvariables vs
            val (v',vT) = qvariables [v]
            val prodT = HOLogic.mk_prodT (vT,vsT)
        in
          (Const(@{const_name qvariable_cons}, mk_qvariablesT vT --> mk_qvariablesT vsT --> 
              mk_qvariablesT prodT) $ v' $ vs',
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

fun mk_INFIMUM A f = 
  let val AT = fastype_of A
      val fT = fastype_of f
      (* val idxT = case AT of Type(@{type_name set}, [T]) => T *)
      val (_,infT) = dest_funT fT 
      val infsetT = HOLogic.mk_setT infT
  in
    Const(@{const_name Inf}, infsetT --> infT) $ (Const(@{const_name image}, fT --> AT --> infsetT) $ f $ A)
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

val _ = measureWp @{term "Cla[x=(x::bool)] :: assertion"} @{term "x::bool"} @{term "a::(bool,bit) measurement"} [@{term "q::bit qvariable"}]
|> Thm.cterm_of @{context}
|> @{print}


end