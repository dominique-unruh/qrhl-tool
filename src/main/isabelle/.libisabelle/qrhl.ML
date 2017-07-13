structure QRHL =
struct

fun mk_qvariablesT T = Type(@{type_name qvariables}, [T])
fun mk_qvariableT T = Type(@{type_name qvariable}, [T])
fun mk_stateT T = Type(@{type_name state}, [T])
fun mk_isometryT T T' = Type(@{type_name isometry}, [T,T'])
fun mk_isometry2T T = mk_isometryT T T

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



val _ = qapplyWp @{term "top :: assertion"} @{term "H"} [@{term "q::bit qvariable"}]
|> Thm.cterm_of @{context}
|> @{print}


end