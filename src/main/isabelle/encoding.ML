structure Encoding = 
struct

fun expression_to_term t =
  let val (vs,e) = case t of Const(@{const_name expression},_) $ vs $ e => (vs,e) | _ => raise (TERM("expression_to_term",[t]))
      val vars = QRHL.parse_varterm vs |> QRHL.vars_in_varterm 
          |> map (fn (x,T) => Free (String.substring (x,0,String.size x - 4),T)) (* unsafe, not checking whether the var name is wellformed *)
          |> @{print}
      val e' = e $ HOLogic.mk_tuple vars
  in
    e'
  end

fun add_index_to_expression t left =
  let val suffix = if left then "1_var" else "2_var"
      fun rename (Free(x,T)) =  Free(String.substring (x,0,String.size x - 4)^suffix,T)
        | rename t = t
      val (vs,e,T) = case t of Const(@{const_name expression},T) $ vs $ e => (vs,e,T) | _ => raise (TERM("add_index_to_expression",[t]))
      val vs = Term.map_aterms rename vs
  in
    Const(@{const_name expression},T) $ vs $ e
  end
      


end
