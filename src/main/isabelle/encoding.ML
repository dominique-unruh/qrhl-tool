structure Encoding = 
struct

fun mk_expressionT T = Type(@{type_name expression}, [T])

(*
datatype cvariable = CVariable of string * typ
fun cvar_typ (CVariable (_,T)) = T
datatype qvariable = QVariable of string * typ
fun qvar_typ (QVariable (_,T)) = T

type expression = term

datatype statement = 
  Block of statement list
| Assign of cvariable * expression
| Sample of cvariable * expression
| IfThenElse of expression * statement list * statement list
| While of expression * statement list
| QInit of qvariable list * expression
| QApply of qvariable list * expression
| Measurement of cvariable * qvariable list * expression
| Call of string

type block = statement list

fun statement_welltyped (_:Proof.context) s =
let fun wt (Block s) = forall wt s
      | wt (Assign (x, e)) = fastype_of e = cvar_typ x
      | wt (Sample (x, e)) = fastype_of e = QRHL.mk_distrT (cvar_typ x)
      | wt (IfThenElse (e,b1,b2)) = fastype_of e = HOLogic.boolT andalso forall wt b1 andalso forall wt b2
      | wt (While (e,b)) = fastype_of e = HOLogic.boolT andalso forall wt b
      | wt (QInit (qvs,e)) = fastype_of e = QRHL.mk_vectorT (HOLogic.mk_tupleT (map qvar_typ qvs))
      | wt (QApply (qvs,e)) = fastype_of e = QRHL.mk_bounded2T (HOLogic.mk_tupleT (map qvar_typ qvs))
      | wt (Measurement (x,qvs,e)) = fastype_of e = QRHL.mk_measurementT (cvar_typ x) (HOLogic.mk_tupleT (map qvar_typ qvs))
      | wt (Call _) = true
in
  wt s
end
*)

fun expression_to_term t =
  let val (vs,e) = case t of Const(@{const_name expression},_) $ vs $ e => (vs,e) | _ => raise (TERM("expression_to_term",[t]))
      val vars = QRHL.parse_varterm vs |> QRHL.vars_in_varterm 
          |> map (fn (x,T) => Free (String.substring (x,0,String.size x - 4),T)) (* unsafe, not checking whether the var name is wellformed *)
          |> @{print}
      val e' = e $ HOLogic.mk_tuple vars
  in
    e'
  end

(*
fun encode_cvar (CVariable(n,T)) = Free(n,QRHL.mk_qvariableT T)
fun encode_qvar (QVariable(n,T)) = Free(n,QRHL.mk_qvariableT T)
fun encode_qvars qvs : term = QRHL.qvariables (map encode_qvar qvs) |> fst

fun encode_expression e = error "nyi"

fun encode_statement (Block b) : term = encode_block b
  | encode_statement (Assign (x,e)) = 
      Const(@{const_name assign}, QRHL.mk_qvariableT (cvar_typ x) --> mk_expressionT (cvar_typ x) --> @{typ program}) $
      encode_cvar x $ encode_expression e 
  | encode_statement (Sample (x,e)) = 
      Const(@{const_name sample}, QRHL.mk_qvariableT (cvar_typ x) --> mk_expressionT (cvar_typ x |> QRHL.mk_distrT) --> @{typ program}) $
      encode_cvar x $ encode_expression e 
  | encode_statement (IfThenElse (e,b1,b2)) = 
      @{const ifthenelse} $ encode_expression e $ encode_block b1 $ encode_block b2
  | encode_statement (While (e,b)) = 
      @{const while} $ encode_expression e $ encode_block b
  | encode_statement (QInit (qvs,e)) = 
      Const(@{const_name qinit}, QRHL.mk_qvariablesT (HOLogic.mk_tupleT (map qvar_typ qvs))
              --> mk_expressionT (QRHL.mk_vectorT (HOLogic.mk_tupleT (map qvar_typ qvs)))
              --> @{typ program}) $
        encode_qvars qvs $ encode_expression e
  | encode_statement (QApply (qvs,e)) =  
      Const(@{const_name qapply}, QRHL.mk_qvariablesT (HOLogic.mk_tupleT (map qvar_typ qvs))
              --> mk_expressionT (QRHL.mk_bounded2T (HOLogic.mk_tupleT (map qvar_typ qvs)))
              --> @{typ program}) $
        encode_qvars qvs $ encode_expression e
  | encode_statement (Measurement (x,qvs,e)) = 
      Const(@{const_name measurement}, QRHL.mk_qvariableT (cvar_typ x)
              --> QRHL.mk_qvariablesT (HOLogic.mk_tupleT (map qvar_typ qvs))
              --> mk_expressionT (QRHL.mk_measurementT (cvar_typ x) (HOLogic.mk_tupleT (map qvar_typ qvs)))
              --> @{typ program}) $
        encode_cvar x $ encode_qvars qvs $ encode_expression e
  | encode_statement (Call p) = Free(p,@{typ program})
and encode_block [] : term = @{const skip}
  | encode_block s = foldl1 (fn (a,b) => @{const sequence} $ a $ b) (map encode_statement s)
  *)

(* val _ = IfThenElse (@{term "1=2"}, [Assign (CVariable("x",@{typ int}),@{term "1::int"})], 
    [QInit ([QVariable("q",@{typ nat}),QVariable("r",@{typ int})],@{term "a::(nat*int) vector"})]) 
|> encode_statement |> @{print}
 *)

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
