structure Programs = struct

datatype call = CALL of string * call list

datatype statement = 
  Block of statement list
| Assign of string * term
| Sample of string * term
| Call of call
| Measurement of string * string list * term
| QInit of string list * term
| QApply of string list * term
| IfThenElse of term * statement list * statement list
| While of term * statement list

fun the_block (Block stmts) = stmts
  | the_block _ = error "the_block"

end
