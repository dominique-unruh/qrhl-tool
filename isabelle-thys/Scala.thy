theory Scala
  imports QRHL.QRHL
begin

setup \<open>
  (Generated_Files.file_type \<^binding>\<open>Scala\<close>
    {ext = "scala",
     make_comment = enclose "/*" "*/",
     make_string = GHC.print_string})
\<close>

generate_file "IsabelleNames.scala" = \<open>
/*

Source is in isabelle-thys/Scala.thy

Run

Run `sbt createIsabelleNames` to recreate/update

to recreate/update

*/

package qrhl.isabellex

object IsabelleTypes {
  val dummy = \<open>\<^type_name>\<open>dummy\<close>\<close> 
  val nat = \<open>\<^type_name>\<open>nat\<close>\<close>
  val int = \<open>\<^type_name>\<open>int\<close>\<close>
  val bool = \<open>\<^type_name>\<open>bool\<close>\<close>
  val set = \<open>\<^type_name>\<open>set\<close>\<close>
  val ell2 = \<open>\<^type_name>\<open>ell2\<close>\<close>
  val bit = \<open>\<^type_name>\<open>bit\<close>\<close>
  val ccsubspace = \<open>\<^type_name>\<open>ccsubspace\<close>\<close>
  val cl = \<open>\<^type_name>\<open>cl\<close>\<close>
  val qu = \<open>\<^type_name>\<open>qu\<close>\<close>
  val program = \<open>\<^type_name>\<open>program\<close>\<close>
  val oracle_program = \<open>\<^type_name>\<open>oracle_program\<close>\<close>
  val distr = \<open>\<^type_name>\<open>distr\<close>\<close>
  val bounded = \<open>\<^type_name>\<open>cblinfun\<close>\<close>
  val measurement = \<open>\<^type_name>\<open>measurement\<close>\<close>
  val list = \<open>\<^type_name>\<open>list\<close>\<close>
  val prop = \<open>\<^type_name>\<open>prop\<close>\<close>
  val unit = \<open>\<^type_name>\<open>unit\<close>\<close>
  val prod = \<open>\<^type_name>\<open>prod\<close>\<close>
  val char = \<open>\<^type_name>\<open>char\<close>\<close>
  val real = \<open>\<^type_name>\<open>real\<close>\<close>
  val program_state = \<open>\<^type_name>\<open>program_state\<close>\<close>
  val infinite = \<open>\<^type_name>\<open>infinite\<close>\<close>
  val cregister = \<open>\<^type_name>\<open>cregister\<close>\<close>
  val qregister = \<open>\<^type_name>\<open>qregister\<close>\<close>
}

object IsabelleConsts {
  val Cons = \<open>\<^const_name>\<open>Cons\<close>\<close>
  val Nil = \<open>\<^const_name>\<open>Nil\<close>\<close>
  val classical_subspace = \<open>\<^const_name>\<open>classical_subspace\<close>\<close>
  val Inf = \<open>\<^const_name>\<open>Inf\<close>\<close>
  val image = \<open>\<^const_name>\<open>image\<close>\<close>
  val inf = \<open>\<^const_name>\<open>inf\<close>\<close>
  val sup = \<open>\<^const_name>\<open>sup\<close>\<close>
  val plus = \<open>\<^const_name>\<open>plus\<close>\<close>
  val bot = \<open>\<^const_name>\<open>bot\<close>\<close>
  val top = \<open>\<^const_name>\<open>top\<close>\<close>
  val zero = \<open>\<^const_name>\<open>zero\<close>\<close>
  val block = \<open>\<^const_name>\<open>block\<close>\<close>
  val instantiateOracles = \<open>\<^const_name>\<open>instantiateOracles\<close>\<close>
  val assign = \<open>\<^const_name>\<open>assign\<close>\<close>
  val sample = \<open>\<^const_name>\<open>sample\<close>\<close>
  val ifthenelse = \<open>\<^const_name>\<open>ifthenelse\<close>\<close>
  val `while` = \<open>\<^const_name>\<open>while\<close>\<close>
  val imp = \<open>\<^const_name>\<open>Pure.imp\<close>\<close>
  val qrhl = \<open>\<^const_name>\<open>qrhl\<close>\<close>
  val qinit = \<open>\<^const_name>\<open>qinit\<close>\<close>
  val qapply = \<open>\<^const_name>\<open>qapply\<close>\<close>
  val implies = \<open>\<^const_name>\<open>HOL.implies\<close>\<close>
  val measurement = \<open>\<^const_name>\<open>measurement\<close>\<close>
  val one = \<open>\<^const_name>\<open>one_class.one\<close>\<close>
  val True = \<open>\<^const_name>\<open>True\<close>\<close>
  val False = \<open>\<^const_name>\<open>False\<close>\<close>
  val probability = \<open>\<^const_name>\<open>probability\<close>\<close>
  val eq = \<open>\<^const_name>\<open>HOL.eq\<close>\<close>
  val numOne = \<open>\<^const_name>\<open>num.One\<close>\<close>
  val numBit0 = \<open>\<^const_name>\<open>num.Bit0\<close>\<close>
  val numBit1 = \<open>\<^const_name>\<open>num.Bit1\<close>\<close>
  val Char = \<open>\<^const_name>\<open>Char\<close>\<close>
  val quantum_equality_full = \<open>\<^const_name>\<open>quantum_equality_full\<close>\<close>
  val idOp = \<open>\<^const_name>\<open>id_cblinfun\<close>\<close>
  val less_eq = \<open>\<^const_name>\<open>less_eq\<close>\<close>
  val tensorOp = \<open>\<^const_name>\<open>tensor_op\<close>\<close>
  val unitary = \<open>\<^const_name>\<open>unitary\<close>\<close>
  val swap_variables_subspace = \<open>\<^const_name>\<open>swap_variables_subspace\<close>\<close>
  val default = \<open>\<^const_name>\<open>default\<close>\<close>
  val ket = \<open>\<^const_name>\<open>ket\<close>\<close>
  val not = \<open>\<^const_name>\<open>Not\<close>\<close>
  val undefined = \<open>\<^const_name>\<open>undefined\<close>\<close>
  val ccspan = \<open>\<^const_name>\<open>ccspan\<close>\<close>
  val apply_qregister_space = \<open>\<^const_name>\<open>apply_qregister_space\<close>\<close>
  val insert = \<open>\<^const_name>\<open>insert\<close>\<close>
  val conj = \<open>\<^const_name>\<open>conj\<close>\<close>
  val disj = \<open>\<^const_name>\<open>disj\<close>\<close>
  val empty_cregister = \<open>\<^const_name>\<open>empty_cregister\<close>\<close>
  val empty_qregister = \<open>\<^const_name>\<open>empty_qregister\<close>\<close>
  val cregister_pair = \<open>\<^const_name>\<open>cregister_pair\<close>\<close>
  val qregister_pair = \<open>\<^const_name>\<open>qregister_pair\<close>\<close>
}
\<close>

export_generated_files _

end
