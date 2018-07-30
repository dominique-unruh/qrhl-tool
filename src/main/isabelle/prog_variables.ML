structure Prog_Variables =
struct

fun mk_variablesT T = Type(\<^type_name>\<open>variables\<close>, [T])
fun mk_conjs [] = \<^const>\<open>True\<close>
  | mk_conjs [t] = t
  | mk_conjs (t::ts) = \<^const>\<open>conj\<close> $ t $ mk_conjs ts
fun mk_variable_name v = 
  Const(\<^const_name>\<open>variable_name\<close>, fastype_of v --> \<^typ>\<open>string\<close>) $ v
fun mk_variableT T = Type(\<^type_name>\<open>variable\<close>, [T])
fun dest_variableT (Type(\<^type_name>\<open>variable\<close>, [T])) = T
  | dest_variableT T = raise TYPE("dest_variableT", [T], [])
fun dest_variablesT (Type(\<^type_name>\<open>variables\<close>, [T])) = T
  | dest_variablesT T = raise TYPE("dest_variablesT", [T], [])

local
  fun mk_var_eq (v as Const ("_constrain", _) $ Free (n, _) $ Free _) =
      @{const HOL.eq("char list")} $ (Const (\<^const_name>\<open>variable_name\<close>, dummyT) $ v) $ HOLogic.mk_string n
    | mk_var_eq t = raise (TERM("the argument to declared_qvars must contain only free variables",[t]))

  fun declared_qvars_parse_tr' (Const (\<^syntax_const>\<open>_variable_list_args\<close>, _) $ v $ vs)
    = mk_var_eq v :: declared_qvars_parse_tr' vs
    | declared_qvars_parse_tr' (Const (\<^syntax_const>\<open>_variable_list_arg\<close>, _) $ v)
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
      Const(\<^const_name>\<open>variable_name\<close>, _) $ Free (n,_) =>
        let val eq = Raw_Simplifier.rewrite_cterm (false,false,false) (fn _ => fn _ => NONE) (WarnDeclaredQvarsData.put true ctx) ct 
            val rhs = eq |> Thm.prop_of |> Logic.dest_equals |> snd
        in
            case rhs of Const(\<^const_name>\<open>variable_name\<close>, _) $ _ => 
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

fun lookup_variable ctx = Symtab.lookup (VarTypes.get ctx)
fun is_classical_variable ctx name = case Symtab.lookup (VarTypes.get ctx) name of
  SOME Classical => true
  | _ => false

fun check_variable_type ctxt T =
  if Sign.of_sort (Proof_Context.theory_of ctxt) (T, \<^sort>\<open>universe\<close>) then () else
    error ("Type of variable ("^Syntax.string_of_typ ctxt T^") must be of sort "^Syntax.string_of_sort ctxt @{sort universe}^".\n"^
           "In the Isabelle theory, use 'derive universe T' for every type T defined using typedef/datatype,\n"^
           "and use declare_variable_type instead of typedecl")

fun declare_variable_lthy name vartype = 
  Local_Theory.declaration {pervasive=true, syntax=false} (fn _ => 
    Context.mapping I (
      VarTypes.map (Symtab.insert op= (name,vartype)) #>
      VarTypes.map (Symtab.insert op= (name^"1",vartype)) #>
      VarTypes.map (Symtab.insert op= (name^"2",vartype))))

fun varname_assumption cq bind T = 
  let val qT = mk_variableT T
      val name = Binding.name_of bind
      val name' = if cq=Classical then "var_"^name else name
      val lhs = Const(\<^const_name>\<open>variable_name\<close>, qT --> HOLogic.stringT) $ Free(name',qT)
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


fun declare_variable ctxt bind T cq =
  let val _ = check_variable_type ctxt T
      val qT = mk_variableT T
      val v = Binding.name_of bind
      val vars = if cq=Classical then [(bind,T),(Binding.suffix_name "1" bind,T),(Binding.suffix_name "2" bind,T),
                                       (bind |> Binding.prefix_name "var_",qT),(bind |> Binding.suffix_name "1" |> Binding.prefix_name "var_",qT),(bind |> Binding.suffix_name "2" |> Binding.prefix_name "var_",qT)]
                                  else [(bind,qT),(Binding.suffix_name "1" bind,qT),(Binding.suffix_name "2" bind,qT)]
      val (_,ctxt) = Variable.add_fixes_binding (map fst vars) ctxt
      val ctxt = fold (fn (v,T) => Variable.declare_term (Free(Binding.name_of v,T))) vars ctxt
      val ctxt = addQVariableNameAssumption cq bind T ctxt
      val ctxt = addQVariableNameAssumption cq (Binding.suffix_name "1" bind) T ctxt
      val ctxt = addQVariableNameAssumption cq (Binding.suffix_name "2" bind) T ctxt
      val ctxt = VarTypes.map (Symtab.insert op= (v,cq)) ctxt
      val ctxt = VarTypes.map (Symtab.insert op= (v^"1",cq)) ctxt
      val ctxt = VarTypes.map (Symtab.insert op= (v^"2",cq)) ctxt
  in
    ctxt
  end


fun variables vars gthy = 
let val _ = app (fn (_,_,T) => check_variable_type (Proof_Context.init_global gthy) T)
    fun elems0 idx = [
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
  Outer_Syntax.command \<^command_keyword>\<open>variables\<close> "declare quantum/classical variables"
    ((Parse.and_list (parse_classical_quantum -- Args.binding --| Parse.$$$ "::" -- Parse.typ >> (fn ((a,b),c) => (a,b,c))) >> 
      (fn vars => Toplevel.begin_local_theory true (variables_cmd vars)))
        --| Parse.begin)

end