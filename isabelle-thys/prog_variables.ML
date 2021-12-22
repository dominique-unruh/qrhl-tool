structure Prog_Variables =
struct

datatype qc = Classical | Quantum

fun mk_ell2T T = Type(\<^type_name>\<open>ell2\<close>, [T])
fun dest_ell2T (Type(\<^type_name>\<open>ell2\<close>, [T])) = T
  | dest_ell2T T = raise TYPE("dest_ell2T",[T],[])

fun mk_boundedT T T' = Type(\<^type_name>\<open>cblinfun\<close>, [mk_ell2T T, mk_ell2T T'])
fun dest_boundedT (Type(\<^type_name>\<open>cblinfun\<close>, [Type(\<^type_name>\<open>ell2\<close>,[T]),Type(\<^type_name>\<open>ell2\<close>,[T'])])) = (T,T')
  | dest_boundedT T = raise TYPE("dest_boundedT",[T],[])
fun dest_bounded2T T = case dest_boundedT T of (T,T') => if T=T' then T else raise TYPE("dest_bounded2T", [T], [])
fun mk_bounded2T T = mk_boundedT T T

(* fun mk_variablesT T = Type(\<^type_name>\<open>variables\<close>, [T]) *)
fun mk_conjs [] = \<^const>\<open>True\<close>
  | mk_conjs [t] = t
  | mk_conjs (t::ts) = \<^const>\<open>conj\<close> $ t $ mk_conjs ts
(* fun mk_variable_name v = 
  Const(\<^const_name>\<open>variable_name\<close>, fastype_of v --> \<^typ>\<open>string\<close>) $ v *)
fun mk_cvariableT T = Type(\<^type_name>\<open>cregister\<close>, [T, \<^typ>\<open>cl\<close>])
fun mk_qvariableT T = Type(\<^type_name>\<open>qregister\<close>, [T, \<^typ>\<open>qu\<close>])
fun mk_c2variableT T = Type(\<^type_name>\<open>cregister\<close>, [T, \<^typ>\<open>cl2\<close>])
fun mk_q2variableT T = Type(\<^type_name>\<open>qregister\<close>, [T, \<^typ>\<open>qu2\<close>])
fun mk_variableT Quantum = mk_qvariableT
  | mk_variableT Classical = mk_cvariableT

fun dest_qregisterT (\<^Type>\<open>qregister T U\<close>) = (T,U)
  | dest_qregisterT T = raise TYPE("dest_qregisterT", [T], [])

fun dest_qregisterT_ct ctyp = let
  val _ = case Thm.typ_of ctyp of \<^Type>\<open>qregister _ _\<close> => ()
             | T => raise TYPE ("dest_qregisterT_ct: not a qregister type", [T], [])
  val [T,U] = Thm.dest_ctyp ctyp
in (T,U) end

fun dest_cregisterT (\<^Type>\<open>qregister T U\<close>) = (T,U)
  | dest_cregisterT T = raise TYPE("dest_cregisterT", [T], [])

fun dest_cvariableT (Type(\<^type_name>\<open>cregister\<close>, [T, \<^typ>\<open>cl\<close>])) = T
  | dest_cvariableT T = raise TYPE("dest_cvariableT", [T], [])

fun dest_qvariableT (Type(\<^type_name>\<open>qregister\<close>, [T, \<^typ>\<open>qu\<close>])) = T
  | dest_qvariableT T = raise TYPE("dest_qvariableT", [T], [])

fun dest_c2variableT (Type(\<^type_name>\<open>cregister\<close>, [T, \<^typ>\<open>cl2\<close>])) = T
  | dest_c2variableT T = raise TYPE("dest_c2variableT", [T], [])

fun dest_q2variableT (Type(\<^type_name>\<open>qregister\<close>, [T, \<^typ>\<open>qu2\<close>])) = T
  | dest_q2variableT T = raise TYPE("dest_q2variableT", [T], [])

(* fun strip_var_prefix x = if String.isPrefix "var_" x 
  then String.extract (x,4,NONE) 
  else error ("strip_var_prefix: Expected string starting with var_, not "^x) *)

(* 
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
 *)
structure WarnDeclaredQvarsData = Proof_Data
(
  type T = bool (* Within a nested call to the simproc *)
  fun init _ = false
)

(* fun warn_declared_qvars_simproc _ ctx ct = 
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
    | _ => NONE *)


type varinfo = {qc : qc, typ : typ, register: term, name: string}
structure VarInfo = Generic_Data
(
  type T = varinfo Symtab.table * varinfo Termtab.table
  val empty = (Symtab.empty, Termtab.empty)
  fun merge ((s1,t1), (s2,t2)) = (Symtab.merge (op=) (s1,s2), Termtab.merge (op=) (t1,t2))
)

fun lookup_variable ctxt = Symtab.lookup (VarInfo.get (Context.Proof ctxt) |> fst)
fun lookup_variable_qc ctxt name = lookup_variable ctxt name |> Option.map #qc

fun find_variable ctxt = Termtab.lookup (VarInfo.get (Context.Proof ctxt) |> snd)

fun is_classical_variable ctxt name = lookup_variable_qc ctxt name = SOME Classical

(* fun check_variable_type ctxt T =
  if Sign.of_sort (Proof_Context.theory_of ctxt) (T, \<^sort>\<open>universe\<close>) then () else
    error ("Type of variable ("^Syntax.string_of_typ ctxt T^") must be of sort "^Syntax.string_of_sort ctxt @{sort universe}^".\n"^
           "In the Isabelle theory, use 'derive universe T' for every type T defined using typedef/datatype,\n"^
           "and use declare_variable_type instead of typedecl") *)

local
fun add_varinfo morph name T qc register context = let
  val reg = Morphism.term morph register
  val varinfo = {qc=qc, name=name, typ=Morphism.typ morph T, register=reg} : varinfo
  val context = VarInfo.map (fn (s,t) => (Symtab.insert (op=) (name,varinfo) s,
                                          Termtab.insert (op=) (reg,varinfo) t)) context
  in context end

fun declare_variable_morph m name qc typ = let
    val register = Free(name, if qc=Classical then mk_cvariableT typ else mk_qvariableT typ)
    val chain = if qc=Classical then Const(\<^const_name>\<open>cregister_chain\<close>, \<^typ>\<open>cl c2variable\<close> --> fastype_of register --> mk_c2variableT typ)
                                    else Const(\<^const_name>\<open>qregister_chain\<close>, \<^typ>\<open>qu q2variable\<close> --> fastype_of register --> mk_q2variableT typ)
    val register1 = if qc=Classical then chain $ @{const cFst(cl,cl)} $ register
                                         else chain $ @{const qFst(qu,qu)} $ register
    val register2 = if qc=Classical then chain $ @{const cSnd(cl,cl)} $ register
                                         else chain $ @{const qSnd(qu,qu)} $ register
  in
      add_varinfo m name typ qc register #>
      add_varinfo m (name^"1") typ qc register1 #>
      add_varinfo m (name^"2") typ qc register2
  end
in
fun declare_variable_lthy name vartype typ = 
  Local_Theory.declaration {pervasive=true, syntax=false} (fn m => 
    declare_variable_morph m name vartype typ)

fun declare_variable_ctxt name vartype typ = Context.proof_map (declare_variable_morph Morphism.identity name vartype typ)

fun register_thms_of thm regs = let
  val reg = case Thm.prop_of thm of
      Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>cregister\<close>, _) $ reg) => reg
    | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>qregister\<close>, _) $ reg) => reg
    | _ => raise THM ("register_thms_of: expecting a fact of the form \<open>c/qregister ...\<close>", 0, [thm])
  val regs = case reg of
      Free _ => thm::regs
    | Const(\<^const_name>\<open>cregister_pair\<close>,_) $ _ $ _ =>
        regs |> register_thms_of (@{thm distinct_cvarsR} OF [thm])
             |> register_thms_of (@{thm distinct_cvarsL} OF [thm])
    | Const(\<^const_name>\<open>qregister_pair\<close>,_) $ _ $ _ =>
        regs |> register_thms_of (@{thm distinct_qvarsR} OF [thm])
             |> register_thms_of (@{thm distinct_qvarsL} OF [thm])
    | t => raise TERM ("register_thms_of: expecting a fact of the form \<open>c/register ...\<close> where ... is a register tuple of free variables. Got:", [t])
  in regs end

fun register_compats_of thm compats = case Thm.prop_of thm of
      Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>cregister\<close>, _) $ (Const(\<^const_name>\<open>cregister_pair\<close>,_) $ _ $ _)) =>
        compats |> register_compats_of (@{thm cregister_pair_iff_compatible[THEN iffD1]} OF [thm])
    | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>qregister\<close>, _) $ (Const(\<^const_name>\<open>qregister_pair\<close>,_) $ _ $ _)) =>
        compats |> register_compats_of (@{thm qregister_pair_iff_compatible[THEN iffD1]} OF [thm])
    | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>cregister\<close>, _) $ Free _) => compats
    | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>qregister\<close>, _) $ Free _) => compats
    | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>ccompatible\<close>, _) $ (Const(\<^const_name>\<open>cregister_pair\<close>,_) $ _ $ _) $ _) =>
        compats |> register_compats_of (@{thm ccompatible3[THEN iffD1, THEN conjunct2, THEN conjunct2]} OF [thm])
                |> register_compats_of (@{thm ccompatible3[THEN iffD1, THEN conjunct2, THEN conjunct1]} OF [thm])
                |> register_compats_of (@{thm ccompatible3[THEN iffD1, THEN conjunct1]} OF [thm])
    | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>qcompatible\<close>, _) $ (Const(\<^const_name>\<open>qregister_pair\<close>,_) $ _ $ _) $ _) =>
        compats |> register_compats_of (@{thm qcompatible3[THEN iffD1, THEN conjunct2, THEN conjunct2]} OF [thm])
                |> register_compats_of (@{thm qcompatible3[THEN iffD1, THEN conjunct2, THEN conjunct1]} OF [thm])
                |> register_compats_of (@{thm qcompatible3[THEN iffD1, THEN conjunct1]} OF [thm])
    | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>ccompatible\<close>, _) $ _ $ (Const(\<^const_name>\<open>cregister_pair\<close>,_) $ _ $ _)) =>
        compats |> register_compats_of (@{thm ccompatible3'[THEN iffD1, THEN conjunct2, THEN conjunct2]} OF [thm])
                |> register_compats_of (@{thm ccompatible3'[THEN iffD1, THEN conjunct2, THEN conjunct1]} OF [thm])
                |> register_compats_of (@{thm ccompatible3'[THEN iffD1, THEN conjunct1]} OF [thm])
    | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>qcompatible\<close>, _) $ _ $ (Const(\<^const_name>\<open>qregister_pair\<close>,_) $ _ $ _)) =>
        compats |> register_compats_of (@{thm qcompatible3'[THEN iffD1, THEN conjunct2, THEN conjunct2]} OF [thm])
                |> register_compats_of (@{thm qcompatible3'[THEN iffD1, THEN conjunct2, THEN conjunct1]} OF [thm])
                |> register_compats_of (@{thm qcompatible3'[THEN iffD1, THEN conjunct1]} OF [thm])
    | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>ccompatible\<close>, _) $ _ $ _) =>
        thm :: (@{thm ccompatible_sym} OF [thm]) :: compats
    | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>qcompatible\<close>, _) $ _ $ _) =>
        thm :: (@{thm qcompatible_sym} OF [thm]) :: compats
    | _ => raise THM ("register_compats_of: expecting a fact of the form \<open>c/qregister \<dots>\<close> or \<open>c/qcompatible \<dots>\<close>", 0, [thm])

fun declare_variable_from_thm (thm:thm) = let
  val (vartype, name, T) = case Thm.prop_of thm of
      Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>cregister\<close>, _) $ Free(name, T')) =>
            (Classical, name, dest_cvariableT T')
    | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>qregister\<close>, _) $ Free(name, T')) =>
            (Quantum, name, dest_qvariableT T')
    | _ => raise THM ("declare_variable_from_thm: theorem must be of the form 'Axioms_Classical.register x' or 'Axioms_Quantum.register x' where x is a free variable", 0, [thm])
  in (declare_variable_morph Morphism.identity name vartype T) end

fun declare_register_simps_from_thm thm = let
  val vars = register_thms_of thm []
  val compats = register_compats_of thm []
  val simp_vars = fold (fn thm => Simplifier.map_ss (Simplifier.add_simp thm)) vars
  val simp_compats = fold (fn thm => Simplifier.map_ss (Simplifier.add_simp thm)) compats
  in simp_vars #> simp_compats end

fun declare_variables_from_thm (thm:thm) = let
  val vars = register_thms_of thm []
  val declare_vars = fold declare_variable_from_thm vars
  in declare_vars #> declare_register_simps_from_thm thm end

val _ = Attrib.setup \<^binding>\<open>variable\<close>
 (Scan.succeed (Thm.declaration_attribute declare_variables_from_thm))
  "Declare a program variable (apply to a theorem of the form \"c/qregister x/\<lbrakk>x,y,...\<rbrakk>\")"
  |> Context.map_theory |> Context.>>

val _ = Attrib.setup \<^binding>\<open>register\<close>
 (Scan.succeed (Thm.declaration_attribute declare_register_simps_from_thm))
  "Extract and adds simplification rules for a register (e.g., indexed variable)"
  |> Context.map_theory |> Context.>>
end


fun register_assumption cq bind T = 
  let val qT = case cq of Classical => mk_cvariableT T | Quantum => mk_qvariableT T
      val name = Binding.name_of bind
      val register_constname = case cq of Classical => \<^const_name>\<open>cregister\<close> | Quantum => \<^const_name>\<open>qregister\<close>
      val register_const = Const(register_constname, qT --> HOLogic.boolT)
  in register_const $ Free(name,qT) |> HOLogic.mk_Trueprop end

fun add_register_assumption cq bind T ctxt =
  let val assm = register_assumption cq bind T
      val ctxt1 = Variable.declare_term assm ctxt
      val ([(_,[thm])],ctxt2) = Proof_Context.add_assms Assumption.assume_export
                  [((Binding.suffix_name "_register" bind,[Simplifier.simp_add]), [(assm,[])])] ctxt1
  in
    ctxt2
  end

fun declare_variable ctxt bind T cq existingVars =
  let val qT = case cq of Classical => mk_cvariableT T | Quantum => mk_qvariableT T
      val v = Binding.name_of bind
      val vars = [(bind,qT),(Binding.suffix_name "1" bind,qT),(Binding.suffix_name "2" bind,qT)]
      val (_,ctxt) = Variable.add_fixes_binding (map fst vars) ctxt
      val ctxt = fold (fn (v,T) => Variable.declare_term (Free (Binding.name_of v, T))) vars ctxt
      val ctxt = add_register_assumption cq bind T ctxt
      (* val ctxt = addQVariableNameAssumption cq (Binding.suffix_name "1" bind) T ctxt *)
      (* val ctxt = addQVariableNameAssumption cq (Binding.suffix_name "2" bind) T ctxt *)
      val ctxt = (* VarTypes.map (Symtab.insert op= (v,cq)) ctxt *)  declare_variable_ctxt v cq T ctxt
      (* val ctxt = (* VarTypes.map (Symtab.insert op= (v^"1",cq)) ctxt *) declare_variable_ctxt (v^"1") cq ctxt *)
      (* val ctxt = (* VarTypes.map (Symtab.insert op= (v^"2",cq)) ctxt *) declare_variable_ctxt (v^"2") cq ctxt *)
      fun declareCompatible (n2,T2) ctxt = let
        val v1 = Free(v, mk_variableT cq T) val v2 = Free(n2, mk_variableT cq T2)
        val compat1 = Const(case cq of Classical => \<^const_name>\<open>ccompatible\<close> | Quantum => \<^const_name>\<open>qcompatible\<close>,
                         fastype_of v1 --> fastype_of v2 --> HOLogic.boolT) $ v1 $ v2
            |> HOLogic.mk_Trueprop
        val compat2 = Const(case cq of Classical => \<^const_name>\<open>ccompatible\<close> | Quantum => \<^const_name>\<open>qcompatible\<close>,
                         fastype_of v2 --> fastype_of v1 --> HOLogic.boolT) $ v2 $ v1
            |> HOLogic.mk_Trueprop
        val (_,ctxt) = Proof_Context.add_assms Assumption.assume_export
                  [((Binding.suffix_name ("_" ^ n2 ^ "_compatible") bind,[Simplifier.simp_add]), [(compat1,[]),(compat2,[])])] ctxt
        in ctxt end
      val ctxt = fold declareCompatible existingVars ctxt
  in
    ctxt
  end

(* fun variables vars gthy = 
let val _ = app (fn (_,_,T) => check_variable_type (Proof_Context.init_global gthy) T)
    fun elems0 idx : Element.context_i list = [
      Element.Fixes (map_filter (fn (cq,bind,T) => 
           case cq of Classical => SOME (bind |> Binding.suffix_name idx, SOME T, Mixfix.NoSyn) | Quantum => NONE) vars),
      Element.Fixes (map (fn (cq,bind,T) => (bind |> (case cq of Classical => Binding.prefix_name "var_" | Quantum => I)
                                                  |> Binding.suffix_name idx, SOME (mk_variableT T), Mixfix.NoSyn)) vars),
      Element.Assumes (map (fn (cq,bind,T) => ((Binding.suffix_name (idx^"_varname") bind, @{attributes [simp]}),
                             [(varname_assumption cq (Binding.suffix_name idx bind) T, [])])) vars)]
    val elems = map elems0 ["", "1", "2"] |> List.concat
    (* val (_,lthy) = Bundle.context [] elems gthy *)
    val (_,lthy) = Expression.add_locale (Binding.name ("variables_"^string_of_int(serial()))) 
                      Binding.empty [] ([],[]) elems gthy
    val lthy2 = fold (fn (cq,bind,_) => fn lthy' => declare_variable_lthy (Binding.name_of bind) cq lthy') vars lthy
in lthy2 end *)

(* fun variables_cmd vars thy = 
  let (* val ctxt = Context.proof_of gthy *)
      val vars' = map (fn (a,b,c) => (a,b,Syntax.read_typ_global thy c)) vars
  in
    variables vars' thy
  end *)

val parse_classical_quantum = (Parse.reserved "classical" >> K Classical) || (Parse.reserved "quantum" >> K Quantum)

(* val _ =
  Outer_Syntax.command \<^command_keyword>\<open>variables\<close> "declare quantum/classical variables"
    ((Parse.and_list (parse_classical_quantum -- Args.binding --| Parse.$$$ "::" -- Parse.typ >> (fn ((a,b),c) => (a,b,c))) >> 
      (fn vars => Toplevel.begin_main_target true (variables_cmd vars)))
        --| Parse.begin)
 *)

datatype 'a tree = VTCons of 'a tree * 'a tree | VTSingle of 'a | VTUnit
type varterm = (string*typ) tree

(* fun parse_varterm (Const(\<^const_name>\<open>variable_concat\<close>,_) $ a $ b) = VTCons (parse_varterm a, parse_varterm b)
  | parse_varterm (Const(\<^const_name>\<open>variable_singleton\<close>,_) $ Free(n,Type(\<^type_name>\<open>variable\<close>,[T]))) = VTSingle (n,T)
  | parse_varterm (Const(\<^const_name>\<open>variable_unit\<close>,_)) = VTUnit
  | parse_varterm t = raise TERM("not a variables expression",[t]) *)

(* fun mk_varterm (VTUnit) = (\<^const>\<open>variable_unit\<close>, \<^typ>\<open>unit\<close>)
  | mk_varterm (VTCons(a,b)) = let
      val (vta,Ta) = mk_varterm a
      val (vtb,Tb) = mk_varterm b
    in
      (Const(\<^const_name>\<open>variable_concat\<close>, 
        mk_variablesT Ta --> mk_variablesT Tb --> mk_variablesT (HOLogic.mk_prodT(Ta,Tb))) $ vta $ vtb,
       HOLogic.mk_prodT(Ta,Tb))
    end
  | mk_varterm (VTSingle(n,T)) = 
      (Const(\<^const_name>\<open>variable_singleton\<close>, mk_variableT T --> mk_variablesT T) $ 
          Free(n,Type(\<^type_name>\<open>variable\<close>,[T])),T) *)

fun type_of_varterm (VTUnit) = \<^typ>\<open>unit\<close>
  | type_of_varterm (VTCons(a,b)) = HOLogic.mk_prodT(type_of_varterm a, type_of_varterm b)
  | type_of_varterm (VTSingle(_,T)) = T

fun varterm_from_list [] = VTUnit
  | varterm_from_list [nT] = VTSingle nT
  | varterm_from_list (nT::xs) = VTCons (VTSingle nT, varterm_from_list xs)

fun varterm_to_VARIABLE Classical VTUnit = \<^term>\<open>CREGISTER_unit :: CVARIABLE\<close>
  | varterm_to_VARIABLE Quantum VTUnit = \<^term>\<open>QREGISTER_unit :: QVARIABLE\<close>
  | varterm_to_VARIABLE Classical (VTSingle (n,T)) = Const(\<^const_name>\<open>CREGISTER_of\<close>, mk_cvariableT T --> \<^typ>\<open>CVARIABLE\<close>) $ Free (n, mk_cvariableT T)
  | varterm_to_VARIABLE Quantum (VTSingle (n,T)) = Const(\<^const_name>\<open>QREGISTER_of\<close>, mk_qvariableT T --> \<^typ>\<open>QVARIABLE\<close>) $ Free (n, mk_qvariableT T)
  | varterm_to_VARIABLE cq (VTCons (t1, t2)) = let
        val v1 = varterm_to_VARIABLE cq t1
        val v2 = varterm_to_VARIABLE cq t2
        val pair = case cq of Classical => \<^term>\<open>CREGISTER_pair :: CVARIABLE \<Rightarrow> CVARIABLE \<Rightarrow> CVARIABLE\<close>
                            | Quantum =>  \<^term>\<open>QREGISTER_pair :: QVARIABLE \<Rightarrow> QVARIABLE \<Rightarrow> QVARIABLE\<close>
      in pair $ v1 $ v2 end

fun varterm_to_variable Classical VTUnit = \<^term>\<open>cvariable_unit :: unit cvariable\<close>
  | varterm_to_variable Quantum VTUnit = \<^term>\<open>qvariable_unit :: unit qvariable\<close>
  | varterm_to_variable Classical (VTSingle (n,T)) = Free (n,mk_cvariableT T)
  | varterm_to_variable Quantum (VTSingle (n,T)) = Free (n,mk_qvariableT T)
  | varterm_to_variable cq (VTCons (t1, t2)) = let
        val v1 = varterm_to_variable cq t1
        val v2 = varterm_to_variable cq t2
        val T1 = case cq of Classical => dest_cvariableT (fastype_of v1) | Quantum => dest_qvariableT (fastype_of v1)
        val T2 = case cq of Classical => dest_cvariableT (fastype_of v2) | Quantum => dest_qvariableT (fastype_of v2)
        val T = HOLogic.mk_prodT (T1, T2)
        val pair = case cq of Classical => Const(\<^const_name>\<open>cregister_pair\<close>, fastype_of v1 --> fastype_of v2 --> mk_cvariableT T)
                            | Quantum => Const(\<^const_name>\<open>qregister_pair\<close>, fastype_of v1 --> fastype_of v2 --> mk_qvariableT T)
      in pair $ v1 $ v2 end

fun varterm_to_variable2 Classical VTUnit = \<^term>\<open>cvariable_unit :: unit c2variable\<close>
  | varterm_to_variable2 Quantum VTUnit = \<^term>\<open>qvariable_unit :: unit q2variable\<close>
  | varterm_to_variable2 Classical (VTSingle (n,T)) = let
      val (name, index) = Substring.splitAt (Substring.full n, String.size n - 1) |> apply2 Substring.string 
      in case index of
          "1" => \<^instantiate>\<open>v=\<open>Free (name, mk_cvariableT T)\<close> and 'a=T in term \<open>cregister_chain cFst v :: 'a c2variable\<close>\<close>
        | "2" => \<^instantiate>\<open>v=\<open>Free (name, mk_cvariableT T)\<close> and 'a=T in term \<open>cregister_chain cSnd v :: 'a c2variable\<close>\<close>
        | _ => raise error ("varterm_to_variable2: not an indexed variable: " ^ n) end
  | varterm_to_variable2 Quantum (VTSingle (n,T)) = let
      val (name, index) = Substring.splitAt (Substring.full n, String.size n - 1) |> apply2 Substring.string 
      in case index of
          "1" => \<^instantiate>\<open>v=\<open>Free (name, mk_qvariableT T)\<close> and 'a=T in term \<open>qregister_chain qFst v :: 'a q2variable\<close>\<close>
        | "2" => \<^instantiate>\<open>v=\<open>Free (name, mk_qvariableT T)\<close> and 'a=T in term \<open>qregister_chain qSnd v :: 'a q2variable\<close>\<close>
        | _ => raise error ("varterm_to_variable2: not an indexed variable: " ^ n) end
  | varterm_to_variable2 cq (VTCons (t1, t2)) = let
        val v1 = varterm_to_variable2 cq t1
        val v2 = varterm_to_variable2 cq t2
        val T1 = case cq of Classical => dest_c2variableT (fastype_of v1) | Quantum => dest_q2variableT (fastype_of v1)
        val T2 = case cq of Classical => dest_c2variableT (fastype_of v2) | Quantum => dest_q2variableT (fastype_of v2)
        val T = HOLogic.mk_prodT (T1, T2)
        val pair = case cq of Classical => Const(\<^const_name>\<open>cregister_pair\<close>, fastype_of v1 --> fastype_of v2 --> mk_c2variableT T)
                            | Quantum => Const(\<^const_name>\<open>qregister_pair\<close>, fastype_of v1 --> fastype_of v2 --> mk_q2variableT T)
      in pair $ v1 $ v2 end

fun variable_to_varterm _    (Const(\<^const_name>\<open>cvariable_unit\<close>,_)) = VTUnit
  | variable_to_varterm _    (Const(\<^const_name>\<open>qvariable_unit\<close>,_)) = VTUnit
  | variable_to_varterm ctxt (Const(\<^const_name>\<open>cregister_pair\<close>,_) $ t1 $ t2) = VTCons (variable_to_varterm ctxt t1, variable_to_varterm ctxt t2)
  | variable_to_varterm ctxt (Const(\<^const_name>\<open>qregister_pair\<close>,_) $ t1 $ t2) = VTCons (variable_to_varterm ctxt t1, variable_to_varterm ctxt t2)
  | variable_to_varterm ctxt v = case find_variable ctxt v of
      NONE => raise TERM("variable_to_varterm: unknown variable", [v])
      | SOME {name, typ, ...} => VTSingle (name, typ)

fun varterm_from_list_untyped [] = VTUnit
  | varterm_from_list_untyped [n] = VTSingle (n,dummyT)
  | varterm_from_list_untyped (n::xs) = VTCons (VTSingle (n,dummyT), varterm_from_list_untyped xs)

fun map_tree _ VTUnit = VTUnit
  | map_tree f (VTSingle x) = VTSingle (f x)
  | map_tree f (VTCons (a, b)) = VTCons (map_tree f a, map_tree f b)

fun varterm_instantiate \<^typ>\<open>unit\<close> VTUnit = VTUnit
  | varterm_instantiate T VTUnit = raise TYPE ("varterm_instantiate: invalid type for VTUnit",[T],[])
  | varterm_instantiate (Type(\<^type_name>\<open>prod\<close>,[T1,T2])) (VTCons (v1,v2)) = VTCons (varterm_instantiate T1 v1, varterm_instantiate T2 v2)
  | varterm_instantiate T (VTCons _) = raise TYPE ("varterm_instantiate: invalid type for VTCons",[T],[])
  | varterm_instantiate T (VTSingle (v,_)) = VTSingle (v,T)

fun varterm_instantiate' T v = varterm_instantiate T (map_tree (fn n => (n,dummyT)) v)

fun vars_in_varterm (VTCons(a,b)) = vars_in_varterm a @ vars_in_varterm b
  | vars_in_varterm (VTSingle nT) = [nT]
  | vars_in_varterm VTUnit = []

fun variable_to_varlist ctxt t =
  let val vt = variable_to_varterm ctxt t
      fun tol (VTSingle nT) = [nT]
        | tol VTUnit = []
        | tol (VTCons (VTSingle _, VTUnit)) = raise TERM("not an explicit variable list",[t])
        | tol (VTCons (VTSingle nT, rest)) = nT :: tol rest
        | tol (VTCons _) = raise TERM("not an explicit variable list",[t])
  in
    tol vt
  end

(* Checks if term is a (not necessarily explict) variable list *)
(* fun is_varlist (Const(\<^const_name>\<open>variable_unit\<close>,_)) = true
  | is_varlist (Const(\<^const_name>\<open>variable_singleton\<close>,_) $ _) = true
  | is_varlist (Const(\<^const_name>\<open>variable_concat\<close>,_) $ _ $ Const(\<^const_name>\<open>variable_unit\<close>,_)) = false
  | is_varlist (Const(\<^const_name>\<open>variable_concat\<close>,_) $ Const(\<^const_name>\<open>variable_singleton\<close>,_) $ rest) = is_varlist rest
  | is_varlist _ = false *)

fun nameq ((x:string,_:typ), (y,_:typ)) = x=y

(* Returns a varterm containing all variables from vt2 that are not in vt1 *)
fun missing_in_varterm vt1 vt2 = let
  val v1 = vars_in_varterm vt1
  val v2 = vars_in_varterm vt2
  val miss = subtract nameq v1 v2
in
  varterm_from_list miss
end


(* Converts "index_var True/False x" (where x is a free variable) into "x1" or "x2",
   assuming x is declared via the variables-command or equivalent.
   (More specifically, it requires that simp rules "variable_name x/x1/x2 = ''...''" with 
   the correct names are declared.) *)
(* TODO: use context data for the variable name theorem (instead of simplifier) *)
(* fun index_var_conv ctxt ct =
  let val (lrname,x,T) = case Thm.term_of ct of
        Const(\<^const_name>\<open>index_var\<close>,_) $ Const(lrname,_) $ Free(x,T) => (lrname,x,T)
      | _ => raise CTERM("index_var_conv: wrong shape",[ct])
      val lr = case lrname of 
          \<^const_name>\<open>True\<close> => true
        | \<^const_name>\<open>False\<close> => false
        | _ => raise CTERM("index_var_conv: wrong shape (expected True/False as first arg)",[ct])

      val suffix = (if lr then "1" else "2")
      val x1 = x ^ suffix

      val varname_x = Raw_Simplifier.rewrite_cterm (false,false,false) (fn _ => fn _ => NONE) ctxt (Thm.cterm_of ctxt 
        (Const(\<^const_name>\<open>variable_name\<close>, T --> \<^typ>\<open>string\<close>) $ Free(x,T)))

      val varname_x1 = Raw_Simplifier.rewrite_cterm (false,false,false) (fn _ => fn _ => NONE) ctxt (Thm.cterm_of ctxt 
        (Const(\<^const_name>\<open>variable_name\<close>, T --> \<^typ>\<open>string\<close>) $ Free(x1,T)))

      val helper_thm = if lr then @{thm index_var_conv1_aux} else  @{thm index_var_conv2_aux}
  
      val name_x = varname_x |> Thm.concl_of |> Logic.dest_equals |> snd
      val name_eq = Raw_Simplifier.rewrite_cterm (false,false,false) (fn _ => fn _ => NONE) ctxt
        (\<^term>\<open>(@) :: string\<Rightarrow>_\<Rightarrow>_\<close> $ name_x $ HOLogic.mk_string suffix |> Thm.cterm_of ctxt)
  in
    helper_thm OF [varname_x, varname_x1, name_eq]
  end *)

(* Simproc that simplifies using index_var_conv, see there.  *)
(* fun index_var_simproc _ ctxt ct = SOME (index_var_conv ctxt ct) handle CTERM _ => NONE *)

(* Converts "index_flip_var x1/2" (where x1/2 is a free variable) into "x2/1",
   assuming x1/2 is declared via the variables-command or equivalent.
   (More specifically, it requires that simp rules "variable_name x/x1/x2 = ''...''" with 
   the correct names are declared.) *)
(* TODO: use context data for the variable name theorem (instead of simplifier) *)
(* fun index_flip_var_conv ctxt ct = let
  val v = case Thm.term_of ct of Const(\<^const_name>\<open>index_flip_var\<close>, _) $ v => v | _ => raise CTERM("index_flip_var_conv: expecting 'index_flip_var v'",[ct])
  val (name,T) = case v of Free(n,T) => (n,T) | _ => raise CTERM("index_flip_var_conv: not a free variable",[ct])
  val _ = case T of Type(\<^type_name>\<open>variable\<close>,_) => () | _ => raise CTERM("index_flip_var_conv: wrong type for a variable",[ct])
  val len = String.size name
  val basename = String.substring (name, 0, len-1)
  (* val index =  *)
  val left = case String.substring (name, len-1, 1) of "1" => true | "2" => false | _ => raise CTERM("index_flip_var_conv: variable name does not end in 1 or 2",[ct])
  val thm = infer_instantiate ctxt [(("v",0), Free(basename,T) |> Thm.cterm_of ctxt)]
            (if left then @{thm index_flip_var_conv_aux1} else @{thm index_flip_var_conv_aux2})
  val thm = thm |> Conv.fconv_rule (Conv.arg1_conv(*lhs*) (Conv.arg_conv(*index_var_flip*) (index_var_conv ctxt)))
  val thm = thm |> Conv.fconv_rule (Conv.arg_conv(*rhs*) (index_var_conv ctxt))
in
  thm
end *)

(* Simproc that simplifies using index_flip_var_conv, see there.  *)
(* fun index_flip_var_simproc _ ctxt ct = SOME (index_flip_var_conv ctxt ct) handle CTERM _ => NONE *)

(* Subgoals of the form "variable_name x ~= variable_name y"
   where x,y are explicit variables *)
(* TODO: something more specific than just simplifier? *)
(* fun different_variable_names_tac ctxt = SOLVED' (simp_tac ctxt) *)

fun distinct_vars_tac ctxt = let
  val ctxt = ctxt addsimps @{thms 
    distinct_cvars_split1 distinct_cvars_split2 cregister_pair_iff_compatible ccompatible3 ccompatible3'
    distinct_qvars_split1 distinct_qvars_split2 qregister_pair_iff_compatible qcompatible3 qcompatible3'
    Cccompatible_CREGISTER_of Qqcompatible_QREGISTER_of}
  in Misc.succeed_or_error_tac' (SOLVED' (simp_tac ctxt)) ctxt (fn t => "Cannot prove that the variables are variables and distinct (using simp): " ^ Syntax.string_of_term ctxt t) end

(* fun register_n qc true 1 = Const(case qc of Classical => \<^const_name>\<open>cregister_id\<close> | Quantum => \<^const_name>\<open>qregister_id\<close>, dummyT)
  | register_n qc false 1 = Const(case qc of Classical => \<^const_name>\<open>cFst\<close> | Quantum => \<^const_name>\<open>qFst\<close>, dummyT)
  | register_n qc last n = let
      val _ = n > 1 orelse error "register_n: n must be >= 1"
      in Const(case qc of Classical => \<^const_name>\<open>cregister_pair\<close> | Quantum => \<^const_name>\<open>qregister_pair\<close>, dummyT) $
          Const(case qc of Classical => \<^const_name>\<open>cSnd\<close> | Quantum => \<^const_name>\<open>qSnd\<close>, dummyT) $
          register_n qc last (n-1) end *)

fun register_n true 1 = Const(\<^const_name>\<open>register_id\<close>, dummyT)
  | register_n false 1 = Const(\<^const_name>\<open>Fst\<close>, dummyT)
  | register_n true 2 = Const(\<^const_name>\<open>Snd\<close>, dummyT)
  | register_n last n = let
      val _ = n > 1 orelse error "register_n: n must be >= 1"
      in Const(\<^const_name>\<open>register_chain\<close>, dummyT) $ Const(\<^const_name>\<open>Snd\<close>, dummyT) $ register_n last (n-1) end

fun is_empty_qregisterT ctxt (\<^Type>\<open>qregister T _\<close>) = Sign.of_sort (Proof_Context.theory_of ctxt) (T,\<^sort>\<open>CARD_1\<close>)
  | is_empty_qregisterT _ T = raise TYPE("is_empty_qregisterT: not a qregister type", [T], [])

fun is_empty_qregister ctxt t = is_empty_qregisterT ctxt (fastype_of t)
  handle TYPE(_, Ts, _) => raise TYPE("is_empty_qregister: not a qregister type", Ts, [t])

local
val qregister_conversion_to_register_conv_simpset = 
  \<^context> addsimps @{thms qregister_chain_pair qregister_chain_assoc[symmetric] 
                          qregister_of_cregister_Fst qregister_of_cregister_Snd}
  |> simpset_of
in
fun qregister_conversion_to_register_conv ctxt ct = let
  val (lhs,rhs) = case Thm.term_of ct of Const(\<^const_name>\<open>qregister_conversion\<close>,_) $ lhs $ rhs => (lhs,rhs)
                                       | _ => raise CTERM ("qregister_conversion_to_register_conv: not a register conversion", [ct])
  val (rhs_inT, _) = dest_qregisterT (fastype_of rhs)
  fun add_to_path prefix path = if Term.is_dummy_pattern path then prefix else
    let val (prefix_inT, _) = dest_qregisterT (fastype_of prefix)
        val (path_inT, path_outT) = dest_qregisterT (fastype_of path)
    in \<^Const>\<open>qregister_chain path_inT path_outT prefix_inT\<close> $ path $ prefix end
  fun get_rhs_registers (\<^Const_>\<open>qregister_pair T1 _ T2\<close> $ r1 $ r2) path found = 
      found |> get_rhs_registers r1 (add_to_path \<^Const>\<open>qFst T1 T2\<close> path)
            |> get_rhs_registers r2 (add_to_path \<^Const>\<open>qSnd T2 T1\<close> path)
   | get_rhs_registers reg path found = 
      if is_empty_qregister ctxt reg then found
      else (reg,path) :: found
  val rhs_registers = get_rhs_registers rhs Term.dummy []
  fun map_lhs (Const(\<^const_name>\<open>qregister_pair\<close>,_) $ r1 $ r2) : term = let
    val r1' = map_lhs r1
    val r2' = map_lhs r2
    val (r1'in, r1'out) = dest_qregisterT (fastype_of r1')
    val (r2'in, _) = dest_qregisterT (fastype_of r2')
    in
      \<^Const>\<open>qregister_pair r1'in r1'out r2'in for r1' r2'\<close>
    end
    | map_lhs r = 
      if is_empty_qregister ctxt r
      then \<^Const>\<open>empty_qregister \<open>fastype_of r |> dest_qregisterT |> fst\<close> rhs_inT\<close>
      else
        (case AList.lookup (op aconv) rhs_registers r of
          NONE => raise TERM ("qregister_conversion_to_register_conv: could not find register from lhs in rhs", [r,Thm.term_of ct])
        | SOME path => path)
  val new_reg = map_lhs lhs |> Thm.cterm_of ctxt
  val new_reg = Conv.bottom_rewrs_conv @{thms qregister_chain_assoc[THEN eq_reflection]} ctxt new_reg |> Thm.rhs_of
  val goal = Misc.mk_ct_equals ct new_reg
  val outer_simpset = simpset_of ctxt
  val simpset_ctxt = ctxt 
          |> put_simpset qregister_conversion_to_register_conv_simpset
          (* |> Raw_Simplifier.set_subgoaler (fn ctxt => K (print_tac ctxt "xxx") THEN' simp_tac (put_simpset outer_simpset ctxt)) *)
          |> Raw_Simplifier.set_subgoaler (fn ctxt => distinct_vars_tac (put_simpset outer_simpset ctxt))
  val tac = resolve_tac ctxt @{thms qregister_conversion_as_register[THEN eq_reflection]} 1
            THEN
            distinct_vars_tac ctxt 1
            THEN
            Misc.succeed_or_error_tac' (SOLVED' (simp_tac simpset_ctxt))
            ctxt (fn t => "qregister_conversion_to_register_conv: cannot prove precondition for rewriting '" ^ 
                Syntax.string_of_term ctxt (Thm.term_of ct) ^ "' into a register:\n" ^ Syntax.string_of_term ctxt t) 1
  val thm = Goal.prove_internal ctxt [] goal (K tac)
in
  thm
end
end


end
