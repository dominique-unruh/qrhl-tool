structure Prog_Variables =
struct

datatype qc = Classical | Quantum
datatype index = NoIndex | Index1 | Index2

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
  | dest_qregisterT (\<^Type>\<open>dummy\<close>) = (dummyT, dummyT) (* So that it also works in not yet type-inferred terms *)
  | dest_qregisterT T = raise TYPE("dest_qregisterT", [T], [])

fun dest_qregisterT_ct ctyp = let
  val _ = case Thm.typ_of ctyp of \<^Type>\<open>qregister _ _\<close> => ()
             | T => raise TYPE ("dest_qregisterT_ct: not a qregister type", [T], [])
  val [T,U] = Thm.dest_ctyp ctyp
in (T,U) end

fun dest_cregisterT (\<^Type>\<open>cregister T U\<close>) = (T,U)
  | dest_cregisterT (\<^Type>\<open>dummy\<close>) = (dummyT, dummyT) (* So that it also works in not yet type-inferred terms *)
  | dest_cregisterT T = raise TYPE("dest_cregisterT", [T], [])

fun dest_cvariableT (Type(\<^type_name>\<open>cregister\<close>, [T, \<^typ>\<open>cl\<close>])) = T
  | dest_cvariableT (\<^Type>\<open>dummy\<close>) = dummyT (* So that it also works in not yet type-inferred terms *)
  | dest_cvariableT T = raise TYPE("dest_cvariableT", [T], [])

fun dest_qvariableT (Type(\<^type_name>\<open>qregister\<close>, [T, \<^typ>\<open>qu\<close>])) = T
  | dest_qvariableT (\<^Type>\<open>dummy\<close>) = dummyT (* So that it also works in not yet type-inferred terms *)
  | dest_qvariableT T = raise TYPE("dest_qvariableT", [T], [])

fun dest_c2variableT (Type(\<^type_name>\<open>cregister\<close>, [T, \<^typ>\<open>cl2\<close>])) = T
  | dest_c2variableT (\<^Type>\<open>dummy\<close>) = dummyT (* So that it also works in not yet type-inferred terms *)
  | dest_c2variableT T = raise TYPE("dest_c2variableT", [T], [])

fun dest_q2variableT (Type(\<^type_name>\<open>qregister\<close>, [T, \<^typ>\<open>qu2\<close>])) = T
  | dest_q2variableT (\<^Type>\<open>dummy\<close>) = dummyT (* So that it also works in not yet type-inferred terms *)
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


type varinfo = {qc : qc, in_typ : typ, out_typ : typ, name: string}

fun lookup_variable ctxt name : varinfo option = case Variable.default_type ctxt name of
    SOME \<^Type>\<open>qregister in_typ out_typ\<close> => SOME {qc=Quantum, in_typ=in_typ, out_typ=out_typ, name=name}
  | SOME \<^Type>\<open>cregister in_typ out_typ\<close> => SOME {qc=Classical, in_typ=in_typ, out_typ=out_typ, name=name}
  | _ => NONE

fun is_classical_variable ctxt name = (lookup_variable ctxt name |> Option.map #qc) = SOME Classical

(* fun check_variable_type ctxt T =
  if Sign.of_sort (Proof_Context.theory_of ctxt) (T, \<^sort>\<open>universe\<close>) then () else
    error ("Type of variable ("^Syntax.string_of_typ ctxt T^") must be of sort "^Syntax.string_of_sort ctxt @{sort universe}^".\n"^
           "In the Isabelle theory, use 'derive universe T' for every type T defined using typedef/datatype,\n"^
           "and use declare_variable_type instead of typedecl") *)

local
(* fun add_varinfo morph name T qc register context = let
  val reg = Morphism.term morph register
  val varinfo = {qc=qc, name=name, typ=Morphism.typ morph T, register=reg} : varinfo
  val _ = Symtab.defined (VarInfo.get context |> fst) name
            andalso error ("Program variable " ^ name ^ " already declared")
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
  end *)
in
(* fun declare_variable_lthy name vartype typ = 
  Local_Theory.declaration {pervasive=true, syntax=false} (fn m => 
    declare_variable_morph m name vartype typ)

fun declare_variable_ctxt name vartype typ = Context.proof_map (declare_variable_morph Morphism.identity name vartype typ) *)

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
      \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>cregister _ _\<close> $ (\<^Const>\<open>cregister_pair _ _ _\<close> $ (\<^Const>\<open>cregister_pair _ _ _\<close> $ _ $ _) $ _)) =>
        compats |> register_compats_of (@{thm ccompatible3[THEN iffD1, THEN conjunct2, THEN conjunct2]} OF [thm])
                |> register_compats_of (@{thm ccompatible3[THEN iffD1, THEN conjunct2, THEN conjunct1]} OF [thm])
                |> register_compats_of (@{thm ccompatible3[THEN iffD1, THEN conjunct1]} OF [thm])
    | \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>qregister _ _\<close> $ (\<^Const>\<open>qregister_pair _ _ _\<close> $ (\<^Const>\<open>qregister_pair _ _ _\<close> $ _ $ _) $ _)) =>
        compats |> register_compats_of (@{thm qcompatible3[THEN iffD1, THEN conjunct2, THEN conjunct2]} OF [thm])
                |> register_compats_of (@{thm qcompatible3[THEN iffD1, THEN conjunct2, THEN conjunct1]} OF [thm])
                |> register_compats_of (@{thm qcompatible3[THEN iffD1, THEN conjunct1]} OF [thm])
    | \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>cregister _ _\<close> $ (\<^Const>\<open>cregister_pair _ _ _\<close> $ _ $ (\<^Const>\<open>cregister_pair _ _ _\<close> $ _ $ _))) =>
        compats |> register_compats_of (@{thm ccompatible3'[THEN iffD1, THEN conjunct2, THEN conjunct2]} OF [thm])
                |> register_compats_of (@{thm ccompatible3'[THEN iffD1, THEN conjunct2, THEN conjunct1]} OF [thm])
                |> register_compats_of (@{thm ccompatible3'[THEN iffD1, THEN conjunct1]} OF [thm])
    | \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>qregister _ _\<close> $ (\<^Const>\<open>qregister_pair _ _ _\<close> $ _ $ (\<^Const>\<open>qregister_pair _ _ _\<close> $ _ $ _))) =>
        compats |> register_compats_of (@{thm qcompatible3'[THEN iffD1, THEN conjunct2, THEN conjunct2]} OF [thm])
                |> register_compats_of (@{thm qcompatible3'[THEN iffD1, THEN conjunct2, THEN conjunct1]} OF [thm])
                |> register_compats_of (@{thm qcompatible3'[THEN iffD1, THEN conjunct1]} OF [thm])
    | \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>cregister _ _\<close> $ (\<^Const>\<open>cregister_pair _ _ _\<close> $ _ $ _)) =>
        thm :: (@{thm ccompatible_sym} OF [thm]) :: compats
    | \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>qregister _ _\<close> $ (\<^Const>\<open>qregister_pair _ _ _\<close> $ _ $ _)) =>
        thm :: (@{thm qcompatible_sym} OF [thm]) :: compats
    | \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>cregister _ _\<close> $ Free _) => compats
    | \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>qregister _ _\<close> $ Free _) => compats
    | _ => raise THM ("register_compats_of: expecting a fact of the form \<open>c/qregister \<dots>\<close> or \<open>c/qcompatible \<dots>\<close>", 0, [thm])

(* fun declare_variable_from_thm (thm:thm) = let
  val (vartype, name, T) = case Thm.prop_of thm of
      Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>cregister\<close>, _) $ Free(name, T')) =>
            (Classical, name, dest_cvariableT T')
    | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>qregister\<close>, _) $ Free(name, T')) =>
            (Quantum, name, dest_qvariableT T')
    | _ => raise THM ("declare_variable_from_thm: theorem must be of the form 'Axioms_Classical.register x' or 'Axioms_Quantum.register x' where x is a free variable", 0, [thm])
  in (declare_variable_morph Morphism.identity name vartype T) end *)

fun declare_register_simps_from_thm thm = let
  val vars = register_thms_of thm []
  val compats = register_compats_of thm []
  val simp_vars = fold (fn thm => Simplifier.map_ss (Simplifier.add_simp thm)) vars
  val simp_compats = fold (fn thm => Simplifier.map_ss (Simplifier.add_simp thm)) compats
  in simp_vars #> simp_compats end

(* fun declare_variables_from_thm (thm:thm) = let
  val vars = register_thms_of thm []
  val declare_vars = fold declare_variable_from_thm vars
  in declare_vars #> declare_register_simps_from_thm thm end *)

(* val _ = Attrib.setup \<^binding>\<open>variable\<close>
 (Scan.succeed (Thm.declaration_attribute declare_variables_from_thm))
  "Declare a program variable (apply to a theorem of the form \"c/qregister x/\<lbrakk>x,y,...\<rbrakk>\")"
  |> Context.map_theory |> Context.>> *)

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
  let val memT = case cq of Classical => \<^typ>\<open>cl\<close> | Quantum => \<^typ>\<open>qu\<close>
      val v = Binding.name_of bind
      val (_,ctxt) = Variable.add_fixes_binding [bind] ctxt
      val ctxt = add_register_assumption cq bind T ctxt
      fun declareCompatible (n2,T2) ctxt = let
        val v1 = Free(v, mk_variableT cq T) val v2 = Free(n2, mk_variableT cq T2)
        val compat1 = (case cq of Classical => \<^Const>\<open>cregister \<open>HOLogic.mk_prodT (T,T2)\<close> memT\<close> $ (\<^Const>\<open>cregister_pair T memT T2\<close> $ v1 $ v2)
                                | Quantum   => \<^Const>\<open>qregister \<open>HOLogic.mk_prodT (T,T2)\<close> memT\<close> $ (\<^Const>\<open>qregister_pair T memT T2\<close> $ v1 $ v2))
            |> HOLogic.mk_Trueprop
        val compat2 = (case cq of Classical => \<^Const>\<open>cregister \<open>HOLogic.mk_prodT (T2,T)\<close> memT\<close> $ (\<^Const>\<open>cregister_pair T2 memT T\<close> $ v2 $ v1)
                                | Quantum   => \<^Const>\<open>qregister \<open>HOLogic.mk_prodT (T2,T)\<close> memT\<close> $ (\<^Const>\<open>qregister_pair T2 memT T\<close> $ v2 $ v1))
            |> HOLogic.mk_Trueprop
        val (_,ctxt) = Proof_Context.add_assms Assumption.assume_export
                  [((Binding.suffix_name ("_" ^ n2 ^ "_compatible") bind,[Simplifier.simp_add]), [(compat1,[]),(compat2,[])])] ctxt
        in ctxt end
      val ctxt = fold declareCompatible existingVars ctxt
  in
    ctxt
  end

(* val parse_classical_quantum = (Parse.reserved "classical" >> K Classical) || (Parse.reserved "quantum" >> K Quantum) *)

(* val _ =
  Outer_Syntax.command \<^command_keyword>\<open>variables\<close> "declare quantum/classical variables"
    ((Parse.and_list (parse_classical_quantum -- Args.binding --| Parse.$$$ "::" -- Parse.typ >> (fn ((a,b),c) => (a,b,c))) >> 
      (fn vars => Toplevel.begin_main_target true (variables_cmd vars)))
        --| Parse.begin)
 *)

datatype 'a tree = VTCons of 'a tree * 'a tree | VTSingle of 'a | VTUnit
type varterm1 = (string*typ) tree
type varterm = (string*index*typ) tree

(* fun parse_varterm (Const(\<^const_name>\<open>variable_concat\<close>,_) $ a $ b) = VTCons (parse_varterm a, parse_varterm b)
  | parse_varterm (Const(\<^const_name>\<open>variable_singleton\<close>,_) $ Free(n,Type(\<^type_name>\<open>variable\<close>,[T]))) = VTSingle (n,T)
  | parse_varterm (Const(\<^const_name>\<open>variable_unit\<close>,_)) = VTUnit
  | parse_varterm t = raise TERM("not a variables expression",[t]) *)

(* fun parse_varterm_syntax (Const(\<^const_syntax>\<open>variable_concat\<close>,_) $ a $ b) = VTCons (parse_varterm_syntax a, parse_varterm_syntax b)
  | parse_varterm_syntax (Const(\<^const_syntax>\<open>variable_singleton\<close>,_) $ Free(n,Type(\<^type_name>\<open>variable\<close>,[T]))) = VTSingle (n,T)
  | parse_varterm_syntax (Const(\<^const_syntax>\<open>variable_singleton\<close>,_) $ (Const("_free",_) $ Free(n,Type(\<^type_name>\<open>variable\<close>,[T])))) = VTSingle (n,T)
  | parse_varterm_syntax (Const(\<^const_syntax>\<open>variable_unit\<close>,_)) = VTUnit
  | parse_varterm_syntax t = raise TERM("not a variables expression",[t]) *)

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

fun varterm1_to_variable1 Classical VTUnit = \<^term>\<open>empty_cregister :: unit cvariable\<close>
  | varterm1_to_variable1 Quantum VTUnit = \<^term>\<open>empty_qregister :: unit qvariable\<close>
  | varterm1_to_variable1 Classical (VTSingle (n,T)) = Free (n,mk_cvariableT T)
  | varterm1_to_variable1 Quantum (VTSingle (n,T)) = Free (n,mk_qvariableT T)
  | varterm1_to_variable1 cq (VTCons (t1, t2)) = let
        val v1 = varterm1_to_variable1 cq t1
        val v2 = varterm1_to_variable1 cq t2
        val T1 = case cq of Classical => dest_cvariableT (fastype_of v1) | Quantum => dest_qvariableT (fastype_of v1)
        val T2 = case cq of Classical => dest_cvariableT (fastype_of v2) | Quantum => dest_qvariableT (fastype_of v2)
        val T = HOLogic.mk_prodT (T1, T2)
        val pair = case cq of Classical => Const(\<^const_name>\<open>cregister_pair\<close>, fastype_of v1 --> fastype_of v2 --> mk_cvariableT T)
                            | Quantum => Const(\<^const_name>\<open>qregister_pair\<close>, fastype_of v1 --> fastype_of v2 --> mk_qvariableT T)
      in pair $ v1 $ v2 end

fun varterm_to_varterm1 VTUnit : varterm1 = VTUnit
  | varterm_to_varterm1 (VTSingle (n,NoIndex,T)) = VTSingle (n,T)
  | varterm_to_varterm1 (VTSingle _) = error "varterm_to_varterm1: encountered index"
  | varterm_to_varterm1 (VTCons (t1,t2)) = VTCons (varterm_to_varterm1 t1, varterm_to_varterm1 t2)

fun varterm1_to_varterm VTUnit : varterm = VTUnit
  | varterm1_to_varterm (VTSingle (n,T)) = VTSingle (n, NoIndex, T)
  | varterm1_to_varterm (VTCons (t1,t2)) = VTCons (varterm1_to_varterm t1, varterm1_to_varterm t2)

fun varterm_to_variable1 cq = varterm_to_varterm1 #> varterm1_to_variable1 cq

fun varterm_to_variable2 Classical VTUnit = \<^term>\<open>empty_cregister :: unit c2variable\<close>
  | varterm_to_variable2 Quantum VTUnit = \<^term>\<open>empty_qregister :: unit q2variable\<close>
  | varterm_to_variable2 Classical (VTSingle (name,Index1,T)) =
          \<^instantiate>\<open>v=\<open>Free (name, mk_cvariableT T)\<close> and 'a=T in term \<open>cregister_chain cFst v :: 'a c2variable\<close>\<close>
  | varterm_to_variable2 Classical (VTSingle (name,Index2,T)) =
          \<^instantiate>\<open>v=\<open>Free (name, mk_cvariableT T)\<close> and 'a=T in term \<open>cregister_chain cSnd v :: 'a c2variable\<close>\<close>
  | varterm_to_variable2 Quantum (VTSingle (name,Index1,T)) =
          \<^instantiate>\<open>v=\<open>Free (name, mk_qvariableT T)\<close> and 'a=T in term \<open>qregister_chain qFst v :: 'a q2variable\<close>\<close>
  | varterm_to_variable2 Quantum (VTSingle (name,Index2,T)) =
          \<^instantiate>\<open>v=\<open>Free (name, mk_qvariableT T)\<close> and 'a=T in term \<open>qregister_chain qSnd v :: 'a q2variable\<close>\<close>
  | varterm_to_variable2 _ (VTSingle (name,NoIndex,T)) =
          raise error ("varterm_to_variable2: not an indexed variable: " ^ name)
  | varterm_to_variable2 cq (VTCons (t1, t2)) = let
        val v1 = varterm_to_variable2 cq t1
        val v2 = varterm_to_variable2 cq t2
        val T1 = case cq of Classical => dest_c2variableT (fastype_of v1) | Quantum => dest_q2variableT (fastype_of v1)
        val T2 = case cq of Classical => dest_c2variableT (fastype_of v2) | Quantum => dest_q2variableT (fastype_of v2)
        val T = HOLogic.mk_prodT (T1, T2)
        val pair = case cq of Classical => Const(\<^const_name>\<open>cregister_pair\<close>, fastype_of v1 --> fastype_of v2 --> mk_c2variableT T)
                            | Quantum => Const(\<^const_name>\<open>qregister_pair\<close>, fastype_of v1 --> fastype_of v2 --> mk_q2variableT T)
      in pair $ v1 $ v2 end

fun decompose_singleton_variable ctxt (v as Free (n,T)) = (case lookup_variable ctxt n of
      NONE => NONE
      | SOME {name, in_typ, out_typ=_, qc} => SOME (qc, name, NoIndex, in_typ))
  | decompose_singleton_variable ctxt (\<^Const_>\<open>qregister_chain _ _ _\<close> $ \<^Const_>\<open>qFst _ _\<close> $ (v as Free (n,T))) = (case lookup_variable ctxt n of
      NONE => NONE
      | SOME {name, in_typ, out_typ=_, qc} => SOME (qc, name, Index1, in_typ))
  | decompose_singleton_variable ctxt (\<^Const_>\<open>qregister_chain _ _ _\<close> $ \<^Const_>\<open>qSnd _ _\<close> $ (v as Free (n,T))) = (case lookup_variable ctxt n of
      NONE => NONE
      | SOME {name, in_typ, out_typ=_, qc} => SOME (qc, name, Index2, in_typ))
  | decompose_singleton_variable ctxt (\<^Const_>\<open>cregister_chain _ _ _\<close> $ \<^Const_>\<open>cFst _ _\<close> $ (v as Free (n,T))) = (case lookup_variable ctxt n of
      NONE => NONE
      | SOME {name, in_typ, out_typ=_, qc} => SOME (qc, name, Index1, in_typ))
  | decompose_singleton_variable ctxt (\<^Const_>\<open>cregister_chain _ _ _\<close> $ \<^Const_>\<open>cSnd _ _\<close> $ (v as Free (n,T))) = (case lookup_variable ctxt n of
      NONE => NONE
      | SOME {name, in_typ, out_typ=_, qc} => SOME (qc, name, Index2, in_typ))
  | decompose_singleton_variable _ _ = NONE

fun variable_to_varterm _    (Const(\<^const_name>\<open>empty_cregister\<close>,_)) = VTUnit
  | variable_to_varterm _    (Const(\<^const_name>\<open>empty_qregister\<close>,_)) = VTUnit
  | variable_to_varterm ctxt (Const(\<^const_name>\<open>cregister_pair\<close>,_) $ t1 $ t2) = VTCons (variable_to_varterm ctxt t1, variable_to_varterm ctxt t2)
  | variable_to_varterm ctxt (Const(\<^const_name>\<open>qregister_pair\<close>,_) $ t1 $ t2) = VTCons (variable_to_varterm ctxt t1, variable_to_varterm ctxt t2)
  | variable_to_varterm ctxt v = case decompose_singleton_variable ctxt v of
      NONE => raise TERM("variable_to_varterm: unknown/unparseable variable", [v])
      | SOME (_, name, index, typ) => VTSingle (name, index, typ)

fun variable_to_varterm1 ctxt = variable_to_varterm ctxt #> varterm_to_varterm1

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

fun nameq ((x:string,i1:index,_:typ), (y,i2:index,_:typ)) = i1=i2 andalso x=y

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

(* TODO something more reliable than just simp'ing *)
fun distinct_vars_tac ctxt = let
  val ctxt = (Config.put Simplifier.simp_trace false ctxt) addsimps @{thms 
    distinct_cvars_split2 ccompatible3 ccompatible3' (* cregister_chain_id *)
    distinct_qvars_split1 distinct_qvars_split2 qcompatible3 qcompatible3' (* qregister_chain_id *)
    Cccompatible_CREGISTER_of Qqcompatible_QREGISTER_of}
  in Misc.succeed_or_error_tac' (SOLVED' (simp_tac ctxt)) ctxt (fn t => "Cannot prove that the variables are variables and distinct (using simp): " ^ Syntax.string_of_term ctxt t) end

(* fun register_n qc true 1 = Const(case qc of Classical => \<^const_name>\<open>cregister_id\<close> | Quantum => \<^const_name>\<open>qregister_id\<close>, dummyT)
  | register_n qc false 1 = Const(case qc of Classical => \<^const_name>\<open>cFst\<close> | Quantum => \<^const_name>\<open>qFst\<close>, dummyT)
  | register_n qc last n = let
      val _ = n > 1 orelse error "register_n: n must be >= 1"
      in Const(case qc of Classical => \<^const_name>\<open>cregister_pair\<close> | Quantum => \<^const_name>\<open>qregister_pair\<close>, dummyT) $
          Const(case qc of Classical => \<^const_name>\<open>cSnd\<close> | Quantum => \<^const_name>\<open>qSnd\<close>, dummyT) $
          register_n qc last (n-1) end *)

fun register_n Quantum true 1 = Const(\<^const_name>\<open>qregister_id\<close>, dummyT)
  | register_n Classical true 1 = Const(\<^const_name>\<open>cregister_id\<close>, dummyT)
  | register_n Quantum false 1 = Const(\<^const_name>\<open>qFst\<close>, dummyT)
  | register_n Classical false 1 = Const(\<^const_name>\<open>cFst\<close>, dummyT)
  | register_n Quantum true 2 = Const(\<^const_name>\<open>qSnd\<close>, dummyT)
  | register_n Classical true 2 = Const(\<^const_name>\<open>cSnd\<close>, dummyT)
  | register_n Quantum last n = let
      val _ = n > 1 orelse error "register_n: n must be >= 1"
      in Const(\<^const_name>\<open>qregister_chain\<close>, dummyT) $ Const(\<^const_name>\<open>qSnd\<close>, dummyT) $ register_n Quantum last (n-1) end
  | register_n Classical last n = let
      val _ = n > 1 orelse error "register_n: n must be >= 1"
      in Const(\<^const_name>\<open>cregister_chain\<close>, dummyT) $ Const(\<^const_name>\<open>cSnd\<close>, dummyT) $ register_n Classical last (n-1) end

fun is_empty_qregisterT ctxt (\<^Type>\<open>qregister T _\<close>) = Sign.of_sort (Proof_Context.theory_of ctxt) (T,\<^sort>\<open>CARD_1\<close>)
  | is_empty_qregisterT _ T = raise TYPE("is_empty_qregisterT: not a qregister type", [T], [])

fun is_empty_qregister ctxt t = is_empty_qregisterT ctxt (fastype_of t)
  handle TYPE(_, Ts, _) => raise TYPE("is_empty_qregister: not a qregister type", Ts, [t])

(* Normalizes a register (e.g., removes id registers etc.) *)
val normalize_register_conv = Conv.bottom_rewrs_conv 
  @{thms qregister_chain_id[THEN eq_reflection] qregister_id_chain[THEN eq_reflection] qregister_chain_pair[symmetric, THEN eq_reflection]}

(* Like normalize_register_conv, but prefers \<lbrakk>Fst o X, Fst o Y\<rbrakk> over Fst o \<lbrakk>X, Y\<rbrakk> *)
fun normalize_register_conv2 ctxt = 
  normalize_register_conv ctxt then_conv Conv.top_rewrs_conv @{thms qregister_chain_pair[THEN eq_reflection]} ctxt

local
val qregister_conversion_to_register_conv_simpset = 
  \<^context> addsimps @{thms qregister_chain_pair qregister_chain_assoc[symmetric] 
                          qregister_of_cregister_Fst qregister_of_cregister_Snd}
  |> simpset_of
(* Specifically for \<lbrakk>F \<mapsto> qregister_id\<rbrakk> *)
val qregister_conversion_to_register_conv_id = Conv.rewr_conv @{thm qregister_conversion_id[THEN eq_reflection]}
fun qregister_conversion_to_register_conv0 ctxt ct = let
  val (lhs,rhs) = case Thm.term_of ct of Const(\<^const_name>\<open>qregister_conversion\<close>,_) $ lhs $ rhs => (lhs,rhs)
                                       | _ => raise CTERM ("qregister_conversion_to_register_conv: not a register conversion", [ct])
  val (rhs_inT, _) = dest_qregisterT (fastype_of rhs)
  fun add_to_path prefix path = case path of \<^Const_>\<open>qregister_id _\<close> => prefix | _ =>
    let val (prefix_inT, _) = dest_qregisterT (fastype_of prefix)
        val (path_inT, path_outT) = dest_qregisterT (fastype_of path)
    in \<^Const>\<open>qregister_chain path_inT path_outT prefix_inT\<close> $ path $ prefix end
  fun get_rhs_registers (\<^Const_>\<open>qregister_pair T1 _ T2\<close> $ r1 $ r2) path found = 
      found |> get_rhs_registers r1 (add_to_path \<^Const>\<open>qFst T1 T2\<close> path)
            |> get_rhs_registers r2 (add_to_path \<^Const>\<open>qSnd T2 T1\<close> path)
   | get_rhs_registers reg path found = 
      if is_empty_qregister ctxt reg then found
      else (reg,path) :: found
  val rhs_registers = get_rhs_registers rhs \<^Const>\<open>qregister_id rhs_inT\<close> []
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
in
(* Tries to rewrite a `qregister_conversion F G` into an index-register.
   (Index-registers are registers build from chain, pair, Fst, Snd, id.) *)
fun qregister_conversion_to_register_conv ctxt = 
  normalize_register_conv2 ctxt then_conv 
  (qregister_conversion_to_register_conv_id else_conv qregister_conversion_to_register_conv0 ctxt)
end

(* Tactic to fully prove a goal of the form `qregister_le F G` *)
(* TODO: support cregisters as well *)
fun qregister_le_tac ctxt = let
  fun tac' ctxt i st = st |>
          ((resolve_tac ctxt @{thms qregister_le_refl qregister_le_id} i THEN distinct_vars_tac ctxt i)
          ORELSE
          (resolve_tac ctxt @{thms qregister_le_pair_rightI1 qregister_le_pair_rightI2} i THEN distinct_vars_tac ctxt i THEN tac' ctxt i)
          ORELSE
          (resolve_tac ctxt @{thms qregister_le_pair_leftI} i THEN distinct_vars_tac ctxt i THEN tac' ctxt i THEN tac' ctxt i)
          ORELSE
          (resolve_tac ctxt [@{lemma \<open>qregister Q ==> qregister_le empty_qregister Q\<close> by simp}] i THEN distinct_vars_tac ctxt i)
          )
in SUBGOAL (fn (t,i) => 
  CONVERSION (normalize_register_conv2 ctxt) i 
  (* THEN print_tac ctxt "qregister_le_tac" *)
  THEN 
  (case t of Const(\<^const_name>\<open>Trueprop\<close>,_) $ (Const(\<^const_name>\<open>qregister_le\<close>,_) $ (Const(\<^const_name>\<open>qregister_pair\<close>,_) $ _ $ _) $ _) =>
    (* Why to we have this special case? *)
    resolve_tac ctxt @{thms qregister_le_pair_leftI} i THEN distinct_vars_tac ctxt i THEN qregister_le_tac ctxt i THEN qregister_le_tac ctxt i
  | _ =>  tac' ctxt i))
end

(* Returns a theorem `qregister_le ctxt lhs rhs` if possible *)
(* TODO: support cregisters as well *)
fun qregister_le_prove ctxt lhs rhs = let
  val (rhs_inT, rhs_outT) = dest_qregisterT_ct (Thm.ctyp_of_cterm rhs)
  val (lhs_inT, lhs_outT) = dest_qregisterT_ct (Thm.ctyp_of_cterm lhs)
  val _ = \<^assert> (Thm.eq_ctyp (rhs_outT, lhs_outT))
  val less_eq_goal = \<^instantiate>\<open>lhs and rhs and 'a=lhs_inT and 'b=rhs_inT and 'c=lhs_outT
          in cprop \<open>qregister_le (lhs::('a,'c) qregister) (rhs::('b,'c) qregister)\<close>\<close>
in
  Goal.prove_internal ctxt [] less_eq_goal (K (qregister_le_tac ctxt 1))
end

(* Rewrites `apply_qregister F A` into `apply_qregister target (apply_qregister (qregister_conversion \<dots>) A)`
  for suitable \<dots>
  Analogously for apply_qregister_space. *)
fun apply_qregister_conversion_conv ctxt target ct = let
  val thm = case Thm.term_of ct of 
              \<^Const_>\<open>apply_qregister _ _\<close> $ _ $ _ => @{thm qregister_apply_conversion[THEN eq_reflection]}
            | \<^Const_>\<open>apply_qregister_space _ _\<close> $ _ $ _ => @{thm apply_qregister_space_conversion[THEN eq_reflection]}
            | _ => raise CTERM ("apply_qregister_conversion_conv: term should be of the form `apply_qregister F A`", [ct])
  val source = Thm.dest_arg1 ct
  val argument = Thm.dest_arg ct
  val less_eq_thm = qregister_le_prove ctxt source target
in
  (infer_instantiate ctxt [(("x",1), argument)] thm) OF [less_eq_thm]
end

(* Returns true if argument is a (quantum) index-register *)
(* TODO: support cregisters as well *)
fun is_index_qregister (Const(\<^const_name>\<open>qregister_pair\<close>,_) $ t $ u) = is_index_qregister t andalso is_index_qregister u
  | is_index_qregister (Const(\<^const_name>\<open>qregister_chain\<close>,_) $ t $ u) = is_index_qregister t andalso is_index_qregister u
  | is_index_qregister (Const(\<^const_name>\<open>qFst\<close>,_)) = true
  | is_index_qregister (Const(\<^const_name>\<open>qSnd\<close>,_)) = true
  | is_index_qregister \<^Const_>\<open>qregister_id _\<close> = true
  | is_index_qregister _ = false

(* Transforms F into [F1,\<dots>,Fn] such that F is equivalent to (F1;\<dots>Fn). *)
(* TODO: support cregisters as well *)
fun explode_variable (Const(\<^const_name>\<open>qregister_pair\<close>,_) $ F $ G) = explode_variable F @ explode_variable G
  | explode_variable (Const(\<^const_name>\<open>qregister_chain\<close>,_) $ \<^Const_>\<open>qregister_id _\<close> $ G) = explode_variable G
  | explode_variable (Const(\<^const_name>\<open>qregister_chain\<close>,_) $ F $ \<^Const_>\<open>qregister_id _\<close>) = explode_variable F
  | explode_variable (Const(\<^const_name>\<open>qregister_chain\<close>,_) $ F $ G) =
      explode_variable G |> map (fn g =>
         \<^Const>\<open>qregister_chain \<open>fastype_of F |> dest_qregisterT |> fst\<close> \<open>fastype_of F |> dest_qregisterT |> snd\<close> \<open>fastype_of g |> dest_qregisterT |> fst\<close>\<close> 
        $ F $ g)
  | explode_variable \<^Const_>\<open>empty_qregister _ _\<close> = []
  | explode_variable F = [F]    

(* Transforms [F1,\<dots>,Fn] into (F1;\<dots>Fn). *)
(* Note: not an exact inverse of explode_variable: it's only guaranteed that 
   "implode_variable (explode_variable X)" is equivalent to X *)
(* TODO: support cregisters as well *)
fun implode_variable T [a] = a
  | implode_variable T [] = \<^Const>\<open>empty_qregister HOLogic.unitT T\<close>
  | implode_variable T (F::Gs) = let
      val G = implode_variable T Gs
      in
       \<^Const>\<open>qregister_pair \<open>fastype_of F |> dest_qregisterT |> fst\<close> \<open>fastype_of F |> dest_qregisterT |> snd\<close> \<open>fastype_of G |> dest_qregisterT |> fst\<close>\<close> 
        $ F $ G
      end

(* Given variables F,G, returns an upper bound FG.
   (Heuristically. Is not guaranteed to be a true upper bound.
   But in simple cases, should be a lub.) *)
(* TODO: support cregisters as well *)
fun join_registers (_:Proof.context) F G = if F aconv G then SOME F else let
  val Fs = explode_variable F
  val Gs = explode_variable G
  fun is_id \<^Const_>\<open>qregister_id _\<close> = true
    | is_id _ = false
  val (_, memoryT) = dest_qregisterT (fastype_of F)
  in if exists is_id Fs orelse exists is_id Fs then
        SOME \<^Const>\<open>qregister_id memoryT\<close>
     else if subset (op aconv) (Gs, Fs) then SOME F
     else if subset (op aconv) (Fs, Gs) then SOME G
     else let
      val FGs = Fs @ Gs |> sort_distinct Term_Ord.fast_term_ord
      val FG = implode_variable memoryT FGs
      in
      SOME FG
      end
  end

(* fun join_registers_ct ctxt F G = join_registers ctxt (Thm.term_of F) (Thm.term_of G) |> Option.map (Thm.cterm_of ctxt) *)

(* Solves a goal of the form \<open>qregister_le Q ?QR \<and> qregister_le R ?QR\<close> by instantiating ?QR
   as small as possible.
*)
fun qregister_lub_tac ctxt = Misc.MY_SUBGOAL ctxt (fn {ctxt, csubgoal, ...} => let
  (* val _ = \<^print>("qregister_lub_tac", Thm.cterm_of ctxt t) *)
  val (Q,R) = case Thm.term_of csubgoal of
            \<^Const_>\<open>Trueprop\<close> $ (\<^Const_>\<open>conj\<close> $ (\<^Const_>\<open>qregister_le _ _ _\<close> $ Q $ _)
                                              $ (\<^Const_>\<open>qregister_le _ _ _\<close> $ R $ _))
                => (Q,R)
          | _ => error "qregister_lub_tac"
  (* val _ = \<^print> (Q,R) *)
  val QR = case join_registers ctxt Q R of
             SOME QR => QR | NONE => error ("could not find upper bound of " ^ Syntax.string_of_term ctxt Q ^ " and " ^ Syntax.string_of_term ctxt R)
  (* val _ = \<^print> QR *)
  val lemma = @{lemma \<open>qregister_le Q QR \<Longrightarrow> qregister_le R QR \<Longrightarrow> qregister_le Q QR \<and> qregister_le R QR\<close> by simp}
  val lemma = infer_instantiate ctxt [(("QR",0), Thm.cterm_of ctxt QR), (("Q",0), Thm.cterm_of ctxt Q), (("R",0), Thm.cterm_of ctxt R)] lemma
  val tac =
   (* Misc.print_here_tac ctxt \<^here> THEN  *)
    resolve_tac ctxt [lemma] 1
 (* THEN Misc.print_here_tac ctxt \<^here>  *)
    THEN qregister_le_tac ctxt 1
 (* THEN Misc.print_here_tac ctxt \<^here>  *)
    THEN qregister_le_tac ctxt 1
  (* THEN Misc.print_here_tac ctxt \<^here>  *)
  in
    tac ORELSE Misc.error_tac (K "qregister_lub_tac: failed to prove le") ctxt
  end
)

(* fun maybe_focus_params ctxt tac = SUBGOAL (fn (t,i) => 
  case t of \<^Const_>\<open>Pure.all _\<close> $ _ => Subgoal.FOCUS_PARAMS (fn {context,...} => tac context 1) ctxt i
          | _ => tac ctxt i) *)

(* 
Does not backtrack once tmp1 succeeds.
*)
fun translate_to_index_registers_assm_lub_tac ctxt = Misc.MY_SUBGOAL ctxt (fn {ctxt,...} =>
  (resolve_tac ctxt @{thms translate_to_index_registers_assm_lub_tac_aux}
  THEN' (qregister_lub_tac ctxt ORELSE' Misc.error_tac' (fn g => "Could not find lub in: " ^ Syntax.string_of_term ctxt g) ctxt)
  THEN' (CONVERSION (qregister_conversion_to_register_conv ctxt |> Conv.arg1_conv |> HOLogic.Trueprop_conv) ORELSE' Misc.error_tac' (K "TODO proper error message in translate_to_index_registers_assm_lub_tac") ctxt)
  THEN' (resolve_tac ctxt @{thms refl} ORELSE' Misc.error_tac' (K "TODO proper error message in translate_to_index_registers_assm_lub_tac") ctxt)
  THEN' (CONVERSION (qregister_conversion_to_register_conv ctxt |> Conv.arg1_conv |> HOLogic.Trueprop_conv) ORELSE' Misc.error_tac' (K "TODO proper error message in translate_to_index_registers_assm_lub_tac") ctxt)
  THEN' (resolve_tac ctxt @{thms refl} ORELSE' Misc.error_tac' (K "TODO proper error message in translate_to_index_registers_assm_lub_tac") ctxt)) 1)

(* TODO: Maybe use this fragment for error messages in translate_to_index_registers_conv_tac:

  fun raise_error e = let
     val term_str = Misc.string_of_term_truncated ctxt 5 (Thm.term_of ct)
     fun exception_to_str (Misc.LAZY_ERROR (Misc.Lazy_Error e)) = e ()
       | exception_to_str e = Runtime.exn_message (Runtime.exn_context (SOME ctxt) e)
  in raise ERROR ("I was trying to process the following subterm:\n  " 
        ^ term_str ^ "\nThis subterm was the result of transforming its children into index registers "
        ^ "(where possible)\nand bringing non-index-registers to the top.\n"
        ^ "In the current step, I tried to push the non-index-registers up further (using lemmas\nfrom "
        ^ (Pretty.marks_str (Proof_Context.markup_extern_fact \<^context> \<^named_theorems>\<open>translate_to_index_registers\<close>) |> Pretty.string_of)
        ^ ") but that failed with the following error:\n" ^ exception_to_str e)
    end

 *)

(* TODO: rewrite all [translate_to_index_registers] rules *)

type translate_to_index_registers_conv_options = {
  trace: bool, (* Activates detailed trace *)
  level: int, (* Nesting level of this invocation (for indentation in tracing) *)
  descend: bool (* If true, descends into the term until it finds something involving registers *)
}

val translate_to_index_registers_conv_default_options : translate_to_index_registers_conv_options =
  {trace = true, level = 0, descend = true}
fun translate_to_index_registers_conv_default_options_inc_level {trace, level, descend} : translate_to_index_registers_conv_options =
  {trace=trace, level=level+1, descend=descend}

fun translate_to_index_registers_conv_tac' ctxt config rules i (st:thm) = let
  fun named_thms_str () = (Pretty.marks_str (Proof_Context.markup_extern_fact ctxt \<^named_theorems>\<open>translate_to_index_registers\<close>) |> Pretty.string_of)
  val thisgoal = Thm.cprem_of st i |> Thm.term_of
  val thisgoal_str = Lazy.lazy (fn () => thisgoal |> Syntax.string_of_term ctxt)
  fun err msg = error ("translate_to_index_registers_conv_tac: TODO need better error message: " ^ msg ^ ", goal: " ^ Lazy.force thisgoal_str)
  val ngoals = Thm.nprems_of st
  val next_config = translate_to_index_registers_conv_default_options_inc_level config
  val trace = if #trace config then
    let val indent = replicate_string (#level config) "  " in fn str => 
        let val lines = split_lines (str ())
            val indented_lines = map (fn line => indent ^ line) lines
            val indented_str = cat_lines indented_lines in        
        tracing indented_str end end
    else fn _ => ()
  val _ = trace (fn () => "Attempting to translate registers in:\n  " ^ Lazy.force thisgoal_str)
  (* fun guarded_some guard x = if guard then SOME x else NONE *)
  val fallback_rules = [
     @{lemma \<open>TTIR_APPLY_QREGISTER A F B \<Longrightarrow> PROP TTIR_EQ A (apply_qregister F B)\<close> by (simp add: TTIR_EQ_def TTIR_APPLY_QREGISTER_def)},
     @{lemma \<open>TTIR_APPLY_QREGISTER_SPACE A F B \<Longrightarrow> PROP TTIR_EQ A (apply_qregister_space F B)\<close> by (simp add: TTIR_EQ_def TTIR_APPLY_QREGISTER_SPACE_def)},
     @{lemma \<open>TTIR_APPLY_QREGISTER_SPACE A qregister_id A\<close> by (simp add: apply_qregister_space_def TTIR_APPLY_QREGISTER_SPACE_def)},
     @{lemma \<open>TTIR_APPLY_QREGISTER A qregister_id A\<close> by (simp add: TTIR_APPLY_QREGISTER_def)}]
  val st = case Misc.resolve_and_remember_rule ctxt rules i st of
               SOME (rule,st) => (trace (fn () => "Successfully applied a rule from " ^ named_thms_str () ^ Misc.theorem_or_name ctxt ". Namely " ".\nNamely " rule);
                                  st)
             | NONE => 
           case Misc.resolve_and_remember_rule ctxt fallback_rules i st of
               SOME (rule,st) => (trace (fn () => "Successfully applied a fallback rule." ^ Misc.theorem_or_name ctxt " Namely " "\nNamely " rule);
                                  st)
             | NONE => 
           case (#descend config, thisgoal) of
               (true, \<^Const_>\<open>TTIR_EQ _\<close> $ (t $ u) $ Var _) => (trace (fn () => "Descending into subterms separately.");
                                 SINGLE (resolve_tac ctxt [infer_instantiate ctxt [(("A",0), Thm.cterm_of ctxt t), (("B",0), Thm.cterm_of ctxt u)]
                                         @{lemma \<open>PROP TTIR_EQ (A::'a::{}\<Rightarrow>'b::{}) C \<Longrightarrow> PROP TTIR_EQ B D ==> PROP TTIR_EQ (A B) (C D)\<close> by (simp add: TTIR_EQ_def)}] i) st |> the)
             | (true, \<^Const_>\<open>TTIR_EQ _\<close> $ (Abs _) $ Var _) => (trace (fn () => "Descending into lambda abstraction.");
                                 SINGLE (resolve_tac ctxt [@{lemma \<open>(\<And>x. PROP TTIR_EQ (A x) (B x)) \<Longrightarrow> PROP TTIR_EQ (A::'a::{}\<Rightarrow>'b::{}) B\<close> by (auto simp add: TTIR_EQ_def intro!: pure_extensional)}] i) st |> the)
             | (true, \<^Const_>\<open>TTIR_EQ _\<close> $ _ $ Var _) => (trace (fn () => "Doing nothing.");
                                 SINGLE (resolve_tac ctxt [@{lemma \<open>PROP TTIR_EQ (A::'a::{}) A\<close> by (simp add: TTIR_EQ_def)}] i) st |> the)
             | _ => 
           error ("No rule matched in " ^ named_thms_str() ^ " when trying to solve:\n" ^ Lazy.force thisgoal_str)
  val nr_new_goals = Thm.nprems_of st - ngoals + 1
  val _ = nr_new_goals < 0 andalso err "nr_new_goals < 0"
  fun condition_tac' i st = let (* Guard against non-solving or giving new subgoals *)
    val ngoals = Thm.nprems_of st
    val subgoal = Thm.cprem_of st i |> Thm.term_of
    val subgoal_str = Lazy.lazy (fn () => subgoal |> Syntax.string_of_term ctxt)
    val _ = trace (fn () => "Solving subgoal " ^ Lazy.force subgoal_str)
    val st = case Logic.strip_assums_concl subgoal of
               (* TODO: Also need to descend into registers themselves via TTIR_EQ *)
               \<^Const_>\<open>Trueprop\<close> $ (\<^Const_>\<open>TTIR_APPLY_QREGISTER_SPACE _ _\<close> $ _ $ _ $ _) => 
                 SINGLE (translate_to_index_registers_conv_tac' ctxt next_config rules i) st
             | \<^Const_>\<open>Trueprop\<close> $ (\<^Const_>\<open>TTIR_APPLY_QREGISTER _ _\<close> $ _ $ _ $ _) => 
                 SINGLE (translate_to_index_registers_conv_tac' ctxt next_config rules i) st
             | \<^Const_>\<open>TTIR_EQ _\<close> $ _ $ _ => 
                 SINGLE (translate_to_index_registers_conv_tac' ctxt next_config rules i) st
             | \<^Const_>\<open>Trueprop\<close> $ (\<^Const_>\<open>TTIR_LUB _ _ _ _\<close> $ _ $ _ $ _ $ _ $ _) => 
                 SINGLE (translate_to_index_registers_assm_lub_tac ctxt i) st
             | \<^Const_>\<open>Trueprop\<close> $ (\<^Const_>\<open>TTIR_QREGISTER _ _\<close> $ _) =>
                SINGLE (resolve_tac ctxt [@{lemma \<open>qregister F \<Longrightarrow> TTIR_QREGISTER F\<close> for F by (simp add: TTIR_QREGISTER_def)}] i
                        THEN distinct_vars_tac ctxt i) st
             | t => (\<^print> t;
                     raise ERROR ("When translating registers, got a condition of the wrong form (" ^ Syntax.string_of_term ctxt subgoal
                                 ^ ").\nThis probably means a there is a malformed rule in " ^ named_thms_str() ^ "."))
    val st = case st of SOME st => st
                      | NONE => err ("condition tac failed")
(*     val st = case SINGLE (condition_tac i) st of SOME st => st
             | NONE => err ("condition_tac failed (subgoal " ^ Lazy.force subgoal_str ^ ")") *)
    val _ = Thm.nprems_of st < ngoals - 1 andalso err ("condition_tac removed more than one subgoal (subgoal " ^ Lazy.force subgoal_str ^ ")")
    val _ = Thm.nprems_of st >= ngoals andalso err ("condition_tac did not remove subgoal (subgoal " ^ Lazy.force subgoal_str ^ ")")
    in st end
  fun repeat_condition_tac 0 _ st = st
    | repeat_condition_tac n i st = condition_tac' i st |> repeat_condition_tac (n-1) i 
  val st = repeat_condition_tac nr_new_goals i st
  val _ = trace (fn () => "Successfully translated.")
in 
  Seq.single st
end

fun translate_to_index_registers_conv_tac ctxt config rules =
  resolve_tac ctxt [@{lemma \<open>PROP TTIR_EQ A B \<Longrightarrow> A::'a::{} \<equiv> B\<close> by (simp add: TTIR_EQ_def)}]
  THEN' translate_to_index_registers_conv_tac' ctxt config rules

(* TODO move to Misc *)
fun conv_from_tac ctxt tac ct = let
  val _ = Term.is_schematic (Thm.term_of ct) andalso error "schematic vars in conv_from_tac not yet supported"
  val idx = Thm.maxidx_of_cterm ct + 1
  val goal = Thm.apply (Thm.apply (Thm.cterm_of ctxt \<^Const>\<open>Pure.eq \<open>Thm.typ_of_cterm ct\<close>\<close>)
                                  ct)
                       (Thm.var ((("rhs",idx),Thm.ctyp_of_cterm ct)))
(* val _ = goal |> \<^print> *)
  val thm = Goal.prove_internal ctxt [] goal (K tac)
(* val _ = thm |> \<^print> *)
in thm end

fun translate_to_index_registers_conv ctxt config = let
  val rules = \<^named_theorems>\<open>translate_to_index_registers\<close> |> Proof_Context.get_thms ctxt
  in conv_from_tac ctxt (translate_to_index_registers_conv_tac ctxt config rules 1) end

end
