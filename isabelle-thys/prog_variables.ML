structure Prog_Variables =
struct

open Registers open Registers_Automation open Registers_Unsorted

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

(* fun declare_variable_from_thm (thm:thm) = let
  val (vartype, name, T) = case Thm.prop_of thm of
      Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>cregister\<close>, _) $ Free(name, T')) =>
            (Classical, name, dest_cvariableT T')
    | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>qregister\<close>, _) $ Free(name, T')) =>
            (Quantum, name, dest_qvariableT T')
    | _ => raise THM ("declare_variable_from_thm: theorem must be of the form 'Axioms_Classical.register x' or 'Axioms_Quantum.register x' where x is a free variable", 0, [thm])
  in (declare_variable_morph Morphism.identity name vartype T) end *)

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

(* fun register_n qc true 1 = Const(case qc of Classical => \<^const_name>\<open>cregister_id\<close> | Quantum => \<^const_name>\<open>qregister_id\<close>, dummyT)
  | register_n qc false 1 = Const(case qc of Classical => \<^const_name>\<open>cFst\<close> | Quantum => \<^const_name>\<open>qFst\<close>, dummyT)
  | register_n qc last n = let
      val _ = n > 1 orelse error "register_n: n must be >= 1"
      in Const(case qc of Classical => \<^const_name>\<open>cregister_pair\<close> | Quantum => \<^const_name>\<open>qregister_pair\<close>, dummyT) $
          Const(case qc of Classical => \<^const_name>\<open>cSnd\<close> | Quantum => \<^const_name>\<open>qSnd\<close>, dummyT) $
          register_n qc last (n-1) end *)


(* fun join_registers_ct ctxt F G = join_registers ctxt (Thm.term_of F) (Thm.term_of G) |> Option.map (Thm.cterm_of ctxt) *)

(* fun maybe_focus_params ctxt tac = SUBGOAL (fn (t,i) => 
  case t of \<^Const_>\<open>Pure.all _\<close> $ _ => Subgoal.FOCUS_PARAMS (fn {context,...} => tac context 1) ctxt i
          | _ => tac ctxt i) *)

end
