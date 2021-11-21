structure Prog_Variables =
struct

fun mk_ell2T T = Type(\<^type_name>\<open>ell2\<close>, [T])
fun dest_ell2T (Type(\<^type_name>\<open>ell2\<close>, [T])) = T
  | dest_ell2T T = raise TYPE("dest_ell2T",[T],[])

fun mk_boundedT T T' = Type(\<^type_name>\<open>cblinfun\<close>, [mk_ell2T T, mk_ell2T T'])
fun dest_boundedT (Type(\<^type_name>\<open>cblinfun\<close>, [Type(\<^type_name>\<open>ell2\<close>,[T]),Type(\<^type_name>\<open>ell2\<close>,[T'])])) = (T,T')
  | dest_boundedT T = raise TYPE("dest_boundedT",[T],[])
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

fun dest_cvariableT (Type(\<^type_name>\<open>cregister\<close>, [T, \<^typ>\<open>cl\<close>])) = T
  | dest_cvariableT T = raise TYPE("dest_cvariableT", [T], [])

fun dest_qvariableT (Type(\<^type_name>\<open>qregister\<close>, [T, \<^typ>\<open>qu\<close>])) = T
  | dest_qvariableT T = raise TYPE("dest_qvariableT", [T], [])

fun strip_var_prefix x = if String.isPrefix "var_" x 
  then String.extract (x,4,NONE) 
  else error ("strip_var_prefix: Expected string starting with var_, not "^x)

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


datatype vartype = Classical | Quantum
type varinfo = {vartype : vartype, register: term(* , name_thm : thm *)}
structure VarInfo = Generic_Data
(
  type T = varinfo Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (op=)
)

fun lookup_variable ctxt = Symtab.lookup (VarInfo.get (Context.Proof ctxt))
fun lookup_variable_type ctxt name = lookup_variable ctxt name |> Option.map #vartype

fun is_classical_variable ctxt name = case lookup_variable_type ctxt name of
  SOME Classical => true
  | _ => false

(* fun check_variable_type ctxt T =
  if Sign.of_sort (Proof_Context.theory_of ctxt) (T, \<^sort>\<open>universe\<close>) then () else
    error ("Type of variable ("^Syntax.string_of_typ ctxt T^") must be of sort "^Syntax.string_of_sort ctxt @{sort universe}^".\n"^
           "In the Isabelle theory, use 'derive universe T' for every type T defined using typedef/datatype,\n"^
           "and use declare_variable_type instead of typedecl") *)

local
fun add_varinfo morph name vartype register context = let
  (* val thm = Proof_Context.get_thm ctxt' (name ^ "_varname") *)
  val varinfo = {vartype=vartype, register=Morphism.term morph register(* , name_thm=Morphism.thm morph thm *)} : varinfo
  val context = VarInfo.map (Symtab.insert (K true) (name,varinfo)) context
  in context end

fun declare_variable_morph m name vartype typ = let
    val register = Free(name, if vartype=Classical then mk_cvariableT typ else mk_qvariableT typ)
    val chain = if vartype=Classical then Const(\<^const_name>\<open>cregister_chain\<close>, \<^typ>\<open>cl c2variable\<close> --> fastype_of register --> mk_c2variableT typ)
                                    else Const(\<^const_name>\<open>qregister_chain\<close>, \<^typ>\<open>qu q2variable\<close> --> fastype_of register --> mk_q2variableT typ)
    val register1 = if vartype=Classical then chain $ @{const cFst(cl,cl)} $ register
                                         else chain $ @{const qFst(qu,qu)} $ register
    val register2 = if vartype=Classical then chain $ @{const cSnd(cl,cl)} $ register
                                         else chain $ @{const qSnd(qu,qu)} $ register
  in
      add_varinfo m name vartype register #>
      add_varinfo m (name^"1") vartype register1 #>
      add_varinfo m (name^"2") vartype register2
  end
in
fun declare_variable_lthy name vartype typ = 
  Local_Theory.declaration {pervasive=true, syntax=false} (fn m => 
    declare_variable_morph m name vartype typ)

fun declare_variable_ctxt name vartype typ = Context.proof_map (declare_variable_morph Morphism.identity name vartype typ)

fun declare_variable_from_thm (thm:thm) = let
  val (vartype, name, T) = case Thm.prop_of thm of
      Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>cregister\<close>, _) $ Free(name, T')) =>
            (Classical, name, dest_cvariableT T')
    | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>qregister\<close>, _) $ Free(name, T')) =>
            (Quantum, name, dest_qvariableT T')
    | _ => raise THM ("declare_variable_from_thm: theorem must be of the form 'Axioms_Classical.register x' or 'Axioms_Quantum.register x' where x is a free variable", 0, [thm])
  in (declare_variable_morph Morphism.identity name vartype T) end

val _ = Attrib.setup \<^binding>\<open>variable\<close>
 (Scan.succeed (Thm.declaration_attribute declare_variable_from_thm))
  "Declare a program variable (apply to a theorem of the form \"Laws_Classical/Quantum.register x\")"
  |> Context.map_theory |> Context.>>
end


(* fun varname_assumption cq bind T = 
  let val qT = mk_variableT T
      val name = Binding.name_of bind           
      val name' = if cq=Classical then "var_"^name else name
      val lhs = Const(\<^const_name>\<open>variable_name\<close>, qT --> HOLogic.stringT) $ Free(name',qT)
      val rhs = HOLogic.mk_string name
  in HOLogic.mk_eq (lhs,rhs) |> HOLogic.mk_Trueprop end *)

(* fun addQVariableNameAssumption cq bind T ctxt =
  let val assm = varname_assumption cq bind T
      val ctxt1 = Variable.declare_term assm ctxt
      val ([(_,[thm])],ctxt2) = Proof_Context.add_assms Assumption.assume_export
                  [((Binding.suffix_name "_varname" bind,[Simplifier.simp_add]), [(assm,[])])] ctxt1
  in
    ctxt2
  end *)

(* 
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
      val ctxt = (* VarTypes.map (Symtab.insert op= (v,cq)) ctxt *)  declare_variable_ctxt v cq ctxt
      (* val ctxt = (* VarTypes.map (Symtab.insert op= (v^"1",cq)) ctxt *) declare_variable_ctxt (v^"1") cq ctxt *)
      (* val ctxt = (* VarTypes.map (Symtab.insert op= (v^"2",cq)) ctxt *) declare_variable_ctxt (v^"2") cq ctxt *)
  in
    ctxt
  end
 *)

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

(* fun parse_varlist t =
  let val vt = parse_varterm t
      fun tol (VTSingle nT) = [nT]
        | tol VTUnit = []
        | tol (VTCons (VTSingle _, VTUnit)) = raise TERM("not an explicit variable list",[t])
        | tol (VTCons (VTSingle nT, rest)) = nT :: tol rest
        | tol (VTCons _) = raise TERM("not an explicit variable list",[t])
  in
    tol vt
  end *)

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



end