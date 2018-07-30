structure Universe =
struct

val universe_markup = Syntax.string_of_sort \<^context> \<^sort>\<open>universe\<close>
fun str_tycon thy tycon = Syntax.string_of_typ_global thy (Type(tycon,[]))

fun instantiate_universe_typ (deps:string list) (typ as Type(tycon,args)) (thy:theory) : (unit Symtab.table*theory) = 
  (case SOME (Sign.arity_sorts thy tycon \<^sort>\<open>universe\<close>) handle ERROR _ => NONE of
    NONE => thy |> instantiate_universe deps tycon |> instantiate_universe_typ deps typ
    | SOME sorts =>
        fold2 (fn sort => fn T => fn (tvs,thy) => 
                if member op= sort \<^class>\<open>universe\<close> 
                then (instantiate_universe_typ deps T thy |> apfst (fn tvs' => Symtab.merge op= (tvs',tvs)))
                else (tvs,thy))
          sorts args (Symtab.empty, thy))
  | instantiate_universe_typ _ (TFree(n,_)) thy = (Symtab.make [(n,())], thy)
  | instantiate_universe_typ _ typ _ = raise (TYPE("instantiate_universe_typ",[typ],[]))
(* and instantiate_universe_dependent (deps:string list) tycon thy =
    case Typedef.get_info_global thy tycon of
                   info::_ => (tracing ("Instantiating types that "^str_tycon thy tycon^" depends on"); 
                               instantiate_universe_typ (tycon::deps) (#rep_type (fst info)) thy) 
                 | [] => thy *)
and instantiate_universe (deps:string list) tycon thy =
let val tycon_markup = str_tycon thy tycon
    (* val arity = Sign.arity_number thy tycon *)
    (* val sorts = replicate arity \<^sort>\<open>universe\<close> *)
    (* val vs = Name.invent_names Name.context "'a" sorts *)
    val tycon_info = 
      case Typedef.get_info_global thy tycon of
        [info] => info
      | [] => error (tycon^" not defined by typedef")
      | _ => error ("Typedef.get_info_global thy \""^tycon_markup^"\" returns several items")
    val Rep_inject = #Rep_inject (snd tycon_info)
    val rep_type = #rep_type (fst tycon_info)
    val abs_type = #abs_type (fst tycon_info)
    val Rep = Const(#Rep_name (fst tycon_info), abs_type --> rep_type)
    (* val thy = instantiate_universe_dependent deps tycon thy *)
    (* univ_vs contains all type variables that should be get sort universe *)
    val (univ_vs,thy) = instantiate_universe_typ (tycon::deps) rep_type thy
    val deps_string = if deps=[] then "" else " ("^String.concatWith ", which is " (map (fn tyco => "needed by "^str_tycon thy tyco) deps)^")"
    val _ = tracing ("Instantiating "^tycon_markup^" :: "^universe_markup^deps_string)
    (* val inst_type = Type(tycon,map TFree vs) *)
    val OFCLASS_universe_typedef = Thm.transfer thy @{thm OFCLASS_universe_typedef}
    val vs = Term.dest_Type abs_type |> snd |> map Term.dest_TFree
              |> map (fn (n,sort) => if Symtab.defined univ_vs n then (n,\<^class>\<open>universe\<close>::sort) else (n,sort))
    val lthy = Class.instantiation ([tycon], vs, \<^sort>\<open>universe\<close>) thy

    val bind = Binding.suffix_name ("_"^(List.last (Long_Name.explode tycon))) \<^binding>\<open>embedding'\<close>
    val rhs = @{ml_term "(fst embedding' \<circ> (Rep::'abs_type::universe\<Rightarrow>'rep_type::universe), snd (embedding'::'rep_type universe_embedding))"
                for Rep=Rep 'abs_type=abs_type 'rep_type=rep_type}
    val ((_,(_,emb_thm)),lthy) = Local_Theory.define ((bind,NoSyn), ((Thm.def_binding bind,[]), rhs)) lthy
    val emb_thm_global = Proof_Context.export lthy (lthy |> Proof_Context.theory_of |> Proof_Context.init_global) [emb_thm] |> hd

    val OFCLASS_thm = OFCLASS_universe_typedef OF [emb_thm_global,Rep_inject]
    val thy = Class.prove_instantiation_exit (fn _ => resolve0_tac [OFCLASS_thm] 1) lthy
in
thy
end

(* fun try_instantiate_universe tycon thy =
  instantiate_universe [] tycon thy
  handle ERROR _ => (tracing ("Did not instantiate "^tycon^" :: universe"); thy)
       | THM _ => (tracing ("Did not instantiate "^tycon^" :: universe"); thy); *)

fun generate_universe_cmd tyco param thy = 
  let val _ = if param <> "" then error ("Unexpected parameter ("^param^")") else ()
  in
    instantiate_universe [] tyco thy
  end

end
