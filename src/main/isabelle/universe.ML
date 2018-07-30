structure Universe =
struct

fun instantiate_value tycon thy =
let val arity = Sign.arity_number thy tycon
    val sorts = replicate arity \<^sort>\<open>value\<close>
    val vs = Name.invent_names Name.context "'a" sorts
    val tycon_info = 
      case Typedef.get_info_global thy tycon of
        [info] => info
      | [] => error (tycon^" not defined by typedef")
      | _ => error ("Typedef.get_info_global thy \""^tycon^"\" returns several items")
    val Rep_inject = #Rep_inject (snd tycon_info)
    val rep_type = #rep_type (fst tycon_info)
    val abs_type = #abs_type (fst tycon_info)
    val Rep = Const(#Rep_name (fst tycon_info), abs_type --> rep_type)
    (* val inst_type = Type(tycon,map TFree vs) *)
    val OFCLASS_value_typedef = @{thm OFCLASS_value_typedef} (* Global_Theory.get_thm thy "Universe.OFCLASS_value_typedef" *)
    val lthy = Class.instantiation ([tycon],vs,\<^sort>\<open>value\<close>) thy

    val bind = Binding.suffix_name ("_"^(List.last (Long_Name.explode tycon))) \<^binding>\<open>embedding'\<close>
    val rhs = @{ml_term "(fst embedding' \<circ> (Rep::'abs_type::value\<Rightarrow>'rep_type::value), snd (embedding'::'rep_type universe_embedding))"
                for Rep=Rep 'abs_type=abs_type 'rep_type=rep_type}
    val ((_,(_,emb_thm)),lthy) = Local_Theory.define ((bind,NoSyn), ((Thm.def_binding bind,[]), rhs)) lthy
    val emb_thm_global = Proof_Context.export lthy (lthy |> Proof_Context.theory_of |> Proof_Context.init_global) [emb_thm] |> hd

    val OFCLASS_thm = OFCLASS_value_typedef OF [emb_thm_global,Rep_inject]
    val thy = Class.prove_instantiation_exit (fn _ => resolve0_tac [OFCLASS_thm] 1) lthy
in
thy
end

fun try_instantiate_value tycon thy =
  let fun err () = (tracing ("Did not instantiate "^Syntax.string_of_typ_global thy (Type(tycon,[]))^" :: "
                              ^Syntax.string_of_sort_global thy @{sort value}); thy) in
    instantiate_value tycon thy
    handle ERROR _ => (err (); thy)
         | THM _ => (err (); thy)
  end

end
