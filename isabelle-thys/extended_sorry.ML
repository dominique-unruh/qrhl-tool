structure Extended_Sorry =
struct

val _ = if !Proofterm.proofs < 1 then error "Need Proofterm.proofs >= 1 for Extended_Sorry.thy" else () 

type sorry_location = { position : Position.T, comment : string }
type sorry_entry = { position : Position.T, comment : string, context : Proof.context }
val sorry_table = Synchronized.var "sorry" (Inttab.empty : sorry_entry Inttab.table)

fun sorry_marker_oracle_function (ctxt, ({position,comment}:sorry_location), t) = let
  val ser = serial ()
  val entry = {position=position, comment=comment, context=ctxt}
  val _ = Synchronized.change sorry_table (Inttab.update (ser, entry))
  val t' = \<^const>\<open>sorry_marker\<close> $ HOLogic.mk_number \<^typ>\<open>int\<close> ser $ t
  val ct = Thm.cterm_of ctxt t'
  in
    ct
  end

val (_,sorry_marker_oracle) = 
  Context.>>> (Context.map_theory_result (Thm.add_oracle (\<^binding>\<open>sorry_marker_oracle\<close>, sorry_marker_oracle_function)))

fun marked_sorry ctxt loc t = 
  sorry_marker_oracle (ctxt,loc,t) |> Conv.fconv_rule (Conv.rewr_conv @{thm sorry_marker_def})

fun marked_sorry_tac ctxt loc = SUBGOAL (fn (goal,i) => let
  val thm = marked_sorry ctxt loc goal
  in
    solve_tac ctxt [thm] i
  end) 

fun show_oracles_lines thm = let
  val known_oracles = thm |> Thm.theory_of_thm |> Proof_Context.init_global
                          |> Thm.extern_oracles false |> map (fn (m as (_,props),name) => 
                              (Properties.get props "name" |> the,
                               Markup.markup m name))
                          |> Symtab.make
  val oracles = thm |> Thm.proof_body_of |> Proofterm.all_oracles_of
  fun show ("Extended_Sorry.sorry_marker_oracle",t) = let
        val (ser,t) = case t of \<^const>\<open>sorry_marker\<close> $ n $ t => (HOLogic.dest_number n |> snd, t)
                          | t => raise (TERM ("show_oracles", [t]))
        val loc = Inttab.lookup (Synchronized.value sorry_table) ser |> the
        val pos = #position loc
        val comment = #comment loc
        val goal = Syntax.string_of_term (#context loc) t
      in "  cheat method: " ^ comment ^ Position.here pos ^ " (" ^ goal ^ ")" end
    | show (name,_) = "  " ^ (Symtab.lookup known_oracles name |> the)
  in
    "Oracles used in theorem:" :: (map show oracles)
  end

val show_oracles = Output.writelns o map (fn s => s^"\n") o show_oracles_lines

end
