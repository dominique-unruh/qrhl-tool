structure Extended_Sorry =
struct

(* Fixed reimplementation of Proofterm.all_oracles_of (REMOVE when the original is fixed) *)
fun join_thms (thms: Proofterm.pthm list) =
  Future.joins (map (Proofterm.thm_node_body o #2) thms);
val oracle_ord = prod_ord fast_string_ord Term_Ord.fast_term_ord;
val unions_oracles = Ord_List.unions oracle_ord;

val all_oracles_of =
  let
    fun collect_inner thms =
        tap join_thms thms |> fold (fn (i, thm_node) => fn (x, seen) =>
          if Inttab.defined seen i then (x, seen)
          else
            let
              val body = Future.join (Proofterm.thm_node_body thm_node);
              val (x', seen') = collect body (x, Inttab.update (i, ()) seen);
            in (x', seen') end)
    and collect (PBody {oracles, thms, ...}) seen = case collect_inner thms seen of (x,seen) => 
            (if null oracles then x else oracles :: x, seen)
  in fn body => unions_oracles (#1 (collect body ([], Inttab.empty))) end;
(* END reimplementation *)

val _ = if !Proofterm.proofs < 1 then 
  (Proofterm.proofs := 1; tracing "Need Proofterm.proofs >= 1 for Extended_Sorry.thy") else () 

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

(* Applies to first subgoal *)
fun marked_sorry_tac1 ctxt loc = PRIMITIVE (fn st => let
  val goal = Thm.cprem_of st 1 |> Thm.term_of
  val thm = marked_sorry ctxt loc goal
  in
    Thm.elim_implies thm st
  end)

fun marked_sorry_tac ctxt loc st = 
  (COND Thm.no_prems all_tac (marked_sorry_tac1 ctxt loc THEN marked_sorry_tac ctxt loc)) st

(* 
fun marked_sorry_tac ctxt loc = SUBGOAL (fn (goal,i) => let
  val thm = marked_sorry ctxt loc goal
  val _ = \<^print> (thm,Thm.cterm_of ctxt goal)
  in
    Thm.elim_implies solve_tac ctxt [thm] i : tactic
  end) 
 *)

fun show_oracles_lines thm = let
  val known_oracles = thm |> Thm.theory_of_thm |> Proof_Context.init_global
                          |> Thm.extern_oracles false |> map (fn (m as (_,props),name) => 
                              (Properties.get props "name" |> the,
                               Markup.markup m name))
                          |> Symtab.make
  val oracles = thm |> Thm.proof_body_of |> all_oracles_of
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
