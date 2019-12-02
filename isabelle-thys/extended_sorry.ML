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
    and collect_many [] seen = seen
      | collect_many (body::bodies) seen = collect_many bodies (collect body seen)
  in fn bodies => unions_oracles (#1 (collect_many bodies ([], Inttab.empty))) end;
(* END reimplementation *)

fun all_axclass_oracles ctxt =
  let val sort_algebra = Proof_Context.tsig_of ctxt |> Type.rep_tsig |> #classes |> snd |> Sorts.dest_algebra []
      val thy = Proof_Context.theory_of ctxt
      val classrels = sort_algebra |> #classrel |> map (fn (cl1,cls2) => map (fn cl2 => (cl1,cl2)) cls2) |> List.concat
      val classrel_proofs = classrels |> map (Proofterm.classrel_proof thy)
      val arity_proofs = sort_algebra |> #arities |> map (fn arity => Proofterm.arity_proof thy arity handle ERROR _ => MinProof)
      val proofs = classrel_proofs @ arity_proofs |> map Proofterm.approximate_proof_body
  in
    all_oracles_of proofs
  end


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

fun show_oracles_lines_generic inwhere ctxt oracles = let
  val known_oracles = ctxt
                          |> Thm.extern_oracles false |> map (fn (m as (_,props),name) => 
                              (Properties.get props "name" |> the,
                               Markup.markup m name))
                          |> Symtab.make
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
    "Oracles used in " ^ inwhere ^ ":" :: (map show oracles)
  end

fun show_oracles_lines ctxt thms = let
  (* val ctxt = thm |> Thm.theory_of_thm |> Proof_Context.init_global *)
  val oracles = thms |> map Thm.proof_body_of |> all_oracles_of
  val inwhere = if length thms = 1 then "theorem" else "theorems"
in show_oracles_lines_generic inwhere ctxt oracles end

fun show_axclass_oracles_lines ctxt = let
  val oracles = all_axclass_oracles ctxt
in show_oracles_lines_generic "type classes" ctxt oracles end


fun show_oracles ctxt thms = show_oracles_lines ctxt thms |> map (fn s => s^"\n") |> Output.writelns
val show_axclass_oracles = Output.writelns o map (fn s => s^"\n") o show_axclass_oracles_lines

fun show_oracles_cmd thms = Toplevel.keep (fn state => 
  let val ctxt = Toplevel.context_of state 
      val thms = Attrib.eval_thms ctxt thms
  in show_oracles ctxt thms end)

val show_axclass_oracles_cmd = Toplevel.keep (fn state => 
  let val ctxt = Toplevel.context_of state 
  in show_axclass_oracles ctxt end)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_oracles\<close> "print oracles using in proving the theorem"
    (Parse.thms1 >> show_oracles_cmd)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_instance_oracles\<close> "print oracles using in proving type class instantiations etc."
    (Scan.succeed show_axclass_oracles_cmd)


end
