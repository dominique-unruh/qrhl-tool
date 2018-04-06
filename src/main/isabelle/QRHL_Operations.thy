theory QRHL_Operations
  imports "HOL-Protocol.Protocol_Main" QRHL_Core Encoding
begin

ML {*
  fun make_ctxt_ref ctx = let
    val id = serial ()
    val _ = Refs.Ctxt.write id ctx
  in
    id
  end
*}

(*
operation_setup create_context = {*
  {from_lib = Codec.string,
   to_lib = Codec.int,
   action = fn (name:string) =>
            let val _ = Thy_Info.use_thy name
              val thy = Thy_Info.get_theory ("Draft."^name)
              val ctx = Proof_Context.init_global thy
            in
              make_ctxt_ref ctx
            end}
*}
*)

operation_setup create_context = {*
  {from_lib = Codec.list Codec.string,
   to_lib = Codec.int,
   action = fn thy_names => let
     val thys = map Thy_Info.get_theory thy_names
     val thy = Theory.begin_theory ("QRHL_Session", Position.none) thys
     val ctx = Proof_Context.init_global thy
   in make_ctxt_ref ctx end}
*}

operation_setup check_type = {*
  {from_lib = Codec.tuple Codec.int Codec.term,
   to_lib = Codec.typ,
   action = fn (ctx_id,t) => QRHL.checkType (Refs.Ctxt.read ctx_id) t} *}

operation_setup delete_context = {*
  {from_lib = Codec.int,
   to_lib = Codec.unit,
   action = Refs.Ctxt.delete}
*}

operation_setup print_term = {*
  {from_lib = Codec.tuple Codec.int Codec.term,
   to_lib = Codec.string,
   action = fn (ctx_id, t) => YXML.content_of (Syntax.string_of_term (Refs.Ctxt.read ctx_id) t)}
*}

operation_setup print_typ = {*
  {from_lib = Codec.tuple Codec.int Codec.typ,
   to_lib = Codec.string,
   action = fn (ctx_id, t) => YXML.content_of (Syntax.string_of_typ (Refs.Ctxt.read ctx_id) t)}
*}

operation_setup add_assumption = {*
  {from_lib = Codec.triple Codec.string Codec.term Codec.int,
   to_lib = Codec.int,
   action = fn (name,assm,ctx_id) => make_ctxt_ref (QRHL.addAssumption name assm (Refs.Ctxt.read ctx_id))}
*}

operation_setup read_typ = {*
  {from_lib = Codec.tuple Codec.int Codec.string,
   to_lib = Codec.typ,
   action = fn (ctx_id, str) => Syntax.read_typ (Refs.Ctxt.read ctx_id) str}
*}

operation_setup simplify_term = {*
  {from_lib = Codec.triple Codec.term (Codec.list Codec.string) Codec.int,
   to_lib = Codec.term,
   action = fn (t,thms,ctx_id) => QRHL.simp t thms (Refs.Ctxt.read ctx_id)}
*}

operation_setup read_term = {*
  {from_lib = Codec.triple Codec.int Codec.string Codec.typ,
   to_lib = Codec.term,
   action = fn (ctx_id, str, T) =>
     let val ctx = Refs.Ctxt.read ctx_id
         val parsed = Syntax.parse_term ctx str
         val constrained = Const("_type_constraint_", T --> T) $ parsed
         val term = Syntax.check_term ctx constrained
     in
       term
     end}
*}

operation_setup byQRHLPre = {*
  {from_lib = Codec.tuple (Codec.list (Codec.triple Codec.string Codec.string Codec.typ)) (Codec.list (Codec.triple Codec.string Codec.string Codec.typ)),
   to_lib = Codec.term,
   action = fn (cvars,qvars) => QRHL.byQRHLPre cvars qvars}
*}

operation_setup declare_variable = {*
  {from_lib = Codec.triple Codec.int Codec.string Codec.typ,
   to_lib = Codec.int,
   action = fn (ctx_id, name, T) =>
            let val ([v],ctx') = Proof_Context.add_fixes [(Binding.name name, SOME T, NoSyn)] (Refs.Ctxt.read ctx_id)
                val _ = if v<>name then error("variable v already declared") else ()
            in make_ctxt_ref ctx' end }
*}

operation_setup declare_quantum_variable = {*
  {from_lib = Codec.triple Codec.string Codec.typ Codec.int,
   to_lib = Codec.int,
   action = fn (name,typ,ctx_id) => make_ctxt_ref (QRHL.declare_variable (Refs.Ctxt.read ctx_id) name typ QRHL.Quantum)}
*}

operation_setup declare_classical_variable = {*
  {from_lib = Codec.triple Codec.string Codec.typ Codec.int,
   to_lib = Codec.int,
   action = fn (name,typ,ctx_id) => make_ctxt_ref (QRHL.declare_variable (Refs.Ctxt.read ctx_id) name typ QRHL.Classical)}
*}

operation_setup callWp = {*
  {from_lib = Codec.tuple (Codec.triple (Codec.list Codec.term) (Codec.list Codec.term) (Codec.list Codec.term))
                          (Codec.tuple  (Codec.list Codec.term) Codec.term),
   to_lib = Codec.tuple Codec.term Codec.term,
   action = fn ((cvars1, cvars2, qvars1), (qvars2, B)) => QRHL.callWp cvars1 cvars2 qvars1 qvars2 B}
*}

operation_setup fixTac = {*
  {from_lib = Codec.tuple Codec.term Codec.string,
   to_lib = Codec.tuple Codec.term Codec.typ,
   action = fn (expr,var) => QRHL.fixTac expr var}
*}

operation_setup rndWp = {*
  {from_lib = Codec.tuple (Codec.triple Codec.string Codec.term Codec.string) (Codec.triple Codec.term Codec.typ Codec.term),
   to_lib = Codec.term,
   action = fn ((v1, e1, v2), (e2, T, B)) => QRHL.rndWp v1 e1 v2 e2 T B}
*}

operation_setup rndWp2 = {*
  {from_lib = Codec.triple (Codec.triple Codec.string Codec.typ Codec.term) (Codec.triple Codec.string Codec.typ Codec.term) (Codec.tuple Codec.term Codec.term),
   to_lib = Codec.term,
   action = fn ((v1, T1, e1), (v2, T2, e2), (f, B)) => QRHL.rndWp2 v1 T1 e1 v2 T2 e2 f B}
*}

operation_setup applyRule = {*
  {from_lib = Codec.triple Codec.string Codec.term Codec.int,
   to_lib = Codec.list Codec.term,
   action = fn (name,goal,ctx_id) => QRHL.applyRule name goal (Refs.Ctxt.read ctx_id)}
*}

operation_setup sampleWp = {*
  {from_lib = Codec.tuple (Codec.tuple Codec.string Codec.typ) (Codec.tuple Codec.term Codec.term),
   to_lib = Codec.term,
   action = fn ((v, T), (e, B)) => QRHL.sampleWp v T e B}
*}

operation_setup qapplyWp = {*
  {from_lib = Codec.triple Codec.term Codec.term (Codec.list Codec.term),
   to_lib = Codec.term,
   action = fn (post, e, q) => QRHL.qapplyWp post e q}
*}

operation_setup measureWp = {*
  {from_lib = Codec.tuple (Codec.tuple Codec.term Codec.term) (Codec.tuple Codec.term (Codec.list Codec.term)),
   to_lib = Codec.term,
   action = fn ((B, x), (e, Q)) => QRHL.measureWp B x e Q}
*}

operation_setup qinitWp = {*
  {from_lib = Codec.triple Codec.term Codec.term (Codec.list Codec.term),
   to_lib = Codec.term,
   action = fn (post, e, Q) => QRHL.qinitWp post e Q}
*}

operation_setup ifWp = {*
  {from_lib = Codec.triple Codec.term Codec.term Codec.term,
   to_lib = Codec.term,
   action = fn (e, thenWp, elseWp) => QRHL.ifWp e thenWp elseWp}
*}

operation_setup expression_to_term = {*
  {from_lib = Codec.term,
   to_lib = Codec.term,
   action = Encoding.expression_to_term}
*}

operation_setup add_index_to_expression = {*
  {from_lib = Codec.tuple Codec.term Codec.bool,
   to_lib = Codec.term,
   action = fn (t,left) => Encoding.add_index_to_expression t left}
*}

end