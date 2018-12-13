structure QRHL_Operations = 
struct

fun make_ctxt_ref ctx = let
  val id = serial ()
  val _ = Refs.Ctxt.write id ctx
in
  id
end

fun make_thm_ref thm = let
  val id = serial ()
  val _ = Refs.Thm.write id thm
in
  id
end

fun tac_dummy_thm NONE = NONE
  | tac_dummy_thm (SOME ts) = SOME (ts,0)

fun parse_term ctx str T = let
  val parsed = Syntax.parse_term ctx str
  val constrained = Const("_type_constraint_", T --> T) $ parsed
  val term = Syntax.check_term ctx constrained
in term end


(** A codec for types that leads to much more compact serializations *)

fun class_tight_encode c = XML.Elem((c,[]),[])
fun class_tight_decode (XML.Elem((c,[]),[])) = Codec.Success c
  | class_tight_decode xml = Codec.Failure ("invalid encoding for a type class",[xml])

fun typ_tight_encode (Type(name,Ts)) = XML.Elem (("t",[]), XML.Text name :: map typ_tight_encode Ts)
  | typ_tight_encode (TFree(name,sort)) = XML.Elem (("f",[]), XML.Text name :: map class_tight_encode sort)
  | typ_tight_encode (TVar((name,idx),sort)) = XML.Elem (("v",[(name,string_of_int idx)]), map class_tight_encode sort)

fun typ_tight_decode (XML.Elem (("t",[]), XML.Text name :: xmls)) : typ Codec.result = 
       Codec.bind_result (fn Ts => Codec.Success (Type(name, Ts))) (Codec.traverse_results typ_tight_decode xmls)
  | typ_tight_decode (XML.Elem (("f",[]), XML.Text name :: xmls)) =
       Codec.bind_result (fn sort => Codec.Success (TFree(name,sort))) (Codec.traverse_results class_tight_decode xmls)
  | typ_tight_decode (xml as XML.Elem (("v",[(name,idx)]), xmls)) =
       (Codec.bind_result (fn sort => Codec.Success (TVar((name,parse_int idx),sort))) (Codec.traverse_results class_tight_decode xmls)
       handle Fail str => Codec.Failure ("invalid encoding for a schematic type variable: "^str, [xml]))
  | typ_tight_decode xml = Codec.Failure ("invalid encoding for a type",[xml])

val typ_tight_codec = Codec.basic {decode=typ_tight_decode, encode=typ_tight_encode}

(** A codec for terms that leads to much more compact serializations *)

fun term_tight_encode (Const(name,typ)) = XML.Elem(("c",[]),[XML.Text name,typ_tight_encode typ])
  | term_tight_encode (t1 $ t2) = XML.Elem(("a",[]),[term_tight_encode t1, term_tight_encode t2])
  | term_tight_encode (Free(name,typ)) = XML.Elem (("f",[]), [XML.Text name, typ_tight_encode typ])
  | term_tight_encode (Var((name,idx),typ)) = XML.Elem (("v",[(name,string_of_int idx)]), [typ_tight_encode typ])
  | term_tight_encode (Abs((name,T,body))) = XML.Elem (("A",[]), [XML.Text name, typ_tight_encode T, term_tight_encode body])
  | term_tight_encode (Bound i) = XML.Elem (("b",[]), [XML.Text (string_of_int i)])

fun term_tight_decode (XML.Elem(("c",[]),[XML.Text name,typ])) = 
      Codec.bind_result (fn typ => Codec.Success (Const(name,typ))) (typ_tight_decode typ)
  | term_tight_decode (XML.Elem(("a",[]),[t1, t2])) =
      Codec.bind_result (fn t1 => Codec.bind_result (fn t2 => Codec.Success (t1$t2)) (term_tight_decode t2))
      (term_tight_decode t1)
  | term_tight_decode (XML.Elem (("f",[]), [XML.Text name, xml])) =
       Codec.bind_result (fn typ => Codec.Success (Free(name,typ))) (typ_tight_decode xml)
  | term_tight_decode (xml as XML.Elem (("v",[(name,idx)]), [xml1])) =
       (Codec.bind_result (fn typ => Codec.Success (Var((name,parse_int idx),typ))) (typ_tight_decode xml1)
       handle Fail str => Codec.Failure ("invalid encoding for a schematic variable: "^str, [xml]))
  | term_tight_decode (XML.Elem (("A",[]), [XML.Text name, xml_T, xml_body])) =
       Codec.bind_result (fn T => Codec.bind_result (fn body => Codec.Success (Abs(name,T,body)))
       (term_tight_decode xml_body)) (typ_tight_decode xml_T)
  | term_tight_decode (xml as XML.Elem (("b",[]), [XML.Text (i)])) =
       (Codec.Success (Bound (parse_int i))
       handle Fail str => Codec.Failure ("invalid encoding for a schematic variable: "^str, [xml]))
  | term_tight_decode xml = Codec.Failure ("invalid encoding for a term",[xml])

val term_tight_codec = Codec.basic { encode=term_tight_encode, decode=term_tight_decode }

(** A codec for terms that additionally attaches a human readable representation *)

fun expression_encode (ctxt,t) = let
  (* val ctxt = Context.the_local_context () *)
  val str = YXML.content_of (Syntax.string_of_term ctxt t)
  val xml = XML.Elem (("expression",[]),[XML.Text str, term_tight_encode t, typ_tight_encode (fastype_of t)])
  in xml end
(* fun expression_decode (XML.Elem (("expression",[]),[XML.Text _, xml, _])) = term_tight_decode xml
  | expression_decode xml = Codec.Failure ("invalid encoding for a term (expression codec)",[xml]) *)
fun expression_decode _ = error "expression_decode: not implemented"

val expression_codec = Codec.basic { encode=expression_encode, decode=expression_decode }






end