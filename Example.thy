theory Example
  imports QRHL
begin

definition "square x = x*x"

lemma square_simp[simp]: "square x = x*x"
  using square_def by auto

(* Uncomment this to get detailed type information in the qRHL tool: *)
(* declare[[show_types,show_sorts]] *)

end
