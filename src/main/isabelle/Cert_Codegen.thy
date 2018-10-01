theory Cert_Codegen
  imports Main ML_Term_Antiquot
begin

definition "list_last list xs x = (xs@[x] = list)"
lemma list_lastI: "(xs@[x] == list) \<Longrightarrow> list_last list xs x"
  unfolding list_last_def by simp

definition "assert_equals a b = (a=b)"
lemma assert_equals_refl: "assert_equals a a" unfolding assert_equals_def by simp
definition [simp]: "assert_string_neq (a::string) b = (a \<noteq> b)"
lemma NO_MATCH_I: "NO_MATCH x y" by simp

definition "constant_function f y = (\<forall>x. f x = y)"
lemma constant_function_absI: "constant_function (%z::'a. y) y"
  unfolding constant_function_def by simp

ML_file "cert_codegen.ML"

setup \<open>
let open Cert_Codegen in
  add_specs [
    list_last_spec,
    constant_function_spec,
    assert_equals_func_spec,
    string_concat_func_spec,
    assert_string_neq_func_spec,
    NO_MATCH_func_spec]
end
\<close>

end
