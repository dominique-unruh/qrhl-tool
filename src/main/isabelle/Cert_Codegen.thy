theory Cert_Codegen
  imports Main ML_Term_Antiquot
begin

definition "assert_equals a b = (a=b)"
lemma assert_equals_refl: "assert_equals a a" unfolding assert_equals_def by simp
definition [simp]: "assert_string_neq (a::string) b = (a \<noteq> b)"
lemma NO_MATCH_I: "NO_MATCH x y" by simp

definition "constant_function f y = (\<forall>x. f x = y)"
lemma constant_function_absI: "constant_function (%z::'a. y) y"
  unfolding constant_function_def by simp

ML_file "cert_codegen.ML"

setup \<open>
  Cert_Codegen.add_specs [
    Cert_Codegen.constant_function_spec,
    Cert_Codegen.assert_equals_func_spec,
    Cert_Codegen.string_concat_func_spec,
    Cert_Codegen.assert_string_neq_func_spec,
    Cert_Codegen.NO_MATCH_func_spec]
\<close>

end
