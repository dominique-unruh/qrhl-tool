theory Test_Misc
  imports UnitTest "../../main/isabelle/QRHL_Core"
begin

ML \<open>
  assert_aconv_conv
  (Misc.pat_lambda_conv @{context} [])
  @{term "\<lambda>_::unit. e ()"}
  @{cterm "e::unit\<Rightarrow>_"}
\<close>

end
