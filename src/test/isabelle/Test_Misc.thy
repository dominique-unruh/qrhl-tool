theory Test_Misc
  imports UnitTest "../../main/isabelle/QRHL_Core"
begin

ML \<open>assert_aconv_conv
(Misc.pat_lambda_conv @{context} [])
@{cterm "e::unit\<Rightarrow>_"}
@{term "\<lambda>_::unit. e ()"}\<close>

end
