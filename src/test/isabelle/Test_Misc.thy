theory Test_Misc
  imports UnitTest "QRHL.QRHL_Core"
begin

ML \<open>
  assert_aconv_conv
  (Misc.pat_lambda_conv \<^context> [])
  \<^cterm>\<open>e::unit\<Rightarrow>_\<close>
  \<^term>\<open>\<lambda>_::unit. e ()\<close>
\<close>

end
