theory OTP
  imports QRHL.QRHL
begin

declare_variable_type msg :: \<open>{finite, xor_group}\<close>

type_synonym key = msg
type_synonym ciph = msg

definition otp :: \<open>key \<Rightarrow> msg \<Rightarrow> ciph\<close> where
  \<open>otp k m = k + m\<close>

end
