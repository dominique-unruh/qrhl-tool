theory TestEx
  imports QRHL.QRHL
begin

definition "x == True"

lemma test2: x
unfolding x_def
      by auto (* FAILS *)


end
