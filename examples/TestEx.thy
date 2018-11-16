theory TestEx
  imports QRHL.QRHL
begin

definition "x == True"

lemma test2: x
      by auto (* FAILS *)


end
