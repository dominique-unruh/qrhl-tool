theory Example
  imports QRHL
begin

definition "square x = x*x"

lemma square_simp[simp]:
  "square x = x*x"
  using square_def by auto

end
