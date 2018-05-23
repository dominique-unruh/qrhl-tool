theory Tactics
  imports Encoding
begin

lemma seq:
  assumes "c = c1@c2" and "d = d1@d2"
  assumes "qrhl A c1 d1 B"
  and "qrhl A c2 d2 B"
  shows "qrhl A c d B"
  sorry

ML_file "tactics.ML"

end