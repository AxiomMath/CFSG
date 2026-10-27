module

public import CFSG.Certificates.Kernel.Misc.Sp8U0CovSound
public import Certificates.Kernel.Misc.Sp8U0.Final
public import Certificates.Kernel.Misc.Sp8U0.ChecksCov
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Sp8U0

open CFSG.KC.Sp8U0 CFSG.KC.Sp8Syl3 CFSG.RankThree.PartTwo.Sec21.FF81.Sp8

theorem u06_pairs : ∀ s < 5, EncS ((gpS.getD s []).take 8) (COV (2 * s)) ∧
    EncS ((gpS.getD s []).drop 8) (COV (2 * s + 1)) := by
  decide +kernel

theorem u06_starts : ∀ k < 133, EncS (repS.getD k []) (CFSG.KD.BfsK.recX COV (oK COV k) 0) := by
  decide +kernel

theorem u06_pair1 :
    gpS.all (fun gg => mulS (gg.take 8) (gg.drop 8) == CFSG.Quasithin.H13.Mat8Cert.one8) = true := by
  decide +kernel

theorem u06_covChk : covChk899106 = true :=
  covChk_of u06_gens u06_tab_ok u06_pairs u06_starts u06_pair1 u06_orb_ok u06_cov_ok

end CFSG.KD.Sp8U0

end
