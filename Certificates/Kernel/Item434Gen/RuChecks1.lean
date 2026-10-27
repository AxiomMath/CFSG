module

public import Certificates.Kernel.Item434Gen.RuData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelItem434.Ru

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Item434Gen
open CFSG.RankThree.PartTwo.Sec4.Item434SporGen

theorem k1s0 : wordEqK 4060 12 (mask 12) (pidn 4060 12) L LI 2 (ruFix1.sw.getD 0 []) (SV 1 0) =
    true := by quickRfl

theorem k1s1 : wordEqK 4060 12 (mask 12) (pidn 4060 12) L LI 2 (ruFix1.sw.getD 1 []) (SV 1 1) =
    true := by quickRfl

theorem k1s2 : wordEqK 4060 12 (mask 12) (pidn 4060 12) L LI 2 (ruFix1.sw.getD 2 []) (SV 1 2) =
    true := by quickRfl

theorem k1s3 : wordEqK 4060 12 (mask 12) (pidn 4060 12) L LI 2 (ruFix1.sw.getD 3 []) (SV 1 3) =
    true := by quickRfl

theorem k1i : allN 4 (fun j => permOK 4060 12 (mask 12) (4060 * 12) (SV 1 j) (SIV 1 j)) = true := by
  quickRfl

theorem k1a : wordEqK 4060 12 (mask 12) (pidn 4060 12) (SV 1) (SIV 1) 4 ruFix1.wa (RV 0) = true := by
  quickRfl

theorem k1b : wordEqK 4060 12 (mask 12) (pidn 4060 12) (SV 1) (SIV 1) 4 ruFix1.wb (RV 2) = true := by
  quickRfl

theorem k1e : (e9K 4060 12 (RV 8) (RV 6) &&
    sigK 4060 12 (SV 1) 4 ruFix1.ords ruFix1.ps (RV 8) (RV 6)) = true := by quickRfl

end CertificateChecks.KernelItem434.Ru

end
