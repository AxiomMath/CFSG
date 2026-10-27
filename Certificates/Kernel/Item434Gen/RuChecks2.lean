module

public import Certificates.Kernel.Item434Gen.RuData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelItem434.Ru

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Item434Gen
open CFSG.RankThree.PartTwo.Sec4.Item434SporGen

theorem k2s0 : wordEqK 4060 12 (mask 12) (pidn 4060 12) L LI 2 (ruFix2.sw.getD 0 []) (SV 2 0) =
    true := by quickRfl

theorem k2s1 : wordEqK 4060 12 (mask 12) (pidn 4060 12) L LI 2 (ruFix2.sw.getD 1 []) (SV 2 1) =
    true := by quickRfl

theorem k2s2 : wordEqK 4060 12 (mask 12) (pidn 4060 12) L LI 2 (ruFix2.sw.getD 2 []) (SV 2 2) =
    true := by quickRfl

theorem k2s3 : wordEqK 4060 12 (mask 12) (pidn 4060 12) L LI 2 (ruFix2.sw.getD 3 []) (SV 2 3) =
    true := by quickRfl

theorem k2i : allN 4 (fun j => permOK 4060 12 (mask 12) (4060 * 12) (SV 2 j) (SIV 2 j)) = true := by
  quickRfl

theorem k2a : wordEqK 4060 12 (mask 12) (pidn 4060 12) (SV 2) (SIV 2) 4 ruFix2.wa (RV 0) = true := by
  quickRfl

theorem k2b : wordEqK 4060 12 (mask 12) (pidn 4060 12) (SV 2) (SIV 2) 4 ruFix2.wb (RV 2) = true := by
  quickRfl

theorem k2e : (e9K 4060 12 (RV 8) (RV 9) &&
    sigK 4060 12 (SV 2) 4 ruFix2.ords ruFix2.ps (RV 8) (RV 9)) = true := by quickRfl

end CertificateChecks.KernelItem434.Ru

end
