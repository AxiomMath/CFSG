module

public import Certificates.Kernel.Item434Gen.RuData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelItem434.Ru

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Item434Gen
open CFSG.RankThree.PartTwo.Sec4.Item434SporGen

theorem k0s0 : wordEqK 4060 12 (mask 12) (pidn 4060 12) L LI 2 (ruFix0.sw.getD 0 []) (SV 0 0) =
    true := by quickRfl

theorem k0s1 : wordEqK 4060 12 (mask 12) (pidn 4060 12) L LI 2 (ruFix0.sw.getD 1 []) (SV 0 1) =
    true := by quickRfl

theorem k0s2 : wordEqK 4060 12 (mask 12) (pidn 4060 12) L LI 2 (ruFix0.sw.getD 2 []) (SV 0 2) =
    true := by quickRfl

theorem k0s3 : wordEqK 4060 12 (mask 12) (pidn 4060 12) L LI 2 (ruFix0.sw.getD 3 []) (SV 0 3) =
    true := by quickRfl

theorem k0i : allN 4 (fun j => permOK 4060 12 (mask 12) (4060 * 12) (SV 0 j) (SIV 0 j)) = true := by
  quickRfl

theorem k0a : wordEqK 4060 12 (mask 12) (pidn 4060 12) (SV 0) (SIV 0) 4 ruFix0.wa (RV 0) = true := by
  quickRfl

theorem k0b : wordEqK 4060 12 (mask 12) (pidn 4060 12) (SV 0) (SIV 0) 4 ruFix0.wb (RV 2) = true := by
  quickRfl

theorem k0e : (e9K 4060 12 (RV 8) (RV 4) &&
    sigK 4060 12 (SV 0) 4 ruFix0.ords ruFix0.ps (RV 8) (RV 4)) = true := by quickRfl

end CertificateChecks.KernelItem434.Ru

end
