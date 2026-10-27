module

public import Certificates.Kernel.Item434Gen.HeData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelItem434.He

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Item434Gen
open CFSG.RankThree.PartTwo.Sec4.Item434SporGen

theorem k0s0 : wordEqK 8330 14 (mask 14) (pidn 8330 14) L LI 2 (heFix0.sw.getD 0 []) (SV 0 0) =
    true := by quickRfl

theorem k0s1 : wordEqK 8330 14 (mask 14) (pidn 8330 14) L LI 2 (heFix0.sw.getD 1 []) (SV 0 1) =
    true := by quickRfl

theorem k0s2 : wordEqK 8330 14 (mask 14) (pidn 8330 14) L LI 2 (heFix0.sw.getD 2 []) (SV 0 2) =
    true := by quickRfl

theorem k0s3 : wordEqK 8330 14 (mask 14) (pidn 8330 14) L LI 2 (heFix0.sw.getD 3 []) (SV 0 3) =
    true := by quickRfl

theorem k0i : allN 4 (fun j => permOK 8330 14 (mask 14) (8330 * 14) (SV 0 j) (SIV 0 j)) = true := by
  quickRfl

theorem k0a : wordEqK 8330 14 (mask 14) (pidn 8330 14) (SV 0) (SIV 0) 4 heFix0.wa (HV 0) = true := by
  quickRfl

theorem k0b : wordEqK 8330 14 (mask 14) (pidn 8330 14) (SV 0) (SIV 0) 4 heFix0.wb (HV 2) = true := by
  quickRfl

theorem k0e : (e9K 8330 14 (HV 8) (HV 4) &&
    sigK 8330 14 (SV 0) 4 heFix0.ords heFix0.ps (HV 8) (HV 4)) = true := by quickRfl

end CertificateChecks.KernelItem434.He

end
