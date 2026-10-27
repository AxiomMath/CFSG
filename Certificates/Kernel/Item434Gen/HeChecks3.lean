module

public import Certificates.Kernel.Item434Gen.HeData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelItem434.He

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Item434Gen
open CFSG.RankThree.PartTwo.Sec4.Item434SporGen

theorem k3s0 : wordEqK 8330 14 (mask 14) (pidn 8330 14) L LI 2 (heFix3.sw.getD 0 []) (SV 3 0) =
    true := by quickRfl

theorem k3s1 : wordEqK 8330 14 (mask 14) (pidn 8330 14) L LI 2 (heFix3.sw.getD 1 []) (SV 3 1) =
    true := by quickRfl

theorem k3s2 : wordEqK 8330 14 (mask 14) (pidn 8330 14) L LI 2 (heFix3.sw.getD 2 []) (SV 3 2) =
    true := by quickRfl

theorem k3s3 : wordEqK 8330 14 (mask 14) (pidn 8330 14) L LI 2 (heFix3.sw.getD 3 []) (SV 3 3) =
    true := by quickRfl

theorem k3i : allN 4 (fun j => permOK 8330 14 (mask 14) (8330 * 14) (SV 3 j) (SIV 3 j)) = true := by
  quickRfl

theorem k3a : wordEqK 8330 14 (mask 14) (pidn 8330 14) (SV 3) (SIV 3) 4 heFix3.wa (HV 0) = true := by
  quickRfl

theorem k3b : wordEqK 8330 14 (mask 14) (pidn 8330 14) (SV 3) (SIV 3) 4 heFix3.wb (HV 2) = true := by
  quickRfl

theorem k3e : (e9K 8330 14 (HV 8) (HV 10) &&
    sigK 8330 14 (SV 3) 4 heFix3.ords heFix3.ps (HV 8) (HV 10)) = true := by quickRfl

end CertificateChecks.KernelItem434.He

end
