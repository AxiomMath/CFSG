module

public import Certificates.Kernel.Item434Gen.HeData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelItem434.He

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Item434Gen
open CFSG.RankThree.PartTwo.Sec4.Item434SporGen

theorem k1s0 : wordEqK 8330 14 (mask 14) (pidn 8330 14) L LI 2 (heFix1.sw.getD 0 []) (SV 1 0) =
    true := by quickRfl

theorem k1s1 : wordEqK 8330 14 (mask 14) (pidn 8330 14) L LI 2 (heFix1.sw.getD 1 []) (SV 1 1) =
    true := by quickRfl

theorem k1s2 : wordEqK 8330 14 (mask 14) (pidn 8330 14) L LI 2 (heFix1.sw.getD 2 []) (SV 1 2) =
    true := by quickRfl

theorem k1s3 : wordEqK 8330 14 (mask 14) (pidn 8330 14) L LI 2 (heFix1.sw.getD 3 []) (SV 1 3) =
    true := by quickRfl

theorem k1i : allN 4 (fun j => permOK 8330 14 (mask 14) (8330 * 14) (SV 1 j) (SIV 1 j)) = true := by
  quickRfl

theorem k1a : wordEqK 8330 14 (mask 14) (pidn 8330 14) (SV 1) (SIV 1) 4 heFix1.wa (HV 0) = true := by
  quickRfl

theorem k1b : wordEqK 8330 14 (mask 14) (pidn 8330 14) (SV 1) (SIV 1) 4 heFix1.wb (HV 2) = true := by
  quickRfl

theorem k1e : (e9K 8330 14 (HV 8) (HV 6) &&
    sigK 8330 14 (SV 1) 4 heFix1.ords heFix1.ps (HV 8) (HV 6)) = true := by quickRfl

end CertificateChecks.KernelItem434.He

end
