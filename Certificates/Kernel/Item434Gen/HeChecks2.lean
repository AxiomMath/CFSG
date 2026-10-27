module

public import Certificates.Kernel.Item434Gen.HeData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelItem434.He

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Item434Gen
open CFSG.RankThree.PartTwo.Sec4.Item434SporGen

theorem k2s0 : wordEqK 8330 14 (mask 14) (pidn 8330 14) L LI 2 (heFix2.sw.getD 0 []) (SV 2 0) =
    true := by quickRfl

theorem k2s1 : wordEqK 8330 14 (mask 14) (pidn 8330 14) L LI 2 (heFix2.sw.getD 1 []) (SV 2 1) =
    true := by quickRfl

theorem k2s2 : wordEqK 8330 14 (mask 14) (pidn 8330 14) L LI 2 (heFix2.sw.getD 2 []) (SV 2 2) =
    true := by quickRfl

theorem k2s3 : wordEqK 8330 14 (mask 14) (pidn 8330 14) L LI 2 (heFix2.sw.getD 3 []) (SV 2 3) =
    true := by quickRfl

theorem k2i : allN 4 (fun j => permOK 8330 14 (mask 14) (8330 * 14) (SV 2 j) (SIV 2 j)) = true := by
  quickRfl

theorem k2a : wordEqK 8330 14 (mask 14) (pidn 8330 14) (SV 2) (SIV 2) 4 heFix2.wa (HV 0) = true := by
  quickRfl

theorem k2b : wordEqK 8330 14 (mask 14) (pidn 8330 14) (SV 2) (SIV 2) 4 heFix2.wb (HV 2) = true := by
  quickRfl

theorem k2e : (e9K 8330 14 (HV 8) (HV 9) &&
    sigK 8330 14 (SV 2) 4 heFix2.ords heFix2.ps (HV 8) (HV 9)) = true := by quickRfl

end CertificateChecks.KernelItem434.He

end
