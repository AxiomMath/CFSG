module

public import Certificates.Kernel.UnitarySix.Sec3.K3604Chk
public import Certificates.Kernel.UnitarySix.Sec3.F3601
import CFSG.Certificates.Kernel.RankThree.F2Perm
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native CFSG.KC.U6

theorem kENat : ((CFSG.EvenSmallLie.UnitarySix.tWords.all fun w => strictB (natK w) fun X =>
    PermK X (pinvS 693 10 (mask 10) X) && sfS X) &&
    CFSG.EvenSmallLie.UnitarySix.kWords.all fun w => strictB (natK w) fun X =>
      PermK X (pinvS 693 10 (mask 10) X) && sfK2 X) = true := by
  decide +kernel

theorem qz_lt : ∀ w ∈ qzWords, ∀ k ∈ w, k < 18 := by decide +kernel

end CertificateChecks.KernelU6.Sec3
