module

public import Certificates.Kernel.UnitarySix.Sec3.G3600Chk
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3EData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaNativeData
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3XData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native

@[expose] noncomputable def eTransK (f : ℕ) : Bool :=
  strictB (wK qzWords[f]!) fun Q => strictB (pinvS 693 10 (mask 10) Q) fun QI =>
    PermK Q QI && Nat.beq (pg 10 (mask 10) Q 0) f &&
      (Nat.beq f 0 || !(sfA1 (pcomp 693 10 (mask 10) QI (pcomp 693 10 (mask 10) (sec3G 14) Q))))

@[expose] noncomputable def eTransRun (lo cnt : ℕ) : Bool := allN cnt fun i => eTransK (lo + i)

end CertificateChecks.KernelU6.Sec3
