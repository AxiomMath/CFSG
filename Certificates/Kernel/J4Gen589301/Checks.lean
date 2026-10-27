module

public import Certificates.Data.Kernel.J4Gen589301.Run
public import Certificates.Kernel.J4Gen589301.Data
public import Certificates.Kernel.J4NPVerdict.Defs
import CFSG.Certificates.Kernel.Common.Harness
import all Init.Data.List.SplitOn.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Gen

open CFSG.KC.J4Gen CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KD.J4NPV CFSG.Quasithin.KGC31.J4M4.Gen

theorem ch589301Z : runK c rm one pad [W1, W2] (fun mem n => Nat.beq (rdK one mem n outZ) CFSG.KD.J4Gen.Z)
    (parseL CFSG.KD.J4Gen.LZ) [] 0 CFSG.KD.J4Gen.IZ = true := by quickRfl

theorem ch589301C : runK c rm one pad [A, B, CFSG.KD.J4Gen.Z]
    (fun mem n => Nat.beq (rdK one mem n outC) CFSG.KD.J4Gen.C)
    (parseL CFSG.KD.J4Gen.LC) [] 0 CFSG.KD.J4Gen.IC = true := by quickRfl

theorem ch589301AB : runK c rm one pad [W1, W2, CFSG.KD.J4Gen.C]
    (fun mem n => andB (Nat.beq (rdK one mem n outA) CFSG.KD.J4Gen.AP)
      (Nat.beq (rdK one mem n outB) CFSG.KD.J4Gen.BP))
    (parseL CFSG.KD.J4Gen.LAB) [] 0 CFSG.KD.J4Gen.IAB = true := by quickRfl

theorem ch589301F : factsK c rm one pad CFSG.KD.J4Gen.Z CFSG.KD.J4Gen.C
    (wordJ c rm one [W1, W2] [W1i, W2i] uWord) FM_9 CFSG.KD.J4Gen.AP CFSG.KD.J4Gen.BP A B
    CFSG.KD.J4Gen.G CFSG.KD.J4Gen.GI = true := by quickRfl

end CertificateChecks.KernelJ4Gen

end
