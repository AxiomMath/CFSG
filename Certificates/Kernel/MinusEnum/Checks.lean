module

public import Certificates.Kernel.MinusEnum.Data
public import CFSG.Certificates.Kernel.LocalCompUnpack
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMinusEnum

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.OddTranspositions.PartThree

theorem kSz : szOK 65 7 = true := by quickRfl

theorem kNums : (Nat.beq ME.ng 65 && Nat.beq ME.N 15600) = true := by quickRfl

theorem kG : allN ME.ng (fun k => canonK 65 7 (mask 7) (Nat.mul 65 7) (ME.G k)) = true := by
  quickRfl

theorem kT0 : Nat.beq (ME.T 0) (pidn 65 7) = true := by quickRfl

theorem kK : keysSK 65 7 minusBase ME.N ME.T ((List.range 15600).map ME.K) = true := by quickRfl

theorem kBind : (Nat.beq minusTable.size ME.ng &&
    allN ME.ng fun k => bindArrK minusTable[k]! 65 7 (ME.G k)) = true := by quickRfl

end CertificateChecks.KernelMinusEnum

end
