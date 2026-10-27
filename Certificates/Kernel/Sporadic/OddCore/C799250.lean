module

public import Certificates.Kernel.Sporadic.OddCore.C129006
public import Certificates.Data.Kernel.Spor.MulH
public import CFSG.RankThree.PartTwo.Sec21.Hering214KJ3CycInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.PkPow CFSG.KS.MulH

@[expose] noncomputable def C799250 : Nat :=
  wfoldK 6156 13 (mask 13) CertificateChecks.KernelCensus.J3S.F
    CFSG.RankThree.PartTwo.Sec21.Hering214.j3NineWord (pidn 6156 13)

theorem k799250 : bAnd(invEqK 6156 13 (mask 13) (6156 * 13) C799250 (ppw 6156 13 C799250 8),
    bAnd(Nat.beq (pcomp 6156 13 (mask 13) C799250 (J3CentP 21))
      (pcomp 6156 13 (mask 13) (J3CentP 21) C799250),
    bAnd(Nat.beq (ppw 6156 13 C799250 9) (pidn 6156 13),
    bAnd(bIf(Nat.beq (ppw 6156 13 C799250 3) (pidn 6156 13), false, true),
      bIf(Nat.beq (ppw 6156 13 C799250 1) (pidn 6156 13), false, true))))) = true := by
  quickRfl

end CertificateChecks.KernelSpor.OddCore

end
