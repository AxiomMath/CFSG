module

public import Certificates.Kernel.Sporadic.OddCore.Beta24601K
public import Certificates.Kernel.Sporadic.OddCore.SqrtK26102
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.O26100

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.J2Cn CertificateChecks.KernelSpor.S16J2

@[expose] noncomputable def nsqK (y : Nat) : Bool := bIf(Nat.beq (pc y y) idK, false, true)

@[expose] noncomputable def sqAll (m x : Nat) : Bool := allN m fun k => nsqK (pc (B24601R.T k) x)

theorem o26100_base : bAnd(cK (TC3HJ2T.F 0), bAnd(iK (TC3HJ2T.F 0) (pw 11 (TC3HJ2T.F 0)),
    bAnd(bIf(sK (TC3HJ2T.F 0), false, true), bAnd(sK (pc (TC3HJ2T.F 0) (F 0)),
    commK (TC3HJ2T.F 0) (J2BetaT.F 7))))) = true := by
  quickRfl

theorem o26100_sq : sqAll 1080 (TC3HJ2T.F 0) = true := by
  quickRfl

end CertificateChecks.KernelSpor.O26100

end
