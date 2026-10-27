module

public import Certificates.Kernel.Sporadic.OddCore.Beta24603C
public import Certificates.Kernel.Sporadic.OddCore.SqrtK26102
public import Certificates.Kernel.Sporadic.OddCore.S16J3K27810
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.O26101

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.ColH
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.S16J3
open CertificateChecks.KernelSpor.SqrtK26102 (j3W)

@[expose] def x0Out : List Int := [-2, -1, -3, -2, -2, -1, -2, -1]

@[expose] def x0uWord : List Int := [1, 5, 1, 5, 3, 5, 1, 2, 5, 5, 3, 1, 3, 1, 5, 5]

@[expose] noncomputable def mvK (X k i : Nat) : Bool :=
  bIf(Nat.beq (lane16 (B24603Col (pg 13 (mask 13) X
    (lane16 (B24603Col (pg 13 (mask 13) X i)) k))) k) i, false, true)

@[expose] noncomputable def mv01 (X k : Nat) : Bool := bIf(mvK X k 0, true, mvK X k 1)

theorem o26101_base : bAnd(cK (TC3HJ3P 0), bAnd(cK (J3CentP 0),
    bAnd(iK (TC3HJ3P 0) (pc (TC3HJ3P 0) (pc (TC3HJ3P 0) (pc (TC3HJ3P 0) (pc (TC3HJ3P 0)
      (pc (TC3HJ3P 0) (pc (TC3HJ3P 0) (TC3HJ3P 0))))))),
    bAnd(outJ3 x0Out (TC3HJ3P 0), bAnd(j3W x0uWord (pc (TC3HJ3P 0) (J3CentP 0)),
    Nat.beq (pc (TC3HJ3P 0) (J3BetaP 7)) (pc (J3BetaP 7) (TC3HJ3P 0))))))) = true := by
  quickRfl

theorem o26101_sq : allN 1080 (fun k => mv01 (TC3HJ3P 0) k) = true := by
  quickRfl

end CertificateChecks.KernelSpor.O26101

end
