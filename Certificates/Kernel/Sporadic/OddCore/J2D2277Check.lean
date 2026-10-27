module

public import Certificates.Kernel.Sporadic.OddCore.J2LocF
public import Certificates.Kernel.SporSch.Pair.J2Chain
public import Certificates.Kernel.Sporadic.OddCore.CntCCmd
meta import CFSG.Sporadic.SmallOddCore.J2LocalCheckInputs
meta import CFSG.Sporadic.Schreier.PairJ2CheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

meta def CertificateChecks.KernelSpor.J2DCnt.gsM : List (Array Nat) :=
  CFSG.Sporadic.SmallOddCore.j2DGens.map CFSG.Sporadic.SmallOddCore.Native.natArr

namespace CertificateChecks.KernelSpor.J2DCnt

@[expose] noncomputable def DP : List Nat :=
  [CertificateChecks.KernelSpor.J2D.GI 0, CertificateChecks.KernelSpor.J2D.GI 1]

end CertificateChecks.KernelSpor.J2DCnt

#kcntc3 CertificateChecks.KernelSpor.J2DC CertificateChecks.KernelSporSch.PJ2 315 9
  CFSG.Sporadic.Schreier.PairJ2.levels CertificateChecks.KernelSpor.J2DCnt.gsM
  CertificateChecks.KernelSpor.J2DCnt.DP

namespace CertificateChecks.KernelSpor.J2DCnt

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch

theorem k_small : bAnd(canonL 315 9 DP, Nat.beq (sumN (rcnt (KernelSporSch.PJ2.LR 0)) J2DC.CS) 12) =
    true := by
  quickRfl

end CertificateChecks.KernelSpor.J2DCnt

end
