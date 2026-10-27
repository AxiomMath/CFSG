module

public import Certificates.Kernel.SporSch.Co1.Quot
public import CFSG.Certificates.Kernel.SporSch.Co1LiftSound
public import CFSG.Sporadic.Schreier.Co1LiftCheckInputs
public meta import Certificates.Kernel.SporSch.Co1.GenLift
public meta import CFSG.Sporadic.Schreier.Co1LiftData
public meta import CFSG.Sporadic.Schreier.Co1StabCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.SporSch.Co1Lift
public import Certificates.Kernel.SporSch.Co1.GenLift

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co1Lift

meta def LR : Array Nat := CFSG.Sporadic.Co1Schreier.Data.liftReps.toArray

meta def Z : Nat := CFSG.Sporadic.Co1Schreier.Native.stabVec 0

end CertificateChecks.KernelSporSch.Co1Lift

#kss_co1lift CertificateChecks.KernelSporSch.Co1Lift.D CertificateChecks.KernelSporSch.Co1Lift.LR
  CertificateChecks.KernelSporSch.Co1Lift.Z

namespace CertificateChecks.KernelSporSch.Co1Lift

open CFSG.KS.Raw CFSG.KS.SporSch.Lift CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.Native
open CFSG.Sporadic.Co2Cert CertificateChecks.KernelSporSch.Co1Stab
open CertificateChecks.KernelSporSch.Co1Quot CertificateChecks.KernelSporSch.Co1Packed

theorem k : liftK D.PR Q0 Q1 PH0 PH1 16663704 D.Ms = true := by quickRfl

theorem bR : bindListK 2300 24 D.PR Data.liftReps = true := by quickRfl

theorem z_eq : stabVec 0 = 16663704 := rfl

theorem spec_eq : liftCheck = liftSpec Data.liftReps.toArray co2OrigArrs[0]! co2OrigArrs[1]!
    hRows0 hRows1 (stabVec 0) := rfl

end CertificateChecks.KernelSporSch.Co1Lift

end
