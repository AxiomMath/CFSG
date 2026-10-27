
module

public import Certificates.Kernel.SporSch.Co1.CRows
public import Certificates.Kernel.SporSch.Co1.Elem
public import CFSG.Certificates.Kernel.SporSch.Co1RigidSound
public meta import Certificates.Kernel.SporSch.GenPerms
public meta import CFSG.Sporadic.Schreier.Co1RigidCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co1Rigid

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.Native

meta def HA : Array (Array Nat) := #[hRows 0, hRows 1, hRows 2]

meta def KA : Array (Array Nat) := #[kRows 0, kRows 1, kRows 2]

meta def RA : Array (Array Nat) := rankA.map fun r => #[r]

end CertificateChecks.KernelSporSch.Co1Rigid

#kss_perms CertificateChecks.KernelSporSch.Co1Rigid.HP 24 CertificateChecks.KernelSporSch.Co1Rigid.HA
#kss_perms CertificateChecks.KernelSporSch.Co1Rigid.KP 24 CertificateChecks.KernelSporSch.Co1Rigid.KA
#kss_perms CertificateChecks.KernelSporSch.Co1Rigid.HQ 24 CFSG.Sporadic.Co1Schreier.Native.hqT
#kss_perms CertificateChecks.KernelSporSch.Co1Rigid.DP 24 CFSG.Sporadic.Co1Schreier.Native.dqT
#kss_perms CertificateChecks.KernelSporSch.Co1Rigid.DSP 24 CFSG.Sporadic.Co1Schreier.Native.dsT
#kss_perms CertificateChecks.KernelSporSch.Co1Rigid.RT 24 CertificateChecks.KernelSporSch.Co1Rigid.RA

namespace CertificateChecks.KernelSporSch.Co1Rigid

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch.M24 CFSG.KS.SporSch.Orb CFSG.KS.Mathieu
open CertificateChecks.KernelSporSch.Co1Elem CertificateChecks.KernelSporSch.Co1Split
open CertificateChecks.KernelSporSch.Co1Gen CFSG.Sporadic.Co1Schreier

@[expose] noncomputable def CC (j : Nat) : Nat := nIf(Nat.beq j 0, CRP 0, nIf(Nat.beq j 1, CRP 1, GF 2))

theorem kQ : transOK (E.M 2) (QP 0) Data.f4vecs = true := by quickRfl
theorem kQI : invOKK (QP 0) (QP 1) = true := by quickRfl
theorem kH : allN 3 (fun i => bAnd(pos3K (pr2 (ngetPL Data.witLeft i)),
    Nat.beq (locK AF CC (ngetPL Data.witLeft i)) (HP i))) = true := by quickRfl
theorem kK : allN 3 (fun i => bAnd(pos3K (pr2 (ngetPL Data.witConj i)),
    Nat.beq (locK AF CC (ngetPL Data.witConj i)) (KP i))) = true := by quickRfl
theorem kHQ : allN 3 (fun i => Nat.beq (mulK (mulK (QP 1) (HP i)) (QP 0)) (HQ i)) = true := by
  quickRfl
theorem kD : allN 8 (fun f => bindListK 24 24 (DP f) (ngetL Data.rigBasis f)) = true := by quickRfl
theorem kDS : allN 8 (fun f => Nat.beq (mulK (mulK (QP 0) (DP f)) (QP 1)) (DSP f)) = true := by
  quickRfl
theorem kR : rankOK RT Data.rigRank = true := by quickRfl
theorem kP0 : propK HQ RT Data.rigEqs (64 * 0) 64 = true := by quickRfl
theorem kP1 : propK HQ RT Data.rigEqs (64 * 1) 64 = true := by quickRfl
theorem kP2 : propK HQ RT Data.rigEqs (64 * 2) 64 = true := by quickRfl
theorem kP3 : propK HQ RT Data.rigEqs (64 * 3) 64 = true := by quickRfl
theorem kP4 : propK HQ RT Data.rigEqs (64 * 4) 64 = true := by quickRfl
theorem kP5 : propK HQ RT Data.rigEqs (64 * 5) 64 = true := by quickRfl
theorem kP6 : propK HQ RT Data.rigEqs (64 * 6) 64 = true := by quickRfl
theorem kP7 : propK HQ RT Data.rigEqs (64 * 7) 64 = true := by quickRfl
theorem kP8 : propK HQ RT Data.rigEqs (64 * 8) 64 = true := by quickRfl
theorem kF : freeK RT Data.rigFree = true := by quickRfl
theorem kB : basisK DP HQ Data.rigFree = true := by quickRfl
theorem kRig : rigK (QP 0) (QP 1) CRP CRIP (GF 2) (GGI 2) (XP 0) (YP 0) HP KP (AF 1)
    Data.rigFree = true := by quickRfl
theorem kC0 : candK XP YP DSP (64 * 0) 64 = true := by quickRfl
theorem kC1 : candK XP YP DSP (64 * 1) 64 = true := by quickRfl
theorem kC2 : candK XP YP DSP (64 * 2) 64 = true := by quickRfl
theorem kC3 : candK XP YP DSP (64 * 3) 64 = true := by quickRfl

end CertificateChecks.KernelSporSch.Co1Rigid

end
