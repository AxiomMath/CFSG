
module

public import Certificates.Kernel.SporSch.Co1.Split
public import CFSG.Certificates.Kernel.SporSch.Co1GenSound
public import CFSG.Sporadic.Schreier.Co1RigidCheckInputs
public meta import Certificates.Kernel.SporSch.GenPerms
public meta import CFSG.Sporadic.Schreier.Co1RigidCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co1Gen

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.Native

meta def CRA : Array (Array Nat) := #[cRows 0, cRows 1]

meta def CRIA : Array (Array Nat) := #[inv (cRows 0), inv (cRows 1)]

meta def XA : Array (Array Nat) := #[xR]

meta def YA : Array (Array Nat) := #[yR]

end CertificateChecks.KernelSporSch.Co1Gen

#kss_perms CertificateChecks.KernelSporSch.Co1Gen.CRP 24 CertificateChecks.KernelSporSch.Co1Gen.CRA
#kss_perms CertificateChecks.KernelSporSch.Co1Gen.CRIP 24 CertificateChecks.KernelSporSch.Co1Gen.CRIA
#kss_perms CertificateChecks.KernelSporSch.Co1Gen.XP 24 CertificateChecks.KernelSporSch.Co1Gen.XA
#kss_perms CertificateChecks.KernelSporSch.Co1Gen.YP 24 CertificateChecks.KernelSporSch.Co1Gen.YA

namespace CertificateChecks.KernelSporSch.Co1Gen

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch.M24 CFSG.KS.SporSch.VOrb
open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.Native
open CertificateChecks.KernelSporSch.Co1Elem CertificateChecks.KernelSporSch.Co1Split
open CertificateChecks.KernelSporSch.Co1ThreeLocal

theorem kC0 : Nat.beq (mulK (powK (mulK (mulK (mulK (GF 2) (GF 0)) (GGI 2)) (GGI 0)) 2) (GF 0))
    (CRP 0) = true := by quickRfl
theorem kC1 : Nat.beq (mulK (powK (mulK (mulK (mulK (GF 2) (GF 1)) (GGI 2)) (GGI 1)) 2) (GF 1))
    (CRP 1) = true := by quickRfl
theorem kCI : allN 2 (fun i => invOKK (CRP i) (CRIP i)) = true := by quickRfl
theorem kX : bindListK 24 24 (XP 0) X.toList = true := by quickRfl
theorem kY : bindListK 24 24 (YP 0) Y.toList = true := by quickRfl

theorem kGI : allN 3 (fun i => invOKK (GF i) (GGI i)) = true := by quickRfl

theorem gi (i : Nat) (hi : i < 3) : invOKK (GF i) (GGI i) = true := allN_spec kGI i hi

theorem c_eq (i : Nat) (hi : i < 2) : cRows i = unpack 24 24 (CRP i) := by
  unfold cRows
  rw [gRows_eq]
  interval_cases i
  · exact cK_sound (gi 2 (by omega)) (gi 0 (by omega)) kC0
  · exact cK_sound (gi 2 (by omega)) (gi 1 (by omega)) kC1

theorem ci_eq (i : Nat) (hi : i < 2) : inv (cRows i) = unpack 24 24 (CRIP i) := by
  rw [c_eq i hi]
  exact (invOKK_sound (allN_spec kCI i hi)).2

theorem x_eq : xR = unpack 24 24 (XP 0) := by
  have h : xR = X := by
    unfold xR X
    rw [inv_c, aR_eq, cR_eq]
  rw [h]
  exact arr kX

theorem y_eq : yR = unpack 24 24 (YP 0) := by
  rw [yR_eq]
  exact arr kY

end CertificateChecks.KernelSporSch.Co1Gen

end
