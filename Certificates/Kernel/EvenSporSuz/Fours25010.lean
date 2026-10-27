module

public import Certificates.Data.Kernel.EvenSporSuz.Outer
public import Certificates.Kernel.EvenSporSuz.Data
public import Certificates.Kernel.Sporadic.OddCore.Suz26990
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.FoursCheck
import all Certificates.Kernel.EvenSporSuz.Data
import all Init.Data.List.SplitOn.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSuz.FW CFSG.EvenSporadicStandard.TwoSuz.foursWitnessText

namespace CertificateChecks.KernelSuz

open CFSG.KC.EvenSporSuz CFSG.EvenSporadicStandard.TwoSuz

@[expose] noncomputable def fwW : List (List ℤ) := (nonEmptyLines FW.chars).map owK

@[expose] noncomputable def l0M : List (List ℕ) := [mulR negR AR, mulR negR BR]

@[expose] noncomputable def l0I : List (List ℕ) := l0M.map invR24

@[expose] noncomputable def x25010 : List ℕ := evalR l0M l0I ((fwW.getD 0 []).map zCode)

set_option maxHeartbeats 0 in
theorem ch25010M_lines : (nonEmptyLines FW.chars).all owOK = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ch25010M_valid : validR l0M l0I = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ch25010M_letters :
    (List.range 5).all (fun i => CFSG.Monster.B.Co2.Native.lettersOK 2 (fwW.getD i [])) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ch25010M_sq : (mulR x25010 x25010 == oneR) = true := by decide +kernel

theorem ch25010Neg_sq :
    (mulR (evalR l0M l0I ((fwW.getD 1 []).map zCode)) (evalR l0M l0I ((fwW.getD 1 []).map zCode))
      == oneR) = false := by
  decide +kernel

end CertificateChecks.KernelSuz

namespace CertificateChecks.KernelSpor.S26990

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def F (i : Nat) : Nat := W3 (CertificateChecks.KernelSuz.fwW.getD i [])

@[expose] noncomputable def FI (i : Nat) : Nat :=
  W3 (CFSG.EvenSporadicStandard.TwoSuz.outerInvW (CertificateChecks.KernelSuz.fwW.getD i []))

theorem ch25010P_letters : (List.range 5).all (fun i =>
    lettersK 2 (CertificateChecks.KernelSuz.fwW.getD i []) &&
      lettersK 2 (CFSG.EvenSporadicStandard.TwoSuz.outerInvW
        (CertificateChecks.KernelSuz.fwW.getD i []))) = true := by
  quickRfl

theorem ch25010P_canon : (List.range 5).all (fun i => cn (F i) && cn (FI i)) = true := by
  quickRfl

theorem ch25010P_t2 :
    Nat.beq (pc (pc (pc (F 1) (SuzTP 2)) (FI 1)) (SuzTP 2)) (pc (pc (F 2) (F 0)) (FI 2)) = true := by
  quickRfl

theorem ch25010P_t3 :
    Nat.beq (pc (pc (pc (F 3) (SuzTP 3)) (FI 3)) (SuzTP 3)) (pc (pc (F 4) (F 0)) (FI 4)) = true := by
  quickRfl

theorem ch25010P_x : Nat.beq (F 0) e = false := by decide +kernel

theorem ch25010Neg_t2 :
    Nat.beq (pc (pc (pc (F 1) (SuzTP 2)) (FI 1)) (SuzTP 2)) (pc (pc (F 4) (F 0)) (FI 4)) = false := by
  decide +kernel

end CertificateChecks.KernelSpor.S26990

end
