module

public import Certificates.Kernel.Sporadic.OddCore.SuzDBind
public import Certificates.Kernel.Sporadic.OddCore.SuzK0
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzOuterCheck
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.CentScanSound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.HeAutKSound
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzOut

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.CentScan
open CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native CFSG.EvenSporadicStandard.Solomon78
open CertificateChecks.KernelSpor.OddCore CertificateChecks.KernelSpor.Suz2306
open CertificateChecks.KernelSpor
open CFSG.KLie.CT (andB notB)

@[expose] noncomputable def M0 : Nat :=
  wordK 1782 11 (mask 11) (pidn 1782 11) triS triSI suzWordM0

@[expose] noncomputable def V0 : Nat := pcomp 1782 11 (mask 11) M0 V

@[expose] noncomputable def VT : Nat := pcomp 1782 11 (mask 11) V0 (SuzTP 0)

@[expose] noncomputable def TV : Nat := pcomp 1782 11 (mask 11) (SuzTP 0) V0

theorem kWord : wordEqK 1782 11 (mask 11) (pidn 1782 11) triS triSI 3 suzWordM0 M0 = true := by
  quickRfl

theorem kRel : bAnd(compEqK 1782 11 (mask 11) (1782 * 11) M0 V V0,
    bAnd(compEqK 1782 11 (mask 11) (1782 * 11) V0 (SuzTP 0) VT,
      bAnd(compEqK 1782 11 (mask 11) (1782 * 11) (SuzTP 0) V0 TV, eqK VT TV))) = true := by
  quickRfl

theorem kSV : bAnd(canonK 1782 11 (mask 11) (1782 * 11) V0,
    bAnd(canonK 42 6 (mask 6) (42 * 6) (SuzSV 0),
      Nat.beq (CFSG.KC.PermTool.restrictK 11 6 SuzD.fixL0 V0) (SuzSV 0))) = true := by
  quickRfl

theorem kD : allN 5 (fun j => Nat.beq (SuzDP j) (SuzD.D j)) = true := by
  quickRfl

theorem kNeg : andB (notB (centIdK 42 6 5 SuzDP (SuzDP 0) (pidn 42 6)))
    (notB (offK 42 6 5 SuzDP (pidn 42 6) (pidn 42 6))) = true := by
  quickRfl

theorem m0_eq : suzArrM0 = unpack 1782 11 M0 := by
  have hS : bTriple.size = 3 ∧ ∀ j < 3, bTriple[j]! = unpack 1782 11 (triS j) := by
    refine ⟨rfl, fun j hj => ?_⟩
    interval_cases j
    · change bTriple[0]! = unpack 1782 11 B0
      simpa [bTriple] using b0Arr_eq
    · change bTriple[1]! = unpack 1782 11 B1
      simpa [bTriple] using b1Arr_eq
    · change bTriple[2]! = unpack 1782 11 V
      simpa [bTriple] using vArr_eq
  have h := (wordEqK_sound hS tri_perms kWord).1
  unfold suzArrM0 suzArr
  exact h

theorem rel_parts : compEqK 1782 11 (mask 11) (1782 * 11) M0 V V0 = true ∧
    compEqK 1782 11 (mask 11) (1782 * 11) V0 (SuzTP 0) VT = true ∧
    compEqK 1782 11 (mask 11) (1782 * 11) (SuzTP 0) V0 TV = true ∧ eqK VT TV = true := by
  simpa only [bAnd_iff] using kRel

theorem v0_eq : suzArrV0 = unpack 1782 11 V0 := by
  unfold suzArrV0
  rw [m0_eq, vArr_eq, compEqK_sound rel_parts.1]

theorem relOK : suzOuterRelOK = true := by
  obtain ⟨-, h2, h3, h4⟩ := rel_parts
  have hl : lettersOK 2 suzWordM0 = true := by decide
  unfold suzOuterRelOK
  rw [hl, v0_eq, (rep_facts (i := 0) (by decide)).1, compEqK_sound h2, compEqK_sound h3,
    eqK_sound h4]
  rfl

theorem sv_parts : canonK 1782 11 (mask 11) (1782 * 11) V0 = true ∧
    canonK 42 6 (mask 6) (42 * 6) (SuzSV 0) = true ∧
    CFSG.KC.PermTool.restrictK 11 6 SuzD.fixL0 V0 = SuzSV 0 := by
  obtain ⟨h1, h2, h3⟩ := (by simpa only [bAnd_iff] using kSV :
    canonK 1782 11 (mask 11) (1782 * 11) V0 = true ∧
    canonK 42 6 (mask 6) (42 * 6) (SuzSV 0) = true ∧
    Nat.beq (CFSG.KC.PermTool.restrictK 11 6 SuzD.fixL0 V0) (SuzSV 0) = true)
  exact ⟨h1, h2, Nat.eq_of_beq_eq_true h3⟩

theorem sv_eq : suzTabV0 = unpack 42 6 (SuzSV 0) := by
  obtain ⟨h1, -, h3⟩ := sv_parts
  have hL : ∀ x ∈ SuzD.fixL0, x < 1782 := fun x hx => List.mem_range.1 (List.mem_filter.1 hx).1
  unfold suzTabV0
  rw [v0_eq, SuzD.fixList_eq,
    CFSG.KC.PermTool.restrictArr_unpack (w' := 6) h1 hL (by rw [SuzD.fixL0_length]; decide),
    SuzD.fixL0_length, h3]

theorem dGens_size : dGens.size = 5 := by
  unfold dGens
  simp

theorem dp_get {j : Nat} (hj : j < 5) :
    dGens[j]! = unpack 42 6 (SuzDP j) ∧ canonK 42 6 (mask 6) (42 * 6) (SuzDP j) = true := by
  rw [Nat.eq_of_beq_eq_true (CFSG.KS.Raw.Orb.allN_iff.1 kD j hj)]
  exact ⟨SuzD.dGens_get hj, SuzD.D_canon hj⟩

end CertificateChecks.KernelSpor.SuzOut

end
