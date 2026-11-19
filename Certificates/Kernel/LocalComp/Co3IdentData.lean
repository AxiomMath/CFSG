module

public import Certificates.Kernel.LocalComp.Co3IdentArrs
public import Certificates.Kernel.Sporadic.Co3.C
public import Certificates.Kernel.Sporadic.Co3.M
public import Certificates.Kernel.Sporadic.Co3.Single
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentDataInputs
meta import Certificates.Kernel.LocalComp.Co3IdentArrs
public import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Common.Loop
public import CFSG.Certificates.Kernel.Spor.SiftRSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Spor.RawSlSound

public section

set_option maxRecDepth 400000

#ks_perm CertificateChecks.KernelLC.Co3Id.P0 9 CFSG.EvenSmallLie.SympSix.Co3Ident.aArr
#ks_perm CertificateChecks.KernelLC.Co3Id.P1 9 CFSG.EvenSmallLie.SympSix.Co3Ident.bArr
#ks_perm CertificateChecks.KernelLC.Co3Id.P2 9 CFSG.EvenSmallLie.SympSix.Co3Ident.cArr
#ks_perm CertificateChecks.KernelLC.Co3Id.P3 9 CFSG.EvenSmallLie.SympSix.Co3Ident.sArr
#ks_perm CertificateChecks.KernelLC.Co3Id.P5 9 CFSG.EvenSmallLie.SympSix.Co3Ident.fArr
#ks_perm CertificateChecks.KernelLC.Co3Id.P6 9 CFSG.EvenSmallLie.SympSix.Co3Ident.gArr
#ks_perm CertificateChecks.KernelLC.Co3Id.I0 9 CertificateChecks.KernelLC.Co3Id.inv0
#ks_perm CertificateChecks.KernelLC.Co3Id.I1 9 CertificateChecks.KernelLC.Co3Id.inv1
#ks_perm CertificateChecks.KernelLC.Co3Id.I2 9 CertificateChecks.KernelLC.Co3Id.inv2
#ks_perm CertificateChecks.KernelLC.Co3Id.I3 9 CertificateChecks.KernelLC.Co3Id.inv3
#ks_perm CertificateChecks.KernelLC.Co3Id.I4 9 CertificateChecks.KernelLC.Co3Id.inv4
#ks_perm CertificateChecks.KernelLC.Co3Id.I5 9 CertificateChecks.KernelLC.Co3Id.inv5
#ks_perm CertificateChecks.KernelLC.Co3Id.I6 9 CertificateChecks.KernelLC.Co3Id.inv6
#ks_perm CertificateChecks.KernelLC.Co3Id.ZS 9 CertificateChecks.KernelLC.Co3Id.zsArr
#ks_perm CertificateChecks.KernelLC.Co3Id.AS 9 CertificateChecks.KernelLC.Co3Id.asArr
#ks_perm CertificateChecks.KernelLC.Co3Id.AC 9 CertificateChecks.KernelLC.Co3Id.acArr

namespace CertificateChecks.KernelLC.Co3Id

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.SympSix.Co3Ident CFSG.Sporadic.Schreier.Co3
open CertificateChecks.KernelSpor

noncomputable abbrev P4 : Nat := Co3Z

@[expose] noncomputable def P (i : Nat) : Nat :=
  match i with
  | 0 => P0 | 1 => P1 | 2 => P2 | 3 => P3 | 4 => P4 | 5 => P5 | _ => P6

@[expose] noncomputable def I (i : Nat) : Nat :=
  match i with
  | 0 => I0 | 1 => I1 | 2 => I2 | 3 => I3 | 4 => I4 | 5 => I5 | _ => I6

theorem bind0 : genArr 0 = unpack 276 9 P0 := by decide +kernel
theorem bind1 : genArr 1 = unpack 276 9 P1 := by decide +kernel
theorem bind2 : genArr 2 = unpack 276 9 P2 := by decide +kernel
theorem bind3 : genArr 3 = unpack 276 9 P3 := by decide +kernel
theorem bind4 : genArr 4 = unpack 276 9 P4 := Co3Single.z_eq
theorem bind5 : genArr 5 = unpack 276 9 P5 := by decide +kernel
theorem bind6 : genArr 6 = unpack 276 9 P6 := by decide +kernel

theorem bind (i : Nat) (hi : i < 7) : genArr i = unpack 276 9 (P i) := by
  interval_cases i
  · exact bind0
  · exact bind1
  · exact bind2
  · exact bind3
  · exact bind4
  · exact bind5
  · exact bind6

theorem kInv : allN 7 (fun i => invEqK 276 9 (mask 9) (276 * 9) (P i) (I i)) = true := by
  quickRfl

theorem kHi : allN 7 (fun i => Co3Text.hiOK (P i)) = true := by quickRfl

theorem s0 : Co3M.sift P0 = true := by quickRfl
theorem s1 : Co3M.sift P1 = true := by quickRfl
theorem s2 : Co3M.sift P2 = true := by quickRfl
theorem s4 : Co3M.sift P4 = true := by quickRfl
theorem s5 : Co3M.sift P5 = true := by quickRfl
theorem s6 : Co3M.sift P6 = true := by quickRfl
theorem s3 : Co3C.sift P3 = true := by quickRfl

theorem r1 : sqIdK 276 9 (mask 9) (276 * 9) (pidn 276 9) P3 = true := by quickRfl
theorem r2 : compEqK 276 9 (mask 9) (276 * 9) P4 P3 ZS = true := by quickRfl
theorem r3 : compEqK 276 9 (mask 9) (276 * 9) P3 ZS P0 = true := by quickRfl
theorem r4 : compEqK 276 9 (mask 9) (276 * 9) P0 P3 AS = true := by quickRfl
theorem r5 : compEqK 276 9 (mask 9) (276 * 9) P3 AS P4 = true := by quickRfl
theorem r6 : compEqK 276 9 (mask 9) (276 * 9) P0 P2 AC = true := by quickRfl
theorem r7 : compEqK 276 9 (mask 9) (276 * 9) P2 P0 AC = true := by quickRfl

theorem facts : (∀ i < 7, isInvA 276 (genArr i) (invCand 276 (genArr i)) = true) ∧
    (∀ i ∈ mLetters, siftA 276 co3MLevels co3MBaseArr 0 (genArr i) = true) ∧
    siftA 276 co3ChainLevels co3ChainBaseArr 0 (genArr 3) = true ∧
    eqA 276 (compA 276 (genArr 3) (genArr 3)) (idA 276) = true ∧
    eqA 276 (compA 276 (genArr 3) (compA 276 (genArr 4) (genArr 3))) (genArr 0) = true ∧
    eqA 276 (compA 276 (genArr 3) (compA 276 (genArr 0) (genArr 3))) (genArr 4) = true ∧
    eqA 276 (compA 276 (genArr 0) (genArr 2)) (compA 276 (genArr 2) (genArr 0)) = true := by
  have hi (i : Nat) (h : i < 7) : Nat.shiftRight (P i) (276 * 9) = 0 :=
    Nat.eq_of_beq_eq_true (allN_spec kHi i h)
  have sM (i : Nat) (h : i < 7) (hs : Co3M.sift (P i) = true) :
      siftA 276 co3MLevels co3MBaseArr 0 (genArr i) = true :=
    siftK_soundR Co3M.binds Co3M.perm Co3M.hl (bind i h) (hi i h)
      (range_of_permOK (allN_spec kInv i h)) hs
  refine ⟨fun i h => ?_, fun i h => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨e, h2⟩ := invEqK_sound (allN_spec kInv i h)
    rw [bind i h, e]
    exact h2
  · simp only [mLetters, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact sM 0 (by omega) s0
    · exact sM 1 (by omega) s1
    · exact sM 2 (by omega) s2
    · exact sM 4 (by omega) s4
    · exact sM 5 (by omega) s5
    · exact sM 6 (by omega) s6
  · exact siftK_soundR Co3C.binds Co3C.perm Co3C.hl bind3 (hi 3 (by omega))
      (range_of_permOK (allN_spec kInv 3 (by omega))) s3
  · rw [bind3]
    exact sqIdK_sound r1
  · rw [bind3, bind4, bind0, compEqK_sound r2, compEqK_sound r3]
    exact eqK_sound (Nat.beq_refl P0)
  · rw [bind3, bind4, bind0, compEqK_sound r4, compEqK_sound r5]
    exact eqK_sound (Nat.beq_refl P4)
  · rw [bind0, bind2, compEqK_sound r6, compEqK_sound r7]
    exact eqK_sound (Nat.beq_refl AC)

end CertificateChecks.KernelLC.Co3Id

end
