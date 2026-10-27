
module

public import Certificates.Kernel.SporSch.J4S.CommGen
public import CFSG.Certificates.Kernel.SporSch.J4SBfsSound
public import CFSG.Certificates.Kernel.Spor.RawSlSound
meta import CFSG.Sporadic.Schreier.J4SOrbitsBase
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
import CFSG.Certificates.Kernel.SporSch.J4SBfsProved

public section

set_option maxRecDepth 400000

#kss_table CertificateChecks.KernelSporSch.J4XYG CFSG.Sporadic.J4Schreier.xyGens 11 11
#kss_table CertificateChecks.KernelSporSch.J4XYI CFSG.Sporadic.J4Schreier.xyInvGens 11 11
#kss_tree CertificateChecks.KernelSporSch.J4G1 CFSG.Sporadic.J4Schreier.gens1 11
#kss_tree CertificateChecks.KernelSporSch.J4G2 CFSG.Sporadic.J4Schreier.gens2 11
#kss_orbit CertificateChecks.KernelSporSch.J4O1 CFSG.Sporadic.J4Schreier.orb1
#kss_orbit CertificateChecks.KernelSporSch.J4O14 CFSG.Sporadic.J4Schreier.orb14
#kss_orbit CertificateChecks.KernelSporSch.J4OB CFSG.Sporadic.J4Schreier.orbB
#kss_orbit CertificateChecks.KernelSporSch.J4OC CFSG.Sporadic.J4Schreier.orbC

namespace CertificateChecks.KernelSporSch.J4Orbits

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.C11
open CFSG.Sporadic.J4Schreier
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.J4XY

theorem g1k : allN 8 (fun g => Nat.beq (W (J4SW.ws.toArray[Nat.add g 1]!)) (J4G1 g)) = true := by
  quickRfl

theorem g2k : allN 5 (fun g => Nat.beq (W (J4SW.ws.toArray[(#[3, 4, 5, 7, 8] : Array Nat)[g]!]!))
    (J4G2 g)) = true := by
  quickRfl

theorem b1 : bfsK J4XYG 2 1 1771 J4O1.PT J4O1.PAR J4O1.LAB J4O1.POS = true := by quickRfl
theorem b14 : bfsK J4XYG 2 14 276 J4O14.PT J4O14.PAR J4O14.LAB J4O14.POS = true := by quickRfl
theorem bB : bfsK J4G1 8 2 1440 J4OB.PT J4OB.PAR J4OB.LAB J4OB.POS = true := by quickRfl
theorem bC : bfsK J4G2 5 4 96 J4OC.PT J4OC.PAR J4OC.LAB J4OC.POS = true := by quickRfl
theorem c1 : closedK J4XYI 2 1771 J4O1.PT J4O1.POS = true := by quickRfl
theorem c14 : closedK J4XYI 2 276 J4O14.PT J4O14.POS = true := by quickRfl

theorem cov : allN 2048 (fun a => bIf(Nat.beq a 0, true,
    bIf(listedK 1771 J4O1.PT J4O1.POS a, true, listedK 276 J4O14.PT J4O14.POS a))) = true := by
  quickRfl

theorem fx1 : allN 8 (fun g => Nat.beq (appK (J4G1 g) 1) 1) = true := by quickRfl

theorem fx2 : allN 5 (fun g => bAnd(Nat.beq (appK (J4G2 g) 1) 1, Nat.beq (appK (J4G2 g) 2) 2)) =
    true := by quickRfl

theorem g1_bind : gens1.size = 8 ∧ ∀ g < 8, gens1[g]! = unpack11 (J4G1 g) := by
  refine ⟨rfl, fun g hg => ?_⟩
  have e : gens1[g]! = sCols (g + 1) := by interval_cases g <;> rfl
  rw [e, sCols, J4CommGen.words_eq, wordCols_eq', Nat.eq_of_beq_eq_true (allN_spec g1k g hg)]

theorem g2_bind : gens2.size = 5 ∧ ∀ g < 5, gens2[g]! = unpack11 (J4G2 g) := by
  refine ⟨rfl, fun g hg => ?_⟩
  have e : gens2[g]! = sCols ((#[3, 4, 5, 7, 8] : Array Nat)[g]!) := by interval_cases g <;> rfl
  rw [e, sCols, J4CommGen.words_eq, wordCols_eq', Nat.eq_of_beq_eq_true (allN_spec g2k g hg)]

theorem xy_bind : xyGens.size = 2 ∧ ∀ g < 2, xyGens[g]! = unpack11 (J4XYG g) :=
  bind2_sound J4XYG.bind

theorem xyi_bind : xyInvGens.size = 2 ∧ ∀ g < 2, xyInvGens[g]! = unpack11 (J4XYI g) :=
  bind2_sound J4XYI.bind

theorem listed_of {n a : Nat} {PT POS : Nat → Nat} (h : listedK n PT POS a = true) :
    ∃ i < n, PT i = a := by
  unfold listedK at h
  obtain ⟨_, h2⟩ := (bAnd_iff _ _).1 h
  rw [CFSG.KS.Raw.strictB_eq] at h2
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
  exact ⟨POS a, Nat.le_of_ble_eq_true h3, Nat.eq_of_beq_eq_true h4⟩

theorem facts : (bfsOK xyGens 1 1771 orb1 = true) ∧ (bfsOK xyGens 14 276 orb14 = true) ∧
    (coverCheck = true) ∧ (closedOK xyInvGens orb1.1 1771 = true) ∧
    (closedOK xyInvGens orb14.1 276 = true) ∧ (fixCheck = true) ∧
    (bfsOK gens1 2 1440 orbB = true) ∧ (bfsOK gens2 4 96 orbC = true) := by
  have h1 := bfsK_sound_proved xy_bind b1
  have h14 := bfsK_sound_proved xy_bind b14
  have hB := bfsK_sound_proved g1_bind bB
  have hC := bfsK_sound_proved g2_bind bC
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [orb1, h1.1]
    exact h1.2
  · rw [orb14, h14.1]
    exact h14.2
  · unfold coverCheck
    rw [List.all_eq_true]
    intro a ha
    have hc := allN_spec cov a (List.mem_range.1 ha)
    rw [orb1, h1.1, orb14, h14.1]
    by_cases a0 : a = 0
    · simp [a0]
    · rw [show Nat.beq a 0 = false from Bool.eq_false_iff.2 fun e => a0 (Nat.eq_of_beq_eq_true e)]
        at hc
      cases hl : listedK 1771 J4O1.PT J4O1.POS a
      · rw [hl] at hc
        obtain ⟨i, hi, e⟩ := listed_of hc
        simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range, beq_iff_eq]
        exact Or.inr ⟨i, hi, by rw [tabA_get hi, e]⟩
      · obtain ⟨i, hi, e⟩ := listed_of hl
        simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range, beq_iff_eq]
        exact Or.inl (Or.inr ⟨i, hi, by rw [tabA_get hi, e]⟩)
  · rw [orb1, h1.1]
    exact closedK_sound_proved xyi_bind c1
  · rw [orb14, h14.1]
    exact closedK_sound_proved xyi_bind c14
  · unfold fixCheck
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq]
    refine ⟨fun g hg => ?_, fun g hg => ?_⟩
    · rw [g1_bind.2 g hg, app_eq]
      exact Nat.eq_of_beq_eq_true (allN_spec fx1 g hg)
    · obtain ⟨e1, e2⟩ := (bAnd_iff _ _).1 (allN_spec fx2 g hg)
      rw [g2_bind.2 g hg, app_eq, app_eq]
      exact ⟨Nat.eq_of_beq_eq_true e1, Nat.eq_of_beq_eq_true e2⟩
  · rw [orbB, hB.1]
    exact hB.2
  · rw [orbC, hC.1]
    exact hC.2

end CertificateChecks.KernelSporSch.J4Orbits

end
