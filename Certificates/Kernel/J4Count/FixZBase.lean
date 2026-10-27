
module

public import Certificates.Kernel.J4Count.Checks
public import Certificates.Kernel.SporSch.J4S.NoCPBase
public import CFSG.Assembly.Defs

@[expose] public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.J4Schreier.NoComp MulAction
open CFSG.Sporadic.SmallF2 CFSG.KC.J4Count CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.J4NoCK CertificateChecks.KernelSporSch.J4NoCP

noncomputable abbrev qv (l : ℕ) : Row := toRow (toVecD 112 repVecs[l]!)

@[expose] def SZ : List ℕ := [1, 32643072, 82575360, 54405120, 3400320, 15180, 28336]

theorem orb1_pt {i : ℕ} (hi : i < 1771) : orb1.1[i]! = J4O1.PT i := by
  have h1 := CFSG.KS.SporSch.C11.bfsK_sound_proved J4Orbits.xy_bind J4Orbits.b1
  rw [orb1, h1.1]
  exact CFSG.KS.SporSch.C11.tabA_get hi

section Rep

theorem basis_parts {l : ℕ} (hl : l < 7) :
    (getL PS l).length = (getL BS l).length ∧
      2 ^ (getL BS l).length = repCounts[l]! ∧
      (∀ b ∈ getL BS l, b < 2048 ∧ etaK (J4RV l) b = J4RV l) ∧
      ∀ m < 2 ^ (getL BS l).length, decode (getL PS l) (combo (getL BS l) m) = m := by
  have h := CFSG.KS.allN_spec basis_ok l hl
  unfold basisOK at h
  obtain ⟨h1, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨h2, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  obtain ⟨h3, h4⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  have e2 : Nat.shiftLeft 1 (getL BS l).length = 2 ^ (getL BS l).length :=
    (Nat.shiftLeft_eq 1 _).trans (one_mul _)
  refine ⟨Nat.eq_of_beq_eq_true h1, ?_, fun b hb => ?_, fun m hm => ?_⟩
  · have e := Nat.eq_of_beq_eq_true h2
    rw [e2] at e
    rw [e]
    interval_cases l <;> rfl
  · obtain ⟨b1, b2⟩ := (CFSG.KS.bAnd_iff _ _).1 (allL_iff.1 h3 b hb)
    exact ⟨Nat.le_of_ble_eq_true b1, Nat.eq_of_beq_eq_true b2⟩
  · rw [e2] at h4
    exact Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec h4 m hm)

end Rep

section Class

noncomputable abbrev zH : H := ⟨z, z_mem_H⟩

theorem mem_stab_iff (w : Row) (s : H) : s ∈ stabilizer H w ↔ (s : J) • w = w := Iff.rfl

noncomputable abbrev fixRecs (l : ℕ) : Finset ℕ :=
  (Finset.range 1771).filter fun i => etaV unMats repVecs[l]! orb1.1[i]! = repVecs[l]!

noncomputable def recElt (i : ℕ) : H := ⟨η orb1.1[i]!, N_le_H (η_mem_N _)⟩

theorem recElt_val (i : ℕ) : (recElt i : J) = η orb1.1[i]! := by
  simp only [recElt]

end Class

theorem SZ_inj : ∀ l < 7, ∀ l' < 7, SZ.getD l 0 = SZ.getD l' 0 → l = l' := by decide

end CertificateChecks.KernelJ4Count

end
