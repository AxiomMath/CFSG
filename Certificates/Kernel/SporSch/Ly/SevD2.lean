module

public import Certificates.Kernel.SporSch.Ly.SevD1
public import Certificates.Kernel.SporSch.Ly.SevCData
import Init.Data.Nat.Fold
import Init.Data.Range.Basic
import Init.Data.Array.Basic
import Init.Data.ByteArray.Basic
import Init.Data.UInt.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.LySvD

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.LySev
open CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.Ly.Native CFSG.Sporadic.He.Native
open CertificateChecks.KernelSporSch

@[expose] noncomputable def HIP (j : Nat) : Nat := pk49 (LySv.HP[j]!.2)

theorem gp : bAnd(Nat.beq LySvV.kg0 2, bAnd(Nat.beq LySvV.kg1 2, bAnd(Nat.beq LySvV.kg2 2,
    bAnd(Nat.beq (LySvV.GP0 0) (VP 0), bAnd(Nat.beq (LySvV.GP0 1) (VP 1),
    bAnd(Nat.beq (LySvV.GP1 0) (VP 60), bAnd(Nat.beq (LySvV.GP1 1) (VP 62),
    bAnd(Nat.beq (LySvV.GP2 0) (VP 85), Nat.beq (LySvV.GP2 1) (VP 91))))))))) = true := by quickRfl

theorem lvGet (i j : Nat) (hi : i < 3) (hj : j < 2) :
    (lvV i).size = 2 ∧ (lvV i)[j]! = dec49 (VP ((hLevelGens[i]!)[j]!)) := by
  have e : (lvV i)[j]! = LySv.VALS.getD ((hLevelGens[i]!)[j]!) (id7 ()) := by
    interval_cases i <;> interval_cases j <;> rfl
  have hs : (lvV i).size = 2 := by
    interval_cases i <;> rfl
  have hk : ∀ i < 3, ∀ j < 2, (hLevelGens[i]!)[j]! < 92 := by decide +kernel
  exact ⟨hs, by rw [e, vals_getD (hk i hi j hj)]⟩

theorem root0 : (stdVec 0 == dec7 (LySvV.E0 0)) = true := by decide +kernel

theorem root1 : (stdVec 1 == dec7 (LySvV.E1 0)) = true := by decide +kernel

theorem root2 : (stdVec 2 == dec7 (LySvV.E2 0)) = true := by decide +kernel

theorem red0 : allN 7 (fun r => Nat.blt (d3 (LySvV.E0 0) r) 5) = true := by quickRfl

theorem red1 : allN 7 (fun r => Nat.blt (d3 (LySvV.E1 0) r) 5) = true := by quickRfl

theorem red2 : allN 7 (fun r => Nat.blt (d3 (LySvV.E2 0) r) 5) = true := by quickRfl

theorem hpOK : allN 5 (fun j => bAnd(is49 (LySv.HP[j]!.1) (RAP j), bAnd(is49 (LySv.HP[j]!.2) (HIP j),
    bAnd(red49 (HIP j), Nat.beq (mul7K (RAP j) (HIP j)) id7K)))) = true := by quickRfl

theorem hpSz : LySv.HP.size = 5 := by decide +kernel

theorem hp_get {j : Nat} (hj : j < 5) :
    LySv.HP[j]! = (dec49 (RAP j), dec49 (HIP j)) ∧ mul7K (RAP j) (HIP j) = id7K ∧
      red49 (HIP j) = true := by
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 (allN_spec hpOK j hj)
  obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h
  exact ⟨Prod.ext (dec49_of h1) (dec49_of h2), Nat.eq_of_beq_eq_true h4, h3⟩

theorem inv_ra {j : Nat} (hj : j < 5) : inv7 LySv.RA[j]! = dec49 (HIP j) := by
  rw [ra_get hj]
  exact inv7_eq (red_ra hj) (hp_get hj).2.2 (hp_get hj).2.1

theorem hp : (Array.ofFn (n := 5) fun j => (LySv.RA[j.val]!, inv7 LySv.RA[j.val]!)) = LySv.HP := by
  apply Array.ext (by rw [hpSz]; simp)
  intro j h1 h2
  simp only [Array.size_ofFn] at h1
  rw [Array.getElem_ofFn, ← getElem!_pos LySv.HP j h2, (hp_get h1).1, inv_ra h1, ra_get h1]

theorem hpInv : (LySv.HP.all fun p => mul7 p.1 p.2 == id7 ()) = true := by
  rw [Array.all_eq_true]
  intro j hj
  have hj' : j < 5 := by rw [hpSz] at hj; exact hj
  rw [← getElem!_pos LySv.HP j hj, (hp_get hj').1]
  dsimp only
  rw [mul7_eq, (hp_get hj').2.1, id7_eq]
  exact beq_self_eq_true _

@[expose] noncomputable def kcQ (j : Nat) : Bool := allN 49 (fun t => allN 49 (fun s =>
  Nat.beq fld(LySc.KC t, Nat.add (Nat.mul 980 j) (Nat.mul 20 s), 1048575)
    (Nat.mod (Nat.mul (d3 (RAP j) (Nat.add (Nat.mul 7 (Nat.div s 7)) (Nat.div t 7)))
      (d3 (HIP j) (Nat.add (Nat.mul 7 (Nat.mod t 7)) (Nat.mod s 7)))) 5)))

theorem kc0 : kcQ 0 = true := by quickRfl
theorem kc1 : kcQ 1 = true := by quickRfl
theorem kc2 : kcQ 2 = true := by quickRfl
theorem kc3 : kcQ 3 = true := by quickRfl
theorem kc4 : kcQ 4 = true := by quickRfl

theorem dec49_get (X : Nat) {i : Nat} (hi : i < 49) : (dec49 X)[i]! = d3 X i := by
  unfold dec49
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem kc (j : Nat) (hj : j < 5) (t : Nat) (ht : t < 49) (s : Nat) (hs : s < 49) :
    fld(LySc.KC t, 980 * j + 20 * s, 1048575) =
      LySv.HP[j]!.1[7 * (s / 7) + t / 7]! * LySv.HP[j]!.2[7 * (t % 7) + s % 7]! % 5 := by
  have h : kcQ j = true := by
    interval_cases j
    · exact kc0
    · exact kc1
    · exact kc2
    · exact kc3
    · exact kc4
  have e := Nat.eq_of_beq_eq_true (allN_spec (allN_spec h t ht) s hs)
  rw [(hp_get hj).1, dec49_get _ (by omega), dec49_get _ (by omega)]
  exact e

theorem rtOK : is49 LySv.RT (LySc.EE 0) = true := by quickRfl

theorem rt : LySv.RT = dec49 (LySc.EE 0) := dec49_of rtOK

end CertificateChecks.KernelSporSch.LySvD

end
