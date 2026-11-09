module

public import Certificates.Kernel.StdOdd.CentOrbBlk
public import CFSG.Certificates.Kernel.StdOdd.RootOrbitSound

public section

namespace CFSG.KD.StdOdd.Cent

open CFSG.KC.StdOdd.Orbit CFSG.KC.StdOdd.Chain CFSG.KC.Misc.E6Std CFSG.KS.StdOdd.Orbit

theorem testBit_blkRec (r : ℕ → ℕ) (m : ℕ) : ∀ (p i : ℕ),
    (Nat.rec (motive := fun _ => ℕ) 0 (fun k ih => ih ||| ((r k &&& full m) <<< (k * m))) p :
      ℕ).testBit i = (decide (i < p * m) && (r (i / m)).testBit (i % m))
  | 0, i => by simp
  | p + 1, i => by
    change (Nat.rec (motive := fun _ => ℕ) 0 (fun k ih => ih ||| ((r k &&& full m) <<< (k * m))) p
      ||| ((r p &&& full m) <<< (p * m))).testBit i = _
    rw [Nat.testBit_or, testBit_blkRec r m p i, Nat.testBit_shiftLeft, Nat.testBit_and,
      testBit_full]
    by_cases h1 : i < p * m
    · have h2 : ¬ p * m ≤ i := by omega
      have h3 : i < (p + 1) * m := by rw [Nat.succ_mul]; omega
      simp [h1, h2, h3]
    · have hm : 0 < m ∨ m = 0 := by omega
      rcases hm with hm | hm
      · by_cases h3 : i < (p + 1) * m
        · have hq : i / m = p := Nat.div_eq_of_lt_le (by omega) h3
          have hr : i % m = i - p * m := by
            rw [Nat.mod_eq_sub_mul_div, hq, Nat.mul_comm]
          have h4 : i - p * m < m := by rw [Nat.succ_mul] at h3; omega
          simp [h1, h3, hq, hr, h4, Nat.le_of_not_lt h1]
        · have h4 : ¬ i - p * m < m := by rw [Nat.succ_mul] at h3; omega
          simp [h1, h3, h4]
      · subst hm
        simp

theorem testBit_orbPlane_blk {X : ℕ} {U : List ℕ} {m p c k j : ℕ} (hk : k < p) (hj : j < m) :
    (orbPlane X U m p c).testBit (k * m + j) =
      (rowX (Nat.shiftRight (powB X k) (156 * c)) U).testBit j := by
  have hi : k * m + j < p * m := by nlinarith
  have hq : (k * m + j) / m = k := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
  have hr : (k * m + j) % m = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  unfold orbPlane
  rw [forceN_eq]
  change ((Nat.rec (motive := fun _ => ℕ) 0 (fun k ih => ih ||| ((rowX (Nat.shiftRight (powB X k)
    (156 * c)) U &&& full m) <<< (k * m))) p : ℕ) ||| ((nthN U c >>> m) <<< (p * m))).testBit
      (k * m + j) = _
  rw [Nat.testBit_or, testBit_blkRec, Nat.testBit_shiftLeft, hq, hr]
  simp [hi, Nat.not_le_of_lt hi]

theorem testBit_orbPlane_fix {X : ℕ} {U : List ℕ} {m p c : ℕ} (j : ℕ) :
    (orbPlane X U m p c).testBit (p * m + j) = (nthN U c).testBit (m + j) := by
  unfold orbPlane
  rw [forceN_eq]
  change ((Nat.rec (motive := fun _ => ℕ) 0 (fun k ih => ih ||| ((rowX (Nat.shiftRight (powB X k)
    (156 * c)) U &&& full m) <<< (k * m))) p : ℕ) ||| ((nthN U c >>> m) <<< (p * m))).testBit
      (p * m + j) = _
  rw [Nat.testBit_or, testBit_blkRec, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  simp [Nat.add_comm m j]

end CFSG.KD.StdOdd.Cent

end
