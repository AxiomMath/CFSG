module

public import Certificates.Kernel.Misc.O73
public import CFSG.Certificates.Kernel.Misc.O73Sound

public section

namespace CFSG.KD.Misc.O73

open CFSG.KC.Misc.O73 CFSG.LieType.Multipliers.O73 CFSG.YGroups CFSG.YGroups.ModelNative
  CFSG.Monster.B.Co2.Native Matrix

theorem code_dec (x : Fin 2187) : code (dec x) = x := by
  obtain ⟨x, hx⟩ := x
  simp only [code, dec, idx, ZMod.val_natCast]
  norm_num
  omega

theorem facts :
    (∀ x : Fin 2187, code (dec x) = x)
    ∧ ((∀ i : Fin 8, q3 (vecs i) = 2) ∧ tTabs.size = 8 ∧ rTabs.size = 8 ∧
      (∀ i : Fin 8, tMat (vecs i) * tMat (vecs i) = 1 ∧ rMat (vecs i) * rMat (vecs i) = 1) ∧
      permsOK 2187 tTabs = true ∧ permsOK 2187 rTabs = true ∧
      (∀ i : Fin 8, ∀ x : Fin 2187, q3 (tMat (vecs i) *ᵥ dec x) = q3 (dec x)))
    ∧ (relatorsOK 2187 tTabs (yRels 3 2 2 ++ eWords) = true ∧
      relatorsOK 2187 rTabs (yRels 3 2 2) = true ∧
      liftArrs.size = 8 ∧ permsOK 1134 liftArrs = true ∧
      relatorsOK 1134 liftArrs eWords = true ∧
      eqA 1134 (evalW 1134 liftArrs spW) (idA 1134) = false)
    ∧ (betaArr.size = 728 ∧ (∀ x : Fin 728, betaArr[x.val]! < 2187) ∧
      (∀ x y : Fin 728, betaArr[x.val]! = betaArr[y.val]! → x = y) ∧
      ∀ i : Fin 8, ∀ x : Fin 728,
      (rTabs[i.val]!)[betaArr[x.val]!]! = betaArr[(y322Arrays[i.val]!)[x.val]!]!) := by
  have h := o73_sound (VL := vecList) (nE := 46) mat relM lift relPAll
    (by rw [Nat.eq_of_beq_eq_true nEW]) sp beta lenL lenB lenY nlB
  rw [← bR1, ← bE, ← bSP] at h
  have eL : liftArrs = parsePerms (CFSG.KC.Misc.O73.strOf cL) := by rw [← bL]; rfl
  have eB : betaArr = parseNats (CFSG.KC.Misc.O73.strOf cB) := by rw [← bB]; rfl
  have eY : y322Arrays = parsePerms (CFSG.KC.Misc.O73.strOf cY) := by rw [← bY]; rfl
  rw [vecs_eq, tTabs_eq, rTabs_eq, eL, eB, eY]
  exact ⟨code_dec, h⟩

end CFSG.KD.Misc.O73

end
