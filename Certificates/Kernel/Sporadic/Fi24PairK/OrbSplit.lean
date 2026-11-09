module

public import Certificates.Kernel.Sporadic.Fi24PairK.Data
public import Certificates.Kernel.Sporadic.Fi24Kit.Split

public section

namespace CFSG.KD.Fi24PairK.Ck

open CFSG.KC CFSG.KC.LceS CFSG.KC.Fi24PairK CFSG.KD.Fi24Kit.Split

theorem letB_eq (v : Nat) (k : Nat → Bool) : letB v k = k v := by cases v <;> rfl

theorem andB_of {a b : Bool} (ha : a = true) (hb : b = true) : andB a b = true := by
  rw [ha, hb]; rfl

theorem orbW_of {NW : Nat → Nat → Nat} {ws : List (List Int)} {d y c P : Nat}
    (hP : itG (stepW NW ws) d (Nat.shiftLeft (nat_lit 1) y) = P)
    (h : andB (Nat.beq (stepW NW ws P) P) (Nat.beq (popcount P (nat_lit 524288)) c) = true) :
    orbW NW ws d y c = true := by
  unfold orbW
  rw [iterK_itG, hP, letB_eq]
  exact h

end CFSG.KD.Fi24PairK.Ck

end
