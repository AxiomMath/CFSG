module

public import Certificates.Kernel.Sporadic.Fi24ThreeO.Data
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_ktree CFSG.KD.Fi24ThreeO CKT "Certificates/Kernel/Sporadic/Fi24ThreeO/data/ck.bin" 65536 1 1048576 11357628353684569019

public section

namespace CFSG.KD.Fi24ThreeO.Ck

open CFSG.KC CFSG.KC.Loop CFSG.KC.Fi24Net CFSG.KC.Fi24ThreeO CFSG.KD.Fi24Net CFSG.KD.Fi24Kit

theorem iterW_chain (NW : Nat → Nat → Nat) (NT : Nat → Nat) (ws : List (List Nat)) (C : Nat → Nat)
    {d : Nat} (h : ∀ k, k < d → stepW NW NT ws (C k) = C (k + 1)) :
    ∀ k, k ≤ d → iterW NW NT ws k (C 0) = C k
  | 0, _ => rfl
  | k + 1, hk => by
    have e : iterW NW NT ws (k + 1) (C 0) = stepW NW NT ws (iterW NW NT ws k (C 0)) := by
      change strictN (iterW NW NT ws k (C 0)) (stepW NW NT ws) = _
      cases iterW NW NT ws k (C 0) <;> rfl
    rw [e, iterW_chain NW NT ws C h k (by omega), h k (by omega)]

theorem covW_chain (NW : Nat → Nat → Nat) (NT : Nat → Nat) (ws : List (List Nat)) (C : Nat → Nat)
    {d S F : Nat} (hS : S = C 0) (h : ∀ k, k < d → stepW NW NT ws (C k) = C (k + 1))
    (hF : Nat.beq (Nat.land (Nat.lor (C d) F) ptsM) ptsM = true) : covW NW NT ws d S F = true := by
  unfold covW
  rw [hS, iterW_chain NW NT ws C h d (Nat.le_refl d)]
  exact hF

noncomputable def ckS (k : Nat) : Bool := Nat.beq (stepW NW NT swC (CKT k)) (CKT (k + 1))

theorem ck0 : Nat.beq (gfr (Nat.lor (plOf crx) cF)) (CKT 0) = true := by quickRfl
theorem st0 : ckS 0 = true := by quickRfl
theorem st1 : ckS 1 = true := by quickRfl
theorem st2 : ckS 2 = true := by quickRfl
theorem st3 : ckS 3 = true := by quickRfl
theorem st4 : ckS 4 = true := by quickRfl
theorem st5 : ckS 5 = true := by quickRfl
theorem st6 : ckS 6 = true := by quickRfl
theorem st7 : ckS 7 = true := by quickRfl
theorem st8 : ckS 8 = true := by quickRfl
theorem st9 : ckS 9 = true := by quickRfl
theorem st10 : ckS 10 = true := by quickRfl
theorem st11 : ckS 11 = true := by quickRfl
theorem st12 : ckS 12 = true := by quickRfl
theorem st13 : ckS 13 = true := by quickRfl
theorem st14 : ckS 14 = true := by quickRfl

theorem ckF : Nat.beq (Nat.land (Nat.lor (CKT 15) (gfr cF)) ptsM) ptsM = true := by quickRfl

theorem ccov_t : CFSG.KD.Fi24ThreeO.ccov = true := by
  have hb : ∀ k, k < 15 → ckS k = true
    | 0, _ => st0
    | 1, _ => st1
    | 2, _ => st2
    | 3, _ => st3
    | 4, _ => st4
    | 5, _ => st5
    | 6, _ => st6
    | 7, _ => st7
    | 8, _ => st8
    | 9, _ => st9
    | 10, _ => st10
    | 11, _ => st11
    | 12, _ => st12
    | 13, _ => st13
    | 14, _ => st14
    | _ + 15, h => absurd h (by omega)
  have hs : ∀ k, k < 15 → stepW NW NT swC (CKT k) = CKT (k + 1) :=
    fun k hk => Nat.eq_of_beq_eq_true (hb k hk)
  have hcd : cd = 15 := rfl
  exact covW_chain NW NT swC CKT (Nat.eq_of_beq_eq_true ck0) (fun k hk => hs k (hcd ▸ hk)) ckF

end CFSG.KD.Fi24ThreeO.Ck

end
