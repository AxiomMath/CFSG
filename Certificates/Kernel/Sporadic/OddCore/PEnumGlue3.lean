module

public import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KS.PEnum

open CFSG.KC.Enum CFSG.KS

theorem allBlk_of {b : Nat} {f : Nat → Bool} :
    ∀ {len : Nat}, (∀ l < len, f (Nat.add b l) = true) → allBlk b f len = true
  | 0, _ => rfl
  | len + 1, h => by
    change Bool.rec (motive := fun _ => Bool) false (allBlk b f len) (f (Nat.add b len)) = true
    rw [h len (by omega), allBlk_of (fun l hl => h l (by omega))]

theorem allN_of {n : Nat} {f : Nat → Bool} (h : ∀ i < n, f i = true) : allN n f = true := by
  have e6 : ∀ x : Nat, Nat.shiftLeft x (nat_lit 6) = x * 64 := fun x => by
    change x <<< 6 = x * 64
    rw [Nat.shiftLeft_eq]
  have e64 : Nat.shiftRight n (nat_lit 6) = n / 64 := by
    change n >>> 6 = n / 64
    rw [Nat.shiftRight_eq_div_pow]
  have er : Nat.land n (nat_lit 63) = n % 64 := by
    change n &&& (2 ^ 6 - 1) = n % 2 ^ 6
    exact Nat.and_two_pow_sub_one_eq_mod n 6
  have hdm := Nat.div_add_mod n 64
  change Bool.rec (motive := fun _ => Bool) false
      (Nat.rec (motive := fun _ => Bool) true
        (fun h ih => Bool.rec (motive := fun _ => Bool) false ih
          (allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64))) (Nat.shiftRight n (nat_lit 6)))
      (allBlk (Nat.shiftLeft (Nat.shiftRight n (nat_lit 6)) (nat_lit 6)) f
        (Nat.land n (nat_lit 63))) = true
  have hb : ∀ q, q ≤ n / 64 → Nat.rec (motive := fun _ => Bool) true
      (fun h ih => Bool.rec (motive := fun _ => Bool) false ih
        (allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64))) q = true := by
    intro q
    induction q with
    | zero => intro _; rfl
    | succ q ih =>
      intro hq
      change Bool.rec (motive := fun _ => Bool) false _ (allBlk (Nat.shiftLeft q (nat_lit 6)) f
        (nat_lit 64)) = true
      have hblk : ∀ l < 64, f (Nat.add (Nat.shiftLeft q (nat_lit 6)) l) = true := fun l hl => by
        apply h
        rw [e6]
        change q * 64 + l < n
        omega
      rw [allBlk_of hblk, ih (by omega)]
  have hlast : ∀ l < Nat.land n (nat_lit 63),
      f (Nat.add (Nat.shiftLeft (Nat.shiftRight n (nat_lit 6)) (nat_lit 6)) l) = true := by
    intro l hl
    apply h
    rw [e6, e64]
    change n / 64 * 64 + l < n
    rw [er] at hl
    omega
  rw [allBlk_of hlast, e64, hb (n / 64) (Nat.le_refl _)]

theorem allN_iff (n : Nat) (f : Nat → Bool) : allN n f = true ↔ ∀ i < n, f i = true :=
  ⟨allN_spec, allN_of⟩

theorem ofFn_range {α : Type} (m : Nat) (f : Nat → α) :
    List.ofFn (n := m) (fun i => f i.val) = (List.range m).map f := by
  apply List.ext_getElem <;> simp

theorem all_range_iff (n : Nat) (f : Nat → Bool) :
    (List.range n).all f = true ↔ ∀ i < n, f i = true := by
  rw [List.all_eq_true]
  simp only [List.mem_range]

end CFSG.KS.PEnum

end
