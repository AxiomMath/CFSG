module

public import Certificates.Data.Kernel.PermCent.U43P1Chk

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelPermCent.U43P1

open CFSG.ComponentClassification.HarrisLit.P1.U43.Cover CFSG.KC.Enum CFSG.KS
open CFSG.LieType.Multipliers.U43 CFSG.ComponentClassification.HarrisLit.P1.U43

@[expose] def u43Cu (x : ℕ) : ℕ := x % 9

@[expose] def u43Tab (t a b : ℕ) : ℕ := (t >>> (4 * (9 * a + b))) % 16

@[expose] def u43Add (a b : ℕ) : ℕ :=
  u43Tab 0x435102768354021687543210876102768435021687354210876543768435102687354021876543210 a b

@[expose] def u43Mul (a b : ℕ) : ℕ :=
  u43Tab 0x264318750615237480453786120327165840138624570876543210741852630582471360000000000 a b

@[expose] def u43Bar (a : ℕ) : ℕ := 3 * (a / 3 % 3) + 2 * (a % 3) % 3

@[expose] def u43Q (a b : ℕ) : ℕ :=
  u43Tab 0x327165840138624570453786120264318750615237480876543210582471360741852630000000000 a b

@[expose] def u43Pt (a b c d : ℕ) : ℕ :=
  if a ≠ 0 then 81 * u43Q a b + 9 * u43Q a c + u43Q a d
  else if b ≠ 0 then 729 + 9 * u43Q b c + u43Q b d
  else if c ≠ 0 then 810 + u43Q c d else 819

@[expose] def u43Dc (i c : ℕ) : ℕ :=
  if i < 729 then
    (if c = 0 then 3 else if c = 1 then u43Cu (i / 81) else if c = 2 then u43Cu (i / 9 % 9)
      else u43Cu (i % 9))
  else if i < 810 then
    (if c = 0 then 0 else if c = 1 then 3 else if c = 2 then u43Cu ((i - 729) / 9)
      else u43Cu ((i - 729) % 9))
  else if i < 819 then
    (if c = 0 then 0 else if c = 1 then 0 else if c = 2 then 3 else u43Cu (i - 810))
  else (if c = 3 then 3 else 0)

@[expose] def u43M (k r c : ℕ) : ℕ := u43Cu (k / 9 ^ (4 * r + c) % 9)

@[expose] def u43W (ε : Bool) (i c : ℕ) : ℕ := cond ε (u43Bar (u43Dc i c)) (u43Dc i c)

@[expose] def u43Row (k r : ℕ) (ε : Bool) (i : ℕ) : ℕ :=
  u43Add (u43Add (u43Add (u43Mul (u43M k r 0) (u43W ε i 0)) (u43Mul (u43M k r 1) (u43W ε i 1)))
    (u43Mul (u43M k r 2) (u43W ε i 2))) (u43Mul (u43M k r 3) (u43W ε i 3))

@[expose] def u43Img (k : ℕ) (ε : Bool) (i : ℕ) : ℕ :=
  u43Pt (u43Row k 0 ε i) (u43Row k 1 ε i) (u43Row k 2 ε i) (u43Row k 3 ε i)

theorem u43_code_uncode (x : ℕ) : code (uncode x) = u43Cu x := by
  simp only [code, uncode, u43Cu, ZMod.val_natCast]
  omega

theorem u43_code_add : ∀ a b : F9, code (a + b) = u43Add (code a) (code b) := by decide

theorem u43_code_mul : ∀ a b : F9, code (a * b) = u43Mul (code a) (code b) := by decide

theorem u43_code_bar : ∀ a : F9, code (barF a) = u43Bar (code a) := by decide

theorem u43_code_q : ∀ a b : F9, code (a⁻¹ * b) = u43Q (code a) (code b) := by decide

theorem u43_code_eq_zero : ∀ a : F9, code a = 0 ↔ a = 0 := by decide

theorem u43_ptIndex (v : V) :
    ptIndex v = u43Pt (code (v 0)) (code (v 1)) (code (v 2)) (code (v 3)) := by
  unfold ptIndex rawIndex CFSG.LieType.Multipliers.U43.normalize lead u43Pt
  simp only [Pi.smul_apply, smul_eq_mul, u43_code_q]
  by_cases h0 : v 0 = 0 <;> by_cases h1 : v 1 = 0 <;> by_cases h2 : v 2 = 0 <;>
    simp [h0, h1, h2, u43_code_eq_zero]

theorem u43_code_decode (i : ℕ) (c : Fin 4) : code (decode i c) = u43Dc i c.val := by
  have e0 : code 0 = 0 := by decide
  have e1 : code 1 = 3 := by decide
  unfold decode u43Dc
  fin_cases c <;> split_ifs <;> simp_all [u43_code_uncode]

theorem u43_imgK (k : ℕ) (ε : Bool) (i : ℕ) : imgK k ε i = u43Img k ε i := by
  have hw : ∀ c : Fin 4, code ((if ε then barV (decode i) else decode i) c) = u43W ε i c.val := by
    intro c
    cases ε <;> simp [u43W, barV, u43_code_bar, u43_code_decode]
  have hm : ∀ r c : Fin 4, code (matK k r c) = u43M k r.val c.val := by
    intro r c
    simp [matK, u43M, u43_code_uncode]
  unfold imgK u43Img u43Row
  rw [u43_ptIndex]
  simp only [mvK, u43_code_add, u43_code_mul, hw, hm]
  rfl

theorem u43_pk (k : ℕ) (ε : Bool) : pk k ε = pmk 820 10 (u43Img k ε) := by
  unfold pk
  congr 1
  funext i
  exact u43_imgK k ε i

theorem u43_matOK (k : ℕ) (ε : Bool) (p : ℕ) :
    matOK k ε p = (List.range 820).all fun i => Nat.beq (at10 p i) (u43Img k ε i) := by
  simp only [matOK, u43_imgK]

theorem u43_gensOK (l : List (ℕ × Bool)) (G : ℕ → ℕ) :
    gensOK l G = (List.range l.length).all fun j =>
      (List.range 820).all fun i =>
        Nat.beq (at10 (G j) i) (u43Img (l.getD j (0, false)).1 (l.getD j (0, false)).2 i) := by
  simp only [gensOK, matOK, u43_imgK]

theorem u43_dgOK (k : ℕ) (y : List ℕ) (p : ℕ) :
    dgOK k y p = (List.range 826).all fun i => Nat.beq (pg 10 (mask 10) p i)
      (cond (Nat.blt i 820) (u43Img k false i) (y.getD (i - 820) 0 + 820)) := by
  simp only [dgOK, u43_imgK]

@[expose] noncomputable def u43TabW (p : ℕ) : List ℕ → ℕ → Bool
  | [], _ => true
  | x :: t, i => Nat.beq (at10 p i) x && u43TabW p t (i + 1)

theorem u43_tabW_iff (p : ℕ) (l : List ℕ) (i : ℕ) :
    u43TabW p l i = true ↔ ∀ j (h : j < l.length), at10 p (i + j) = l[j] := by
  induction l generalizing i with
  | nil => simp [u43TabW]
  | cons x t ih =>
    simp only [u43TabW, Bool.and_eq_true, Nat.beq_eq, ih, List.length_cons]
    constructor
    · rintro ⟨h0, h1⟩ j hj
      cases j with
      | zero => exact h0
      | succ j =>
        have e : i + (j + 1) = i + 1 + j := by omega
        rw [e]
        exact h1 j (by omega)
    · intro h
      refine ⟨h 0 (by omega), fun j hj => ?_⟩
      have e : i + 1 + j = i + (j + 1) := by omega
      rw [e]
      exact h (j + 1) (by omega)

theorem u43_tabOK (a : Array ℕ) (hs : a.size = 820) (p : ℕ) :
    tabOK a p = u43TabW p a.toList 0 := by
  apply Bool.eq_iff_iff.mpr
  rw [u43_tabW_iff]
  simp only [tabOK, List.all_eq_true, List.mem_range, Nat.beq_eq, Array.length_toList,
    Nat.zero_add, hs, Array.getElem_toList]
  constructor
  · intro h j hj
    have := h j hj
    rw [getElem!_pos a j (by omega)] at this
    exact this
  · intro h j hj
    rw [getElem!_pos a j (by omega)]
    exact h j hj

end CertificateChecks.KernelPermCent.U43P1

end
