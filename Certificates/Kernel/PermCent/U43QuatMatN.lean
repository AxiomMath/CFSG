module

public import Certificates.Data.Kernel.PermCent.U43P1Chk

public section

namespace CertificateChecks.KernelPermCent.U43Quat

open CFSG.LieType.Multipliers.U43 CFSG.ComponentClassification.HarrisLit.P1.U43
  CFSG.ComponentClassification.HarrisLit.P1.U43.Cover

@[expose] def tab (t c : Nat) : Nat := Nat.land (Nat.shiftRight t (Nat.mul 4 c)) 15

@[expose] noncomputable def mulT : Nat :=
  5107958271419843920193557880922165469200445146711473720438786334434434179969678641066430418649088

@[expose] noncomputable def addT : Nat :=
  8986690708024339884259668388453865091868182506470258411551265922896781674643265104972283578167824

@[expose] noncomputable def mulN (c d : Nat) : Nat := tab mulT (Nat.add (Nat.mul 9 c) d)

@[expose] noncomputable def addN (c d : Nat) : Nat := tab addT (Nat.add (Nat.mul 9 c) d)

@[expose] noncomputable def invN (c : Nat) : Nat := tab 22658101536 c

@[expose] noncomputable def barN (c : Nat) : Nat := tab 32317452576 c

theorem code_mul : ∀ a b : F9, code (a * b) = mulN (code a) (code b) := by decide
theorem code_add : ∀ a b : F9, code (a + b) = addN (code a) (code b) := by decide
theorem code_inv : ∀ a : F9, code a⁻¹ = invN (code a) := by decide
theorem code_barF : ∀ a : F9, code (barF a) = barN (code a) := by decide
theorem code_eq_zero : ∀ a : F9, code a = 0 ↔ a = 0 := by decide
theorem code_one : code 1 = 3 := by decide
theorem code_zero : code 0 = 0 := by decide

theorem code_uncode {c : Nat} (h : c < 9) : code (uncode c) = c := by
  unfold code uncode
  simp only [ZMod.val_natCast]
  omega

@[expose] noncomputable def leadN (c0 c1 c2 c3 : Nat) : Nat :=
  cond (Nat.beq c0 0) (cond (Nat.beq c1 0) (cond (Nat.beq c2 0) c3 c2) c1) c0

@[expose] noncomputable def rawN (c0 c1 c2 c3 : Nat) : Nat :=
  cond (Nat.beq c0 0)
    (cond (Nat.beq c1 0) (cond (Nat.beq c2 0) 819 (Nat.add 810 c3))
      (Nat.add (Nat.add 729 (Nat.mul 9 c2)) c3))
    (Nat.add (Nat.add (Nat.mul 81 c1) (Nat.mul 9 c2)) c3)

@[expose] noncomputable def ptNt (t c0 c1 c2 c3 : Nat) : Nat :=
  rawN (mulN t c0) (mulN t c1) (mulN t c2) (mulN t c3)

@[expose] noncomputable def ptN (c0 c1 c2 c3 : Nat) : Nat :=
  ptNt (invN (leadN c0 c1 c2 c3)) c0 c1 c2 c3

theorem beq_code : ∀ a : F9, Nat.beq (code a) 0 = decide (a = 0) := by decide

theorem code_lead (v : V) :
    code (lead v) = leadN (code (v 0)) (code (v 1)) (code (v 2)) (code (v 3)) := by
  unfold lead leadN
  simp only [beq_code]
  by_cases h0 : v 0 = 0 <;> by_cases h1 : v 1 = 0 <;> by_cases h2 : v 2 = 0 <;> simp [h0, h1, h2]

theorem rawIndex_code (v : V) :
    rawIndex v = rawN (code (v 0)) (code (v 1)) (code (v 2)) (code (v 3)) := by
  unfold rawIndex rawN
  simp only [beq_code]
  by_cases h0 : v 0 = 0 <;> by_cases h1 : v 1 = 0 <;> by_cases h2 : v 2 = 0 <;> simp [h0, h1, h2]

theorem ptIndex_code (w : V) :
    ptIndex w = ptN (code (w 0)) (code (w 1)) (code (w 2)) (code (w 3)) := by
  have e : ∀ j, code (normalize w j) =
      mulN (invN (leadN (code (w 0)) (code (w 1)) (code (w 2)) (code (w 3)))) (code (w j)) := by
    intro j
    unfold CFSG.LieType.Multipliers.U43.normalize
    rw [Pi.smul_apply, smul_eq_mul, code_mul, code_inv, code_lead]
  rw [ptIndex, rawIndex_code, e 0, e 1, e 2, e 3]
  rfl

@[expose] noncomputable def ucN (k r j : Nat) : Nat := k / 9 ^ (4 * r + j) % 9

theorem code_matK (k : Nat) (r j : Fin 4) : code (matK k r j) = ucN k r j := by
  rw [matK, Matrix.of_apply, code_uncode (Nat.mod_lt _ (by decide))]
  rfl

@[expose] noncomputable def mvN (k r u0 u1 u2 u3 : Nat) : Nat :=
  addN (addN (addN (mulN (ucN k r 0) u0) (mulN (ucN k r 1) u1)) (mulN (ucN k r 2) u2))
    (mulN (ucN k r 3) u3)

theorem code_mvK (k : Nat) (u : V) (r : Fin 4) :
    code (mvK (matK k) u r) = mvN k r (code (u 0)) (code (u 1)) (code (u 2)) (code (u 3)) := by
  simp only [mvK, code_add, code_mul, code_matK, mvN]
  rfl

@[expose] noncomputable def dN0 (i : Nat) : Nat := cond (Nat.blt i 729) 3 0
@[expose] noncomputable def dN1 (i : Nat) : Nat :=
  cond (Nat.blt i 729) (i / 81) (cond (Nat.blt i 810) 3 0)
@[expose] noncomputable def dN2 (i : Nat) : Nat :=
  cond (Nat.blt i 729) (i / 9 % 9) (cond (Nat.blt i 810) ((i - 729) / 9) (cond (Nat.blt i 819) 3 0))
@[expose] noncomputable def dN3 (i : Nat) : Nat :=
  cond (Nat.blt i 729) (i % 9)
    (cond (Nat.blt i 810) ((i - 729) % 9) (cond (Nat.blt i 819) (i - 810) 3))

theorem code_decode (i : Nat) : code (decode i 0) = dN0 i ∧ code (decode i 1) = dN1 i ∧
    code (decode i 2) = dN2 i ∧ code (decode i 3) = dN3 i := by
  unfold decode dN0 dN1 dN2 dN3
  by_cases h1 : i < 729
  · have b1 : Nat.blt i 729 = true := by rw [Nat.blt_eq]; omega
    simp [h1, b1, code_one, code_uncode (show i / 81 < 9 by omega),
      code_uncode (show i / 9 % 9 < 9 by omega), code_uncode (show i % 9 < 9 by omega)]
  · have b1 : Nat.blt i 729 = false := Bool.eq_false_iff.mpr (by rw [Ne, Nat.blt_eq]; omega)
    by_cases h2 : i < 810
    · have b2 : Nat.blt i 810 = true := by rw [Nat.blt_eq]; omega
      simp [h1, h2, b1, b2, code_one, code_zero,
        code_uncode (show (i - 729) / 9 < 9 by omega),
        code_uncode (show (i - 729) % 9 < 9 by omega)]
    · have b2 : Nat.blt i 810 = false := Bool.eq_false_iff.mpr (by rw [Ne, Nat.blt_eq]; omega)
      by_cases h3 : i < 819
      · have b3 : Nat.blt i 819 = true := by rw [Nat.blt_eq]; omega
        simp [h1, h2, h3, b1, b2, b3, code_one, code_zero,
          code_uncode (show i - 810 < 9 by omega)]
      · have b3 : Nat.blt i 819 = false := Bool.eq_false_iff.mpr (by rw [Ne, Nat.blt_eq]; omega)
        simp [h1, h2, h3, b1, b2, b3, code_one, code_zero]

@[expose] noncomputable def imgKu (k u0 u1 u2 u3 : Nat) : Nat :=
  ptN (mvN k 0 u0 u1 u2 u3) (mvN k 1 u0 u1 u2 u3) (mvN k 2 u0 u1 u2 u3) (mvN k 3 u0 u1 u2 u3)

@[expose] noncomputable def imgKN (k : Nat) (ε : Bool) (i : Nat) : Nat :=
  cond ε (imgKu k (barN (dN0 i)) (barN (dN1 i)) (barN (dN2 i)) (barN (dN3 i)))
    (imgKu k (dN0 i) (dN1 i) (dN2 i) (dN3 i))

theorem imgK_eq (k : Nat) (ε : Bool) (i : Nat) : imgK k ε i = imgKN k ε i := by
  obtain ⟨e0, e1, e2, e3⟩ := code_decode i
  unfold imgK imgKN imgKu
  rw [ptIndex_code, code_mvK, code_mvK, code_mvK, code_mvK]
  cases ε
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.cond_false, e0, e1, e2, e3]
    rfl
  · simp only [↓reduceIte, Bool.cond_true, barV, code_barF, e0, e1, e2, e3]
    rfl

@[expose] noncomputable def matOKN (k : ℕ) (ε : Bool) (p : ℕ) : Bool :=
  (List.range 820).all fun i => Nat.beq (at10 p i) (imgKN k ε i)

theorem matOK_eq (k : ℕ) (ε : Bool) (p : ℕ) : matOK k ε p = matOKN k ε p := by
  unfold matOK matOKN
  simp only [imgK_eq]

end CertificateChecks.KernelPermCent.U43Quat

end
