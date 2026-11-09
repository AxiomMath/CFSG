module

public import CFSG.Monster.B.TwoA.Census.XiFusionInputs

public section

namespace CertificateChecks.KernelXiFusion

open CFSG.Monster.B.TwoA.Census Matrix

set_option maxHeartbeats 0

@[expose] def fin24 (n : ℕ) : Fin 24 := ⟨n % 24, Nat.mod_lt _ (by decide)⟩

theorem fin24_val (n : ℕ) : (fin24 n : ℕ) = n % 24 := rfl

@[expose] def sg (d : ℕ) (i : Fin 24) : ℚ := if d.testBit i then -1 else 1

theorem mulArr_eq (a b : Array (Array ℚ)) : mulArr a b = ofMat (toMat a * toMat b) := rfl

theorem dsgn_mul (d : ℕ) (M : Matrix (Fin 24) (Fin 24) ℚ) :
    dsgn d * M = Matrix.of fun (i k : Fin 24) => sg d i * M i k := by
  ext i k
  rw [dsgn, Matrix.diagonal_mul, Matrix.of_apply]
  rfl

theorem mul_dsgn (M : Matrix (Fin 24) (Fin 24) ℚ) (d : ℕ) :
    M * dsgn d = Matrix.of fun (i k : Fin 24) => M i k * sg d k := by
  ext i k
  rw [dsgn, Matrix.mul_diagonal, Matrix.of_apply]
  rfl

theorem pmatA_mul (a : Array ℕ) (M : Matrix (Fin 24) (Fin 24) ℚ) :
    pmatA a * M = Matrix.of fun (i k : Fin 24) =>
      if a[(i : ℕ)]! < 24 then M (fin24 a[(i : ℕ)]!) k else 0 := by
  ext i k
  rw [Matrix.mul_apply, Matrix.of_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single (fin24 a[(i : ℕ)]!)]
    · simp only [pmatA, Matrix.of_apply]
      rw [if_pos (by rw [fin24_val, Nat.mod_eq_of_lt h]), one_mul]
    · intro j _ hj
      simp only [pmatA, Matrix.of_apply]
      rw [if_neg, zero_mul]
      intro hh
      apply hj
      apply Fin.ext
      rw [fin24_val, hh, Nat.mod_eq_of_lt j.isLt]
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · apply Finset.sum_eq_zero
    intro j _
    simp only [pmatA, Matrix.of_apply]
    rw [if_neg, zero_mul]
    intro hh
    exact h (by rw [hh]; exact j.isLt)

@[expose] def invOK (a : Array ℕ) : Bool :=
  (List.finRange 24).all fun k => decide (a[(k : ℕ)]! < 24) && a[a[(k : ℕ)]!]! == (k : ℕ)

theorem inv_facts {a : Array ℕ} (h : invOK a = true) (k : Fin 24) :
    a[(k : ℕ)]! < 24 ∧ a[a[(k : ℕ)]!]! = k := by
  have := List.all_eq_true.1 h k (List.mem_finRange k)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
  exact this

theorem mul_pmatA (M : Matrix (Fin 24) (Fin 24) ℚ) {a : Array ℕ} (ha : invOK a = true) :
    M * pmatA a = Matrix.of fun (i k : Fin 24) => M i (fin24 a[(k : ℕ)]!) := by
  ext i k
  rw [Matrix.mul_apply, Matrix.of_apply]
  have hk := inv_facts ha k
  rw [Finset.sum_eq_single (fin24 a[(k : ℕ)]!)]
  · simp only [pmatA, Matrix.of_apply]
    rw [if_pos (by rw [fin24_val, Nat.mod_eq_of_lt hk.1, hk.2]), mul_one]
  · intro j _ hj
    simp only [pmatA, Matrix.of_apply]
    rw [if_neg, mul_zero]
    intro hh
    apply hj
    apply Fin.ext
    have h2 := (inv_facts ha j).2
    rw [hh] at h2
    rw [fin24_val, h2, Nat.mod_eq_of_lt j.isLt]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

@[expose] def LF (s : ℕ) (a : Array ℕ) (c : ℕ) (w : Array ℕ) (i k : Fin 24) : ℚ :=
  sg s i * (if a[(i : ℕ)]! < 24 then sg c (fin24 a[(i : ℕ)]!) *
    (if w[((fin24 a[(i : ℕ)]! : Fin 24) : ℕ)]! < 24 then
      CFSG.Monster.Xi.gXi (fin24 w[((fin24 a[(i : ℕ)]! : Fin 24) : ℕ)]!) k else 0) else 0)

@[expose] def RF (c : ℕ) (w : Array ℕ) (d : ℕ) (p : Array ℕ) (i k : Fin 24) : ℚ :=
  sg c i * (if w[(i : ℕ)]! < 24 then
      CFSG.Monster.Xi.gXi (fin24 w[(i : ℕ)]!) (fin24 p[(k : ℕ)]!) else 0) *
    sg d (fin24 p[(k : ℕ)]!)

theorem lhs_eq (s c : ℕ) (a w : Array ℕ) :
    dsgn s * pmatA a * (dsgn c * pmatA w * CFSG.Monster.Xi.gXi) = Matrix.of (LF s a c w) := by
  simp only [Matrix.mul_assoc]
  rw [dsgn_mul, pmatA_mul, dsgn_mul, pmatA_mul]
  rfl

theorem rhs_eq (c d : ℕ) (w : Array ℕ) {p : Array ℕ} (hp : invOK p = true) :
    dsgn c * pmatA w * CFSG.Monster.Xi.gXi * (dsgn d * pmatA p) = Matrix.of (RF c w d p) := by
  rw [← Matrix.mul_assoc (dsgn c * pmatA w * CFSG.Monster.Xi.gXi) (dsgn d) (pmatA p),
    mul_pmatA _ hp, mul_dsgn, Matrix.mul_assoc (dsgn c) (pmatA w) CFSG.Monster.Xi.gXi, dsgn_mul,
    pmatA_mul]
  rfl

@[expose] def edgeOK (e : XiEdge) : Bool :=
  invOK e.afterPerm &&
    decide (ofMat (Matrix.of (LF (monoSign.getD e.source 0) (seedA (monoSeed.getD e.source 0))
      e.conjSign (wordArr e.word))) =
    ofMat (Matrix.of (RF e.conjSign (wordArr e.word) e.afterSign e.afterPerm)))

theorem edge_ok {e : XiEdge} (h : edgeOK e = true) :
    mulArr (xiArrA e) (xiArrM e) = mulArr (xiArrM e) (xiArrR e) := by
  have h' := h
  simp only [edgeOK, Bool.and_eq_true, decide_eq_true_eq] at h'
  rw [mulArr_eq, mulArr_eq]
  simp only [xiArrA, xiArrM, xiArrR, toMat_mulArr, toMat_ofMat]
  rw [lhs_eq, rhs_eq _ _ _ h'.1]
  exact h'.2

theorem edges0 : ∀ e ∈ xiEdges.take 1, edgeOK e = true := by decide +kernel

theorem edges1 : ∀ e ∈ (xiEdges.drop 1).take 1, edgeOK e = true := by decide +kernel

theorem edges2 : ∀ e ∈ xiEdges.drop 2, edgeOK e = true := by decide +kernel

theorem arr_check0 :
    ∀ e ∈ xiEdges.take 1, mulArr (xiArrA e) (xiArrM e) = mulArr (xiArrM e) (xiArrR e) :=
  fun e he => edge_ok (edges0 e he)

theorem arr_check1 : ∀ e ∈ (xiEdges.drop 1).take 1,
    mulArr (xiArrA e) (xiArrM e) = mulArr (xiArrM e) (xiArrR e) :=
  fun e he => edge_ok (edges1 e he)

theorem arr_check2 :
    ∀ e ∈ xiEdges.drop 2, mulArr (xiArrA e) (xiArrM e) = mulArr (xiArrM e) (xiArrR e) :=
  fun e he => edge_ok (edges2 e he)

theorem arr_check :
    ∀ e ∈ xiEdges, mulArr (xiArrA e) (xiArrM e) = mulArr (xiArrM e) (xiArrR e) := by
  intro e he
  rw [← List.take_append_drop 1 xiEdges, List.mem_append] at he
  rcases he with he | he
  · exact arr_check0 e he
  rw [← List.take_append_drop 1 (xiEdges.drop 1), List.mem_append] at he
  rcases he with he | he
  · exact arr_check1 e he
  · exact arr_check2 e (by simpa [List.drop_drop] using he)

end CertificateChecks.KernelXiFusion

end
