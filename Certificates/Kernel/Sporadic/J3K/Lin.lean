module

public import Certificates.Data.CFSGNative.J3.Basic

public section

namespace CertificateChecks.KernelSpor.J3K

open CFSG.Sporadic.J3.Native

def LinX (f : Nat → Nat) : Prop := f 0 = 0 ∧ ∀ a b, f (a ^^^ b) = f a ^^^ f b

theorem vecMulN_succ (d : Nat) (R : Array Nat) (v : Nat) :
    vecMulN (d + 1) R v = vecMulN d R v ^^^ (if v.testBit d then R[d]?.getD 0 else 0) := by
  unfold vecMulN
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  split <;> simp

theorem vecMulN_dim0 (R : Array Nat) (v : Nat) : vecMulN 0 R v = 0 := by
  simp [vecMulN]

theorem xor_cancel_mid (X Y Z : Nat) : X ^^^ Y = X ^^^ Z ^^^ (Y ^^^ Z) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases X.testBit i <;> cases Y.testBit i <;> cases Z.testBit i <;> rfl

theorem vecMulN_xorL (d : Nat) (R : Array Nat) (a b : Nat) :
    vecMulN d R (a ^^^ b) = vecMulN d R a ^^^ vecMulN d R b := by
  induction d with
  | zero => simp [vecMulN_dim0]
  | succ d ih =>
    rw [vecMulN_succ, vecMulN_succ, vecMulN_succ, ih, Nat.testBit_xor]
    cases a.testBit d <;> cases b.testBit d <;>
      simp only [Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte, Nat.xor_zero]
    all_goals first | ac_rfl | exact xor_cancel_mid _ _ _

theorem vecMulN_lin (d : Nat) (R : Array Nat) : LinX (vecMulN d R) := by
  refine ⟨?_, vecMulN_xorL d R⟩
  induction d with
  | zero => exact vecMulN_dim0 R 0
  | succ d ih => simp [vecMulN_succ, ih]

theorem LinX.comp {f g : Nat → Nat} (hf : LinX f) (hg : LinX g) : LinX (fun v => f (g v)) :=
  ⟨by simp only [hg.1, hf.1], fun a b => by simp only [hg.2, hf.2]⟩

theorem LinX.id : LinX (fun v => v) := ⟨rfl, fun _ _ => rfl⟩

theorem LinX.vecMulN_eq {f : Nat → Nat} (hf : LinX f) {d : Nat} {R R' : Array Nat}
    (h : ∀ j < d, f (R[j]?.getD 0) = R'[j]?.getD 0) (v : Nat) :
    f (vecMulN d R v) = vecMulN d R' v := by
  induction d with
  | zero => exact hf.1
  | succ d ih =>
    rw [vecMulN_succ, vecMulN_succ, hf.2, ih fun j hj => h j (by omega)]
    split
    · rw [h d (by omega)]
    · rw [hf.1]

theorem vecMulN_idRows {D d : Nat} (hd : d ≤ D) (v i : Nat) :
    (vecMulN d (idRows D) v).testBit i = (decide (i < d) && v.testBit i) := by
  induction d with
  | zero => simp [vecMulN_dim0]
  | succ d ih =>
    have hdD : d < D := by omega
    have e : (idRows D)[d]?.getD 0 = 2 ^ d := by
      simp [idRows, hdD, Nat.one_shiftLeft]
    rw [vecMulN_succ, e, Nat.testBit_xor, ih (by omega)]
    by_cases hi : i = d
    · subst hi
      split <;> simp_all
    · have : (i < d + 1) = (i < d) := propext ⟨fun h => by omega, fun h => by omega⟩
      split <;> simp [Ne.symm hi, this]

theorem vecMulN_id {d v : Nat} (hv : v < 2 ^ d) : vecMulN d (idRows d) v = v := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [vecMulN_idRows (Nat.le_refl d)]
  by_cases hi : i < d
  · simp [hi]
  · have : v.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [hi, this]

theorem LinX.fix_of_basis {f : Nat → Nat} (hf : LinX f) {d : Nat} {W Binv : Array Nat}
    (hI : mulRows d Binv W = idRows d) (hW : ∀ j < d, f (W[j]?.getD 0) = W[j]?.getD 0)
    {v : Nat} (hv : v < 2 ^ d) : f v = v := by
  have he : ∀ j < d, f ((idRows d)[j]?.getD 0) = (idRows d)[j]?.getD 0 := by
    intro j hj
    have hs : Binv.size = d := by
      have := congrArg Array.size hI
      simpa [mulRows, idRows] using this
    have hj' : j < Binv.size := by omega
    have e : (idRows d)[j]?.getD 0 = vecMulN d W Binv[j] := by
      rw [← hI]
      simp [mulRows, hj']
    rw [e]
    exact hf.vecMulN_eq hW _
  rw [← vecMulN_id hv]
  exact hf.vecMulN_eq he v

theorem foldr_linX {α : Type} {F : α → Nat → Nat} {w : List α} (hF : ∀ l ∈ w, LinX (F l)) :
    LinX (fun v => List.foldr F v w) := by
  induction w with
  | nil => exact LinX.id
  | cons l w ih =>
    exact (hF l List.mem_cons_self).comp (ih fun l hl => hF l (List.mem_cons_of_mem _ hl))

theorem foldr_transfer {α : Type} {n : Nat} {P : Nat → Nat} {act F : α → Nat → Nat} {w : List α}
    (hact : ∀ l ∈ w, ∀ x < n, act l x < n ∧ P (act l x) = F l (P x)) {x : Nat} (hx : x < n) :
    List.foldr act x w < n ∧ P (List.foldr act x w) = List.foldr F (P x) w := by
  induction w with
  | nil => exact ⟨hx, rfl⟩
  | cons l w ih =>
    obtain ⟨h1, h2⟩ := ih fun l hl => hact l (List.mem_cons_of_mem _ hl)
    obtain ⟨h3, h4⟩ := hact l List.mem_cons_self _ h1
    exact ⟨h3, by rw [List.foldr_cons, List.foldr_cons, h4, h2]⟩

theorem word_fix_lin {α : Type} {n d : Nat} {P : Nat → Nat}
    (hP : ∀ x < n, ∀ y < n, P x = P y → x = y) (hPd : ∀ x < n, P x < 2 ^ d) {act F : α → Nat → Nat} {w : List α}
    (hact : ∀ l ∈ w, ∀ x < n, act l x < n ∧ P (act l x) = F l (P x))
    (hF : ∀ l ∈ w, LinX (F l)) {W Binv : Array Nat} (hI : mulRows d Binv W = idRows d)
    (hW : ∀ j < d, ∃ b < n, P b = W[j]?.getD 0 ∧ List.foldr act b w = b) :
    ∀ x < n, List.foldr act x w = x := by
  intro x hx
  have hL := foldr_linX hF
  have hfix : ∀ v < 2 ^ d, List.foldr F v w = v := fun v hv =>
    hL.fix_of_basis (f := fun v => List.foldr F v w) hI (fun j hj => by
      obtain ⟨b, hb, e, hfb⟩ := hW j hj
      rw [← e, ← (foldr_transfer hact hb).2, hfb]) hv
  obtain ⟨h1, h2⟩ := foldr_transfer hact hx
  exact hP _ h1 _ hx (by rw [h2, hfix _ (hPd x hx)])

theorem inj_of_strict {n : Nat} {P : Nat → Nat} (h : ∀ i, i + 1 < n → P i < P (i + 1)) :
    ∀ x < n, ∀ y < n, P x = P y → x = y := by
  have hlt : ∀ i k, i + k + 1 < n → P i < P (i + k + 1) := by
    intro i k
    induction k with
    | zero => exact h i
    | succ k ih => exact fun hk => Nat.lt_trans (ih (by omega)) (h _ (by omega))
  intro x hx y hy e
  rcases Nat.lt_trichotomy x y with hxy | hxy | hxy
  · have e : x + (y - x - 1) + 1 = y := by omega
    have := hlt x (y - x - 1) (by omega)
    rw [e] at this
    omega
  · exact hxy
  · have e : y + (x - y - 1) + 1 = x := by omega
    have := hlt y (x - y - 1) (by omega)
    rw [e] at this
    omega

@[expose] noncomputable def bitDisjK (D : Nat → Nat) (T : Nat) (m : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ acc => Nat.beq acc T)
    (fun _ ih l acc => Nat.beq (Nat.land acc (D l)) 0 && ih (Nat.succ l) (Nat.lor acc (D l))) m

theorem bitDisjK_spec {D : Nat → Nat} {T : Nat} : ∀ m l acc, bitDisjK D T m l acc = true →
    (∀ b, acc.testBit b = true → T.testBit b = true) ∧
    ∀ i < m, ∀ b, (D (l + i)).testBit b = true → T.testBit b = true ∧ acc.testBit b = false ∧
      ∀ i' < m, i' ≠ i → (D (l + i')).testBit b = false := by
  intro m
  induction m with
  | zero =>
    intro l acc h
    have e : acc = T := Nat.eq_of_beq_eq_true h
    subst e
    exact ⟨fun b hb => hb, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ m ih =>
    intro l acc h
    have e : bitDisjK D T (m + 1) l acc =
        (Nat.beq (Nat.land acc (D l)) 0 && bitDisjK D T m (Nat.succ l) (Nat.lor acc (D l))) := rfl
    rw [e, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have h0 : acc &&& D l = 0 := Nat.eq_of_beq_eq_true h1
    have hdis : ∀ b, acc.testBit b = true → (D l).testBit b = false := fun b hb => by
      have := congrArg (fun x => x.testBit b) h0
      simpa [Nat.testBit_and, hb] using this
    obtain ⟨A, B⟩ := ih (l + 1) (acc ||| D l) h2
    refine ⟨fun b hb => A b (by simp [Nat.testBit_or, hb]), ?_⟩
    intro i hi b hb
    rcases i with _ | j
    · rw [Nat.add_zero] at hb
      refine ⟨A b (by simp [Nat.testBit_or, hb]), ?_, ?_⟩
      · cases ha : acc.testBit b
        · rfl
        · rw [hdis b ha] at hb
          exact absurd hb (by decide)
      · intro i' hi' hne
        rcases i' with _ | j'
        · exact absurd rfl hne
        · cases hc : (D (l + (j' + 1))).testBit b
          · rfl
          · have e2 : l + 1 + j' = l + (j' + 1) := by omega
            have := (B j' (by omega) b (by rw [e2]; exact hc)).2.1
            simp [Nat.testBit_or, hb] at this
    · have e2 : l + 1 + j = l + (j + 1) := by omega
      obtain ⟨t1, t2, t3⟩ := B j (by omega) b (by rw [e2]; exact hb)
      refine ⟨t1, ?_, ?_⟩
      · cases ha : acc.testBit b
        · rfl
        · simp [Nat.testBit_or, ha] at t2
      · intro i' hi' hne
        rcases i' with _ | j'
        · cases hc : (D (l + 0)).testBit b
          · rfl
          · rw [Nat.add_zero] at hc
            simp [Nat.testBit_or, hc] at t2
        · have e3 : l + 1 + j' = l + (j' + 1) := by omega
          have := t3 j' (by omega) (by omega)
          rwa [e3] at this

end CertificateChecks.KernelSpor.J3K

end
