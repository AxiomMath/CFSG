module

public import Certificates.Data.CFSGNative.MonsterB.Max2Tower
public import CFSG.Certificates.Kernel.Co1F2Sound

public section

namespace CertificateChecks.KernelSpor.Co2Inv

open CFSG.KC.Co1F2

@[expose] def inv22Col (A : Array (Nat × Nat)) (c : Nat) : Array (Nat × Nat) :=
  let p := (List.range' c ((22 - c + 1 - 1) / 1)).foldl
    (fun p r => if p == 22 && (A[r]!.1.testBit c) then r else p) 22
  if p < 22 then
    (List.range' 0 ((22 - 0 + 1 - 1) / 1)).foldl
      (fun A r => if r != c && (A[r]!.1.testBit c) then
          A.set! r (A[r]!.1 ^^^ A[c]!.1, A[r]!.2 ^^^ A[c]!.2) else A)
      ((A.set! c A[p]!).set! p A[c]!)
  else A

@[expose] def inv22F (rows : Array Nat) : Array Nat :=
  ((List.range' 0 ((22 - 0 + 1 - 1) / 1)).foldl inv22Col
    ((Array.range 22).map fun i => (rows[i]!, 1 <<< i))).map (·.2)

theorem ite_pure_yield22 {β : Type} (p : Prop) [Decidable p] (x y : β) :
    (if p then (pure (ForInStep.yield x) : Id (ForInStep β)) else pure (ForInStep.yield y)) =
      pure (ForInStep.yield (if p then x else y)) := by
  split <;> rfl

theorem inv22_eq_F (rows : Array Nat) : CFSG.Monster.B.Max2.Native.inv22 rows = inv22F rows := by
  simp only [CFSG.Monster.B.Max2.Native.inv22, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, ite_pure_yield22, List.forIn_pure_yield_eq_foldl, pure_bind,
    Id.run_pure]
  rfl

@[expose] def rowK (P r : Nat) : Nat := (P >>> (22 * r)) % 2 ^ 22

@[expose] def setK (P r v : Nat) : Nat := P ^^^ ((rowK P r ^^^ v) <<< (22 * r))

@[expose] def invColK (A : Nat × Nat) (c : Nat) : Nat × Nat :=
  let p := (List.range' c ((22 - c + 1 - 1) / 1)).foldl
    (fun p r => if p == 22 && (rowK A.1 r).testBit c then r else p) 22
  if p < 22 then
    let s1 := setK (setK A.1 c (rowK A.1 p)) p (rowK A.1 c)
    let s2 := setK (setK A.2 c (rowK A.2 p)) p (rowK A.2 c)
    (List.range' 0 ((22 - 0 + 1 - 1) / 1)).foldl
      (fun A r => if r != c && (rowK A.1 r).testBit c then
          (setK A.1 r (rowK A.1 r ^^^ rowK A.1 c), setK A.2 r (rowK A.2 r ^^^ rowK A.2 c)) else A)
      (s1, s2)
  else A

@[expose] def idP22 : Nat := (List.range' 0 22).foldl (fun P i => P ||| (1 <<< (22 * i + i))) 0

@[expose] def invP22 (P : Nat) : Nat :=
  ((List.range' 0 ((22 - 0 + 1 - 1) / 1)).foldl invColK (P, idP22)).2

theorem rowK_lt (P r : Nat) : rowK P r < 2 ^ 22 := Nat.mod_lt _ (by decide)

theorem testBit_hi {v j : Nat} (hv : v < 2 ^ 22) (hj : 22 ≤ j) : v.testBit j = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) hj))

theorem rowK_setK (P r v i : Nat) (hv : v < 2 ^ 22) :
    rowK (setK P r v) i = if r = i then v else rowK P i := by
  have hD : rowK P r ^^^ v < 2 ^ 22 := Nat.xor_lt_two_pow (rowK_lt P r) hv
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 22
  · by_cases hri : r = i
    · subst hri
      simp only [rowK, setK, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.testBit_xor,
        Nat.testBit_shiftLeft, hj, decide_true, Bool.true_and, ite_true]
      simp only [Nat.le_add_right, decide_true, Bool.true_and, Nat.add_sub_cancel_left, hj]
      cases P.testBit (22 * r + j) <;> simp
    · simp only [rowK, setK, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.testBit_xor,
        Nat.testBit_shiftLeft, hj, decide_true, Bool.true_and, hri, ite_false]
      by_cases hlt : i < r
      · have h1 : ¬ (22 * i + j ≥ 22 * r) := by omega
        simp [h1]
      · have h1 : ¬ (22 * i + j - 22 * r < 22) := by omega
        have h2 := testBit_hi hv (show 22 ≤ 22 * i + j - 22 * r by omega)
        simp [h1, h2]
  · have h1 : (rowK (setK P r v) i).testBit j = false := testBit_hi (rowK_lt _ _) (by omega)
    rw [h1]
    split
    · exact (testBit_hi hv (by omega)).symm
    · exact (testBit_hi (rowK_lt _ _) (by omega)).symm

def RelK (A : Array (Nat × Nat)) (K : Nat × Nat) : Prop :=
  A.size = 22 ∧ ∀ i < 22, A[i]! = (rowK K.1 i, rowK K.2 i)

theorem relK_set {A : Array (Nat × Nat)} {K : Nat × Nat} (h : RelK A K) {r x y : Nat}
    (hx : x < 2 ^ 22) (hy : y < 2 ^ 22) :
    RelK (A.set! r (x, y)) (setK K.1 r x, setK K.2 r y) := by
  refine ⟨by simp [h.1], fun i hi => ?_⟩
  have hs : i < (A.set! r (x, y)).size := by simp [h.1, hi]
  rw [getElem!_pos _ i hs]
  simp only [Array.set!_eq_setIfInBounds]
  rw [Array.getElem_setIfInBounds (by rw [h.1]; exact hi), rowK_setK _ _ _ _ hx,
    rowK_setK _ _ _ _ hy]
  split
  · rfl
  · rw [← getElem!_pos A i (by rw [h.1]; exact hi), h.2 i hi]

theorem foldl_eqOn {α β : Type} {l : List α} {f g : β → α → β} (h : ∀ a ∈ l, ∀ b, f b a = g b a)
    (i : β) : l.foldl f i = l.foldl g i := by
  induction l generalizing i with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldl_cons]
    rw [h a (List.mem_cons_self) i]
    exact ih (fun a' ha' b => h a' (List.mem_cons_of_mem _ ha') b) _

theorem foldl_relK {α : Type} {l : List α} {f : Array (Nat × Nat) → α → Array (Nat × Nat)}
    {g : Nat × Nat → α → Nat × Nat} (h : ∀ a ∈ l, ∀ A K, RelK A K → RelK (f A a) (g K a))
    {A K} (h0 : RelK A K) : RelK (l.foldl f A) (l.foldl g K) := by
  induction l generalizing A K with
  | nil => exact h0
  | cons a l ih =>
    exact ih (fun a' ha' => h a' (List.mem_cons_of_mem _ ha')) (h a List.mem_cons_self A K h0)

theorem relK_col {A K} (h : RelK A K) {c : Nat} (hc : c < 22) :
    RelK (inv22Col A c) (invColK K c) := by
  have hp : (List.range' c ((22 - c + 1 - 1) / 1)).foldl
      (fun p r => if p == 22 && (A[r]!.1.testBit c) then r else p) 22 =
      (List.range' c ((22 - c + 1 - 1) / 1)).foldl
      (fun p r => if p == 22 && (rowK K.1 r).testBit c then r else p) 22 := by
    refine foldl_eqOn (fun r hr p => ?_) _
    have hr' : r < 22 := by
      rw [List.mem_range'_1] at hr
      omega
    rw [h.2 r hr']
  unfold inv22Col invColK
  dsimp only
  rw [hp]
  split
  · next hp22 =>
    refine foldl_relK (fun r hr B L hB => ?_) ?_
    · have hr' : r < 22 := by
        rw [List.mem_range'_1] at hr
        omega
      rw [hB.2 r hr', hB.2 c hc]
      split
      · exact relK_set hB (Nat.xor_lt_two_pow (rowK_lt _ _) (rowK_lt _ _))
          (Nat.xor_lt_two_pow (rowK_lt _ _) (rowK_lt _ _))
      · exact hB
    · rw [h.2 _ hp22, h.2 c hc]
      exact relK_set (relK_set h (rowK_lt _ _) (rowK_lt _ _)) (rowK_lt _ _) (rowK_lt _ _)
  · exact h

theorem rowK_idP22 : ∀ i < 22, rowK idP22 i = 1 <<< i := by decide

theorem inv22F_unpack (M : Nat) : inv22F (unpackR 22 M) = unpackR 22 (invP22 M) := by
  have h0 : RelK ((Array.range 22).map fun i => ((unpackR 22 M)[i]!, 1 <<< i)) (M, idP22) := by
    refine ⟨by simp, fun i hi => ?_⟩
    rw [getElem!_pos _ i (by simp [hi])]
    simp only [Array.getElem_map, Array.getElem_range]
    rw [rowK_idP22 i hi, getElem!_pos _ i (by simp [unpackR, hi])]
    simp [unpackR, rowK, Nat.shiftRight_eq_div_pow]
  have hcol : ∀ c ∈ List.range' 0 ((22 - 0 + 1 - 1) / 1), ∀ A K, RelK A K →
      RelK (inv22Col A c) (invColK K c) := by
    intro c hc A K hA
    rw [List.mem_range'_1] at hc
    exact relK_col hA (by omega)
  obtain ⟨hs, hrow⟩ := foldl_relK hcol h0
  unfold inv22F invP22
  apply Array.ext
  · rw [Array.size_map, hs]
    simp [unpackR]
  · intro i hi1 hi2
    have hi : i < 22 := by
      rw [Array.size_map, hs] at hi1
      exact hi1
    rw [Array.getElem_map, ← getElem!_pos _ i (by rw [hs]; exact hi), hrow i hi]
    simp [unpackR, rowK, Nat.shiftRight_eq_div_pow]

theorem inv22_unpack (M : Nat) :
    CFSG.Monster.B.Max2.Native.inv22 (unpackR 22 M) = unpackR 22 (invP22 M) := by
  rw [inv22_eq_F, inv22F_unpack]

end CertificateChecks.KernelSpor.Co2Inv

end
