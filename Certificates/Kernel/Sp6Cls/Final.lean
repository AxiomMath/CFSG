module

public import Certificates.Kernel.Sp6Cls.Checks
public import Certificates.Kernel.Sp6A2.Final
public import Certificates.Kernel.Sp6Two.Final

public section

namespace CFSG.KD.Sp6Cls

open CFSG.KD.Sp62 CFSG.KC.Sp62 CFSG.KC.Sp6Two CFSG.Quasithin.G2U
  CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Cls
  CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII

theorem andC_eq (a b : Bool) : andC a b = (a && b) := by cases a <;> rfl

theorem orC_eq (a b : Bool) : orC a b = (a || b) := by cases a <;> rfl

theorem notC_eq (a : Bool) : notC a = !a := by cases a <;> rfl

theorem letC_eq (y : ℕ) (k : ℕ → Bool) : letC y k = k y := by cases y <;> rfl

theorem allNC_iff (m : ℕ) (f : ℕ → Bool) : allNC m f = true ↔ ∀ i < m, f i = true := by
  induction m with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ m ih =>
    have e : allNC (m + 1) f = andC (f m) (allNC m f) := rfl
    rw [e, andC_eq, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact h2 i h
      · exact h1
    · intro h
      exact ⟨h m (Nat.lt_succ_self m), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem anyNC_iff (m : ℕ) (f : ℕ → Bool) : anyNC m f = true ↔ ∃ i < m, f i = true := by
  induction m with
  | zero => exact ⟨fun h => absurd h Bool.false_ne_true, fun ⟨i, hi, _⟩ => absurd hi (Nat.not_lt_zero i)⟩
  | succ m ih =>
    have e : anyNC (m + 1) f = orC (f m) (anyNC m f) := rfl
    rw [e, orC_eq, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨m, Nat.lt_succ_self m, h⟩
      · exact ⟨i, Nat.lt_succ_of_lt hi, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hl | rfl
      · exact Or.inr ⟨i, hl, h⟩
      · exact Or.inl h

theorem getD_of_lt {E : Array (List ℕ)} {i : ℕ} (hi : i < E.size) : E.getD i [] = E[i] := by
  simp [Array.getD, hi]

theorem arr_all {p : List ℕ → Bool} {E : Array (List ℕ)} {n : ℕ} (hE : E.size = n)
    (h : ∀ t < n, p (E.getD t []) = true) : E.all p = true := by
  rw [Array.all_eq_true]
  intro i hi
  have := h i (hE ▸ hi)
  rwa [getD_of_lt hi] at this

theorem not_contains {O : Array (List ℕ)} {R : ℕ → ℕ} {o n : ℕ} (hO : O.size = n)
    (hr : ∀ t < n, canon6 (O.getD t []) = true ∧ pk (O.getD t []) = recX R o t) {c : List ℕ}
    (h : outO R o n (pk c) = true) : O.contains c = false := by
  rw [Bool.eq_false_iff]
  intro hm
  obtain ⟨i, hi, e⟩ := Array.mem_iff_getElem.1 (Array.contains_iff_mem.1 hm)
  have hi' : i < n := hO ▸ hi
  have h2 := (allNC_iff _ _).1 h i hi'
  rw [← (hr i hi').2, getD_of_lt hi, e, notC_eq, Nat.beq_refl] at h2
  exact absurd h2 (by decide)

theorem contains_of {O : Array (List ℕ)} {R : ℕ → ℕ} {o n : ℕ} (hO : O.size = n)
    (hr : ∀ t < n, canon6 (O.getD t []) = true ∧ pk (O.getD t []) = recX R o t) {c : List ℕ}
    (hc : canon6 c = true) (h : anyNC n (fun t => Nat.beq (recX R o t) (pk c)) = true) :
    O.contains c = true := by
  obtain ⟨i, hi, e⟩ := (anyNC_iff _ _).1 h
  rw [Nat.beq_eq, ← (hr i hi).2] at e
  have e2 := pk_inj (hr i hi).1 hc e
  have hi' : i < O.size := by omega
  rw [Array.contains_iff_mem, Array.mem_iff_getElem]
  exact ⟨i, hi', by rw [← getD_of_lt hi', e2]⟩

theorem forall_mem_getD {L : List (List ℕ)} {f : List ℕ → Bool} :
    (∀ x ∈ L, f x = true) ↔ ∀ s < L.length, f (L.getD s []) = true := by
  constructor
  · intro h s hs
    rw [List.getD_eq_getElem _ _ hs]
    exact h _ (List.getElem_mem hs)
  · intro h x hx
    obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hx
    have := h s hs
    rwa [List.getD_eq_getElem _ _ hs] at this

theorem gensS : ∀ s < 5, canon6 ((sylowP.map Prod.fst).getD s []) = true ∧
    pk ((sylowP.map Prod.fst).getD s []) = at2 CFSG.KD.Sp6Two.REC 16 s := by
  decide +kernel

theorem sylT : closureOK (sylowP.map Prod.fst) sylowT 512 = true ∧
    ∀ t < 512, canon6 (sylowT.getD t []) = true ∧
      pk (sylowT.getD t []) = recX CFSG.KD.Sp6Two.REC 34728 t :=
  closureKG_ok rfl (by decide) (by decide) (by decide) gensS CFSG.KD.Sp6Two.tabS_ok (by decide)
    (by decide) (by decide)

theorem hInv_c : canon6 hInv = true := by decide +kernel

theorem hCode_c : canon6 hCode = true := by decide +kernel

theorem t0p : canon6 t0pC = true ∧ pk t0pC = T0P := by
  have h := mulE (mulE ⟨hInv_c, rfl⟩ CFSG.KD.Sp6Two.t8151_ok.1) ⟨hCode_c, rfl⟩
  exact ⟨h.1, h.2⟩

theorem sq_one {c : List ℕ} {X : ℕ} (hc : canon6 c = true ∧ pk c = X) :
    (mul6 c c == one6) = Nat.beq (MULF X X) ONE := by
  rw [beq_pk (mulE hc hc).1 canon6_one6, (mulE hc hc).2, pk_one6]

theorem eq_one {c : List ℕ} {X : ℕ} (hc : canon6 c = true ∧ pk c = X) :
    (c == one6) = Nat.beq X ONE := by
  rw [beq_pk hc.1 canon6_one6, hc.2, pk_one6]

theorem comm_pk {a b : List ℕ} {A B : ℕ} (ha : canon6 a = true ∧ pk a = A)
    (hb : canon6 b = true ∧ pk b = B) : commutes6 a b = Nat.beq (MULF A B) (MULF B A) := by
  unfold commutes6
  rw [beq_pk (mulE ha hb).1 (mulE hb ha).1, (mulE ha hb).2, (mulE hb ha).2]

theorem pairs_part : pairsChk899111 = true := by
  unfold pairsChk899111
  exact all_pairs (by decide +kernel)

theorem wit_part : witChk899111 = true := by decide +kernel

theorem c7_part : c7Chk899111 = true := by
  have hC := CFSG.KD.Sp6A2.c7_799751
  have hsz := CFSG.KD.Sp6Two.size_of_closureOK hC.1
  have o0 := CFSG.KD.Sp6Two.orb0_8151
  have h := ch899111_c7
  unfold c7Chk899111
  refine arr_all hsz fun t ht => ?_
  have hx := hC.2 t ht
  have ht' := (allNC_iff _ _).1 h t ht
  rw [letC_eq, orC_eq, orC_eq, notC_eq] at ht'
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at ht'
  rw [sq_one hx, eq_one hx]
  rcases ht' with h1 | h1 | h1
  · simp [h1]
  · simp [h1]
  · rw [not_contains o0.2.1 o0.2.2 (by rw [hx.2]; exact h1)]
    simp

theorem syl_part : sylChk899111 = true := by
  have hsz := CFSG.KD.Sp6Two.size_of_closureOK sylT.1
  have o0 := CFSG.KD.Sp6Two.orb0_8151
  have h := ch899111_syl
  unfold sylK at h
  rw [letC_eq, andC_eq, andC_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨hA, hB, hC⟩ := h
  have hlen : (sylowP.map Prod.fst).length = 5 := rfl
  have gall : ∀ {f : List ℕ → Bool}, (sylowP.all fun p => f p.1) =
      (sylowP.map Prod.fst).all f := by
    intro f
    rw [List.all_map]
    rfl
  have commAll : ∀ {y : List ℕ} {Y : ℕ}, canon6 y = true ∧ pk y = Y →
      (sylowP.all fun p => commutes6 y p.1) = commG (at2 CFSG.KD.Sp6Two.REC 16) 5 Y := by
    intro y Y hy
    refine (gall (f := fun x => commutes6 y x)).trans ?_
    apply Bool.eq_iff_iff.2
    rw [List.all_eq_true, forall_mem_getD, hlen, commG, allNC_iff]
    refine forall_congr' fun s => forall_congr' fun hs => ?_
    rw [comm_pk hy (gensS s hs)]
  unfold sylChk899111
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, contains_of hsz sylT.2 t0p.1 (by rw [t0p.2]; exact hB)⟩, ?_⟩
  · refine (gall (f := fun x => commutes6 x t0pC)).trans ?_
    rw [List.all_eq_true, forall_mem_getD, hlen]
    intro s hs
    rw [comm_pk (gensS s hs) t0p]
    exact (allNC_iff _ _).1 hA s hs
  · refine arr_all hsz fun t ht => ?_
    have hx := sylT.2 t ht
    have ht' := (allNC_iff _ _).1 hC t ht
    rw [letC_eq, orC_eq, orC_eq, orC_eq, orC_eq, notC_eq, notC_eq] at ht'
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at ht'
    rw [commAll hx, sq_one hx, eq_one hx, beq_pk hx.1 t0p.1, hx.2, t0p.2]
    rcases ht' with h1 | h1 | h1 | h1 | h1
    · simp [h1]
    · simp [h1]
    · simp [h1]
    · rw [not_contains o0.2.1 o0.2.2 (by rw [hx.2]; exact h1)]
      simp
    · simp [h1]

theorem facts : pairsChk899111 = true ∧ c7Chk899111 = true ∧ witChk899111 = true ∧
    sylChk899111 = true :=
  ⟨pairs_part, c7_part, wit_part, syl_part⟩

end CFSG.KD.Sp6Cls

end
