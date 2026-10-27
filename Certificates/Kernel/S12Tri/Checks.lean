module

public import CFSG.LargeExtraspecial.S12TriGData
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.AutSix
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CertificateChecks.KernelS12Tri

open Equiv Subgroup CFSG.LargeExtraspecial.S12Tri
  CFSG.HardMathSupport.Timmesfeld.Balance.Alt

variable {n : ℕ}

@[expose] def enc (x : Perm (Fin n)) : List ℕ := List.ofFn fun i => (x i : ℕ)

@[expose] def comp (l m : List ℕ) : List ℕ := m.map fun i => l.getD i 0

@[expose] def idE (n : ℕ) : List ℕ := List.ofFn fun i : Fin n => (i : ℕ)

@[expose] def sqE (l : List ℕ) : List ℕ := comp l l

theorem enc_inj : Function.Injective (enc (n := n)) := fun _ _ h =>
  Equiv.ext fun i => Fin.ext (congrFun (List.ofFn_injective h) i)

theorem enc_length (x : Perm (Fin n)) : (enc x).length = n := List.length_ofFn

theorem enc_mul (x y : Perm (Fin n)) : enc (x * y) = comp (enc x) (enc y) := by
  refine List.ext_getElem (by simp [enc_length, comp]) fun i h1 h2 => ?_
  simp only [comp, enc, List.getElem_map, List.getElem_ofFn]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp)]
  simp only [List.getElem_ofFn, Option.getD_some, Perm.coe_mul, Function.comp_apply]

theorem enc_one : enc (1 : Perm (Fin n)) = idE n := rfl

theorem enc_sq (x : Perm (Fin n)) : sqE (enc x) = enc (x ^ 2) := by
  rw [sqE, ← enc_mul, sq]

theorem enc_pow3 (x : Perm (Fin n)) : comp (sqE (enc x)) (enc x) = enc (x ^ 3) := by
  rw [enc_sq, ← enc_mul, ← pow_succ]

theorem enc_pow4 (x : Perm (Fin n)) : sqE (sqE (enc x)) = enc (x ^ 4) := by
  rw [enc_sq, enc_sq, ← pow_mul]

theorem enc_pow5 (x : Perm (Fin n)) : comp (sqE (sqE (enc x))) (enc x) = enc (x ^ 5) := by
  rw [enc_pow4, ← enc_mul, ← pow_succ]

theorem enc_eq_idE {x : Perm (Fin n)} : enc x = idE n ↔ x = 1 :=
  ⟨fun h => enc_inj (h.trans enc_one.symm), fun h => h ▸ enc_one⟩

@[expose] def gen (g₀ g₁ : Perm (Fin n)) (c : Bool) : Perm (Fin n) := if c then g₁ else g₀

@[expose] def buildD (g₀ g₁ : Perm (Fin n)) (L : List (Perm (Fin n) × ℕ)) :
    List (Bool × ℕ) → List (Perm (Fin n) × ℕ)
  | [] => L
  | (c, j) :: t =>
    buildD g₀ g₁ (L ++ [(gen g₀ g₁ c * (L.getD j (1, 0)).1, (L.getD j (1, 0)).2 + 1)]) t

@[expose] def buildE (e₀ e₁ e : List ℕ) (L : List (List ℕ)) : List (Bool × ℕ) → List (List ℕ)
  | [] => L
  | (c, j) :: t => buildE e₀ e₁ e (L ++ [comp (if c then e₁ else e₀) (L.getD j e)]) t

@[expose] def buildN (L : List ℕ) : List (Bool × ℕ) → List ℕ
  | [] => L
  | (_, j) :: t => buildN (L ++ [L.getD j 0 + 1]) t

theorem buildD_enc (g₀ g₁ : Perm (Fin n)) (s : List (Bool × ℕ)) :
    ∀ L : List (Perm (Fin n) × ℕ), (buildD g₀ g₁ L s).map (fun p => enc p.1) =
      buildE (enc g₀) (enc g₁) (idE n) (L.map fun p => enc p.1) s := by
  induction s with
  | nil => intro L; rfl
  | cons cj t ih =>
    intro L
    obtain ⟨c, j⟩ := cj
    have hd : idE n = (fun p : Perm (Fin n) × ℕ => enc p.1) (1, 0) := rfl
    have hg : enc (gen g₀ g₁ c) = if c then enc g₁ else enc g₀ := by cases c <;> rfl
    simp only [buildD, buildE]
    rw [ih, List.map_append, List.map_singleton, enc_mul, hg, hd, List.getD_map]

theorem buildD_depth (g₀ g₁ : Perm (Fin n)) (s : List (Bool × ℕ)) :
    ∀ L : List (Perm (Fin n) × ℕ), (buildD g₀ g₁ L s).map Prod.snd =
      buildN (L.map Prod.snd) s := by
  induction s with
  | nil => intro L; rfl
  | cons cj t ih =>
    intro L
    obtain ⟨c, j⟩ := cj
    simp only [buildD, buildN]
    rw [ih, List.map_append, List.map_singleton]
    change _ = buildN (L.map Prod.snd ++
      [(L.map Prod.snd).getD j (Prod.snd ((1 : Perm (Fin n)), (0 : ℕ))) + 1]) t
    rw [List.getD_map]

theorem buildD_mem (g₀ g₁ : Perm (Fin n)) (P : Perm (Fin n) → ℕ → Prop) (h1 : P 1 0)
    (hstep : ∀ c x d, P x d → P (gen g₀ g₁ c * x) (d + 1)) (s : List (Bool × ℕ)) :
    ∀ L : List (Perm (Fin n) × ℕ), (∀ p ∈ L, P p.1 p.2) → ∀ p ∈ buildD g₀ g₁ L s, P p.1 p.2 := by
  induction s with
  | nil => intro L hL; exact hL
  | cons cj t ih =>
    intro L hL
    obtain ⟨c, j⟩ := cj
    refine ih _ ?_
    intro p hp
    rw [List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact hL p hp
    · refine hstep c _ _ ?_
      by_cases hj : j < L.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
        exact hL _ (List.getElem_mem hj)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        exact h1

theorem bfs_mono (k : ℕ) : ∀ m, ∀ x ∈ bfs k, x ∈ bfs (k + m)
  | 0, x, hx => hx
  | m + 1, x, hx => by
    change x ∈ bfsStep (bfs (k + m))
    simp only [bfsStep, List.mem_dedup, List.mem_append]
    exact Or.inl (Or.inl (bfs_mono k m x hx))

theorem sign_of_mem_bfs : ∀ k, ∀ x ∈ bfs k, Perm.sign x = 1
  | 0, x, hx => by
    simp only [bfs, List.mem_singleton] at hx
    rw [hx, map_one]
  | k + 1, x, hx => by
    simp only [bfs, bfsStep, List.mem_dedup, List.mem_append, List.mem_map] at hx
    rcases hx with (hx | ⟨y, hy, rfl⟩) | ⟨y, hy, rfl⟩
    · exact sign_of_mem_bfs k x hx
    · rw [map_mul, sign_of_mem_bfs k y hy, mul_one]; decide +kernel
    · rw [map_mul, sign_of_mem_bfs k y hy, mul_one]; decide +kernel

theorem buildE6_nodup :
    (buildE (enc a6a) (enc a6b) (idE 6) [idE 6] autSixSteps).Nodup := by decide +kernel

theorem buildE6_length :
    (buildE (enc a6a) (enc a6b) (idE 6) [idE 6] autSixSteps).length = 360 := by decide +kernel

theorem buildN6_le : (buildN [0] autSixSteps).all (fun d => Nat.ble d 16) = true := by
  decide +kernel

theorem bfs16_length : (bfs 16).length = 360 := by
  have hnd : (bfs 16).Nodup := List.nodup_dedup _
  refine le_antisymm ?_ ?_
  · have hsub : ((bfs 16).toFinset : Set (Perm (Fin 6))) ⊆ alternatingGroup (Fin 6) :=
      fun x hx => Perm.mem_alternatingGroup.2 (sign_of_mem_bfs 16 x (List.mem_toFinset.1 hx))
    calc (bfs 16).length = ((bfs 16).toFinset : Set (Perm (Fin 6))).ncard := by
          rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]
      _ ≤ ((alternatingGroup (Fin 6) : Subgroup (Perm (Fin 6))) : Set (Perm (Fin 6))).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = Nat.card (alternatingGroup (Fin 6)) := (Nat.card_coe_set_eq _).symm
      _ = 360 := by rw [nat_card_alternatingGroup, Nat.card_fin]; rfl
  · set T := buildD a6a a6b [(1, 0)] autSixSteps
    have hE : T.map (fun p => enc p.1) =
        buildE (enc a6a) (enc a6b) (idE 6) [idE 6] autSixSteps := buildD_enc _ _ _ _
    have hD : T.map Prod.snd = buildN [0] autSixSteps := buildD_depth _ _ _ _
    have hmem := buildD_mem a6a a6b (fun x d => x ∈ bfs d) (by simp [bfs])
      (fun c x d hx => by
        change _ ∈ bfsStep (bfs d)
        simp only [bfsStep, List.mem_dedup, List.mem_append, List.mem_map]
        cases c
        · exact Or.inl (Or.inr ⟨x, hx, rfl⟩)
        · exact Or.inr ⟨x, hx, rfl⟩) autSixSteps [(1, 0)] (by simp [bfs])
    have hle : ∀ p ∈ T, p.2 ≤ 16 := by
      intro p hp
      have hm : p.2 ∈ T.map Prod.snd := List.mem_map_of_mem hp
      rw [hD] at hm
      exact Nat.le_of_ble_eq_true (List.all_eq_true.1 buildN6_le p.2 hm)
    have he : (T.map Prod.fst).map enc = T.map (fun p => enc p.1) := by
      rw [List.map_map]
      rfl
    have hnd' : (T.map Prod.fst).Nodup := by
      refine List.Nodup.of_map enc ?_
      rw [he, hE]
      exact buildE6_nodup
    have hlen : (T.map Prod.fst).length = 360 := by
      rw [← List.length_map (f := enc), he, hE, buildE6_length]
    have hsub : T.map Prod.fst ⊆ bfs 16 := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (hle p hp)
      exact hm ▸ bfs_mono p.2 m p.1 (hmem p hp)
    calc 360 = (T.map Prod.fst).length := hlen.symm
      _ ≤ (bfs 16).length := (List.subperm_of_subset hnd' hsub).length_le

@[expose] def evenE (n : ℕ) : Finset (List ℕ) :=
  (Finset.univ.filter fun x : Perm (Fin n) => Perm.sign x = 1).map ⟨enc, enc_inj⟩

@[expose] def pairs6 : Finset (List ℕ × List ℕ) :=
  ((evenE 6).filter (fun l => sqE l = idE 6 ∧ l ≠ idE 6) ×ˢ
      (evenE 6).filter (fun l => sqE (sqE l) = idE 6 ∧ sqE l ≠ idE 6)).filter fun q =>
    comp (sqE (sqE (comp q.1 q.2))) (comp q.1 q.2) = idE 6 ∧ comp q.1 q.2 ≠ idE 6

theorem pairs6_card : pairs6.card ≤ 1440 := by decide +kernel

theorem mem_evenE {x : Perm (Fin n)} (h : Perm.sign x = 1) : enc x ∈ evenE n :=
  Finset.mem_map.2 ⟨x, by simpa using h, rfl⟩

set_option maxRecDepth 100000 in
theorem a6Count_le : a6Count ≤ 1440 := by
  unfold a6Count
  refine le_trans (Finset.card_le_card_of_injOn (fun p => (enc p.1, enc p.2)) ?_ ?_) pairs6_card
  · intro p hp
    have h := (Finset.mem_filter.1 (Finset.mem_coe.1 hp)).2
    simp only [a6Pair, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, hx⟩, hy⟩ := h
    refine Finset.mem_coe.2 ?_
    simp only [pairs6, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨⟨mem_evenE hx, ?_, ?_⟩, mem_evenE hy, ?_, ?_⟩, ?_, ?_⟩
    · rw [enc_sq, h1, enc_one]
    · exact fun h => h2 (enc_eq_idE.1 h)
    · rw [enc_pow4, h3, enc_one]
    · exact fun h => h4 (enc_eq_idE.1 ((enc_sq _).symm.trans h))
    · rw [← enc_mul, enc_pow5, h5, enc_one]
    · exact fun h => h6 (enc_eq_idE.1 ((enc_mul _ _).trans h))
  · rintro ⟨x, y⟩ - ⟨x', y'⟩ - h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (enc_inj h.1) (enc_inj h.2)

theorem a6Pair_ab : a6Pair a6a a6b = true := by decide +kernel

theorem a6Check_true : a6Check = true := by
  simp only [a6Check, Bool.and_eq_true, beq_iff_eq, Nat.ble_eq]
  exact ⟨⟨bfs16_length, a6Pair_ab⟩, a6Count_le⟩

@[expose] def a5Steps : List (Bool × ℕ) := [
  (false, 0), (true, 0), (true, 1), (false, 2), (true, 2), (false, 3), (true, 3), (true, 4),
  (false, 5), (true, 6), (false, 7), (false, 8), (true, 8), (true, 9), (false, 10), (true, 10),
  (true, 11), (true, 12), (false, 13), (false, 14), (true, 14), (true, 15), (false, 16),
  (false, 17), (true, 17), (true, 18), (true, 19), (true, 20), (true, 22), (true, 23), (true, 24),
  (false, 26), (false, 27), (true, 27), (true, 28), (false, 29), (false, 30), (true, 30),
  (true, 31), (true, 32), (true, 33), (false, 35), (true, 36), (true, 37), (false, 39),
  (false, 40), (true, 40), (true, 41), (true, 42), (false, 43), (true, 43), (true, 44), (true, 45),
  (false, 48), (false, 49), (false, 52), (false, 53), (true, 54), (true, 56)]

theorem bfs5_mono (k : ℕ) : ∀ m, ∀ x ∈ bfs5 k, x ∈ bfs5 (k + m)
  | 0, x, hx => hx
  | m + 1, x, hx => by
    change x ∈ bfs5Step (bfs5 (k + m))
    simp only [bfs5Step, List.mem_dedup, List.mem_append]
    exact Or.inl (Or.inl (bfs5_mono k m x hx))

theorem sign_of_mem_bfs5 : ∀ k, ∀ x ∈ bfs5 k, Perm.sign x = 1
  | 0, x, hx => by
    simp only [bfs5, List.mem_singleton] at hx
    rw [hx, map_one]
  | k + 1, x, hx => by
    simp only [bfs5, bfs5Step, List.mem_dedup, List.mem_append, List.mem_map] at hx
    rcases hx with (hx | ⟨y, hy, rfl⟩) | ⟨y, hy, rfl⟩
    · exact sign_of_mem_bfs5 k x hx
    · rw [map_mul, sign_of_mem_bfs5 k y hy, mul_one]; decide +kernel
    · rw [map_mul, sign_of_mem_bfs5 k y hy, mul_one]; decide +kernel

theorem buildE5_nodup :
    (buildE (enc a5a) (enc a5b) (idE 5) [idE 5] a5Steps).Nodup := by decide +kernel

theorem buildE5_length :
    (buildE (enc a5a) (enc a5b) (idE 5) [idE 5] a5Steps).length = 60 := by decide +kernel

theorem buildN5_le : (buildN [0] a5Steps).all (fun d => Nat.ble d 12) = true := by
  decide +kernel

theorem bfs5_12_length : (bfs5 12).length = 60 := by
  have hnd : (bfs5 12).Nodup := List.nodup_dedup _
  refine le_antisymm ?_ ?_
  · have hsub : ((bfs5 12).toFinset : Set (Perm (Fin 5))) ⊆ alternatingGroup (Fin 5) :=
      fun x hx => Perm.mem_alternatingGroup.2 (sign_of_mem_bfs5 12 x (List.mem_toFinset.1 hx))
    calc (bfs5 12).length = ((bfs5 12).toFinset : Set (Perm (Fin 5))).ncard := by
          rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]
      _ ≤ ((alternatingGroup (Fin 5) : Subgroup (Perm (Fin 5))) : Set (Perm (Fin 5))).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = Nat.card (alternatingGroup (Fin 5)) := (Nat.card_coe_set_eq _).symm
      _ = 60 := by rw [nat_card_alternatingGroup, Nat.card_fin]; rfl
  · set T := buildD a5a a5b [(1, 0)] a5Steps
    have hE : T.map (fun p => enc p.1) =
        buildE (enc a5a) (enc a5b) (idE 5) [idE 5] a5Steps := buildD_enc _ _ _ _
    have hD : T.map Prod.snd = buildN [0] a5Steps := buildD_depth _ _ _ _
    have hmem := buildD_mem a5a a5b (fun x d => x ∈ bfs5 d) (by simp [bfs5])
      (fun c x d hx => by
        change _ ∈ bfs5Step (bfs5 d)
        simp only [bfs5Step, List.mem_dedup, List.mem_append, List.mem_map]
        cases c
        · exact Or.inl (Or.inr ⟨x, hx, rfl⟩)
        · exact Or.inr ⟨x, hx, rfl⟩) a5Steps [(1, 0)] (by simp [bfs5])
    have hle : ∀ p ∈ T, p.2 ≤ 12 := by
      intro p hp
      have hm : p.2 ∈ T.map Prod.snd := List.mem_map_of_mem hp
      rw [hD] at hm
      exact Nat.le_of_ble_eq_true (List.all_eq_true.1 buildN5_le p.2 hm)
    have he : (T.map Prod.fst).map enc = T.map (fun p => enc p.1) := by
      rw [List.map_map]
      rfl
    have hnd' : (T.map Prod.fst).Nodup := by
      refine List.Nodup.of_map enc ?_
      rw [he, hE]
      exact buildE5_nodup
    have hlen : (T.map Prod.fst).length = 60 := by
      rw [← List.length_map (f := enc), he, hE, buildE5_length]
    have hsub : T.map Prod.fst ⊆ bfs5 12 := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (hle p hp)
      exact hm ▸ bfs5_mono p.2 m p.1 (hmem p hp)
    calc 60 = (T.map Prod.fst).length := hlen.symm
      _ ≤ (bfs5 12).length := (List.subperm_of_subset hnd' hsub).length_le

@[expose] def pairs5 : Finset (List ℕ × List ℕ) :=
  ((evenE 5).filter (fun l => sqE l = idE 5 ∧ l ≠ idE 5) ×ˢ
      (evenE 5).filter (fun l => comp (sqE l) l = idE 5 ∧ l ≠ idE 5)).filter fun q =>
    comp (sqE (sqE (comp q.1 q.2))) (comp q.1 q.2) = idE 5 ∧ comp q.1 q.2 ≠ idE 5

theorem pairs5_card : pairs5.card ≤ 120 := by decide +kernel

set_option maxRecDepth 100000 in
theorem a5Count_le : a5Count ≤ 120 := by
  unfold a5Count
  refine le_trans (Finset.card_le_card_of_injOn (fun p => (enc p.1, enc p.2)) ?_ ?_) pairs5_card
  · intro p hp
    have h := (Finset.mem_filter.1 (Finset.mem_coe.1 hp)).2
    simp only [a5Pair, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, hx⟩, hy⟩ := h
    refine Finset.mem_coe.2 ?_
    simp only [pairs5, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨⟨mem_evenE hx, ?_, ?_⟩, mem_evenE hy, ?_, ?_⟩, ?_, ?_⟩
    · rw [enc_sq, h1, enc_one]
    · exact fun h => h2 (enc_eq_idE.1 h)
    · rw [enc_pow3, h3, enc_one]
    · exact fun h => h4 (enc_eq_idE.1 h)
    · rw [← enc_mul, enc_pow5, h5, enc_one]
    · exact fun h => h6 (enc_eq_idE.1 ((enc_mul _ _).trans h))
  · rintro ⟨x, y⟩ - ⟨x', y'⟩ - h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (enc_inj h.1) (enc_inj h.2)

theorem a5Pair_ab : a5Pair a5a a5b = true := by decide +kernel

theorem a5Check_true : a5Check = true := by
  simp only [a5Check, Bool.and_eq_true, beq_iff_eq, Nat.ble_eq]
  exact ⟨⟨bfs5_12_length, a5Pair_ab⟩, a5Count_le⟩

end CertificateChecks.KernelS12Tri

end
