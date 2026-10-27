module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsWeyl

public section

namespace CertificateChecks.KernelWeylHyp

open CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3.Native

@[expose] def dotM (b : List ℕ) : List ℕ → ℕ :=
  @List.rec ℕ (fun _ => List ℕ → ℕ) (fun _ => 0)
    (fun x _ ih r => @List.rec ℕ (fun _ => ℕ) 0
      (fun y ys _ => Nat.add (Nat.mul x y) (ih ys)) r) b

@[expose] def codeL : List ℤ → ℕ
  | [] => 0
  | x :: xs => x.toNat + 1 + 4 * codeL xs

@[expose] def codeK (kb : List (List ℕ)) (r : List ℕ) : ℕ :=
  @List.rec (List ℕ) (fun _ => ℕ) 0
    (fun b _ ih => Nat.add (Nat.add (Nat.mod (dotM b r) 3) 1) (Nat.mul 4 ih)) kb

@[expose] def mod3 (v : List ℤ) : List ℕ := v.map fun x => (x % 3).toNat

@[expose] def candN (FR : List (List ℤ × ℤ × ℕ)) (c : ℕ) (ne : ℤ) : List (List ℤ) :=
  (FR.filter fun p => p.2.1 == ne && p.2.2 == c).map Prod.fst

@[expose] def kerN (FR : List (List ℤ × ℤ × ℕ)) (c : ℕ) : List (List ℤ) :=
  (FR.filter fun p => p.2.2 == c).map Prod.fst

@[expose] def tuplesG (B : List (List ℤ)) (E : List (List ℤ)) (C : ℕ → List (List ℤ)) :
    List (List (List ℤ)) :=
  (List.range E.length).foldl (fun acc i => acc.flatMap fun t =>
    ((C i).filter fun β =>
      (List.range i).all fun j =>
        formB B (t.getD j []) β == formB B (E.getD j []) (E.getD i [])).map
          fun β => t ++ [β]) [[]]

@[expose] def famG (B : List (List ℤ)) (E : List (List ℤ)) (T : List (List (List ℤ)))
    (K : List (List ℤ)) : Bool :=
  match K with
  | [] => T.all (· == E)
  | [α, β] => β == α.map (- ·) && T.all fun t => t == E || t == E.map (reflB B α)
  | _ => false

@[expose] def famOKN (B : List (List ℤ)) (RM : List (List ℤ × ℤ × List ℕ)) (E : List (List ℤ))
    (EM : List (List ℕ)) (NE : List ℤ) (kb : List (List ℕ)) : Bool :=
  let FR := RM.map fun p => (p.1, p.2.1, codeK kb p.2.2)
  let FC := EM.map (codeK kb)
  famG B E (tuplesG B E fun i => candN FR (FC.getD i 0) (NE.getD i 0))
    (kerN FR (codeL (kb.map fun _ => 0)))

theorem dotM_modEq : ∀ (b : List ℕ) (v : List ℤ), ((dotM b (mod3 v) : ℕ) : ℤ) ≡ dotN b v [ZMOD 3]
  | [], _ => by simp [dotM, dotN, Int.ModEq]
  | _ :: _, [] => by simp [dotM, dotN, mod3, Int.ModEq]
  | x :: xs, y :: ys => by
    have ih := dotM_modEq xs ys
    have h1 : dotM (x :: xs) (mod3 (y :: ys)) = x * (y % 3).toNat + dotM xs (mod3 ys) := rfl
    have h2 : dotN (x :: xs) (y :: ys) = x * y + dotN xs ys := by simp [dotN]
    have hy : (((y % 3).toNat : ℕ) : ℤ) = y % 3 :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
    rw [h1, h2, Nat.cast_add, Nat.cast_mul, hy]
    exact (Int.ModEq.mul_left _ (Int.mod_modEq y 3)).add ih

theorem codeK_eq (v : List ℤ) : ∀ kb : List (List ℕ), codeK kb (mod3 v) = codeL (fibL kb v)
  | [] => rfl
  | b :: kb => by
    have h1 : codeK (b :: kb) (mod3 v) = dotM b (mod3 v) % 3 + 1 + 4 * codeK kb (mod3 v) := rfl
    have h2 : codeL (fibL (b :: kb) v) = (dotN b v % 3).toNat + 1 + 4 * codeL (fibL kb v) := rfl
    have hm : ((dotM b (mod3 v) : ℕ) : ℤ) % 3 = dotN b v % 3 := dotM_modEq b v
    have hd := Int.toNat_of_nonneg (Int.emod_nonneg (dotN b v) (b := 3) (by decide))
    rw [h1, h2, codeK_eq v kb]
    omega

theorem codeL_inj : ∀ (l m : List ℤ), (∀ x ∈ l, 0 ≤ x ∧ x < 3) → (∀ x ∈ m, 0 ≤ x ∧ x < 3) →
    codeL l = codeL m → l = m
  | [], [], _, _, _ => rfl
  | [], y :: ys, _, _, h => by
    simp only [codeL] at h
    omega
  | x :: xs, [], _, _, h => by
    simp only [codeL] at h
    omega
  | x :: xs, y :: ys, hl, hm, h => by
    have hx := hl x List.mem_cons_self
    have hy := hm y List.mem_cons_self
    have hx' := Int.toNat_of_nonneg hx.1
    have hy' := Int.toNat_of_nonneg hy.1
    simp only [codeL] at h
    have hxy : x = y := by omega
    have hc : codeL xs = codeL ys := by omega
    rw [hxy, codeL_inj xs ys (fun z hz => hl z (List.mem_cons_of_mem _ hz))
      (fun z hz => hm z (List.mem_cons_of_mem _ hz)) hc]

theorem codeL_beq (l m : List ℤ) (hl : ∀ x ∈ l, 0 ≤ x ∧ x < 3) (hm : ∀ x ∈ m, 0 ≤ x ∧ x < 3) :
    (codeL l == codeL m) = (l == m) := by
  by_cases h : l = m
  · simp [h]
  · have hc : codeL l ≠ codeL m := fun e => h (codeL_inj l m hl hm e)
    simp [h, hc]

theorem fibL_range (kb : List (List ℕ)) (v : List ℤ) : ∀ x ∈ fibL kb v, 0 ≤ x ∧ x < 3 := by
  intro x hx
  simp only [fibL, List.mem_map] at hx
  obtain ⟨b, -, rfl⟩ := hx
  exact ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩

theorem getD_fib_range (kb : List (List ℕ)) :
    ∀ (E : List (List ℤ)) (i : ℕ), ∀ x ∈ (E.map (fibL kb)).getD i [], 0 ≤ x ∧ x < 3
  | [], _ => by simp
  | e :: _, 0 => by
    rw [List.map_cons, List.getD_cons_zero]
    exact fibL_range kb e
  | _ :: es, i + 1 => by
    rw [List.map_cons, List.getD_cons_succ]
    exact getD_fib_range kb es i

theorem getD_codeK (kb : List (List ℕ)) : ∀ (E : List (List ℤ)) (i : ℕ),
    ((E.map mod3).map (codeK kb)).getD i 0 = codeL ((E.map (fibL kb)).getD i [])
  | [], _ => by simp [codeL]
  | e :: _, 0 => by
    rw [List.map_cons, List.map_cons, List.map_cons, List.getD_cons_zero, List.getD_cons_zero]
    exact codeK_eq e kb
  | _ :: es, i + 1 => by
    rw [List.map_cons, List.map_cons, List.map_cons, List.getD_cons_succ, List.getD_cons_succ]
    exact getD_codeK kb es i

theorem map_codeK (RN : List (List ℤ × ℤ)) (kb : List (List ℕ)) :
    ((RN.map fun p => (p.1, p.2, mod3 p.1)).map fun p => (p.1, p.2.1, codeK kb p.2.2)) =
      (fibRoots RN kb).map fun p => (p.1, p.2.1, codeL p.2.2) := by
  simp only [fibRoots, List.map_map]
  apply List.map_congr_left
  intro p _
  simp [codeK_eq]

theorem candN_eq (FR : List (List ℤ × ℤ × List ℤ)) (hFR : ∀ p ∈ FR, ∀ x ∈ p.2.2, 0 ≤ x ∧ x < 3)
    (fe : List ℤ) (hfe : ∀ x ∈ fe, 0 ≤ x ∧ x < 3) (ne : ℤ) :
    candN (FR.map fun p => (p.1, p.2.1, codeL p.2.2)) (codeL fe) ne = candL FR fe ne := by
  rw [candN, candL, List.filter_map, List.map_map]
  congr 1
  apply List.filter_congr
  intro p hp
  simp only [Function.comp_apply]
  rw [codeL_beq _ _ (hFR p hp) hfe]

theorem kerN_eq (FR : List (List ℤ × ℤ × List ℤ)) (hFR : ∀ p ∈ FR, ∀ x ∈ p.2.2, 0 ≤ x ∧ x < 3)
    (z : List ℤ) (hz : ∀ x ∈ z, 0 ≤ x ∧ x < 3) :
    kerN (FR.map fun p => (p.1, p.2.1, codeL p.2.2)) (codeL z) = kerRootsL FR z := by
  rw [kerN, kerRootsL, List.filter_map, List.map_map]
  congr 1
  apply List.filter_congr
  intro p hp
  simp only [Function.comp_apply]
  rw [codeL_beq _ _ (hFR p hp) hz]

theorem fibRoots_range (RN : List (List ℤ × ℤ)) (kb : List (List ℕ)) :
    ∀ p ∈ fibRoots RN kb, ∀ x ∈ p.2.2, 0 ≤ x ∧ x < 3 := by
  intro p hp
  simp only [fibRoots, List.mem_map] at hp
  obtain ⟨q, -, rfl⟩ := hp
  exact fibL_range kb q.1

theorem famOKN_eq (B : List (List ℤ)) (RN : List (List ℤ × ℤ)) (E : List (List ℤ))
    (NE : List ℤ) (kb : List (List ℕ)) :
    famOKN B (RN.map fun p => (p.1, p.2, mod3 p.1)) E (E.map mod3) NE kb = famOK B RN E NE kb := by
  have hF : famOK B RN E NE kb = famG B E
      (tuplesG B E fun i => candL (fibRoots RN kb) ((E.map (fibL kb)).getD i []) (NE.getD i 0))
      (kerRootsL (fibRoots RN kb) (kb.map fun _ => 0)) := rfl
  have hz : ∀ x ∈ kb.map (fun _ => (0 : ℤ)), 0 ≤ x ∧ x < 3 := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨_, -, rfl⟩ := hx
    decide
  rw [hF, famOKN, map_codeK, kerN_eq _ (fibRoots_range RN kb) _ hz]
  congr 1
  congr 1
  funext i
  rw [getD_codeK, candN_eq _ (fibRoots_range RN kb) _ (getD_fib_range kb E i)]

end CertificateChecks.KernelWeylHyp

end
