
module

public import Certificates.Kernel.HS589206.E16Tabs
public import Certificates.Kernel.HS589206.E16Pair
public import Certificates.Kernel.HS589206.E16QuadA
public import Certificates.Kernel.HS589206.E16QuadB
public import Certificates.Kernel.HS589206.E16QuadC
public import Certificates.Kernel.HS589206.E16QuadD
public import Certificates.Kernel.HS589206.E16Sub
public import CFSG.Certificates.Kernel.HS589206E16Sound
public import CFSG.Certificates.Kernel.HS589206E16BSound
public import CFSG.Quasithin.H13.HSLocInv

set_option maxRecDepth 100000

public section

namespace CFSG.KD.HS589206.E16Fix

open CFSG.KC.DcHSOutK CFSG.KC.E64F CFSG.KC.DcK CFSG.KC.HS589206E16 CFSG.KD.HS589206.E16
  CFSG.KD.HS589207 CFSG.KD.HS589207.Tabs CFSG.KD.HS589206.E16Tabs CFSG.Quasithin.H13.LocDbl.HSLoc
  CFSG.Quasithin.H13.LocDbl.DcNative CFSG.Quasithin.H13.LocDbl.Dc
open CFSG.QuasithinUnique.K1.SporadicPerm hiding img keyNat

theorem elemK_row' {G : Nat → Nat → Nat} {m : Nat} {E : EnumK} {k : Nat}
    (h : elemK 100 B100 G m E k = true) :
    (k = 0 → E.row 0 = B100) ∧
      (k ≠ 0 → E.par k < k ∧ E.lab k < m ∧ E.row k = (E.row (E.par k)).map (G (E.lab k))) := by
  unfold elemK at h
  by_cases hk : k = 0
  · subst hk
    simp only [beq_self_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at h
    simp only [and_assoc] at h
    exact ⟨fun _ => h.1, fun h0 => absurd rfl h0⟩
  · have hk' : (k == 0) = false := by simpa using hk
    simp only [hk', Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
      beq_iff_eq] at h
    simp only [and_assoc] at h
    exact ⟨fun h0 => absurd h0 hk, fun _ => ⟨h.1, h.2.1, h.2.2.1⟩⟩

theorem rec_row_getD (N : Nat) (T : Nat → Nat) (k : Nat) {q : Nat} (hq : q < 100) :
    ((recK N 100 T).row k).getD q 0 = fl (T k) q := by
  simp [recK, List.getD_eq_getElem?_getD, hq, fl]

theorem rec_facts {N m : Nat} {T : Nat → Nat} {G : Nat → Nat → Nat}
    (hG : ∀ t < m, ∀ q < 100, G t q < 100) (hN : 0 < N)
    (he : ∀ k < N, elemK 100 B100 G m (recK N 100 T) k = true) :
    (∀ q < 100, fl (T 0) q = q) ∧
      (∀ k, 0 < k → k < N → (recK N 100 T).par k < k ∧ (recK N 100 T).lab k < m ∧
        ∀ q < 100, fl (T k) q = G ((recK N 100 T).lab k) (fl (T ((recK N 100 T).par k)) q)) ∧
      ∀ k < N, ∀ q < 100, fl (T k) q < 100 := by
  have h0 : ∀ q < 100, fl (T 0) q = q := fun q hq => by
    rw [← rec_row_getD N T 0 hq, (elemK_row' (he 0 hN)).1 rfl]
    simp [B100, List.getD_eq_getElem?_getD, hq]
  have hs : ∀ k, 0 < k → k < N → (recK N 100 T).par k < k ∧ (recK N 100 T).lab k < m ∧
      ∀ q < 100, fl (T k) q = G ((recK N 100 T).lab k) (fl (T ((recK N 100 T).par k)) q) := by
    intro k hk0 hk
    obtain ⟨hp, hl, hr⟩ := (elemK_row' (he k hk)).2 (by omega)
    refine ⟨hp, hl, fun q hq => ?_⟩
    rw [← rec_row_getD N T k hq, ← rec_row_getD N T _ hq, hr]
    have hlen : q < ((recK N 100 T).row ((recK N 100 T).par k)).length := by simp [recK, hq]
    simp [List.getD_eq_getElem?_getD, hlen]
  refine ⟨h0, hs, ?_⟩
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk q hq
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [h0 q hq]; exact hq
    · obtain ⟨hp, hl, hr⟩ := hs k hk0 hk
      rw [hr q hq]
      exact hG _ hl _ (ih _ hp (by omega) q hq)

theorem GS_lt : ∀ t < 3, ∀ q < 100, GS t q < 100 := fun t ht q hq =>
  ((good_sTabs t (by rw [sTabs_size]; exact ht)).2 q hq).2

theorem GS5_lt : ∀ t < 3, ∀ q < 100, GS5 t q < 100 := fun t ht q hq =>
  ((good_s5Tabs t (by rw [s5Tabs_size]; exact ht)).2 q hq).2

theorem getD_toArray_map' (f : Nat → Nat) {N k : Nat} (hk : k < N) :
    ((List.range N).map f).toArray.getD k 0 = f k := by
  simp [Array.getD_eq_getD_getElem?, hk]

theorem good_sElems : ∀ k < 512, Good 100 (sElems.getD k #[]) (sF k) := by
  have hb : bfsEnumL 100 B100 sTabs 600 =
      (((List.range 512).map ES.par).toArray, ((List.range 512).map ES.lab).toArray) :=
    bfsEnumL_of_elemK good_sTabs (by decide) E16RecA.hd (by rw [sTabs_size]; exact sElemK)
  obtain ⟨h0, hs, hlt⟩ := rec_facts (T := SR.TF) GS_lt (N := 512) (by norm_num) sElemK
  unfold sElems
  rw [hb]
  refine enumTabs_good good_sTabs h0 (fun k hk0 hk => ?_) hlt
  obtain ⟨hp, hl, hr⟩ := hs k hk0 hk
  rw [getD_toArray_map' _ hk, getD_toArray_map' _ hk, sTabs_size]
  exact ⟨hp, hl, hr⟩

theorem good_s5Elems : ∀ k < 125, Good 100 (s5Elems.getD k #[]) (s5F k) := by
  have hb : bfsEnumL 100 B100 s5Tabs 200 =
      (((List.range 125).map ES5.par).toArray, ((List.range 125).map ES5.lab).toArray) :=
    bfsEnumL_of_elemK good_s5Tabs (by decide) E16Rec5.hd (by rw [s5Tabs_size]; exact s5ElemK)
  obtain ⟨h0, hs, hlt⟩ := rec_facts (T := S5R.TF) GS5_lt (N := 125) (by norm_num) s5ElemK
  unfold s5Elems
  rw [hb]
  refine enumTabs_good good_s5Tabs h0 (fun k hk0 hk => ?_) hlt
  obtain ⟨hp, hl, hr⟩ := hs k hk0 hk
  rw [getD_toArray_map' _ hk, getD_toArray_map' _ hk, s5Tabs_size]
  exact ⟨hp, hl, hr⟩

theorem sElems_size : sElems.size = 512 := by simp [sElems, enumTabs]

theorem s5Elems_size : s5Elems.size = 125 := by simp [s5Elems, enumTabs]

theorem sSpec' : SubSpec Sg sElems 512 :=
  subSpec_words sWords_lt enum_S

theorem s5Spec' : SubSpec S5g s5Elems 125 :=
  subSpec_words s5Words_lt enum_S5

theorem map_of_mem {X : Array (Array Nat)} {F : Nat → Nat → Nat} {N : Nat} (hX : X.size = N)
    (hg : ∀ k < N, Good 100 (X.getD k #[]) (F k)) {x : PG} (hx : T x ∈ X.toList) :
    ∃ k < N, ∀ q < 100, act 100 x q = F k q := by
  obtain ⟨k, hk, hkx⟩ := List.mem_iff_getElem.mp hx
  have hk' : k < N := by simpa [hX] using hk
  refine ⟨k, hk', fun q hq => ?_⟩
  have e : X.getD k #[] = T x := by
    rw [Array.getD_eq_getD_getElem?]
    simp only [Array.length_toList] at hk
    simp [hk, ← hkx]
  rw [← img_T, ← e]
  exact ((hg k hk').2 q hq).1

theorem map_of_mem_Sg {x : PG} (hx : x ∈ Sg) :
    ∃ k < 512, ∀ q < 100, act 100 x q = sF k q :=
  map_of_mem sElems_size good_sElems ((sSpec'.mem_iff x).mp hx)

theorem map_of_mem_S5g {x : PG} (hx : x ∈ S5g) :
    ∃ k < 125, ∀ q < 100, act 100 x q = s5F k q :=
  map_of_mem s5Elems_size good_s5Elems ((s5Spec'.mem_iff x).mp hx)

theorem wordF_eq {w : List Nat} (hw : ∀ l ∈ w, l < 4) {q : Nat}
    (hq : q < 100) : wordF A w q = act 100 (wAB ga gb w) q := by
  rw [← act_wAB ABOK_ab hw hq]
  induction w with
  | nil => rfl
  | cons l w ih =>
    have hw' : ∀ l' ∈ w, l' < 4 := fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')
    have hlt : evalW AB w q < 100 := by
      rw [act_wAB ABOK_ab hw' hq]; exact act_lt _ hq
    have e1 : wordF A (l :: w) q = A l (wordF A w q) := rfl
    have e2 : evalW AB (l :: w) q = img (AB.getD l #[]) (evalW AB w q) := rfl
    rw [e1, e2, ih hw', ← ((good_AB l (hw l List.mem_cons_self)).2 _ hlt).1]
    rfl

theorem testBit_two_pow_add_of {M a : Nat} (hM : M.testBit a = false) (i : Nat) :
    (2 ^ a + M).testBit i = (M.testBit i || decide (i = a)) := by
  rcases Nat.lt_or_ge i a with h | h
  · have e : decide (i = a) = false := decide_eq_false (by omega)
    rw [Nat.testBit_two_pow_add_gt h, e, Bool.or_false]
  · obtain ⟨j, rfl⟩ : ∃ j, i = a + j := ⟨i - a, by omega⟩
    rw [← Nat.testBit_shiftRight, ← Nat.testBit_shiftRight (x := M)]
    have e : (2 ^ a + M) >>> a = 1 + (M >>> a) := by
      rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.add_comm,
        Nat.add_div_right _ (Nat.two_pow_pos a)]
      omega
    have hc : (M >>> a) % 2 = 0 := by
      have h' : (M >>> a).testBit 0 = false := by rw [Nat.testBit_shiftRight, Nat.add_zero]; exact hM
      rw [Nat.testBit_zero] at h'
      simp only [decide_eq_false_iff_not] at h'
      omega
    rw [e]
    cases j with
    | zero =>
      rw [Nat.testBit_zero, Nat.testBit_zero]
      simp only [Nat.add_zero, decide_true, Bool.or_true, decide_eq_true_eq]
      omega
    | succ j =>
      rw [Nat.testBit_succ, Nat.testBit_succ]
      have e2 : (1 + (M >>> a)) / 2 = (M >>> a) / 2 := by omega
      rw [e2]
      simp

theorem testBit_maskS : ∀ {xs : List Nat}, xs.Nodup → ∀ i, (maskS xs).testBit i = true ↔ i ∈ xs
  | [], _, i => by simp [maskS]
  | x :: xs, hnd, i => by
    rw [List.nodup_cons] at hnd
    have ih := @testBit_maskS xs hnd.2
    have e : maskS (x :: xs) = 2 ^ x + maskS xs := by
      change 1 <<< x + maskS xs = _
      rw [Nat.one_shiftLeft]
    have hx : (maskS xs).testBit x = false := by
      rcases h : (maskS xs).testBit x with _ | _
      · rfl
      · exact absurd ((ih x).mp h) hnd.1
    rw [e, testBit_two_pow_add_of hx, Bool.or_eq_true, ih, decide_eq_true_eq, List.mem_cons]
    tauto

theorem bit_maskS {xs : List Nat} (hnd : xs.Nodup) (i : Nat) : bit (maskS xs) i = true ↔ i ∈ xs := by
  rw [bit_iff, testBit_maskS hnd]

section Prods

variable {Γ : Type} [Group Γ]

def pr : List Γ → List Γ
  | [] => [1]
  | t :: l => pr l ++ (pr l).map (t * ·)

theorem mem_pr : ∀ (l : List Γ) (H : Subgroup Γ), (∀ x ∈ l, x ∈ H) → ∀ x ∈ pr l, x ∈ H
  | [], H, _, x, hx => by
    simp only [pr, List.mem_singleton] at hx
    rw [hx]; exact H.one_mem
  | t :: l, H, hl, x, hx => by
    have hl' : ∀ x ∈ l, x ∈ H := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    simp only [pr, List.mem_append, List.mem_map] at hx
    rcases hx with hx | ⟨z, hz, rfl⟩
    · exact mem_pr l H hl' x hx
    · exact H.mul_mem (hl t List.mem_cons_self) (mem_pr l H hl' z hz)

theorem pr_length : ∀ (l : List Γ), (pr l).length = 2 ^ l.length
  | [] => by simp [pr]
  | t :: l => by simp [pr, pr_length l, pow_succ]; ring

theorem eq_pr_of_nodup [Finite Γ] {E : Subgroup Γ} (hcard : Nat.card E = 16) {l : List Γ}
    (hl : l.length = 4) (hmem : ∀ x ∈ l, x ∈ E) (hnd : (pr l).Nodup) : ∀ x ∈ E, x ∈ pr l := by
  classical
  haveI : Fintype Γ := Fintype.ofFinite Γ
  let Ef : Finset Γ := Finset.univ.filter (· ∈ E)
  have hEcard : Ef.card = 16 := by
    rw [← hcard, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsub : (pr l).toFinset ⊆ Ef := by
    intro x hx
    rw [List.mem_toFinset] at hx
    simp only [Ef, Finset.mem_filter, Finset.mem_univ, true_and]
    exact mem_pr l E hmem x hx
  have hPc : (pr l).toFinset.card = 16 := by
    rw [List.toFinset_card_of_nodup hnd, pr_length, hl]
    norm_num
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hPc, hEcard])
  intro x hx
  have : x ∈ Ef := by simp [Ef, hx]
  rw [← heq] at this
  exact List.mem_toFinset.mp this

theorem comm_of_sq {E : Subgroup Γ} (h2 : ∀ a ∈ E, a * a = 1) {a b : Γ} (ha : a ∈ E)
    (hb : b ∈ E) : a * b = b * a := by
  have ia : a⁻¹ = a := inv_eq_of_mul_eq_one_right (h2 a ha)
  have ib : b⁻¹ = b := inv_eq_of_mul_eq_one_right (h2 b hb)
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right (h2 _ (E.mul_mem ha hb))).symm
    _ = b * a := by rw [mul_inv_rev, ia, ib]

theorem pr_mul_mem {E : Subgroup Γ} (h2 : ∀ a ∈ E, a * a = 1) :
    ∀ (l : List Γ), (∀ x ∈ l, x ∈ E) → ∀ x ∈ pr l, ∀ y ∈ pr l, x * y ∈ pr l
  | [], _, x, hx, y, hy => by
    simp only [pr, List.mem_singleton] at hx hy ⊢
    rw [hx, hy, mul_one]
  | t :: l, hl, x, hx, y, hy => by
    have hl' : ∀ x ∈ l, x ∈ E := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    have ht : t ∈ E := hl t List.mem_cons_self
    have ih := pr_mul_mem h2 l hl'
    have hE := mem_pr l E hl'
    simp only [pr, List.mem_append, List.mem_map] at hx hy ⊢
    rcases hx with hx | ⟨x', hx', rfl⟩ <;> rcases hy with hy | ⟨y', hy', rfl⟩
    · exact Or.inl (ih x hx y hy)
    · refine Or.inr ⟨x * y', ih x hx y' hy', ?_⟩
      rw [← mul_assoc, ← mul_assoc, comm_of_sq h2 ht (hE x hx)]
    · exact Or.inr ⟨x' * y, ih x' hx' y hy, (mul_assoc _ _ _).symm⟩
    · left
      have e : x' * t = t * x' := comm_of_sq h2 (hE x' hx') ht
      have e2 : t * x' * (t * y') = x' * y' := by
        calc t * x' * (t * y') = t * (x' * t) * y' := by simp only [mul_assoc]
          _ = (t * t) * (x' * y') := by rw [e]; simp only [mul_assoc]
          _ = x' * y' := by rw [h2 t ht, one_mul]
      rw [e2]
      exact ih x' hx' y' hy'

theorem pr_cons_nodup {E : Subgroup Γ} (h2 : ∀ a ∈ E, a * a = 1) {t : Γ} {l : List Γ}
    (hl : ∀ x ∈ t :: l, x ∈ E) (hnd : (pr l).Nodup) (ht : t ∉ pr l) :
    (pr (t :: l)).Nodup := by
  have hl' : ∀ x ∈ l, x ∈ E := fun x hx => hl x (List.mem_cons_of_mem _ hx)
  simp only [pr]
  refine List.nodup_append.2 ⟨hnd, hnd.map (fun a b h => mul_left_cancel h), ?_⟩
  intro a ha b hb hab
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
  apply ht
  have e : t = a * y := by
    rw [hab, mul_assoc, h2 y (mem_pr l E hl' y hy), mul_one]
  rw [e]
  exact pr_mul_mem h2 l hl' a ha y hy

end Prods

theorem map_range_eq {f g : Nat → Nat} (h : (List.range 100).map f = (List.range 100).map g) :
    ∀ q < 100, f q = g q := by
  intro q hq
  have := congrArg (fun L => L.getD q 0) h
  simpa [List.getD_eq_getElem?_getD, hq] using this

theorem map_range_of {f g : Nat → Nat} (h : ∀ q < 100, f q = g q) :
    (List.range 100).map f = (List.range 100).map g :=
  List.map_congr_left fun q hq => h q (List.mem_range.1 hq)

theorem F0_lt' : ∀ f ∈ F0, f < 100 := by decide

theorem inv_index {z : PG} (hz : z ∈ Sg) (h1 : z ≠ 1) (h2 : z * z = 1) :
    ∃ i < 87, ∀ q < 100, IF i q = act 100 z q := by
  obtain ⟨k, hk, hkz⟩ := map_of_mem_Sg hz
  have hfix : ∃ q < 100, sF k q ≠ q := by
    by_contra hcon
    push Not at hcon
    exact h1 (eq_of_act fun q hq => by rw [hkz q hq, hcon q hq, act_one hq])
  obtain ⟨i, hi, hik⟩ := (invsK_spec E16Pair.invs).2.2 k hk (fun q hq => by
      rw [← hkz q hq, ← hkz _ (act_lt _ hq), ← act_mul _ _ hq, h2, act_one hq]) hfix
  refine ⟨i, hi, fun q hq => ?_⟩
  rw [hkz q hq]
  simp only [IF, hik]

theorem pair_facts {a b : Nat} (ha : a < 87) (hb : b < 87) {u v : PG}
    (hu : ∀ q < 100, IF a q = act 100 u q) (hv : ∀ q < 100, IF b q = act 100 v q)
    (huv : u ≠ v) (hc : u * v = v * u) :
    cm PT a b = true ∧ mul PT a b < 87 ∧ ∀ q < 100, IF (mul PT a b) q = act 100 (v * u) q := by
  obtain ⟨h0, hcm, h128⟩ : (pe PT a b = 0 → a = b) ∧
      (cm PT a b = true → a ≠ b ∧ mul PT a b < 87 ∧
        ∀ q < 100, IF a (IF b q) = IF (mul PT a b) q ∧ IF b (IF a q) = IF (mul PT a b) q) ∧
      (128 ≤ pe PT a b → ∃ q < 100, IF a (IF b q) ≠ IF b (IF a q)) := by
    by_cases h : a < 44
    · exact pairsK_spec E16Pair.p0 a (Nat.zero_le _) (by omega) b hb
    · exact pairsK_spec E16Pair.p1 a (by omega) (by omega) b hb
  have hab : a ≠ b := by
    rintro rfl
    exact huv (eq_of_act fun q hq => by rw [← hu q hq, ← hv q hq])
  have hlt : pe PT a b < 128 := by
    by_contra hge
    obtain ⟨q, hq, hne⟩ := h128 (by omega)
    apply hne
    rw [hv q hq, hu q hq, hu _ (act_lt _ hq), hv _ (act_lt _ hq), ← act_mul _ _ hq,
      ← act_mul _ _ hq, hc]
  have hcm' : cm PT a b = true := by
    simp only [cm, Bool.and_eq_true, Nat.blt_eq]
    exact ⟨Nat.pos_of_ne_zero fun h => hab (h0 h), hlt⟩
  obtain ⟨-, hm, hq⟩ := hcm hcm'
  refine ⟨hcm', hm, fun q hq' => ?_⟩
  rw [← (hq q hq').2, hu q hq', hv _ (act_lt _ hq'), ← act_mul _ _ hq']

theorem card_filter_E {E : Subgroup PG} [Fintype PG] [DecidablePred (· ∈ E)]
    (hcard : Nat.card E = 16) : (Finset.univ.filter fun z => z ∈ E ∧ z ≠ 1).card = 15 := by
  have e : (Finset.univ.filter fun z => z ∈ E ∧ z ≠ 1) = (Finset.univ.filter (· ∈ E)).erase 1 := by
    ext z
    simp [and_comm]
  rw [e, Finset.card_erase_of_mem (by simp [E.one_mem])]
  have : (Finset.univ.filter (· ∈ E)).card = 16 := by
    rw [← hcard, Nat.card_eq_fintype_card, Fintype.card_subtype]
  omega

theorem mask_of_le_Sg {E : Subgroup PG} (hES : E ≤ Sg) (h2 : ∀ x ∈ E, x * x = 1)
    (hcard : Nat.card E = 16) :
    ∃ t < 8, ∃ xs : List Nat, xs.Nodup ∧ MK t = maskS xs ∧ (∀ x ∈ xs, x < 87) ∧
      (∀ x ∈ xs, ∃ z ∈ E, ∀ q < 100, IF x q = act 100 z q) ∧
      ∀ z ∈ E, z ≠ 1 → ∃ x ∈ xs, ∀ q < 100, IF x q = act 100 z q := by
  classical
  haveI : Fintype PG := Fintype.ofFinite PG
  have hc : ∀ {a b : PG}, a ∈ E → b ∈ E → a * b = b * a := fun ha hb => comm_of_sq h2 ha hb
  have hι : ∀ z : PG, ∃ i, z ∈ E → z ≠ 1 → i < 87 ∧ ∀ q < 100, IF i q = act 100 z q := by
    intro z
    by_cases h : z ∈ E ∧ z ≠ 1
    · obtain ⟨i, hi, hiz⟩ := inv_index (hES h.1) h.2 (h2 z h.1)
      exact ⟨i, fun _ _ => ⟨hi, hiz⟩⟩
    · exact ⟨0, fun h1 h2' => absurd ⟨h1, h2'⟩ h⟩
  choose ι hι using hι
  have hinj : ∀ {a b : PG}, a ∈ E → a ≠ 1 → b ∈ E → b ≠ 1 → ι a = ι b → a = b := by
    intro a b ha ha1 hb hb1 h
    exact eq_of_act fun q hq => by rw [← (hι a ha ha1).2 q hq, ← (hι b hb hb1).2 q hq, h]
  set s1 : Finset PG := Finset.univ.filter fun z => z ∈ E ∧ z ≠ 1 with hs1def
  have hs1 : s1.card = 15 := card_filter_E hcard
  have hne : ∀ L : List PG, L.length ≤ 8 → (s1.filter fun z => z ∉ L).Nonempty := by
    intro L hL
    rw [← Finset.card_pos]
    have h1 := Finset.card_filter_add_card_filter_not (s := s1) (fun z => z ∈ L)
    have h2 : (s1.filter fun z => z ∈ L).card ≤ L.length :=
      (Finset.card_le_card fun z hz => List.mem_toFinset.2 (Finset.mem_filter.1 hz).2).trans
        (List.toFinset_card_le L)
    omega
  have mem1 : ∀ {z : PG}, z ∈ s1 ↔ z ∈ E ∧ z ≠ 1 := by intro z; simp [hs1def]
  have memF : ∀ {z : PG} {L : List PG}, z ∈ s1.filter (fun z => z ∉ L) ↔ (z ∈ E ∧ z ≠ 1) ∧ z ∉ L := by
    intro z L; simp [hs1def]
  obtain ⟨e1, he1, hm1⟩ := s1.exists_min_image ι (Finset.card_pos.1 (by omega))
  obtain ⟨e2, he2, hm2⟩ := (s1.filter fun z => z ∉ pr [e1]).exists_min_image ι
    (hne _ (by simp [pr]))
  obtain ⟨e3, he3, hm3⟩ := (s1.filter fun z => z ∉ pr [e2, e1]).exists_min_image ι
    (hne _ (by simp [pr]))
  obtain ⟨e4, he4, -⟩ := (s1.filter fun z => z ∉ pr [e3, e2, e1]).exists_min_image ι
    (hne _ (by simp [pr]))
  rw [mem1] at he1
  rw [memF] at he2 he3 he4
  obtain ⟨h1E, h11⟩ := he1
  obtain ⟨⟨h2E, h21⟩, h2n⟩ := he2
  obtain ⟨⟨h3E, h31⟩, h3n⟩ := he3
  obtain ⟨⟨h4E, h41⟩, h4n⟩ := he4
  have n2 : e2 ≠ 1 ∧ e2 ≠ e1 := by simp [pr] at h2n; tauto
  have n3 : e3 ≠ 1 ∧ e3 ≠ e1 ∧ e3 ≠ e2 ∧ e3 ≠ e2 * e1 := by simp [pr] at h3n; tauto
  have n4 : e4 ≠ 1 ∧ e4 ≠ e1 ∧ e4 ≠ e2 ∧ e4 ≠ e2 * e1 ∧ e4 ≠ e3 ∧ e4 ≠ e3 * e1 ∧ e4 ≠ e3 * e2 ∧
      e4 ≠ e3 * (e2 * e1) := by simp [pr] at h4n; tauto
  have o12 : ι e1 < ι e2 := lt_of_le_of_ne (hm1 e2 (mem1.2 ⟨h2E, h21⟩))
    fun h => n2.2 (hinj h2E h21 h1E h11 h.symm)
  have o23 : ι e2 < ι e3 := by
    refine lt_of_le_of_ne (hm2 e3 (memF.2 ⟨⟨h3E, h31⟩, ?_⟩)) fun h => n3.2.2.1 (hinj h3E h31 h2E h21 h.symm)
    simp [pr]; exact ⟨n3.1, n3.2.1⟩
  have o34 : ι e3 < ι e4 := by
    refine lt_of_le_of_ne (hm3 e4 (memF.2 ⟨⟨h4E, h41⟩, ?_⟩)) fun h => n4.2.2.2.2.1 (hinj h4E h41 h3E h31 h.symm)
    simp [pr]; exact ⟨n4.1, n4.2.1, n4.2.2.1, n4.2.2.2.1⟩
  have hl4 : ∀ x ∈ [e4, e3, e2, e1], x ∈ E := by
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have nd1 : (pr [e1]).Nodup :=
    pr_cons_nodup h2 (fun x hx => hl4 x (by simp at hx ⊢; tauto)) (by simp [pr])
      (by simp [pr]; exact h11)
  have nd2 : (pr [e2, e1]).Nodup :=
    pr_cons_nodup h2 (fun x hx => hl4 x (by simp at hx ⊢; tauto)) nd1 h2n
  have nd3 : (pr [e3, e2, e1]).Nodup :=
    pr_cons_nodup h2 (fun x hx => hl4 x (by simp at hx ⊢; tauto)) nd2 h3n
  have nd4 : (pr [e4, e3, e2, e1]).Nodup := pr_cons_nodup h2 hl4 nd3 h4n
  have hspan := eq_pr_of_nodup hcard rfl hl4 nd4
  obtain ⟨hi, hie⟩ := hι e1 h1E h11
  obtain ⟨hj, hje⟩ := hι e2 h2E h21
  obtain ⟨hk, hke⟩ := hι e3 h3E h31
  obtain ⟨hl, hle⟩ := hι e4 h4E h41
  have hE21 := E.mul_mem h2E h1E
  have hE31 := E.mul_mem h3E h1E
  have hE32 := E.mul_mem h3E h2E
  have hE321 := E.mul_mem h3E hE21
  obtain ⟨c12, m12, f12⟩ := pair_facts hi hj hie hje (Ne.symm n2.2) (hc h1E h2E)
  obtain ⟨c13, m13, f13⟩ := pair_facts hi hk hie hke (Ne.symm n3.2.1) (hc h1E h3E)
  obtain ⟨c14, m14, f14⟩ := pair_facts hi hl hie hle (Ne.symm n4.2.1) (hc h1E h4E)
  obtain ⟨c23, m23, f23⟩ := pair_facts hj hk hje hke (Ne.symm n3.2.2.1) (hc h2E h3E)
  obtain ⟨c24, m24, f24⟩ := pair_facts hj hl hje hle (Ne.symm n4.2.2.1) (hc h2E h4E)
  obtain ⟨c34, m34, f34⟩ := pair_facts hk hl hke hle (Ne.symm n4.2.2.2.2.1) (hc h3E h4E)
  obtain ⟨c123, m123, f123⟩ := pair_facts m12 hk f12 hke (Ne.symm n3.2.2.2) (hc hE21 h3E)
  obtain ⟨c124, m124, f124⟩ := pair_facts m12 hl f12 hle (Ne.symm n4.2.2.2.1) (hc hE21 h4E)
  obtain ⟨c134, m134, f134⟩ := pair_facts m13 hl f13 hle (Ne.symm n4.2.2.2.2.2.1)
    (hc hE31 h4E)
  obtain ⟨c234, m234, f234⟩ := pair_facts m23 hl f23 hle (Ne.symm n4.2.2.2.2.2.2.1)
    (hc hE32 h4E)
  obtain ⟨c1234, m1234, f1234⟩ := pair_facts m123 hl f123 hle (Ne.symm n4.2.2.2.2.2.2.2)
    (hc hE321 h4E)
  set i := ι e1
  set j := ι e2
  set k := ι e3
  set l := ι e4
  set L15 : List PG := [e1, e2, e3, e4, e2 * e1, e3 * e1, e4 * e1, e3 * e2, e4 * e2, e4 * e3,
    e3 * (e2 * e1), e4 * (e2 * e1), e4 * (e3 * e1), e4 * (e3 * e2), e4 * (e3 * (e2 * e1))]
    with hL15
  have hmap : (qEl PT i j k l).map (fun x => (List.range 100).map (IF x)) =
      L15.map (fun z => (List.range 100).map (act 100 z)) := by
    simp only [qEl, hL15, List.map_cons, List.map_nil, map_range_of hie, map_range_of hje,
      map_range_of hke, map_range_of hle, map_range_of f12, map_range_of f13, map_range_of f14,
      map_range_of f23, map_range_of f24, map_range_of f34, map_range_of f123,
      map_range_of f124, map_range_of f134, map_range_of f234, map_range_of f1234]
  have hL15PL : ∀ z ∈ L15, z ∈ pr [e4, e3, e2, e1] := by
    intro z hz
    simp only [hL15, List.mem_cons, List.mem_nil_iff, or_false] at hz
    simp only [pr, List.map_cons, List.map_nil, List.cons_append, List.nil_append, mul_one]
    rcases hz with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
      simp only [List.mem_cons, true_or, or_true]
  have hL15E : ∀ z ∈ L15, z ∈ E := fun z hz => mem_pr _ E hl4 z (hL15PL z hz)
  have hspan' : ∀ z ∈ E, z ≠ 1 → z ∈ L15 := by
    intro z hz hz1
    have h := hspan z hz
    simp only [pr, List.map_cons, List.map_nil, List.cons_append, List.nil_append, mul_one,
      List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact absurd h hz1
    all_goals (subst h; simp only [hL15, List.mem_cons, true_or, or_true])
  have hL15nd : L15.Nodup := by
    have hsub : s1 ⊆ L15.toFinset := fun z hz => by
      rw [mem1] at hz
      exact List.mem_toFinset.2 (hspan' z hz.1 hz.2)
    have h1 := Finset.card_le_card hsub
    rw [hs1, List.card_toFinset] at h1
    have h2 := List.dedup_sublist L15
    have hlen : L15.length = 15 := rfl
    have h3 : L15.dedup.length = L15.length := le_antisymm h2.length_le (by omega)
    rw [← h2.eq_of_length h3]
    exact List.nodup_dedup L15
  have hinjF : Function.Injective (fun z : PG => (List.range 100).map (act 100 z)) :=
    fun a b h => eq_of_act (map_range_eq h)
  have hnd : (qEl PT i j k l).Nodup := by
    have : ((qEl PT i j k l).map (fun x => (List.range 100).map (IF x))).Nodup := by
      rw [hmap]; exact hL15nd.map hinjF
    exact List.Nodup.of_map _ this
  have hqDef : qDef PT i j k l = true := by
    simp only [qDef, c123, c124, c134, c234, c1234, Bool.and_self]
  obtain ⟨t, ht, hMK⟩ : ∃ t < 8, MK t = maskS (qEl PT i j k l) := by
    have hq : ∀ lo len, quadBlk PT MK 8 87 lo len = true → lo ≤ i → i < lo + len →
        ∃ t < 8, MK t = maskS (qEl PT i j k l) := fun lo len h h1 h2 =>
      quadBlk_spec h i j k l h1 h2 o12 o23 o34 hl c12 c13 c23 c14 c24 c34 hqDef hnd
    by_cases b1 : i < 15
    · exact hq 0 15 E16QuadA.q0 (by omega) (by omega)
    by_cases b2 : i < 30
    · exact hq 15 15 E16QuadB.q1 (by omega) (by omega)
    by_cases b3 : i < 44
    · exact hq 30 14 E16QuadC.q2 (by omega) (by omega)
    · exact hq 44 43 E16QuadD.q3 (by omega) (by omega)
  refine ⟨t, ht, qEl PT i j k l, hnd, hMK, ?_, ?_, ?_⟩
  · intro x hx
    simp only [qEl, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
      assumption
  · intro x hx
    have hm : (List.range 100).map (IF x) ∈ L15.map (fun z => (List.range 100).map (act 100 z)) := by
      rw [← hmap]; exact List.mem_map_of_mem hx
    obtain ⟨z, hz, hze⟩ := List.mem_map.mp hm
    exact ⟨z, hL15E z hz, map_range_eq hze.symm⟩
  · intro z hz hz1
    have hm : (List.range 100).map (act 100 z) ∈
        (qEl PT i j k l).map (fun x => (List.range 100).map (IF x)) := by
      rw [hmap]; exact List.mem_map_of_mem (hspan' z hz hz1)
    obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hm
    exact ⟨x, hx, map_range_eq hxe⟩

theorem act_inj {g : PG} {a b : Nat} (ha : a < 100) (hb : b < 100)
    (h : act 100 g a = act 100 g b) : a = b := by
  have := congrArg (act 100 g⁻¹) h
  rwa [← act_mul _ _ ha, ← act_mul _ _ hb, inv_mul_cancel, act_one ha, act_one hb] at this

theorem act_conj_pt (g z : PG) {q : Nat} (hq : q < 100) :
    act 100 (g * z * g⁻¹) (act 100 g q) = act 100 g (act 100 z q) := by
  have e : g * z * g⁻¹ * g = g * z := by group
  rw [← act_mul _ _ hq, e, act_mul _ _ hq]

theorem act_inv_act' (g : PG) {p : Nat} (hp : p < 100) : act 100 g⁻¹ (act 100 g p) = p := by
  rw [← act_mul _ _ hp, inv_mul_cancel, act_one hp]

theorem act_act_inv' (g : PG) {p : Nat} (hp : p < 100) : act 100 g (act 100 g⁻¹ p) = p := by
  rw [← act_mul _ _ hp, mul_inv_cancel, act_one hp]

def Blk (R : Nat → Nat) (b r : Nat) : Prop := r = R (2 * b + 1) ∨ r = R (2 * b + 2)

theorem iter5_id' : ∀ a ∈ List.range 4, ∀ b ∈ List.range 4, ∀ c ∈ List.range 4,
    ∀ d ∈ List.range 4, (∀ x ∈ List.range 4, (fun z => [a, b, c, d].getD z 0)^[5] x = x) →
      ∀ x ∈ List.range 4, [a, b, c, d].getD x 0 = x := by
  decide

theorem iter5_id : ∀ a < 4, ∀ b < 4, ∀ c < 4, ∀ d < 4,
    (∀ x < 4, (fun z => [a, b, c, d].getD z 0)^[5] x = x) → ∀ x < 4, [a, b, c, d].getD x 0 = x :=
  fun a ha b hb c hc d hd h x hx =>
    iter5_id' a (List.mem_range.2 ha) b (List.mem_range.2 hb) c (List.mem_range.2 hc) d
      (List.mem_range.2 hd) (fun x hx => h x (List.mem_range.1 hx)) x (List.mem_range.2 hx)

theorem no_bad {E : Subgroup PG} {y : PG} (hy5 : orderOf y = 5)
    (hnorm : ∀ x ∈ E, y * x * y⁻¹ ∈ E) {m : Nat} {R : Nat → Nat}
    (hB1 : ∀ x, bit m x = true → ∃ z ∈ E, ∀ q < 100, IF x q = act 100 z q)
    (hB2 : ∀ z ∈ E, z ≠ 1 → ∃ x < 87, bit m x = true ∧ ∀ q < 100, IF x q = act 100 z q)
    (hrow : eT IF A F0 87 m R = true) (h0 : R 0 ≠ 0) : False := by
  obtain ⟨hA, hB, hC⟩ := eT_bad hrow h0
  have hy5' : y ^ 5 = 1 := by rw [← hy5]; exact pow_orderOf_eq_one y
  have hpow : ∀ n : Nat, ∀ x ∈ E, y ^ n * x * (y ^ n)⁻¹ ∈ E := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      have e : y ^ (n + 1) * x * (y ^ (n + 1))⁻¹ = y * (y ^ n * x * (y ^ n)⁻¹) * y⁻¹ := by
        rw [pow_succ', mul_inv_rev]
        simp only [mul_assoc]
      rw [e]
      exact hnorm _ (ih x hx)
  have hyinv : y⁻¹ = y ^ 4 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hy5')
  have hnorm' : ∀ x ∈ E, y⁻¹ * x * y ∈ E := by
    intro x hx
    have := hpow 4 x hx
    rwa [← hyinv, inv_inv] at this
  have hPt : ∀ b < 4, R (2 * b + 1) < 100 ∧ R (2 * b + 2) < 100 := fun b hb =>
    ⟨(hB b hb).1, (hB b hb).2.1⟩
  have hBlt : ∀ {b r}, b < 4 → Blk R b r → r < 100 := by
    intro b r hb hr
    rcases hr with rfl | rfl
    exacts [(hPt b hb).1, (hPt b hb).2]
  have hG1 : ∀ b < 4, ∀ z ∈ E, Blk R b (act 100 z (R (2 * b + 1))) := by
    intro b hb z hz
    by_cases hz1 : z = 1
    · rw [hz1, act_one (hPt b hb).1]; exact Or.inl rfl
    · obtain ⟨x, hx, hbx, hxz⟩ := hB2 z hz hz1
      rw [← hxz _ (hPt b hb).1]
      exact (hB b hb).2.2.1 x hx hbx
  have hG2 : ∀ b < 4, ∃ w ∈ E, act 100 w (R (2 * b + 1)) = R (2 * b + 2) := by
    intro b hb
    obtain ⟨i, -, hbi, hii⟩ := (hB b hb).2.2.2
    obtain ⟨z, hz, hzi⟩ := hB1 i hbi
    exact ⟨z, hz, by rw [← hzi _ (hPt b hb).1]; exact hii⟩
  have hblk : ∀ b < 4, ∀ r, Blk R b r → ∀ z ∈ E, Blk R b (act 100 z r) := by
    intro b hb r hr z hz
    rcases hr with rfl | rfl
    · exact hG1 b hb z hz
    · obtain ⟨w, hw, hwe⟩ := hG2 b hb
      rw [← hwe, ← act_mul _ _ (hPt b hb).1]
      exact hG1 b hb _ (E.mul_mem hz hw)
  have hTpt : ∀ s < 8, Blk R (s / 2) (R (s + 1)) ∧ s / 2 < 4 := by
    intro s hs
    refine ⟨?_, by omega⟩
    rcases (by omega : s % 2 = 0 ∨ s % 2 = 1) with h | h
    · exact Or.inl (congrArg R (by omega))
    · exact Or.inr (congrArg R (by omega))
  have hC' : ∀ q < 100, (∃ s < 8, R (s + 1) = q) ∨ ∃ u ∈ E, ∃ v ∈ E,
      act 100 u q ≠ q ∧ act 100 v q ≠ q ∧ act 100 u q ≠ act 100 v q := by
    intro q hq
    rcases hC q hq with h | ⟨a, -, c, -, hba, hbc, h1, h2, h3⟩
    · exact Or.inl h
    · obtain ⟨u, hu, hue⟩ := hB1 a hba
      obtain ⟨v, hv, hve⟩ := hB1 c hbc
      rw [hue q hq] at h1 h3
      rw [hve q hq] at h2 h3
      exact Or.inr ⟨u, hu, v, hv, h1, h2, h3⟩
  have claim1 : ∀ b < 4, ∀ r, Blk R b r → ∃ s < 8, R (s + 1) = act 100 y r := by
    intro b hb r hr
    have hr100 := hBlt hb hr
    rcases hC' _ (act_lt y hr100) with h | ⟨u, hu, v, hv, h1, h2, h3⟩
    · exact h
    · exfalso
      have eu : act 100 u (act 100 y r) = act 100 y (act 100 (y⁻¹ * u * y) r) := by
        have e : y * (y⁻¹ * u * y) = u * y := by group
        rw [← act_mul _ _ hr100, ← act_mul _ _ hr100, e]
      have ev : act 100 v (act 100 y r) = act 100 y (act 100 (y⁻¹ * v * y) r) := by
        have e : y * (y⁻¹ * v * y) = v * y := by group
        rw [← act_mul _ _ hr100, ← act_mul _ _ hr100, e]
      have hu' := hblk b hb r hr _ (hnorm' u hu)
      have hv' := hblk b hb r hr _ (hnorm' v hv)
      have ne1 : act 100 (y⁻¹ * u * y) r ≠ r := fun h => h1 (by rw [eu, h])
      have ne2 : act 100 (y⁻¹ * v * y) r ≠ r := fun h => h2 (by rw [ev, h])
      have ne3 : act 100 (y⁻¹ * u * y) r ≠ act 100 (y⁻¹ * v * y) r :=
        fun h => h3 (by rw [eu, ev, h])
      unfold Blk at hr hu' hv'
      omega
  have claim2 : ∀ b, ∃ c, b < 4 → c < 4 ∧ ∀ r, Blk R b r → Blk R c (act 100 y r) := by
    intro b
    by_cases hb : b < 4
    · obtain ⟨s, hs, hsy⟩ := claim1 b hb _ (Or.inl rfl)
      obtain ⟨hblkS, hc4⟩ := hTpt s hs
      refine ⟨s / 2, fun _ => ⟨hc4, fun r hr => ?_⟩⟩
      rw [hsy] at hblkS
      rcases hr with rfl | rfl
      · exact hblkS
      · obtain ⟨w, hw, hwe⟩ := hG2 b hb
        rw [← hwe, ← act_conj_pt y w (hPt b hb).1]
        exact hblk _ hc4 _ hblkS _ (hnorm w hw)
    · exact ⟨0, fun h => absurd h hb⟩
  choose β hβ using claim2
  have hiter : ∀ n, ∀ b < 4, β^[n] b < 4 ∧ ∀ r, Blk R b r → Blk R (β^[n] b) (act 100 (y ^ n) r) := by
    intro n
    induction n with
    | zero => exact fun b hb => ⟨hb, fun r hr => by rw [pow_zero, act_one (hBlt hb hr)]; exact hr⟩
    | succ n ih =>
      intro b hb
      obtain ⟨h1, h2⟩ := ih b hb
      obtain ⟨h3, h4⟩ := hβ _ h1
      rw [Function.iterate_succ_apply']
      refine ⟨h3, fun r hr => ?_⟩
      rw [pow_succ', act_mul _ _ (hBlt hb hr)]
      exact h4 _ (h2 r hr)
  have h5 : ∀ b < 4, β^[5] b = b := by
    intro b hb
    obtain ⟨hc, h⟩ := hiter 5 b hb
    have h' := h _ (Or.inl rfl)
    rw [hy5', act_one (hPt b hb).1] at h'
    rcases h' with h' | h'
    · have := hA (2 * b) (by omega) (2 * β^[5] b) (by omega) h'
      omega
    · have := hA (2 * b) (by omega) (2 * β^[5] b + 1) (by omega)
        (h'.trans (congrArg R (by omega)))
      omega
  have hgβ : ∀ x < 4, [β 0, β 1, β 2, β 3].getD x 0 = β x := by
    intro x hx
    interval_cases x <;> rfl
  have hit : ∀ n, ∀ x < 4, (fun z => [β 0, β 1, β 2, β 3].getD z 0)^[n] x = β^[n] x := by
    intro n
    induction n with
    | zero => intro x _; rfl
    | succ n ih =>
      intro x hx
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih x hx,
        hgβ _ (hiter n x hx).1]
  have hβid : ∀ b < 4, β b = b := by
    intro b hb
    rw [← hgβ b hb]
    exact iter5_id _ (hβ 0 (by norm_num)).1 _ (hβ 1 (by norm_num)).1 _ (hβ 2 (by norm_num)).1 _
      (hβ 3 (by norm_num)).1 (fun x hx => by rw [hit 5 x hx]; exact h5 x hx) b hb
  have hfix : ∀ b < 4, act 100 y (R (2 * b + 1)) = R (2 * b + 1) ∧
      act 100 y (R (2 * b + 2)) = R (2 * b + 2) := by
    intro b hb
    have hP := (hPt b hb).1
    have hP' := (hPt b hb).2
    have hPP : R (2 * b + 1) ≠ R (2 * b + 2) := fun h => by
      have := hA (2 * b) (by omega) (2 * b + 1) (by omega) (h.trans (congrArg R (by omega)))
      omega
    have hyP : Blk R b (act 100 y (R (2 * b + 1))) := by
      have := (hβ b hb).2 _ (Or.inl rfl)
      rwa [hβid b hb] at this
    have hyP' : Blk R b (act 100 y (R (2 * b + 2))) := by
      have := (hβ b hb).2 _ (Or.inr rfl)
      rwa [hβid b hb] at this
    have e5 : ∀ x < 100, act 100 (y ^ 5) x =
        act 100 y (act 100 y (act 100 y (act 100 y (act 100 y x)))) := by
      intro x hx
      have e : y ^ 5 = y * (y * (y * (y * y))) := by
        rw [pow_succ', pow_succ', pow_succ', pow_succ', pow_one]
      rw [e, act_mul _ _ hx, act_mul _ _ hx, act_mul _ _ hx, act_mul _ _ hx]
    rcases hyP with h | h
    · refine ⟨h, ?_⟩
      rcases hyP' with h' | h'
      · exact absurd (act_inj hP' hP (h'.trans h.symm)) hPP.symm
      · exact h'
    · exfalso
      rcases hyP' with h' | h'
      · have := e5 _ hP
        rw [hy5', act_one hP, h, h', h, h', h] at this
        exact hPP this
      · exact hPP (act_inj hP hP' (h.trans h'.symm))
  have hR100 : ∀ s < 8, R (s + 1) < 100 := fun s hs => hBlt (hTpt s hs).2 (hTpt s hs).1
  have hfix8 : ∀ s < 8, act 100 y (R (s + 1)) = R (s + 1) := by
    intro s hs
    have hb : s / 2 < 4 := by omega
    rcases (hTpt s hs).1 with h | h <;> rw [h]
    exacts [(hfix _ hb).1, (hfix _ hb).2]
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨h, hh⟩ := exists_conj_mem_sylow (by rw [s5Spec'.card, factorization_PG_five]; norm_num) hy5
  obtain ⟨k, hk, hkm⟩ := map_of_mem_S5g hh
  have hQfix : ∀ s < 8, s5F k (act 100 h⁻¹ (R (s + 1))) = act 100 h⁻¹ (R (s + 1)) := by
    intro s hs
    have e : h⁻¹ * y * h = h⁻¹ * y * h⁻¹⁻¹ := by rw [inv_inv]
    rw [← hkm _ (act_lt _ (hR100 s hs)), e, act_conj_pt _ _ (hR100 s hs), hfix8 s hs]
  rcases fix5K_spec E16Sub.fix5 k hk with hid | hcnt
  · have hy51 : h⁻¹ * y * h = 1 :=
      eq_of_act fun q hq => by rw [hkm q hq, hid q hq, act_one hq]
    have hy1 : y = 1 := by
      have e : y = h * (h⁻¹ * y * h) * h⁻¹ := by group
      rw [e, hy51]
      group
    rw [hy1, orderOf_one] at hy5
    omega
  · have hnd8 : ((List.range 8).map fun s => act 100 h⁻¹ (R (s + 1))).Nodup := by
      refine List.Nodup.map_on (fun a ha b hb hab => ?_) List.nodup_range
      have ha' := List.mem_range.1 ha
      have hb' := List.mem_range.1 hb
      exact hA a ha' b hb' (act_inj (hR100 a ha') (hR100 b hb') hab)
    have hsub : ((List.range 8).map fun s => act 100 h⁻¹ (R (s + 1))) ⊆
        (List.range 100).filter fun q => s5F k q == q := by
      intro x hx
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
      have hs' := List.mem_range.1 hs
      rw [List.mem_filter]
      exact ⟨List.mem_range.2 (act_lt _ (hR100 s hs')), by rw [hQfix s hs']; exact beq_self_eq_true _⟩
    have := (hnd8.subperm hsub).length_le
    rw [List.length_map, List.length_range] at this
    omega

theorem fix_of_le_Sg {E : Subgroup PG} (hES : E ≤ Sg) (h2 : ∀ x ∈ E, x * x = 1)
    (hcard : Nat.card E = 16) {y : PG} (hy5 : orderOf y = 5) (hnorm : ∀ x ∈ E, y * x * y⁻¹ ∈ E) :
    ∃ X : PG, ∀ q < 100, (∀ z ∈ E, act 100 z q = q) ↔ q ∈ F0.map (act 100 X) := by
  obtain ⟨t, ht, xs, hnd, hMK, hlt, hR1, hR2⟩ := mask_of_le_Sg hES h2 hcard
  have hrow : eT IF A F0 87 (maskS xs) (eR t) = true := by
    have := CFSG.KS.allN_spec E16Sub.subs t ht
    rwa [hMK] at this
  have hB1 : ∀ x, bit (maskS xs) x = true → ∃ z ∈ E, ∀ q < 100, IF x q = act 100 z q :=
    fun x hx => hR1 x ((bit_maskS hnd x).1 hx)
  have hB2 : ∀ z ∈ E, z ≠ 1 →
      ∃ x < 87, bit (maskS xs) x = true ∧ ∀ q < 100, IF x q = act 100 z q := by
    intro z hz hz1
    obtain ⟨x, hx, hxz⟩ := hR2 z hz hz1
    exact ⟨x, hlt x hx, (bit_maskS hnd x).2 hx, hxz⟩
  by_cases h0 : eR t 0 = 0
  · obtain ⟨hw, hfix⟩ := eT_good hrow h0
    refine ⟨wAB ga gb (wdR (eR t)), fun q hq => ?_⟩
    have e : F0.map (wordF A (wdR (eR t))) = F0.map (act 100 (wAB ga gb (wdR (eR t)))) :=
      List.map_congr_left fun f hf => wordF_eq hw (F0_lt' f hf)
    rw [← e, ← hfix q hq]
    constructor
    · intro hz i _ hbi
      obtain ⟨z, hz', hzi⟩ := hB1 i hbi
      rw [hzi q hq]
      exact hz z hz'
    · intro hm z hz
      by_cases hz1 : z = 1
      · rw [hz1]; exact act_one hq
      · obtain ⟨x, hx, hbx, hxz⟩ := hB2 z hz hz1
        rw [← hxz q hq]
        exact hm x hx hbx
  · exact (no_bad hy5 hnorm hB1 hB2 hrow h0).elim

theorem exists_conj_le {G : Type*} [Group G] [Finite G] {Q : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hQ : Nat.card Q = p ^ (Nat.card G).factorization p) {E : Subgroup G} (hE : IsPGroup p E) :
    ∃ g : G, E.map (MulAut.conj g).toMonoidHom ≤ Q := by
  let S₀ : Sylow p G := Sylow.ofCard Q hQ
  have hS₀ : (S₀ : Subgroup G) = Q := Sylow.coe_ofCard _ _
  obtain ⟨S, hS⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S S₀
  refine ⟨g, fun x hx => ?_⟩
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hx
  rw [← hS₀, ← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simpa [MulAut.smul_def, ← map_inv, MulAut.conj_apply, mul_assoc] using hS hz

theorem fix_PG {E : Subgroup PG} (h2 : ∀ x ∈ E, x * x = 1) (hcard : Nat.card E = 16) {y : PG}
    (hy5 : orderOf y = 5) (hnorm : ∀ x ∈ E, y * x * y⁻¹ ∈ E) :
    ∃ X : PG, ∀ q < 100, (∀ z ∈ E, act 100 z q = q) ↔ q ∈ F0.map (act 100 X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 E := IsPGroup.of_card (n := 4) (by rw [hcard]; norm_num)
  obtain ⟨g, hg⟩ := exists_conj_le (by rw [sSpec'.card, factorization_PG_two]; norm_num) hp
  set E' := E.map (MulAut.conj g).toMonoidHom with hE'
  have hmem : ∀ z ∈ E, g * z * g⁻¹ ∈ E' := fun z hz =>
    Subgroup.mem_map.2 ⟨z, hz, by simp [MulAut.conj_apply]⟩
  have hmem' : ∀ x ∈ E', ∃ z ∈ E, x = g * z * g⁻¹ := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hx
    exact ⟨z, hz, by simp [MulAut.conj_apply]⟩
  have h2' : ∀ x ∈ E', x * x = 1 := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hmem' x hx
    have e : g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
    rw [e, h2 z hz]
    group
  have hcard' : Nat.card E' = 16 := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hcard
  have hy5' : orderOf (g * y * g⁻¹) = 5 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hy5
  have hnorm' : ∀ x ∈ E', g * y * g⁻¹ * x * (g * y * g⁻¹)⁻¹ ∈ E' := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hmem' x hx
    have e : g * y * g⁻¹ * (g * z * g⁻¹) * (g * y * g⁻¹)⁻¹ = g * (y * z * y⁻¹) * g⁻¹ := by group
    rw [e]
    exact hmem _ (hnorm z hz)
  obtain ⟨X, hX⟩ := fix_of_le_Sg hg h2' hcard' hy5' hnorm'
  refine ⟨g⁻¹ * X, fun q hq => ?_⟩
  have hgq := act_lt g hq
  constructor
  · intro hz
    have h1 : ∀ x ∈ E', act 100 x (act 100 g q) = act 100 g q := by
      intro x hx
      obtain ⟨z, hz', rfl⟩ := hmem' x hx
      rw [act_conj_pt _ _ hq, hz z hz']
    obtain ⟨f, hf, hfe⟩ := List.mem_map.1 ((hX _ hgq).1 h1)
    refine List.mem_map.2 ⟨f, hf, ?_⟩
    rw [act_mul _ _ (F0_lt' f hf), hfe, act_inv_act' g hq]
  · intro hm z hz
    obtain ⟨f, hf, hfe⟩ := List.mem_map.1 hm
    have hfX : act 100 X f = act 100 g q := by
      rw [← hfe, act_mul _ _ (F0_lt' f hf), act_act_inv' g (act_lt _ (F0_lt' f hf))]
    have h1 := (hX _ hgq).2 (List.mem_map.2 ⟨f, hf, hfX⟩) _ (hmem z hz)
    rw [act_conj_pt _ _ hq] at h1
    exact act_inj (act_lt _ hq) hq h1

theorem e16Fix : ∀ E : Subgroup (Equiv.Perm (Fin 100)), E ≤ CFSG.RankThree.Native.hs100P →
    (∀ x ∈ E, x ^ 2 = 1) → Nat.card E = 16 → ∀ y ∈ CFSG.RankThree.Native.hs100P, orderOf y = 5 →
    (∀ x ∈ E, y * x * y⁻¹ ∈ E) → ∃ X ∈ CFSG.RankThree.Native.hs100P, ∀ q : Fin 100,
      (∀ z ∈ E, z q = q) ↔ ∃ f : Fin 100, (f : ℕ) ∈ F0 ∧ X f = q := by
  intro E hE h2 hcard y hy hy5 hnorm
  set E' : Subgroup PG := E.comap CFSG.RankThree.Native.hs100P.subtype with hE'
  have hmap : E'.map CFSG.RankThree.Native.hs100P.subtype = E :=
    Subgroup.map_comap_eq_self (by rwa [Subgroup.range_subtype])
  have h2' : ∀ x ∈ E', x * x = 1 := fun x hx =>
    Subtype.ext (by simpa [sq] using h2 _ (Subgroup.mem_comap.1 hx))
  have hcard' : Nat.card E' = 16 := by
    have : Nat.card (E'.map CFSG.RankThree.Native.hs100P.subtype) = Nat.card E' :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
    rw [hmap] at this
    rw [← this, hcard]
  have hy5' : orderOf (⟨y, hy⟩ : PG) = 5 := by
    rw [← Subgroup.orderOf_coe]
    exact hy5
  have hnorm' : ∀ x ∈ E', (⟨y, hy⟩ : PG) * x * (⟨y, hy⟩ : PG)⁻¹ ∈ E' := fun x hx =>
    Subgroup.mem_comap.2 (by simpa using hnorm _ (Subgroup.mem_comap.1 hx))
  obtain ⟨X, hX⟩ := fix_PG h2' hcard' hy5' hnorm'
  refine ⟨X, X.2, ?_⟩
  have := (fixF0_iff_perm (E := E') (X := X)).1 hX
  rwa [hmap] at this

end CFSG.KD.HS589206.E16Fix

end
