module

public import CFSG.Certificates.Kernel.GL62.Theory

public section

namespace CFSG.KC.GL62

open CFSG.OddStandard.AltStdSmall4.GL62

@[expose] def memL (m : ℕ) : List ℕ := (List.range 17).filter fun p => m.testBit p

structure GL62Facts (rep : ℕ → GL (Fin 6) (ZMod 2)) (S : ℕ → ℕ) (C H : ℕ → ℕ → ℕ)
    (fams : List (ℕ × ℕ × ℕ)) : Prop where
  rep_zero : rep 0 = z₀
  cover : ∀ g : GL (Fin 6) (ZMod 2), ∃ y, (Bad y ∨ ∃ p < 17, y = rep p) ∧ g * z₀ * g⁻¹ ∈ orb y
  size : ∀ p < 17, (orb (rep p)).ncard = S p
  disj : ∀ p < 17, ∀ q < 17, p ≠ q → Disjoint (orb (rep p)) (orb (rep q))
  comm : ∀ a < 17, ∀ b < 17, {x | x ∈ orb (rep b) ∧ x * rep a = rep a * x}.ncard = C a b
  hit : ∀ a < 17, ∀ b < 17, ∀ n, (H a b).testBit n →
    (n < 17 ∧ ∃ x ∈ orb (rep b), rep a * x * (rep a)⁻¹ ∈ orb (rep n)) ∨
      (n = 17 ∧ ∃ x ∈ orb (rep b), Bad (rep a * x * (rep a)⁻¹))
  elim : ∀ m < 2 ^ 17, m.testBit 0 →
    (∀ a ∈ memL m, ∀ b ∈ memL m, H a b &&& m = H a b) →
    (∀ a ∈ memL m, ((memL m).map (C a)).sum = ((memL m).map (C 0)).sum) →
    (m, ((memL m).map S).sum) ∈ (1, 1) :: fams.map fun f => (f.1, f.2.1)
  fam : ∀ f ∈ fams, f.2.2 < 17 ∧ f.1.testBit f.2.2 ∧ ∀ b < 17, f.1.testBit b →
    ∃ e ∈ B₀ ⊔ Subgroup.zpowers (rep f.2.2), rep b = e * z₀ * e⁻¹
  fam_gen : ∀ f ∈ fams, (rep f.2.2 = gN ∧ f.2.1 = 3) ∨ (rep f.2.2 = gW ∧ f.2.1 = 168) ∨
    (rep f.2.2 = gS ∧ f.2.1 = 360) ∨ (rep f.2.2 = gG ∧ f.2.1 = 1080)

theorem ncard_union_list {G : Type*} [Finite G] (T : ℕ → Set G) (L : List ℕ) (hL : L.Nodup)
    (hd : ∀ p ∈ L, ∀ q ∈ L, p ≠ q → Disjoint (T p) (T q)) :
    {x | ∃ p ∈ L, x ∈ T p}.ncard = (L.map fun p => (T p).ncard).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have hset : {x | ∃ p ∈ a :: L, x ∈ T p} = T a ∪ {x | ∃ p ∈ L, x ∈ T p} := by
      ext x
      simp only [List.mem_cons, Set.mem_setOf_eq, Set.mem_union]
      constructor
      · rintro ⟨p, rfl | hp, hx⟩
        · exact Or.inl hx
        · exact Or.inr ⟨p, hp, hx⟩
      · rintro (hx | ⟨p, hp, hx⟩)
        · exact ⟨a, Or.inl rfl, hx⟩
        · exact ⟨p, Or.inr hp, hx⟩
    have ha := (List.nodup_cons.1 hL).1
    have hdis : Disjoint (T a) {x | ∃ p ∈ L, x ∈ T p} := by
      refine Set.disjoint_left.2 fun x hx ⟨p, hp, hxp⟩ => ?_
      exact Set.disjoint_left.1 (hd a List.mem_cons_self p (List.mem_cons_of_mem _ hp)
        (fun h => ha (h ▸ hp))) hx hxp
    rw [hset, Set.ncard_union_eq hdis, ih (List.nodup_cons.1 hL).2
      (fun p hp q hq => hd p (List.mem_cons_of_mem _ hp) q (List.mem_cons_of_mem _ hq)),
      List.map_cons, List.sum_cons]

theorem testBit_foldl_mask (P : ℕ → Prop) [DecidablePred P] (L : List ℕ) (acc n : ℕ) :
    (L.foldl (fun acc p => if P p then acc ||| 1 <<< p else acc) acc).testBit n = true ↔
      acc.testBit n = true ∨ (n ∈ L ∧ P n) := by
  induction L generalizing acc with
  | nil => simp
  | cons p L ih =>
    rw [List.foldl_cons, ih]
    by_cases hp : P p
    · rw [if_pos hp, Nat.testBit_or, Bool.or_eq_true, Nat.one_shiftLeft, Nat.testBit_two_pow,
        decide_eq_true_eq]
      constructor
      · rintro ((h | rfl) | ⟨h1, h2⟩)
        · exact Or.inl h
        · exact Or.inr ⟨List.mem_cons_self, hp⟩
        · exact Or.inr ⟨List.mem_cons_of_mem _ h1, h2⟩
      · rintro (h | ⟨h1, h2⟩)
        · exact Or.inl (Or.inl h)
        · rcases List.mem_cons.1 h1 with rfl | h1
          · exact Or.inl (Or.inr rfl)
          · exact Or.inr ⟨h1, h2⟩
    · rw [if_neg hp]
      constructor
      · rintro (h | ⟨h1, h2⟩)
        · exact Or.inl h
        · exact Or.inr ⟨List.mem_cons_of_mem _ h1, h2⟩
      · rintro (h | ⟨h1, h2⟩)
        · exact Or.inl h
        · rcases List.mem_cons.1 h1 with rfl | h1
          · exact absurd h2 hp
          · exact Or.inr ⟨h1, h2⟩

@[expose] def cls (X : Subgroup (GL (Fin 6) (ZMod 2))) : Set (GL (Fin 6) (ZMod 2)) :=
  {d | ∃ x ∈ X, d = x * z₀ * x⁻¹}

section Cls

variable {X : Subgroup (GL (Fin 6) (ZMod 2))}

theorem z0_mem_cls : z₀ ∈ cls X := ⟨1, X.one_mem, by group⟩

theorem z0_mem_B₀' : z₀ ∈ B₀ := Subgroup.mem_sup_right (Subgroup.mem_zpowers z₀)

theorem mem_of_mem_cls (hB : B₀ ≤ X) {d : GL (Fin 6) (ZMod 2)} (hd : d ∈ cls X) : d ∈ X := by
  obtain ⟨x, hx, rfl⟩ := hd
  exact X.mul_mem (X.mul_mem hx (hB z0_mem_B₀')) (X.inv_mem hx)

theorem conj_mem_cls {y d : GL (Fin 6) (ZMod 2)} (hy : y ∈ X) (hd : d ∈ cls X) :
    y * d * y⁻¹ ∈ cls X := by
  obtain ⟨x, hx, rfl⟩ := hd
  exact ⟨y * x, X.mul_mem hy hx, by group⟩

theorem mem_cls_of_conj_mem {y d : GL (Fin 6) (ZMod 2)} (hy : y ∈ X) (hd : y * d * y⁻¹ ∈ cls X) :
    d ∈ cls X := by
  have h := conj_mem_cls (X.inv_mem hy) hd
  rwa [show y⁻¹ * (y * d * y⁻¹) * y⁻¹⁻¹ = d by group] at h

theorem cls_mono {Y : Subgroup (GL (Fin 6) (ZMod 2))} (h : X ≤ Y) : cls X ⊆ cls Y := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, h hx, rfl⟩

theorem orb_subset_cls (hB : B₀ ≤ X) {y : GL (Fin 6) (ZMod 2)} (hy : y ∈ cls X) :
    orb y ⊆ cls X := by
  rintro _ ⟨c, hc, rfl⟩
  exact conj_mem_cls (hB hc) hy

theorem mem_cls_of_orb (hB : B₀ ≤ X) {y d : GL (Fin 6) (ZMod 2)} (hd : d ∈ orb y)
    (hdX : d ∈ cls X) : y ∈ cls X := by
  obtain ⟨c, hc, rfl⟩ := hd
  exact mem_cls_of_conj_mem (hB hc) hdX

theorem ncard_comm_eq {x : GL (Fin 6) (ZMod 2)} (hx : x ∈ X) :
    {d | d ∈ cls X ∧ d * (x * z₀ * x⁻¹) = x * z₀ * x⁻¹ * d}.ncard =
      {d | d ∈ cls X ∧ d * z₀ = z₀ * d}.ncard := by
  have himg : (fun d => x * d * x⁻¹) '' {d | d ∈ cls X ∧ d * z₀ = z₀ * d} =
      {d | d ∈ cls X ∧ d * (x * z₀ * x⁻¹) = x * z₀ * x⁻¹ * d} := by
    ext d
    constructor
    · rintro ⟨e, ⟨he, hez⟩, rfl⟩
      refine ⟨conj_mem_cls hx he, ?_⟩
      calc x * e * x⁻¹ * (x * z₀ * x⁻¹) = x * (e * z₀) * x⁻¹ := by group
        _ = x * (z₀ * e) * x⁻¹ := by rw [hez]
        _ = x * z₀ * x⁻¹ * (x * e * x⁻¹) := by group
    · rintro ⟨hd, hdz⟩
      refine ⟨x⁻¹ * d * x, ⟨?_, ?_⟩, by group⟩
      · simpa using conj_mem_cls (X.inv_mem hx) hd
      · calc x⁻¹ * d * x * z₀ = x⁻¹ * (d * (x * z₀ * x⁻¹)) * x := by group
          _ = x⁻¹ * (x * z₀ * x⁻¹ * d) * x := by rw [hdz]
          _ = z₀ * (x⁻¹ * d * x) := by group
  rw [← himg, Set.ncard_image_of_injective _ fun a b h => by simpa using h]

theorem card_eq_mul_ncard (hB : B₀ ≤ X) (hC : ∀ x ∈ X, x * z₀ = z₀ * x → x ∈ B₀) :
    Nat.card X = 336 * (cls X).ncard := by
  have h := ncard_conj_mul X z₀
  have hs : {c | c ∈ X ∧ c * z₀ = z₀ * c} = (B₀ : Set (GL (Fin 6) (ZMod 2))) := by
    ext c
    simp only [Set.mem_setOf_eq, SetLike.mem_coe]
    exact ⟨fun h => hC c h.1 h.2, fun h => ⟨hB h, comm_z0_of_mem_B₀ h⟩⟩
  have h3 : (B₀ : Set (GL (Fin 6) (ZMod 2))).ncard = 336 :=
    (Nat.card_coe_set_eq _).symm.trans card_B₀
  rw [hs, h3] at h
  change (cls X).ncard * 336 = Nat.card X at h
  rw [← h, mul_comm]

theorem not_bad_of_mem (hB : B₀ ≤ X) (hC : ∀ x ∈ X, x * z₀ = z₀ * x → x ∈ B₀)
    {y : GL (Fin 6) (ZMod 2)} (hy : y ∈ X) : ¬ Bad y := by
  rintro ⟨e, he, hez, heB⟩
  have hle : Subgroup.closure (insert y (B₀ : Set (GL (Fin 6) (ZMod 2)))) ≤ X :=
    (Subgroup.closure_le X).2 (Set.insert_subset hy fun b hb => hB hb)
  exact heB (hC e (hle he) hez)

end Cls

section Facts

variable {rep : ℕ → GL (Fin 6) (ZMod 2)} {S : ℕ → ℕ} {C H : ℕ → ℕ → ℕ}
  {fams : List (ℕ × ℕ × ℕ)} (F : GL62Facts rep S C H fams)
  {X : Subgroup (GL (Fin 6) (ZMod 2))}

open scoped Classical in
noncomputable def maskOf (rep : ℕ → GL (Fin 6) (ZMod 2)) (X : Subgroup (GL (Fin 6) (ZMod 2))) :
    ℕ :=
  (List.range 17).foldl (fun acc p => if rep p ∈ cls X then acc ||| 1 <<< p else acc) 0

theorem testBit_maskOf {n : ℕ} :
    (maskOf rep X).testBit n = true ↔ n < 17 ∧ rep n ∈ cls X := by
  rw [maskOf, testBit_foldl_mask, List.mem_range]
  simp

theorem maskOf_lt : maskOf rep X < 2 ^ 17 :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    by_contra h
    rw [Bool.not_eq_false] at h
    exact absurd (testBit_maskOf.1 h).1 (by omega)

theorem mem_memL_maskOf {p : ℕ} : p ∈ memL (maskOf rep X) ↔ p < 17 ∧ rep p ∈ cls X := by
  rw [memL, List.mem_filter, List.mem_range, testBit_maskOf]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

theorem nodup_memL (m : ℕ) : (memL m).Nodup := List.nodup_range.filter _

include F

theorem mem_cls_iff (hB : B₀ ≤ X) (hC : ∀ x ∈ X, x * z₀ = z₀ * x → x ∈ B₀)
    {d : GL (Fin 6) (ZMod 2)} : d ∈ cls X ↔ ∃ p ∈ memL (maskOf rep X), d ∈ orb (rep p) := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := F.cover x
    have hyX : y ∈ cls X := mem_cls_of_orb hB hxy ⟨x, hx, rfl⟩
    rcases hy with hbad | ⟨p, hp, rfl⟩
    · exact absurd hbad (not_bad_of_mem hB hC (mem_of_mem_cls hB hyX))
    · exact ⟨p, mem_memL_maskOf.2 ⟨hp, hyX⟩, hxy⟩
  · rintro ⟨p, hp, hd⟩
    exact orb_subset_cls hB (mem_memL_maskOf.1 hp).2 hd

theorem disj_memL (m : ℕ) : ∀ p ∈ memL m, ∀ q ∈ memL m, p ≠ q →
    Disjoint (orb (rep p)) (orb (rep q)) := fun p hp q hq hpq =>
  F.disj p (List.mem_range.1 (List.mem_filter.1 hp).1) q
    (List.mem_range.1 (List.mem_filter.1 hq).1) hpq

theorem ncard_cls (hB : B₀ ≤ X) (hC : ∀ x ∈ X, x * z₀ = z₀ * x → x ∈ B₀) :
    (cls X).ncard = ((memL (maskOf rep X)).map S).sum := by
  have hset : cls X = {d | ∃ p ∈ memL (maskOf rep X), d ∈ orb (rep p)} :=
    Set.ext fun d => mem_cls_iff F hB hC
  rw [hset, ncard_union_list _ _ (nodup_memL _) (disj_memL F _)]
  exact congrArg List.sum (List.map_congr_left fun p hp => F.size p (mem_memL_maskOf.1 hp).1)

theorem ncard_cls_comm (hB : B₀ ≤ X) (hC : ∀ x ∈ X, x * z₀ = z₀ * x → x ∈ B₀) {a : ℕ}
    (ha : a < 17) : {d | d ∈ cls X ∧ d * rep a = rep a * d}.ncard =
      ((memL (maskOf rep X)).map (C a)).sum := by
  have hset : {d | d ∈ cls X ∧ d * rep a = rep a * d} =
      {d | ∃ p ∈ memL (maskOf rep X), d ∈ {x | x ∈ orb (rep p) ∧ x * rep a = rep a * x}} := by
    ext d
    simp only [Set.mem_setOf_eq, mem_cls_iff F hB hC]
    constructor
    · rintro ⟨⟨p, hp, hd⟩, hc⟩
      exact ⟨p, hp, hd, hc⟩
    · rintro ⟨p, hp, hd, hc⟩
      exact ⟨⟨p, hp, hd⟩, hc⟩
  rw [hset, ncard_union_list _ _ (nodup_memL _) fun p hp q hq hpq =>
    Set.disjoint_of_subset (fun _ h => h.1) (fun _ h => h.1) (disj_memL F _ p hp q hq hpq)]
  exact congrArg List.sum (List.map_congr_left fun p hp => F.comm a ha p (mem_memL_maskOf.1 hp).1)

theorem closed_maskOf (hB : B₀ ≤ X) (hC : ∀ x ∈ X, x * z₀ = z₀ * x → x ∈ B₀) :
    ∀ a ∈ memL (maskOf rep X), ∀ b ∈ memL (maskOf rep X),
      H a b &&& maskOf rep X = H a b := by
  intro a ha b hb
  obtain ⟨ha17, haX⟩ := mem_memL_maskOf.1 ha
  obtain ⟨hb17, hbX⟩ := mem_memL_maskOf.1 hb
  apply Nat.eq_of_testBit_eq
  intro n
  rw [Nat.testBit_and]
  cases hn : (H a b).testBit n
  · rfl
  · rw [Bool.true_and]
    have hconj : ∀ x ∈ orb (rep b), rep a * x * (rep a)⁻¹ ∈ cls X := fun x hx =>
      conj_mem_cls (mem_of_mem_cls hB haX) (orb_subset_cls hB hbX hx)
    rcases F.hit a ha17 b hb17 n hn with ⟨hn17, x, hx, hxn⟩ | ⟨-, x, hx, hbad⟩
    · exact testBit_maskOf.2 ⟨hn17, mem_cls_of_orb hB hxn (hconj x hx)⟩
    · exact absurd hbad (not_bad_of_mem hB hC (mem_of_mem_cls hB (hconj x hx)))

theorem homog_maskOf (hB : B₀ ≤ X) (hC : ∀ x ∈ X, x * z₀ = z₀ * x → x ∈ B₀) :
    ∀ a ∈ memL (maskOf rep X),
      ((memL (maskOf rep X)).map (C a)).sum = ((memL (maskOf rep X)).map (C 0)).sum := by
  intro a ha
  obtain ⟨ha17, haX⟩ := mem_memL_maskOf.1 ha
  rw [← ncard_cls_comm F hB hC ha17, ← ncard_cls_comm F hB hC (by norm_num : 0 < 17), F.rep_zero]
  obtain ⟨x, hx, hxe⟩ := haX
  rw [hxe]
  exact ncard_comm_eq hx

theorem mask_mem (hB : B₀ ≤ X) (hC : ∀ x ∈ X, x * z₀ = z₀ * x → x ∈ B₀) :
    (maskOf rep X, (cls X).ncard) ∈ (1, 1) :: fams.map fun f => (f.1, f.2.1) := by
  rw [ncard_cls F hB hC]
  refine F.elim _ maskOf_lt (testBit_maskOf.2 ⟨by norm_num, ?_⟩) (closed_maskOf F hB hC)
    (homog_maskOf F hB hC)
  rw [F.rep_zero]
  exact z0_mem_cls

theorem eq_of_fam (hB : B₀ ≤ X) (hC : ∀ x ∈ X, x * z₀ = z₀ * x → x ∈ B₀)
    {f : ℕ × ℕ × ℕ} (hf : f ∈ fams) (hm : maskOf rep X = f.1) :
    X = B₀ ⊔ Subgroup.zpowers (rep f.2.2) := by
  obtain ⟨hq17, hqm, hwords⟩ := F.fam f hf
  generalize hg : rep f.2.2 = g at hwords
  have hgX : g ∈ X := by
    rw [← hg]
    exact mem_of_mem_cls hB (testBit_maskOf.1 (hm ▸ hqm)).2
  have hMX : B₀ ⊔ Subgroup.zpowers g ≤ X := sup_le hB (Subgroup.zpowers_le.2 hgX)
  have hBM : B₀ ≤ B₀ ⊔ Subgroup.zpowers g := le_sup_left
  have hcls : cls X ⊆ cls (B₀ ⊔ Subgroup.zpowers g) := by
    intro d hd
    obtain ⟨b, hb, c, hc, rfl⟩ := (mem_cls_iff F hB hC).1 hd
    obtain ⟨hb17, hbX⟩ := mem_memL_maskOf.1 hb
    obtain ⟨e, heM, he⟩ := hwords b hb17 (hm ▸ testBit_maskOf.2 ⟨hb17, hbX⟩)
    rw [he]
    exact ⟨c * e, Subgroup.mul_mem _ (hBM hc) heM, by group⟩
  have hcard : Nat.card (B₀ ⊔ Subgroup.zpowers g : Subgroup (GL (Fin 6) (ZMod 2))) =
      Nat.card X := by
    rw [card_eq_mul_ncard hBM (fun x hx => hC x (hMX hx)), card_eq_mul_ncard hB hC,
      (cls_mono hMX).antisymm hcls]
  exact (Subgroup.eq_of_le_of_card_ge hMX hcard.ge).symm

theorem gl62OvergroupsEq_of_facts : GL62OvergroupsEq := by
  intro X hB hC
  have hcard := card_eq_mul_ncard hB hC
  rcases List.mem_cons.1 (mask_mem F hB hC) with h | h
  · obtain ⟨-, h1⟩ := Prod.mk.inj h
    refine Or.inl ⟨(Subgroup.eq_of_le_of_card_ge hB ?_).symm, by rw [hcard, h1]⟩
    rw [hcard, h1, card_B₀]
  · obtain ⟨f, hf, hfe⟩ := List.mem_map.1 h
    obtain ⟨hm, hs⟩ := Prod.mk.inj hfe
    have hX := eq_of_fam F hB hC hf hm.symm
    have hc : Nat.card X = 336 * f.2.1 := by rw [hcard, hs]
    rcases F.fam_gen f hf with ⟨hg, h3⟩ | ⟨hg, h3⟩ | ⟨hg, h3⟩ | ⟨hg, h3⟩ <;>
      rw [hg] at hX <;> rw [h3] at hc
    · exact Or.inr (Or.inl ⟨hX, hc⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hX, hc⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hX, hc⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hX, hc⟩)))

end Facts

theorem gl62OvergroupsEq_of_exists
    (h : ∃ (rep : ℕ → GL (Fin 6) (ZMod 2)) (S : ℕ → ℕ) (C H : ℕ → ℕ → ℕ)
      (fams : List (ℕ × ℕ × ℕ)), GL62Facts rep S C H fams) : GL62OvergroupsEq := by
  obtain ⟨rep, S, C, H, fams, F⟩ := h
  exact gl62OvergroupsEq_of_facts F

end CFSG.KC.GL62
