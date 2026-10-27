module

public import Certificates.Kernel.MonsterExist.ShortKey.Lanes
public import Certificates.Kernel.MonsterExist.ShortKey.Short
public import CFSG.Monster.Existence.ELevelCheck

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.MonsterExist.ShortKey

open CFSG.KC CFSG.KC.Loop CFSG.KC.KDense CFSG.Monster CFSG.Monster.B CFSG.Monster.Code
  CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Griess CFSG.Monster.VisCert
  CFSG.Monster.Existence CFSG.Monster.B.Rep4371 CFSG.Monster.AxisCount

theorem natRec_add_sum (F : ℕ → ℕ) : ∀ k,
    Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 => Nat.add (F l) ih2) k =
      ∑ l ∈ Finset.range k, F l
  | 0 => by simp
  | k + 1 => by
    change F k + Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 => Nat.add (F l) ih2) k = _
    rw [natRec_add_sum F k, Finset.sum_range_succ, Nat.add_comm]

theorem sumBelow_g (m : ℕ) (f : ℕ → ℕ) : ∀ hi, sumBelow m hi f =
    ∑ i ∈ Finset.range (64 * hi), Bool.rec (motive := fun _ => ℕ) 0 (f i) (Nat.blt i m)
  | 0 => by simp [sumBelow]
  | hi + 1 => by
    have e : sumBelow m (hi + 1) f = Nat.add (Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 =>
        Nat.add ((fun i => Bool.rec (motive := fun _ => ℕ) 0 (f i) (Nat.blt i m))
          (Nat.add (Nat.shiftLeft hi 6) l)) ih2) 64) (sumBelow m hi f) := rfl
    have e2 : ∀ l, Nat.add (Nat.shiftLeft hi 6) l = 64 * hi + l := fun l => by
      change hi <<< 6 + l = _
      rw [Nat.shiftLeft_eq, Nat.mul_comm]
    rw [e, natRec_add_sum, sumBelow_g m f hi, Nat.mul_succ, Finset.sum_range_add]
    simp only [e2]
    exact Nat.add_comm _ _

theorem sumBelow_spec {m hi : ℕ} (f : ℕ → ℕ) (hm : m ≤ 64 * hi) :
    sumBelow m hi f = ∑ i ∈ Finset.range m, f i := by
  rw [sumBelow_g]
  obtain ⟨d, hd⟩ : ∃ d, 64 * hi = m + d := ⟨64 * hi - m, by omega⟩
  rw [hd, Finset.sum_range_add]
  have h2 : ∑ l ∈ Finset.range d,
      Bool.rec (motive := fun _ => ℕ) 0 (f (m + l)) (Nat.blt (m + l) m) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    have hb : Nat.blt (m + l) m = false := by
      cases e : Nat.blt (m + l) m
      · rfl
      · rw [Nat.blt_eq] at e
        omega
    rw [hb]
  rw [h2, Nat.add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  have hb : Nat.blt i m = true := by
    rw [Nat.blt_eq]
    exact Finset.mem_range.1 hi
  rw [hb]

theorem listSum_range (f : ℕ → ℕ) : ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, listSum_range f n, Finset.sum_range_succ]
    simp

theorem natRec_and_iff (P : ℕ → Bool) : ∀ n,
    Nat.rec (motive := fun _ => Bool) true (fun k ih => bAnd(P k, ih)) n = true ↔ ∀ k < n, P k = true
  | 0 => by simp
  | n + 1 => by
    change bAnd(P n, Nat.rec (motive := fun _ => Bool) true (fun k ih => bAnd(P k, ih)) n) = true ↔ _
    rw [bAnd_true, natRec_and_iff P n]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact h2 k hk
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun k hk => h k (Nat.lt_succ_of_lt hk)⟩

theorem bucketsOK_iff (lo n : ℕ) : bucketsOK lo n = true ↔ ∀ k < n, bucketOK (lo + k) = true :=
  natRec_and_iff (fun k => bucketOK (Nat.add lo k)) n

theorem laneW_fld {W : ℕ} (_hW : 0 < W) (T off n k : ℕ) (hk : k < n) :
    laneW W (fld(T, Nat.mul W off, maskW (Nat.mul W n))) k = laneW W T (off + k) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < W
  · rw [testBit_laneW _ _ _ hi, testBit_laneW _ _ _ hi, land_maskW]
    change ((T >>> (W * off)) % 2 ^ (W * n)).testBit (W * k + i) = _
    rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
    have h1 : W * k + i < W * n := by
      have : W * (k + 1) ≤ W * n := Nat.mul_le_mul_left _ hk
      rw [Nat.mul_succ] at this
      omega
    rw [decide_eq_true h1, Bool.true_and]
    congr 1
    ring
  · have hi' : W ≤ i := Nat.le_of_not_lt hi
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (laneW_lt _ k) (Nat.pow_le_pow_right (by norm_num) hi')),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (laneW_lt _ _) (Nat.pow_le_pow_right (by norm_num) hi'))]

theorem laneW_slice (T off n k : ℕ) (hk : k < n) :
    laneW 13 (slice T off n) k = laneW 13 T (off + k) :=
  laneW_fld (by norm_num) T off n k hk

@[expose] noncomputable def cnt (a : ℕ) : ℕ := cntB (bkt a)

@[expose] noncomputable def dAt (a k : ℕ) : ℕ := laneW 13 SKV (offB (bkt a) + k)

@[expose] noncomputable def keyList : List ℕ :=
  (List.range 4096).flatMap fun a => (List.range (cnt a)).map fun k => a + 4096 * dAt a k

section Checks

variable (hb : ∀ a < 4096, bucketOK a = true)
include hb

theorem lane_facts {a : ℕ} (ha : a < 4096) {k : ℕ} (hk : k < cnt a) :
    dAt a k < 4096 ∧ IsShortCoord (toC a, toD (dAt a k)) ∧ (0 < k → dAt a (k - 1) < dAt a k) := by
  have h := hb a ha
  unfold bucketOK at h
  dsimp only at h
  have h2 := (natRec_and_iff _ _).1 h k hk
  unfold laneOK at h2
  dsimp only at h2
  have e1 : laneW (nat_lit 13) (slice SKV (offB (bkt a)) (cntB (bkt a))) k = dAt a k :=
    laneW_slice SKV _ _ k hk
  rw [e1, bAnd_true, bAnd_true, blt_true] at h2
  obtain ⟨hd, he, hlt⟩ := h2
  refine ⟨hd, isShortCoord_of_entryOK he, fun hk0 => ?_⟩
  have hk1 : k - 1 < cntB (bkt a) := by
    change k < cnt a at hk
    unfold cnt at hk
    omega
  rw [bRec_true] at hlt
  rcases hlt with ⟨h0, -⟩ | ⟨-, hlt⟩
  · exact absurd (beq_true.1 h0) (by omega)
  · have e2 : laneW (nat_lit 13) (slice SKV (offB (bkt a)) (cntB (bkt a))) (Nat.sub k (nat_lit 1)) =
        dAt a (k - 1) := laneW_slice SKV _ _ _ hk1
    rw [e2] at hlt
    exact blt_true.1 hlt

theorem dAt_strictMono {a : ℕ} (ha : a < 4096) {j k : ℕ} (hjk : j < k) (hk : k < cnt a) :
    dAt a j < dAt a k := by
  induction k with
  | zero => omega
  | succ k ih =>
    have h1 := (lane_facts hb ha hk).2.2 (Nat.succ_pos k)
    simp only [Nat.add_sub_cancel] at h1
    rcases Nat.lt_succ_iff_lt_or_eq.1 hjk with h | rfl
    · exact lt_trans (ih h (by omega)) h1
    · exact h1

omit hb in
theorem mem_keyList_iff {x : ℕ} :
    x ∈ keyList ↔ ∃ a < 4096, ∃ k < cnt a, x = a + 4096 * dAt a k := by
  unfold keyList
  simp only [List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨a, ha, k, hk, rfl⟩
    exact ⟨a, ha, k, hk, rfl⟩
  · rintro ⟨a, ha, k, hk, rfl⟩
    exact ⟨a, ha, k, hk, rfl⟩

theorem keyList_facts {x : ℕ} (hx : x ∈ keyList) : x < 2 ^ 24 ∧ vecX x ∈ shortSet := by
  obtain ⟨a, ha, k, hk, rfl⟩ := mem_keyList_iff.1 hx
  obtain ⟨hd, hs, -⟩ := lane_facts hb ha hk
  refine ⟨by norm_num; omega, ?_⟩
  rw [vecX_eq_mod]
  have e1 : (a + 4096 * dAt a k) % 4096 = a := by omega
  have e2 : (a + 4096 * dAt a k) / 4096 % 4096 = dAt a k := by omega
  rw [e1, e2]
  exact hs

theorem keyList_nodup : keyList.Nodup := by
  unfold keyList
  rw [List.nodup_flatMap]
  refine ⟨fun a ha => ?_, ?_⟩
  · have ha' := List.mem_range.1 ha
    refine (List.nodup_range).map_on fun j hj k hk e => ?_
    have hj' := List.mem_range.1 hj
    have hk' := List.mem_range.1 hk
    have e' : dAt a j = dAt a k := by omega
    rcases Nat.lt_trichotomy j k with h | h | h
    · exact absurd e' (Nat.ne_of_lt (dAt_strictMono hb ha' h hk'))
    · exact h
    · exact absurd e'.symm (Nat.ne_of_lt (dAt_strictMono hb ha' h hj'))
  · refine List.nodup_range.pairwise_of_forall_ne fun a ha b hb' hab => ?_
    rw [Function.onFun, List.disjoint_left]
    intro x hxa hxb
    simp only [List.mem_map, List.mem_range] at hxa hxb
    obtain ⟨j, -, rfl⟩ := hxa
    obtain ⟨k, -, e⟩ := hxb
    have ha' := List.mem_range.1 ha
    have hb'' := List.mem_range.1 hb'
    omega

omit hb in
theorem keyList_length (hc : countOK = true) : keyList.length = 98280 := by
  unfold countOK at hc
  have hs := beq_true.1 hc
  rw [sumBelow_spec _ (by norm_num)] at hs
  unfold keyList
  rw [List.length_flatMap]
  simp only [List.length_map, List.length_range]
  rw [← hs, listSum_range]
  rfl

theorem memK_iff_mem {x : ℕ} (hx : x < 2 ^ 24) : memK x = true ↔ x ∈ keyList := by
  set a := x % 4096 with ha
  set d := x / 4096 with hd
  have ha4 : a < 4096 := Nat.mod_lt _ (by norm_num)
  have hd4 : d < 4096 := by rw [hd]; norm_num at hx ⊢; omega
  have hxad : x = a + 4096 * d := by omega
  have e1 : Nat.land x (nat_lit 4095) = a := by
    rw [ha]
    exact Nat.and_two_pow_sub_one_eq_mod x 12
  have e2 : Nat.shiftRight x (nat_lit 12) = d := by
    rw [hd]
    change x >>> 12 = _
    rw [Nat.shiftRight_eq_div_pow]
  have hl : ∀ k < cntB (bkt a), laneW 13 (slice SKV (offB (bkt a)) (cntB (bkt a))) k < 2 ^ (13 - 1) :=
    fun k hk => by
      rw [laneW_slice SKV _ _ k hk]
      exact (lane_facts hb ha4 hk).1
  have hv : slice SKV (offB (bkt a)) (cntB (bkt a)) < 2 ^ (13 * cntB (bkt a)) := by
    unfold slice
    rw [land_maskW]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  unfold memK
  dsimp only
  rw [e1, e2, bRec_true]
  have hab := absentL_iff (W := 13) (by norm_num) hv hl (by norm_num; omega : d < 2 ^ (13 - 1))
  rw [mem_keyList_iff]
  constructor
  · rintro (⟨-, h1⟩ | ⟨h1, -⟩)
    · exact absurd h1 (by simp)
    · rw [← Bool.not_eq_true] at h1
      rw [hab] at h1
      simp only [not_forall, not_not] at h1
      obtain ⟨k, hk, hkd⟩ := h1
      rw [laneW_slice SKV _ _ k hk] at hkd
      exact ⟨a, ha4, k, hk, by rw [hxad]; unfold dAt; rw [hkd]⟩
  · rintro ⟨b, hb4, k, hk, hx'⟩
    have hd' := (lane_facts hb hb4 hk).1
    have e3 : b = a := by omega
    subst e3
    have e4 : dAt a k = d := by omega
    right
    refine ⟨?_, rfl⟩
    rw [← Bool.not_eq_true, hab]
    simp only [not_forall, not_not]
    exact ⟨k, hk, by rw [laneW_slice SKV (offB (bkt a)) (cntB (bkt a)) k hk]; exact e4⟩

theorem memK_iff_of_checks (hc : countOK = true) {x : ℕ} (hx : x < 2 ^ 24) :
    memK x = true ↔ vecX x ∈ shortSet := by
  rw [memK_iff_mem hb hx]
  refine ⟨fun h => (keyList_facts hb h).2, fun h => ?_⟩
  have hsub : vecX '' (keyList.toFinset : Set ℕ) ⊆ shortSet := by
    rintro _ ⟨y, hy, rfl⟩
    exact (keyList_facts hb (List.mem_toFinset.1 hy)).2
  have hinj : Set.InjOn vecX (keyList.toFinset : Set ℕ) := fun y hy z hz e =>
    vecX_injective_lt (keyList_facts hb (List.mem_toFinset.1 hy)).1
      (keyList_facts hb (List.mem_toFinset.1 hz)).1 e
  have hcard : (vecX '' (keyList.toFinset : Set ℕ)).ncard = 98280 := by
    rw [hinj.ncard_image, Set.ncard_coe_finset, List.toFinset_card_of_nodup (keyList_nodup hb),
      keyList_length hc]
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [ncard_shortSet, hcard])
    (Set.finite_of_ncard_ne_zero (by rw [ncard_shortSet]; norm_num))
  rw [← heq] at h
  obtain ⟨y, hy, e⟩ := h
  have hy' := List.mem_toFinset.1 hy
  rwa [vecX_injective_lt (keyList_facts hb hy').1 hx e] at hy'

theorem memK_eq_isShortX_of_checks (hc : countOK = true) {x : ℕ}
    (hx : x < 2 ^ 24) : memK x = isShortX x :=
  Bool.eq_iff_iff.2 ((memK_iff_of_checks hb hc hx).trans (isShortX_iff hx).symm)

end Checks

theorem mem_shortPacked_iff {x : ℕ} : x ∈ shortPacked ↔ x < 2 ^ 24 ∧ isShortX x = true := by
  unfold shortPacked foundCodes
  rw [List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [mem_findAll] at ha
    rcases ha with ⟨ha, hs⟩ | ha
    · refine ⟨actRows_convInvRows_lt a, ?_⟩
      unfold isShortX
      rw [actRows_convRows_convInvRows ha]
      exact hs
    · exact absurd ha (List.not_mem_nil)
  · rintro ⟨hx, hs⟩
    refine ⟨actRows convRows x, ?_, actRows_convInvRows_convRows hx⟩
    rw [mem_findAll]
    exact Or.inl ⟨actRows_convRows_lt x, hs⟩

end CertificateChecks.MonsterExist.ShortKey

end
