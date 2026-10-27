module

public import Certificates.Kernel.SporE81.HN27Checks
public import Certificates.Kernel.SporSch.HN.Pt2108
public import Certificates.Kernel.SporSch.HN.Pt2085
public import CFSG.Sporadic.HNSchreier.Sylow3
public import CFSG.Assembly.Defs

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelE81.HN27K

open CFSG.KC.Enum CFSG.KC.LL CFSG.KS CFSG.KS.SporSch CFSG.KS.Ord
open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.KD.HN27
open CertificateChecks.KernelSporSch

local notation "OM'" => ordMat 5 133 13 1729

attribute [local irreducible] lamP rowP pGenJ eAux

theorem sbE (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by cases y <;> rfl

theorem lamRow_spec {P c : ℕ} : ∀ (l : List ℕ) (i : ℕ), lamRow P c l i = true →
    ∀ k (hk : k < l.length), fld2 P l[k] = (fld2 P (i + k) + c) % 3
  | [], _, _, k, hk => absurd hk (by simp)
  | x :: t, i, h, k, hk => by
    change (Nat.beq (fld2 P x) (Nat.mod (Nat.add (fld2 P i) c) 3) && lamRow P c t (Nat.succ i))
      = true at h
    rw [Bool.and_eq_true] at h
    rcases k with _ | k
    · exact Nat.eq_of_beq_eq_true h.1
    · have := lamRow_spec t (i + 1) h.2 k (by simpa using hk)
      rw [List.getElem_cons_succ, this, show i + 1 + k = i + (k + 1) by omega]

theorem rowChk_spec {Q : ℕ} : ∀ (l : List ℕ) (i : ℕ), rowChk Q l i = true →
    ∀ k (hk : k < l.length), fld10 Q (i + k) = l[k]
  | [], _, _, k, hk => absurd hk (by simp)
  | x :: t, i, h, k, hk => by
    change (Nat.beq (fld10 Q i) x && rowChk Q t (Nat.succ i)) = true at h
    rw [Bool.and_eq_true] at h
    rcases k with _ | k
    · exact Nat.eq_of_beq_eq_true h.1
    · have := rowChk_spec t (i + 1) h.2 k (by simpa using hk)
      rw [List.getElem_cons_succ, ← this, show i + 1 + k = i + (k + 1) by omega]

theorem clsOK_spec {P z1 z2 : ℕ} : ∀ (l : List (List ℕ)) (c : ℕ), clsOK P z1 z2 l c = true →
    ∀ k (hk : k < l.length), c + k ∉ WC → ∀ i ∈ l[k], labZ P i = false ∨ i = z1 ∨ i = z2
  | [], _, _, k, hk => absurd hk (by simp)
  | cl :: t, c, h, k, hk => by
    change ((WC.contains c || cl.all fun i => !labZ P i || Nat.beq i z1 || Nat.beq i z2) &&
      clsOK P z1 z2 t (Nat.succ c)) = true at h
    rw [Bool.and_eq_true] at h
    rcases k with _ | k
    · intro hc i hi
      rw [add_zero] at hc
      rw [List.getElem_cons_zero] at hi
      have h1 := h.1
      rw [Bool.or_eq_true, List.contains_iff_mem] at h1
      rcases h1 with h1 | h1
      · exact absurd h1 hc
      · have := List.all_eq_true.1 h1 i hi
        simp only [Bool.or_eq_true, Bool.not_eq_true'] at this
        rcases this with (h2 | h2) | h2
        · exact Or.inl h2
        · exact Or.inr (Or.inl (Nat.eq_of_beq_eq_true h2))
        · exact Or.inr (Or.inr (Nat.eq_of_beq_eq_true h2))
    · intro hc
      have := clsOK_spec t (c + 1) h.2 k (by simpa using hk)
        (by rw [show c + 1 + k = c + (k + 1) by omega]; exact hc)
      simpa using this

theorem C3J_eq (m : ℕ) : HNPt2109.C3J m = c3J m := by
  obtain ⟨-, -, hl3, hg, -⟩ := HNPt2109.letters_ok
  unfold HNPt2109.C3J HNPt2109.G3J c3J g3J
  split_ifs with h
  · exact HNPt2085.wJ_sL _ (hl3 m h)
  · rw [HNPt2085.seedWordJ_eq, HNPt2085.wJ_sL _ hg]

theorem PG_eq (j : ℕ) : HNPt2108.PG j = pGenJ j := by
  obtain ⟨-, -, hk⟩ := HNPt2108.lift_data
  unfold HNPt2108.PG pGenJ
  split_ifs with h
  · simp only [C3J_eq]
  · exact HNPt2085.wJ_sL _ hk

theorem E_eq : ∀ i < 729, HNPt2108.E i = eJ i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases h0 : i = 0
    · subst h0
      rw [HNPt2108.E_zero, eJ_zero]
    · have hp := (HNPt2108.par_data.2.2 i hi h0).1
      rw [HNPt2108.E_succ hi h0, eJ_succ hi h0, PG_eq, ih _ hp (by omega)]

theorem EM_eJ {i : ℕ} (hi : i < 729) :
    Canon 5 133 13 (HNPt2108.EM i) ∧ OM' (HNPt2108.EM i) = matJ (eJ i) := by
  obtain ⟨c, m⟩ := HNPt2108.EM_mat 729 i
  exact ⟨c, by rw [← E_eq i hi]; exact m⟩

noncomputable def liftJ (w : List ℕ) : JH := (w.map fun l => c3J (l - 1)).prod

theorem liftM_eJ {w : List ℕ} (hw : ∀ l ∈ w, 1 ≤ l ∧ l ≤ 7) :
    Canon 5 133 13 (HNPt2108.liftM w) ∧ OM' (HNPt2108.liftM w) = matJ (liftJ w) := by
  have := HNPt2108.liftM_mat w hw (one_sound CFSG.KD.OrdHN.consts).1
    (by rw [HNXP.one_ord, ← matJ_one])
  rw [one_mul] at this
  refine ⟨this.1, ?_⟩
  change OM' (w.foldl (fun acc l => CFSG.KC.LL.HN.mm acc (HNPt2108.C3S (l - 1))) CFSG.KD.OrdHN.ONE)
    = _
  rw [this.2, liftJ]
  simp only [C3J_eq]

theorem liftJ_comm
    {w : List ℕ} (hw : ∀ l ∈ w, 1 ≤ l ∧ l ≤ 7) :
    liftJ w * sJ 2 = sJ 2 * liftJ w := by
  have h : liftJ w ∈ CJ (sJ 2) := by
    refine Subgroup.list_prod_mem _ fun y hy => ?_
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hy
    have := hw l hl
    exact mem_CJ.2 (c3J_comm (j := l - 1) (by omega)).symm
  exact (mem_CJ.1 h).symm

noncomputable abbrev Lt (j i : ℕ) : ℕ := (FAData.pLeft[j]!)[i]!

theorem row_len {j : ℕ} (hj : j < 6) : (FAData.pLeft[j]!).toList.length = 729 := by
  rw [Array.length_toList, (HNPt2108.left_data j hj).1]

theorem row_get {j i : ℕ} (h : i < (FAData.pLeft[j]!).toList.length) :
    (FAData.pLeft[j]!).toList[i] = Lt j i := by
  rw [Array.getElem_toList]
  exact (getElem!_pos _ _ _).symm

theorem L_mul
    {j i : ℕ} (hj : j < 6) (hi : i < 729) : Lt j i < 729 ∧ pGenJ j * eJ i = eJ (Lt j i) :=
  ⟨(HNPt2108.left_data j hj).2 i hi, left_action hj hi⟩

theorem rowP_get {j : ℕ} (hj : j ∈ [1, 3, 4, 5]) {i : ℕ} (hi : i < 729) :
    fld10 (rowP j) i = Lt j i := by
  have hj6 : j < 6 := by simp at hj; omega
  have h := rows_ok
  rw [List.all_eq_true] at h
  have := h j hj
  rw [sbE] at this
  have e := rowChk_spec _ 0 this i (by rw [row_len hj6]; exact hi)
  rw [zero_add] at e
  rw [e, row_get]

theorem itR_spec
    {j : ℕ} (hj : j ∈ [1, 3, 4, 5]) : ∀ (n x : ℕ), x < 729 →
      itR (rowP j) n x < 729 ∧ eJ (itR (rowP j) n x) = pGenJ j ^ n * eJ x
  | 0, x, hx => ⟨hx, by rw [pow_zero, one_mul]; rfl⟩
  | n + 1, x, hx => by
    have hj6 : j < 6 := by simp at hj; omega
    obtain ⟨h1, h2⟩ := itR_spec hj n x hx
    change fld10 (rowP j) (itR (rowP j) n x) < 729 ∧ eJ (fld10 (rowP j) (itR (rowP j) n x)) = _
    rw [rowP_get hj h1]
    obtain ⟨h3, h4⟩ := L_mul hj6 h1
    exact ⟨h3, by rw [← h4, h2, pow_succ', mul_assoc]⟩

noncomputable def lab (i : ℕ) : ℕ := fld2 lamP i % 3

theorem lab_lt (i : ℕ) : lab i < 3 := Nat.mod_lt _ (by norm_num)

theorem lab_zero : lab 0 = 0 := by
  have h := lam_ok
  rw [sbE, Bool.and_eq_true] at h
  rw [lab, Nat.eq_of_beq_eq_true h.1]

theorem lab_L {j i : ℕ} (hj : j < 6) (hi : i < 729) : lab (Lt j i) = (lab i + cG j) % 3 := by
  have h := lam_ok
  rw [sbE, Bool.and_eq_true, List.all_eq_true] at h
  have := lamRow_spec _ 0 (h.2 j (List.mem_range.2 hj)) i (by rw [row_len hj]; exact hi)
  rw [row_get, zero_add] at this
  rw [lab, lab, this]
  omega

theorem lab_mul :
    ∀ a < 729, ∀ b < 729, ∃ m < 729, eJ a * eJ b = eJ m ∧ lab m = (lab a + lab b) % 3 := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro ha b hb
    by_cases h0 : a = 0
    · subst h0
      refine ⟨b, hb, by rw [eJ_zero, one_mul], ?_⟩
      rw [lab_zero, zero_add, Nat.mod_eq_of_lt (lab_lt b)]
    · obtain ⟨hp, hg⟩ := HNPt2108.par_data.2.2 a ha h0
      set p := (FAData.pParents[a]!).1
      set g := (FAData.pParents[a]!).2
      obtain ⟨m, hm, e1, e2⟩ := ih p hp (by omega) b hb
      obtain ⟨hL, eL⟩ := L_mul hg hm
      obtain ⟨hLp, eLp⟩ := L_mul hg (show p < 729 by omega)
      have ea : eJ a = pGenJ g * eJ p := eJ_succ ha h0
      have hap : a = Lt g p := eJ_inj ha hLp (ea.trans eLp)
      refine ⟨Lt g m, hL, by rw [ea, mul_assoc, e1, eL], ?_⟩
      rw [lab_L hg hm, hap, lab_L hg (by omega), e2]
      omega

noncomputable def monR :
    Submonoid JH where
  carrier := {x | ∃ i < 729, lab i = 0 ∧ eJ i = x}
  one_mem' := ⟨0, by norm_num, lab_zero, eJ_zero⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, la, rfl⟩ ⟨b, hb, lb, rfl⟩
    obtain ⟨m, hm, e, lm⟩ := lab_mul a ha b hb
    exact ⟨m, hm, by rw [lm, la, lb], e.symm⟩

noncomputable def RJ :
    Subgroup JH :=
  { monR with
    inv_mem' := by
      intro x hx
      have e : x ^ (orderOf x - 1) = x⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
      rw [← e]
      exact monR.pow_mem hx _ }

theorem mem_RJ
    {x : JH} : x ∈ RJ ↔ ∃ i < 729, lab i = 0 ∧ eJ i = x := Iff.rfl

theorem RJ_le :
    RJ ≤ PJ := by
  rintro _ ⟨i, hi, -, rfl⟩
  exact eJ_mem_PJ hi

theorem labZ_of {i : ℕ} (h : lab i = 0) : labZ lamP i = true := by
  change Nat.beq (fld2 lamP i % 3) 0 = true
  rw [show fld2 lamP i % 3 = 0 from h]
  rfl

noncomputable abbrev rL : List ℕ := (List.range 729).filter (labZ lamP)

theorem mem_rL {i : ℕ} : i ∈ rL ↔ i < 729 ∧ lab i = 0 := by
  rw [List.mem_filter, List.mem_range]
  exact and_congr_right fun _ => ⟨fun h => Nat.eq_of_beq_eq_true h, labZ_of⟩

theorem rL_length : rL.length = 243 := by
  have h := cnt_ok
  rw [sbE] at h
  exact Nat.eq_of_beq_eq_true h

theorem card_RJ :
    Nat.card RJ = 243 := by
  have hset : ((RJ : Subgroup JH) : Set JH) = (fun i : ℕ => eJ i) '' (rL.toFinset : Set ℕ) := by
    ext x
    simp only [SetLike.mem_coe, mem_RJ, Set.mem_image, List.coe_toFinset, Set.mem_setOf_eq,
      mem_rL]
    constructor
    · rintro ⟨i, hi, hl, rfl⟩
      exact ⟨i, ⟨hi, hl⟩, rfl⟩
    · rintro ⟨i, ⟨hi, hl⟩, rfl⟩
      exact ⟨i, hi, hl, rfl⟩
  rw [← SetLike.coe_sort_coe, hset, Nat.card_image_of_injOn, Finset.coe_sort_coe,
    Nat.card_eq_finsetCard, List.toFinset_card_of_nodup (List.nodup_range.filter _), rL_length]
  intro a ha b hb hab
  simp only [Finset.mem_coe, List.mem_toFinset, mem_rL] at ha hb
  exact eJ_inj ha.1 hb.1 hab

noncomputable def DJ : Subgroup JH := Subgroup.closure {pGenJ 1, pGenJ 3, pGenJ 4, pGenJ 5}

theorem main_parts : CFSG.Decide.bitsetNodup (dList (rowP 1) (rowP 3) (rowP 4) (rowP 5)) = true ∧
    (∀ a ∈ [1, 3, 4, 5], ∀ b ∈ [1, 3, 4, 5], itR (rowP a) 1 (itR (rowP b) 1 0) =
      itR (rowP b) 1 (itR (rowP a) 1 0)) ∧
    (∀ a ∈ [1, 3, 4, 5], itR (rowP a) 3 0 = 0) ∧ itR (rowP 5) 1 0 ≠ 0 ∧
    (∀ t ∈ WT, t ∈ dList (rowP 1) (rowP 3) (rowP 4) (rowP 5)) ∧
    clsOK lamP (itR (rowP 5) 1 0) (itR (rowP 5) 2 0) FAData.wClass.toList 0 = true := by
  have h := main_ok
  simp only [sbE] at h
  unfold mainK gComm at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h13⟩, h14⟩, h15⟩, h34⟩, h35⟩, h45⟩, c1⟩, c3⟩, c4⟩, c5⟩, n5⟩, hw⟩,
    hc⟩ := h
  have e := fun {a b : ℕ} (h : Nat.beq a b = true) => Nat.eq_of_beq_eq_true h
  refine ⟨h1, ?_, ?_, fun h => ?_, hw, hc⟩
  · intro a ha b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      first | exact e h13 | exact (e h13).symm | exact e h14 | exact (e h14).symm |
        exact e h15 | exact (e h15).symm | exact e h34 | exact (e h34).symm | exact e h35 |
        exact (e h35).symm | exact e h45 | exact (e h45).symm | exact Eq.refl _
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact e c1
    · exact e c3
    · exact e c4
    · exact e c5
  · rw [h, Nat.beq_refl] at n5
    exact absurd n5 (by decide)

theorem gen_mem {a : ℕ} (ha : a ∈ [1, 3, 4, 5]) :
    pGenJ a ∈ ({pGenJ 1, pGenJ 3, pGenJ 4, pGenJ 5} : Set JH) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl <;> simp

theorem gen_cases {x : JH} (hx : x ∈ ({pGenJ 1, pGenJ 3, pGenJ 4, pGenJ 5} : Set JH)) :
    ∃ a ∈ [1, 3, 4, 5], x = pGenJ a := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> simp

theorem gen_one
    {a : ℕ} (ha : a ∈ [1, 3, 4, 5]) : pGenJ a = eJ (itR (rowP a) 1 0) := by
  rw [(itR_spec ha 1 0 (by norm_num)).2, eJ_zero, pow_one, mul_one]

theorem gen_comm :
    ∀ x ∈ ({pGenJ 1, pGenJ 3, pGenJ 4, pGenJ 5} : Set JH),
      ∀ y ∈ ({pGenJ 1, pGenJ 3, pGenJ 4, pGenJ 5} : Set JH), x * y = y * x := by
  intro x hx y hy
  obtain ⟨a, ha, rfl⟩ := gen_cases hx
  obtain ⟨b, hb, rfl⟩ := gen_cases hy
  have e1 := (itR_spec ha 1 _ (itR_spec hb 1 0 (by norm_num)).1).2
  have e2 := (itR_spec hb 1 _ (itR_spec ha 1 0 (by norm_num)).1).2
  rw [main_parts.2.1 a ha b hb, ← gen_one hb, pow_one] at e1
  rw [← gen_one ha, pow_one] at e2
  exact e1.symm.trans e2

theorem gen_cube
    {a : ℕ} (ha : a ∈ [1, 3, 4, 5]) : pGenJ a ^ 3 = 1 := by
  have e := (itR_spec ha 3 0 (by norm_num)).2
  rw [main_parts.2.2.1 a ha, eJ_zero, mul_one] at e
  exact e.symm

theorem DJ_le_CJ {y : JH}
    (hy : ∀ b ∈ ({pGenJ 1, pGenJ 3, pGenJ 4, pGenJ 5} : Set JH), b * y = y * b) : DJ ≤ CJ y :=
  (Subgroup.closure_le _).2 fun b hb => mem_CJ.2 (hy b hb).symm

theorem DJ_comm
    {x y : JH} (hx : x ∈ DJ) (hy : y ∈ DJ) : x * y = y * x := by
  have hy' : ∀ b ∈ ({pGenJ 1, pGenJ 3, pGenJ 4, pGenJ 5} : Set JH), b * y = y * b :=
    fun b hb => mem_CJ.1 (DJ_le_CJ (fun a ha => gen_comm a ha b hb) hy)
  exact (mem_CJ.1 (DJ_le_CJ hy' hx)).symm

theorem DJ_cube
    {x : JH} (hx : x ∈ DJ) : x ^ 3 = 1 := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := gen_cases hx
    exact gen_cube ha
  | one => exact one_pow 3
  | mul x y hx hy ihx ihy =>
    have h2 : y * x = x * y := (DJ_comm hx hy).symm
    have sw : ∀ z : JH, y * (x * z) = x * (y * z) := fun z => by rw [← mul_assoc, h2, mul_assoc]
    rw [pow_three] at ihx ihy ⊢
    simp only [mul_assoc, sw]
    rw [show x * (x * (x * (y * (y * y)))) = x * (x * x) * (y * (y * y)) by simp only [mul_assoc],
      ihx, ihy, one_mul]
  | inv x _ ihx => rw [inv_pow, ihx, inv_one]

theorem DJ_elem :
    CFSG.Assembly.IsElemAbelian 3 DJ :=
  ⟨⟨⟨fun a b => Subtype.ext (DJ_comm a.2 b.2)⟩⟩, fun _ hx => DJ_cube hx⟩

theorem itR_mem
    {a : ℕ} (ha : a ∈ [1, 3, 4, 5]) (n : ℕ) {x : ℕ} (hx : x < 729) (hD : eJ x ∈ DJ) :
    itR (rowP a) n x < 729 ∧ eJ (itR (rowP a) n x) ∈ DJ := by
  obtain ⟨h1, h2⟩ := itR_spec ha n x hx
  refine ⟨h1, ?_⟩
  rw [h2]
  exact mul_mem (pow_mem (Subgroup.subset_closure (gen_mem ha)) n) hD

theorem dIdx_mem
    (n : ℕ) : dIdx (rowP 1) (rowP 3) (rowP 4) (rowP 5) n < 729 ∧
      eJ (dIdx (rowP 1) (rowP 3) (rowP 4) (rowP 5) n) ∈ DJ := by
  have h0 : eJ 0 ∈ DJ := by rw [eJ_zero]; exact one_mem _
  obtain ⟨a5, b5⟩ := itR_mem (a := 5) (by simp) (n % 3) (by norm_num) h0
  obtain ⟨a4, b4⟩ := itR_mem (a := 4) (by simp) (n / 3 % 3) a5 b5
  obtain ⟨a3, b3⟩ := itR_mem (a := 3) (by simp) (n / 9 % 3) a4 b4
  exact itR_mem (a := 1) (by simp) (n / 27) a3 b3

theorem dList_mem
    {t : ℕ} (ht : t ∈ dList (rowP 1) (rowP 3) (rowP 4) (rowP 5)) : t < 729 ∧ eJ t ∈ DJ := by
  obtain ⟨n, -, rfl⟩ := List.mem_map.1 ht
  exact dIdx_mem n

theorem card_DJ :
    81 ≤ Nat.card DJ := by
  set S := dList (rowP 1) (rowP 3) (rowP 4) (rowP 5)
  have hnd : S.Nodup := CFSG.Decide.nodup_of_bitsetNodup_nat main_parts.1
  have hlen : S.length = 81 := by simp [S, dList]
  have hsub : (fun i : ℕ => eJ i) '' (S.toFinset : Set ℕ) ⊆ (DJ : Set JH) := by
    rintro _ ⟨i, hi, rfl⟩
    exact (dList_mem (List.mem_toFinset.1 hi)).2
  have hinj : Set.InjOn (fun i : ℕ => eJ i) (S.toFinset : Set ℕ) := by
    intro a ha b hb hab
    exact eJ_inj (dList_mem (List.mem_toFinset.1 ha)).1 (dList_mem (List.mem_toFinset.1 hb)).1 hab
  have h := Nat.card_mono (Set.toFinite _) hsub
  rw [Nat.card_image_of_injOn hinj, Finset.coe_sort_coe, Nat.card_eq_finsetCard,
    List.toFinset_card_of_nodup hnd, hlen] at h
  exact h

noncomputable abbrev zJ : JH := pGenJ 5

theorem zJ_eq : zJ = sJ 2 := by
  have hk : FAData.pKernel = FAData.sWords[2]! := by decide +kernel
  rw [zJ, pGenJ, if_neg (by norm_num), sJ, hk]

theorem gen_comm_z
    {j : ℕ} (hj : j < 6) :
    pGenJ j * zJ = zJ * pGenJ j := by
  rcases Nat.lt_or_ge j 5 with h | h
  · rw [zJ_eq, pGenJ, if_pos h]
    exact liftJ_comm (pLift_letters h)
  · obtain rfl : j = 5 := by omega
    rfl

theorem zJ_central :
    ∀ q ∈ PJ, q * zJ = zJ * q := by
  have h : PJ ≤ CJ zJ := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨⟨j, hj⟩, rfl⟩
    exact mem_CJ.2 (gen_comm_z hj).symm
  intro q hq
  exact (mem_CJ.1 (h hq)).symm

theorem wit_get {k : ℕ} (hk : k < 32) :
    witK (WC.getD k 0) (WW.getD k []) (WT.getD k 0) = true := witC.all k hk

theorem wit_conj
    {k : ℕ} (hk : k < 32) (hr : FAData.wRep[WC.getD k 0]! < 729) (ht : WT.getD k 0 < 729) :
    liftJ (WW.getD k []) * eJ FAData.wRep[WC.getD k 0]! = eJ (WT.getD k 0) * liftJ (WW.getD k []) := by
  obtain ⟨-, hl, -, -, hw⟩ := wit_data
  have hwk : ∀ l ∈ WW.getD k [], 1 ≤ l ∧ l ≤ 7 := by
    intro l hl'
    rw [List.getD_eq_getElem _ _ (by rw [hl]; exact hk)] at hl'
    exact hw _ (List.getElem_mem _) l hl'
  have h := wit_get hk
  unfold witK at h
  rw [sbE] at h
  obtain ⟨cW, mW⟩ := liftM_eJ hwk
  obtain ⟨cr, mr⟩ := EM_eJ hr
  obtain ⟨ct, mt⟩ := EM_eJ ht
  have e := congrArg OM' (Nat.eq_of_beq_eq_true h)
  rw [(HNXP.mm_sound cW cr).2, (HNXP.mm_sound ct cW).2, mW, mr, mt, ← matJ_mul,
    ← matJ_mul] at e
  exact matJ_injective e

theorem hn27_local :
    ∃ (z : JH) (R D : Subgroup JH),
      z ^ 3 = 1 ∧ z ≠ 1 ∧ z ∈ PJ ∧ (∀ q ∈ PJ, q * z = z * q) ∧
      CFSG.Assembly.IsElemAbelian 3 D ∧ 81 ≤ Nat.card D ∧
      R ≤ PJ ∧ Nat.card R * 3 = Nat.card PJ ∧
      ∀ s ∈ R, s ^ 3 = 1 → s ∉ Subgroup.zpowers z →
        ∃ g : JH, g * s * g⁻¹ ∈ D ∧ g * z * g⁻¹ ∈ D := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, -, hz0, hwt, hcls⟩ := main_parts
  have hz5 : (5 : ℕ) ∈ [1, 3, 4, 5] := by simp
  have hz1 := itR_spec hz5 1 0 (by norm_num)
  have hz2 := itR_spec hz5 2 0 (by norm_num)
  rw [eJ_zero, mul_one, pow_one] at hz1
  rw [eJ_zero, mul_one] at hz2
  have hzD : zJ ∈ DJ := Subgroup.subset_closure (gen_mem hz5)
  refine ⟨zJ, RJ, DJ, gen_cube hz5, fun h => hz0 ?_, pGen_mem_PJ (by norm_num), zJ_central,
    DJ_elem, card_DJ, RJ_le, by rw [card_RJ, card_PJ], ?_⟩
  · exact eJ_inj hz1.1 (by norm_num) (by rw [hz1.2, eJ_zero]; exact h)
  intro s hsR hs3 hsz
  obtain ⟨i, hi, hli, rfl⟩ := hsR
  have hne1 : eJ i ≠ 1 := fun h => hsz (by rw [h]; exact one_mem _)
  have hne1' : i ≠ itR (rowP 5) 1 0 := fun h => hsz (by
    rw [h, hz1.2]
    exact Subgroup.mem_zpowers _)
  have hne2' : i ≠ itR (rowP 5) 2 0 := fun h => hsz (by
    rw [h, hz2.2]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) 2)
  have hm : markArr[i]! = true := (mark_iff hi).2 (orderOf_eq_prime hs3 hne1)
  obtain ⟨-, -, -, -, -, -, -, -, -, hcov, ht, hw⟩ := sylow_parts
  obtain ⟨hc48, hic⟩ := hcov i hi hm
  obtain ⟨p, hp, hpe⟩ := tree_conj 729 i hi hm (ht i hi hm).1
  set c := labArr[i]!
  have hsz48 : FAData.wClass.size = 48 := by decide +kernel
  have hcW : c ∈ WC := by
    by_contra hcn
    have hcl : c < FAData.wClass.toList.length := by rw [Array.length_toList, hsz48]; exact hc48
    have := clsOK_spec _ 0 hcls c hcl (by rw [zero_add]; exact hcn) i (by
      rw [Array.getElem_toList, ← getElem!_pos]
      exact hic)
    rcases this with h | h | h
    · rw [labZ_of hli] at h
      exact absurd h (by decide)
    · exact hne1' h
    · exact hne2' h
  obtain ⟨hlW, -, hlT, -, -⟩ := wit_data
  obtain ⟨k, hk, hkc⟩ := List.mem_iff_getElem.1 hcW
  rw [hlW] at hk
  have hkc' : WC.getD k 0 = c := by rw [List.getD_eq_getElem _ _ (by rw [hlW]; exact hk), hkc]
  have htm : WT.getD k 0 ∈ dList (rowP 1) (rowP 3) (rowP 4) (rowP 5) :=
    hwt _ (by rw [List.getD_eq_getElem _ _ (by rw [hlT]; exact hk)]; exact List.getElem_mem _)
  obtain ⟨ht7, htD⟩ := dList_mem htm
  have hr7 : FAData.wRep[c]! < 729 := (hw c hc48).1
  have hW := wit_conj hk (by rw [hkc']; exact hr7) ht7
  rw [hkc'] at hW
  obtain ⟨-, hl, -, -, hwl⟩ := wit_data
  have hwk : ∀ l ∈ WW.getD k [], 1 ≤ l ∧ l ≤ 7 := by
    intro l hl'
    rw [List.getD_eq_getElem _ _ (by rw [hl]; exact hk)] at hl'
    exact hwl _ (List.getElem_mem _) l hl'
  set W := liftJ (WW.getD k [])
  refine ⟨W * p⁻¹, ?_, ?_⟩
  · rw [← hpe]
    have e : W * p⁻¹ * (p * eJ FAData.wRep[c]! * p⁻¹) * (W * p⁻¹)⁻¹ =
        W * eJ FAData.wRep[c]! * W⁻¹ := by group
    rw [e, hW, mul_inv_cancel_right]
    exact htD
  · have hpz : p⁻¹ * zJ * p = zJ := by
      rw [mul_assoc, ← zJ_central p hp, ← mul_assoc, inv_mul_cancel, one_mul]
    have hWz : W * zJ * W⁻¹ = zJ := by
      rw [zJ_eq, liftJ_comm hwk, mul_inv_cancel_right]
    have e : W * p⁻¹ * zJ * (W * p⁻¹)⁻¹ = W * (p⁻¹ * zJ * p) * W⁻¹ := by group
    rw [e, hpz, hWz]
    exact hzD

end CertificateChecks.KernelE81.HN27K

end
