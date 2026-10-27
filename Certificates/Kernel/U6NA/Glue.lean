module

public import Certificates.Kernel.U6NA.Checks
public import Certificates.Kernel.U6Three.Checks
public import CFSG.Certificates.Kernel.U6NA.Sound
public import CFSG.Certificates.Kernel.F4NA.Group
public import CFSG.RankThree.PartOne.F106.NoQD32NAU6Tab

set_option linter.unusedSectionVars false

public section

namespace CFSG.KD.U6NA

open CFSG.KC.U6NA CFSG.KC.F4NA CFSG.KC.U6Three CFSG.KC.Loop CFSG.RankThree.PartOne.F106
  CFSG.Assembly.LowTwoRank

theorem tabArr_getD {i : ℕ} (hi : i < 729) :
    u6ThreeCert.tabArr.getD i U6Mon.one = u6ThreeCert.tab i := by
  unfold U6SylowCert.tabArr
  simp [Array.getD, hi]

theorem enc_tab' (i : ℕ) : enc (u6ThreeCert.tab i) = tabN D.TP i :=
  enc_tab ch271061_tab (of_decide_eq_true ch271061_paths) i

theorem l10_eq (X k : ℕ) : l10 X k = Nat.land (Nat.shiftRight X (10 * k)) (2 ^ 10 - 1) := rfl

theorem rtv_eq (a g : ℕ) : u6ThreeCert.rtv a g = l10 RT (6 * a + g) := by
  rw [l10_eq, bind_sound ch271034_rt]
  rfl

theorem invv_eq' (u : ℕ) : u6ThreeCert.invv u = l10 INV u := by
  rw [l10_eq, bind_sound ch271034_inv]
  rfl

abbrev pth (j : ℕ) : List ℕ := u6ThreeCert.paths.getD j []

theorem pw_eq (j : ℕ) : l32 PW j = pwOf (pth j) ∧ (pth j).length ≤ 8 ∧ ∀ g ∈ pth j, g < 8 :=
  pw_sound ch271034_pw j

theorem mulI_eq (i j : ℕ) : mulI RT PW i j = (pth j).foldl u6ThreeCert.rtv i := by
  obtain ⟨h1, h2, h3⟩ := pw_eq j
  obtain ⟨r1, r2⟩ := pwOf_read h2
  unfold mulI
  rw [h1, r1, r2, walk_eq RT _ h3]
  congr 1
  funext a g
  rw [rtv_eq]

theorem tab19 : u6ThreeCert.tab 19 = U6Mon.zc := by
  apply enc_inj
  have h := ch271034_z
  rw [Bool.and_eq_true] at h
  rw [enc_tab']
  exact Nat.eq_of_beq_eq_true h.1

theorem blk_tab (i : ℕ) : decide ((u6ThreeCert.tab i).blk = 0) = blkN (tabN D.TP i) := by
  rw [blkN_enc, enc_tab']

theorem tor_tab (i : ℕ) :
    decide ((u6ThreeCert.tab i).t0 = 0 ∧ (u6ThreeCert.tab i).t1 = 0) = torN (tabN D.TP i) := by
  rw [torN_enc, enc_tab']

theorem trB_tab (i : ℕ) : (u6ThreeCert.tab i).trB = trN (tabN D.TP i) := by
  rw [trN_enc, enc_tab']

theorem blk_arr {i : ℕ} (hi : i < 729) :
    decide ((u6ThreeCert.tabArr.getD i U6Mon.one).blk = 0) = blkN (tabN D.TP i) :=
  (congrArg (fun x => decide (U6Mon.blk x = 0)) (tabArr_getD hi)).trans (blk_tab i)

theorem tor_arr {i : ℕ} (hi : i < 729) :
    decide ((u6ThreeCert.tabArr.getD i U6Mon.one).t0 = 0 ∧
      (u6ThreeCert.tabArr.getD i U6Mon.one).t1 = 0) = torN (tabN D.TP i) :=
  (congrArg (fun x => decide (U6Mon.t0 x = 0 ∧ U6Mon.t1 x = 0)) (tabArr_getD hi)).trans (tor_tab i)

theorem trB_arr {i : ℕ} (hi : i < 729) :
    (u6ThreeCert.tabArr.getD i U6Mon.one).trB = trN (tabN D.TP i) :=
  (congrArg U6Mon.trB (tabArr_getD hi)).trans (trB_tab i)

theorem count_of {p q : ℕ → Bool} {n : ℕ} (hpq : ∀ i < 729, p i = q i)
    (h : Nat.beq (cnt q) n = true) : ((List.range 729).filter p).length = n := by
  rw [List.filter_congr (fun i hi => hpq i (List.mem_range.1 hi)), ← cnt_eq]
  exact Nat.eq_of_beq_eq_true h

theorem dec_ne (i : ℕ) : decide (i ≠ 0) = !Nat.beq i 0 := by
  cases h : Nat.beq i 0
  · have := Nat.ne_of_beq_eq_false h
    simp [this]
  · have := Nat.eq_of_beq_eq_true h
    simp [this]

section Sel

variable {K : Type} [Field K] [CharP K 2] (ω : Cube K) (hK : Nat.card K = (2 ^ 1) ^ 2)
  (hf : u6ThreeCert.Facts)

include ω hK hf

theorem path_lt6 {j : ℕ} (hj : j < 729) : ∀ g ∈ pth j, g < 6 := by
  have hj' : j < u6ThreeCert.paths.length := hf.len ▸ hj
  have hmem : pth j ∈ u6ThreeCert.paths := by
    rw [pth, List.getD_eq_getElem _ _ hj']
    exact List.getElem_mem hj'
  exact hf.path _ hmem

theorem tab0 : u6ThreeCert.tab 0 = U6Mon.one := by
  change U6Mon.evalWord (u6ThreeCert.paths.getD 0 []) = _
  rw [hf.zero]
  rfl

theorem sel_fold : ∀ p : List ℕ, (∀ g ∈ p, g < 6) → ∀ i < 729,
    u6ThreeCert.sel ω hK i * (p.map fun k => ω.mu hK (U6Mon.gen k)).prod =
      u6ThreeCert.sel ω hK (p.foldl u6ThreeCert.rtv i) ∧ p.foldl u6ThreeCert.rtv i < 729
  | [], _, i, hi => ⟨by simp, hi⟩
  | g :: p, h, i, hi => by
    have hg := h g List.mem_cons_self
    obtain ⟨hlt, _⟩ := hf.rt i hi g hg
    obtain ⟨e, l⟩ := sel_fold p (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))
      (u6ThreeCert.rtv i g) hlt
    refine ⟨?_, l⟩
    have hs : ω.mu hK (U6Mon.gen g) = ω.genMu hK g := rfl
    rw [List.map_cons, List.prod_cons, ← mul_assoc, hs, U6SylowCert.sel_rt ω hK hf hi hg,
      List.foldl_cons]
    exact e

theorem sel_mulI {i j : ℕ} (hi : i < 729) (hj : j < 729) :
    u6ThreeCert.sel ω hK i * u6ThreeCert.sel ω hK j = u6ThreeCert.sel ω hK (mulI RT PW i j) ∧
      mulI RT PW i j < 729 := by
  have hs : u6ThreeCert.sel ω hK j = ((pth j).map fun k => ω.mu hK (U6Mon.gen k)).prod :=
    ω.mu_evalWord hK _
  rw [hs, mulI_eq]
  exact sel_fold ω hK hf _ (path_lt6 ω hK hf hj) i hi

theorem tab_mulI {i j : ℕ} (hi : i < 729) (hj : j < 729) :
    (u6ThreeCert.tab i).mul (u6ThreeCert.tab j) = u6ThreeCert.tab (mulI RT PW i j) ∧
      mulI RT PW i j < 729 := by
  obtain ⟨m, l⟩ := sel_mulI ω hK hf hi hj
  exact ⟨(sel_mul_eq_iff (ω := ω) (hK := hK) (c := u6ThreeCert) i j _).1 m, l⟩

theorem cubeB_eq {i : ℕ} (hi : i < 729) : (u6ThreeCert.tab i).cubeB = cubeI RT PW i := by
  obtain ⟨m1, l1⟩ := tab_mulI ω hK hf hi hi
  obtain ⟨m2, l2⟩ := tab_mulI ω hK hf l1 hi
  rw [U6Mon.cubeB, m1, m2, ← tab0 ω hK hf, cubeI, Bool.eq_iff_iff, decide_eq_true_iff, Nat.beq_eq]
  exact ⟨fun h => U6SylowCert.tab_inj hf l2 (by norm_num) h, fun h => by rw [h]⟩

theorem commB_eq {a b : ℕ} (ha : a < 729) (hb : b < 729) :
    U6Mon.commB (u6ThreeCert.tab a) (u6ThreeCert.tab b) = commI RT PW a b := by
  obtain ⟨m1, l1⟩ := tab_mulI ω hK hf ha hb
  obtain ⟨m2, l2⟩ := tab_mulI ω hK hf hb ha
  rw [U6Mon.commB, m1, m2, commI, Bool.eq_iff_iff, decide_eq_true_iff, Nat.beq_eq]
  exact ⟨fun h => U6SylowCert.tab_inj hf l1 l2 h, fun h => by rw [h]⟩

theorem arr_cube {i : ℕ} (hi : i < 729) :
    (u6ThreeCert.tabArr.getD i U6Mon.one).cubeB = cubeI RT PW i :=
  (congrArg U6Mon.cubeB (tabArr_getD hi)).trans (cubeB_eq ω hK hf hi)

theorem arr_comm {a b : ℕ} (ha : a < 729) (hb : b < 729) :
    U6Mon.commB (u6ThreeCert.tabArr.getD a U6Mon.one) (u6ThreeCert.tabArr.getD b U6Mon.one) =
      commI RT PW a b :=
  (congrArg₂ U6Mon.commB (tabArr_getD ha) (tabArr_getD hb)).trans (commB_eq ω hK hf ha hb)

theorem qB_tab {i : ℕ} (hi : i < 729) : (u6ThreeCert.tab i).qB =
    (!trN (tabN D.TP i) && !trN (tabN D.TP (mulI RT PW i 19)) &&
      !trN (tabN D.TP (mulI RT PW (mulI RT PW i 19) 19))) := by
  have hz : (19 : ℕ) < 729 := by norm_num
  obtain ⟨m1, l1⟩ := tab_mulI ω hK hf hi hz
  obtain ⟨m2, l2⟩ := tab_mulI ω hK hf l1 hz
  rw [U6Mon.qB, ← tab19, m1, m2, trB_tab, trB_tab, trB_tab]

theorem comm_sel_iff {a b : ℕ} (ha : a < 729) (hb : b < 729) :
    commI RT PW a b = true ↔
      u6ThreeCert.sel ω hK a * u6ThreeCert.sel ω hK b =
        u6ThreeCert.sel ω hK b * u6ThreeCert.sel ω hK a := by
  rw [sel_comm_iff, commB_eq ω hK hf ha hb]

theorem conj_sel {u x : ℕ} (hu : u < 729) (hx : x < 729) :
    u6ThreeCert.sel ω hK u * u6ThreeCert.sel ω hK x * (u6ThreeCert.sel ω hK u)⁻¹ =
      u6ThreeCert.sel ω hK (conjI RT PW INV u x) ∧ conjI RT PW INV u x < 729 := by
  obtain ⟨m1, l1⟩ := sel_mulI ω hK hf hu hx
  have hinv := (hf.inv u hu).1
  rw [invv_eq'] at hinv
  obtain ⟨m2, l2⟩ := sel_mulI ω hK hf l1 hinv
  refine ⟨?_, l2⟩
  rw [conjI, ← m2, ← m1, ← invv_eq', U6SylowCert.sel_inv ω hK hf hu]

theorem uniq_ok [Finite (StatedProj (StatedSU 6 (2 ^ 1) K))] {i : ℕ} (hi : i < 729)
    (ht : torN (tabN D.TP i) = false) :
    U6SylowCert.uniqOK (fun i => u6ThreeCert.tabArr.getD i U6Mon.one)
      ((List.range 729).filter fun i => (u6ThreeCert.tabArr.getD i U6Mon.one).cubeB) i =
        true := by
  classical
  set C := ((List.range 729).filter fun i => (u6ThreeCert.tabArr.getD i U6Mon.one).cubeB).filter
    fun j => U6Mon.commB (u6ThreeCert.tabArr.getD j U6Mon.one)
      (u6ThreeCert.tabArr.getD i U6Mon.one) with hCdef
  have hmemC : ∀ j, j ∈ C ↔ j < 729 ∧ cubeI RT PW j = true ∧ commI RT PW j i = true := by
    intro j
    simp only [hCdef, List.mem_filter, List.mem_range]
    constructor
    · rintro ⟨⟨hj, h1⟩, h2⟩
      exact ⟨hj, (arr_cube ω hK hf hj).symm.trans h1, (arr_comm ω hK hf hj hi).symm.trans h2⟩
    · rintro ⟨hj, h1, h2⟩
      exact ⟨⟨hj, (arr_cube ω hK hf hj).trans h1⟩, (arr_comm ω hK hf hj hi).trans h2⟩
  obtain ⟨r, hr, rfl⟩ := cov6_sound ch271034_cover i hi ht
  obtain ⟨hx, hus, hnd, hcase⟩ := wit_sound (wits_sound ch271034_wits r hr)
  obtain ⟨S, hS, hmem, -⟩ := table_subgroup (fun k : Fin 6 => ω.genMu hK (k : ℕ))
    (u6ThreeCert.sel ω hK) (U6SylowCert.sel_zero ω hK hf)
    (fun i hi j hj h => U6SylowCert.sel_inj ω hK hf hi hj h)
    (fun i hi => U6SylowCert.sel_mem_closure ω hK hf hi)
    (fun i hi k => ⟨u6ThreeCert.rtv i k, (hf.rt i hi k k.2).1, U6SylowCert.sel_rt ω hK hf hi k.2⟩)
  have hS' : Nat.card S = 729 := by rw [hS]; norm_num
  have hd : ((r.2.1.map (u6ThreeCert.sel ω hK)).map fun u =>
      u * u6ThreeCert.sel ω hK r.1 * u⁻¹).Nodup := by
    rw [List.map_map]
    have e : ∀ u ∈ r.2.1, ((fun u => u * u6ThreeCert.sel ω hK r.1 * u⁻¹) ∘
        u6ThreeCert.sel ω hK) u = u6ThreeCert.sel ω hK (conjI RT PW INV u r.1) :=
      fun u hu => (conj_sel ω hK hf (hus u hu) hx).1
    have e2 : (r.2.1.map fun a => u6ThreeCert.sel ω hK (conjI RT PW INV a r.1)) =
        (r.2.1.map fun a => conjI RT PW INV a r.1).map (u6ThreeCert.sel ω hK) := by
      rw [List.map_map]
      rfl
    rw [List.map_congr_left e, e2]
    refine List.Nodup.map_on (fun a ha b hb h => ?_) hnd
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ha
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hb
    exact U6SylowCert.sel_inj ω hK hf (conj_sel ω hK hf (hus u hu) hx).2
      (conj_sel ω hK hf (hus v hv) hx).2 h
  have hus' : ∀ u ∈ r.2.1.map (u6ThreeCert.sel ω hK), u ∈ S := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hu
    exact hmem v (hus v hv)
  have hCn : C.Nodup := ((List.nodup_range).filter _).filter _
  have hC' : ∀ y ∈ C.toFinset.image (u6ThreeCert.sel ω hK),
      y ∈ S ∧ y * u6ThreeCert.sel ω hK r.1 = u6ThreeCert.sel ω hK r.1 * y := by
    intro y hy
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨hj1, -, hj3⟩ := (hmemC j).1 (List.mem_toFinset.1 hj)
    exact ⟨hmem j hj1, (comm_sel_iff ω hK hf hj1 hx).1 hj3⟩
  obtain ⟨d, hd729, hCd, hdl⟩ := card_le_of_conjs S hS' (hmem _ hx) _ hus' hd _ hC'
  have hcard : (C.toFinset.image (u6ThreeCert.sel ω hK)).card = C.length := by
    rw [Finset.card_image_of_injOn, List.toFinset_card_of_nodup hCn]
    intro a ha b hb h
    exact U6SylowCert.sel_inj ω hK hf ((hmemC a).1 (List.mem_toFinset.1 ha)).1
      ((hmemC b).1 (List.mem_toFinset.1 hb)).1 h
  rw [hcard] at hCd
  rw [List.length_map] at hdl
  obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
    (show d ∣ 3 ^ 6 by norm_num; exact hd729)
  unfold U6SylowCert.uniqOK
  simp only [← hCdef, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
  rcases hcase with h10 | ⟨h4, ha, hb, hca, hcb, hcomma, hcommb, hab⟩
  · rw [h10] at hdl
    have : 3 ^ k ≤ 27 := by interval_cases k <;> omega
    exact ⟨by omega, Or.inl (by omega)⟩
  · rw [h4] at hdl
    have : 3 ^ k ≤ 81 := by interval_cases k <;> omega
    refine ⟨by omega, Or.inr ?_⟩
    rw [List.any_eq_true]
    refine ⟨r.2.2.1, (hmemC _).2 ⟨ha, hca, hcomma⟩, ?_⟩
    rw [List.any_eq_true]
    refine ⟨r.2.2.2, (hmemC _).2 ⟨hb, hcb, hcommb⟩, ?_⟩
    rw [Bool.not_eq_true']
    exact (arr_comm ω hK hf ha hb).trans hab

theorem naCheck_of [Finite (StatedProj (StatedSU 6 (2 ^ 1) K))] : u6ThreeCert.naCheck = true := by
  have hz : u6NaZ < 729 := by decide
  have hz' : (19 : ℕ) < 729 := by norm_num
  have zf := ch271034_z
  rw [Bool.and_eq_true] at zf
  unfold U6SylowCert.naCheck U6SylowCert.naCheckWith
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  refine ⟨count_of (fun i hi => (arr_cube ω hK hf hi).trans (e3_sound ch271034_e3 i hi).symm)
      ch271034_cE3,
    count_of (fun i hi => blk_arr hi) ch271034_cblk, ?_, by decide, ?_,
    fun h => absurd (congrArg enc h) (by decide), hz, (tabArr_getD hz).trans tab19,
    (trN_enc U6Mon.one).trans ((congrArg trN enc_one).trans rfl), ?_,
    count_of (fun i hi => congrArg₂ (· && ·) (blk_arr hi)
      ((congrArg U6Mon.qB (tabArr_getD hi)).trans (qB_tab ω hK hf hi))) ch271034_cq,
    count_of (fun i hi => tor_arr hi) ch271034_ctor,
    count_of (fun i hi => congrArg₂ (· && ·) (congrArg₂ (· && ·) (tor_arr hi) (dec_ne i))
      (trB_arr hi)) ch271034_ctr, ?_⟩
  · rw [List.all_eq_true]
    intro i hi
    have hi' := List.mem_range.1 hi
    have h := allBelow_sound ch271034_blk3 (by norm_num) i hi'
    have e2 : (u6ThreeCert.tabArr.getD i U6Mon.one).cubeB = bt E3 i :=
      (arr_cube ω hK hf hi').trans (e3_sound ch271034_e3 i hi').symm
    refine (congrArg₂ (fun a b => (!a || b)) (blk_arr hi') e2).trans ?_
    revert h
    cases blkN (tabN D.TP i) <;> intro h
    · rfl
    · exact h
  · exact (congrArg U6Mon.cubeB tab19.symm).trans
      ((cubeB_eq ω hK hf hz').trans ((e3_sound ch271034_e3 _ hz').symm.trans zf.2))
  · rw [List.all_eq_true]
    intro i hi
    have hi' := List.mem_range.1 hi
    exact (congrArg₂ U6Mon.commB (tabArr_getD hi') tab19.symm).trans
      ((commB_eq ω hK hf hi' hz').trans (allBelow_sound ch271034_cent (by norm_num) i hi'))
  · rw [List.all_eq_true]
    intro i hi
    have hi' := List.mem_range.1 hi
    rw [Bool.or_eq_true]
    cases ht : torN (tabN D.TP i)
    · exact Or.inr (uniq_ok ω hK hf hi' ht)
    · exact Or.inl ((tor_arr hi').trans ht)

end Sel

theorem naCheck_true (hf : u6ThreeCert.Facts) : u6ThreeCert.naCheck = true := by
  have hK : Nat.card (GaloisField 2 2) = (2 ^ 1) ^ 2 := by
    simp [Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num : (2 : ℕ) ≠ 0)]
  obtain ⟨ω⟩ := exists_cube (K := GaloisField 2 2) (by rw [hK]; norm_num)
  have : Finite (Matrix (Fin 6) (Fin 6) (GaloisField 2 2)) :=
    inferInstanceAs (Finite (Fin 6 → Fin 6 → GaloisField 2 2))
  have : Finite (GL (Fin 6) (GaloisField 2 2)) :=
    Finite.of_injective (fun g : GL (Fin 6) (GaloisField 2 2) =>
      (g : Matrix (Fin 6) (Fin 6) (GaloisField 2 2))) fun _ _ h => Units.ext h
  have : Finite (StatedProj (StatedSU 6 (2 ^ 1) (GaloisField 2 2))) :=
    Finite.of_surjective _ QuotientGroup.mk_surjective
  exact naCheck_of ω hK hf

end CFSG.KD.U6NA

end
