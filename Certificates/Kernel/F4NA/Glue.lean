module

public import Certificates.Kernel.F4NA.Checks
public import CFSG.Certificates.Kernel.F4NA.Sound
public import CFSG.Certificates.Kernel.F4NA.Group
public import CFSG.RankThree.PartOne.F106.F4Three
public import CFSG.RankThree.PartOne.F106.NoQD32NAF4Facts
public import CFSG.RankThree.PartOne.F106.NoQD32NAGen
public import CFSG.RankThree.PartOne.F106.QD32Center

set_option linter.unusedSectionVars false

public section

namespace CFSG.KD.F4NA

open CFSG.KC.F4NA CFSG.KC.F4Salt CFSG.RankThree.PartOne.F106 CFSG.LieType.Simplicity.TitsBits
  CFSG.RankThree.PartOne.SEITZX CFSG.Blueprint.Chevalley CFSG.LieType.Ree CFSG.LieType.Chevalley
  CFSG.Blueprint

theorem getD_toArray (l : List ℕ) (i : ℕ) : l.toArray.getD i 0 = l.getD i 0 := by
  simp only [Array.getD, List.size_toArray, List.getElem_toArray, List.getD_eq_getElem?_getD]
  split
  · simp_all [List.getElem?_eq_getElem]
  · simp_all [List.getElem?_eq_none]

theorem tb_eq (i : ℕ) : f4ThreeCert.tabArr.getD i 0 = f4ThreeCert.tab.getD i 0 :=
  getD_toArray _ i

theorem l10_eq (X k : ℕ) : l10 X k = Nat.land (Nat.shiftRight X (10 * k)) (2 ^ 10 - 1) := rfl

theorem rtv_eq (a g : ℕ) : f4ThreeCert.rtv a g = l10 RT (6 * a + g) := by
  rw [l10_eq, bind_sound ch271035_rt]
  rfl

theorem invv_eq (u : ℕ) : f4ThreeCert.invv u = l10 INV u := by
  rw [l10_eq, bind_sound ch271035_inv]
  rfl

abbrev pth (j : ℕ) : List ℕ := f4ThreeCert.paths.getD j []

theorem pw_eq (j : ℕ) : l32 PW j = pwOf (pth j) ∧ (pth j).length ≤ 8 ∧ ∀ g ∈ pth j, g < 8 :=
  pw_sound ch271035_pw j

theorem mulI_eq (i j : ℕ) : mulI RT PW i j = (pth j).foldl f4ThreeCert.rtv i := by
  obtain ⟨h1, h2, h3⟩ := pw_eq j
  obtain ⟨r1, r2⟩ := pwOf_read h2
  unfold mulI
  rw [h1, r1, r2, walk_eq RT _ h3]
  congr 1
  funext a g
  rw [rtv_eq]

section Sel

variable (hf : f4ThreeCert.Facts)

include hf

local notation "sl" => f4ThreeCert.sel (X := ZMod 2)

theorem path_lt6 {j : ℕ} (hj : j < 729) : ∀ g ∈ pth j, g < 6 :=
  hf.path _ (path_mem hf hj)

theorem sel_fold : ∀ p : List ℕ, (∀ g ∈ p, g < 6) → ∀ i < 729,
    sl i * (p.map (f4ThreeCert.gen (X := ZMod 2))).prod = sl (p.foldl f4ThreeCert.rtv i) ∧
      p.foldl f4ThreeCert.rtv i < 729
  | [], _, i, hi => ⟨by simp, hi⟩
  | g :: p, h, i, hi => by
    have hg := h g List.mem_cons_self
    obtain ⟨hlt, _⟩ := hf.rt i hi g hg
    obtain ⟨e, l⟩ := sel_fold p (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))
      (f4ThreeCert.rtv i g) hlt
    refine ⟨?_, l⟩
    rw [List.map_cons, List.prod_cons, ← mul_assoc, sel_rt hf hi hg, List.foldl_cons]
    exact e

theorem sel_mulI {i j : ℕ} (hi : i < 729) (hj : j < 729) :
    sl i * sl j = sl (mulI RT PW i j) ∧ mulI RT PW i j < 729 := by
  rw [mulI_eq]
  exact sel_fold hf _ (path_lt6 hf hj) i hi

theorem hasBits_tb {i : ℕ} (hi : i < 729) :
    HasBits (ZMod 2) (sl i) (f4ThreeCert.tabArr.getD i 0) := by
  rw [tb_eq]
  exact hasBits_sel hf hi

theorem sel_eq_one_iff {k : ℕ} (hk : k < 729) : sl k = 1 ↔ k = 0 := by
  constructor
  · intro h
    exact sel_inj hf hk (by norm_num) (h.trans (sel_zero hf).symm)
  · rintro rfl
    exact sel_zero hf

theorem cubeF_eq {i : ℕ} (hi : i < 729) :
    cubeF (fun i => f4ThreeCert.tabArr.getD i 0) i = cubeI RT PW i := by
  have H := ((hasBits_tb hf hi).mul (hasBits_tb hf hi)).mul (hasBits_tb hf hi)
  have e := H.eq_iff (hasBits_one (K := ZMod 2))
  obtain ⟨m1, l1⟩ := sel_mulI hf hi hi
  obtain ⟨m2, l2⟩ := sel_mulI hf l1 hi
  rw [Bool.eq_iff_iff, cubeF, decide_eq_true_eq, ← e, cubeI, Nat.beq_eq, m1, m2,
    sel_eq_one_iff hf l2]

theorem commF_eq {a b : ℕ} (ha : a < 729) (hb : b < 729) :
    commF (fun i => f4ThreeCert.tabArr.getD i 0) a b = commI RT PW a b := by
  have H1 := (hasBits_tb hf ha).mul (hasBits_tb hf hb)
  have H2 := (hasBits_tb hf hb).mul (hasBits_tb hf ha)
  have e := H1.eq_iff H2
  obtain ⟨m1, l1⟩ := sel_mulI hf ha hb
  obtain ⟨m2, l2⟩ := sel_mulI hf hb ha
  rw [Bool.eq_iff_iff, commF, decide_eq_true_eq, ← e, commI, Nat.beq_eq, m1, m2]
  exact ⟨fun h => sel_inj hf l1 l2 h, fun h => by rw [h]⟩

theorem comm_sel_iff {a b : ℕ} (ha : a < 729) (hb : b < 729) :
    commI RT PW a b = true ↔ sl a * sl b = sl b * sl a := by
  obtain ⟨m1, l1⟩ := sel_mulI hf ha hb
  obtain ⟨m2, l2⟩ := sel_mulI hf hb ha
  rw [commI, Nat.beq_eq, m1, m2]
  exact ⟨fun h => by rw [h], fun h => sel_inj hf l1 l2 h⟩

omit hf in
theorem gen_lane {g : ℕ} (hg : g < 6) : l32 PW (g + 1) = 1 + 16 * g ∧
    dataS (lS MSP (g + 1)) = f4ThreeCert.genBits g % 2 ^ 2704 := by
  have key : ∀ g < 6, genB PW MSP g (GW.getD g (0, 0)).1 (GW.getD g (0, 0)).2 = true := by
    intro g hg
    interval_cases g
    exacts [ch271035_g0, ch271035_g1, ch271035_g2, ch271035_g3, ch271035_g4, ch271035_g5]
  obtain ⟨h1, h2⟩ := gen_sound (key g hg)
  refine ⟨h1, ?_⟩
  rw [h2, gw_sound ch271035_gw g]
  rfl

omit hf in
theorem enc8_append : ∀ (l : List ℕ) (g : ℕ), enc8 (l ++ [g]) = enc8 l + g * 8 ^ l.length
  | [], g => by simp [enc8]
  | v :: l, g => by
    rw [List.cons_append, enc8_cons, enc8_cons, enc8_append l g, List.length_cons, pow_succ]
    ring

omit hf in
theorem enc8_inj : ∀ (a b : List ℕ), a.length = b.length → (∀ x ∈ a, x < 8) → (∀ x ∈ b, x < 8) →
    enc8 a = enc8 b → a = b
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, h, _, _, _ => by simp at h
  | _ :: _, [], h, _, _, _ => by simp at h
  | v :: a, w :: b, h, ha, hb, he => by
    rw [enc8_cons, enc8_cons] at he
    have hv := ha v List.mem_cons_self
    have hw := hb w List.mem_cons_self
    have e1 : v = w := by omega
    have e2 : enc8 a = enc8 b := by omega
    rw [e1, enc8_inj a b (by simpa using h) (fun x hx => ha x (List.mem_cons_of_mem _ hx))
      (fun x hx => hb x (List.mem_cons_of_mem _ hx)) e2]

omit hf in
theorem edge_all {j : ℕ} (h1 : 0 < j) (h2 : j < 729) : edgeB PW PAR MSP j = true := by
  have e : ∀ {lo n : ℕ}, edgesB PW PAR MSP lo n = true → lo ≤ j → j < lo + n →
      edgeB PW PAR MSP j = true := by
    intro lo n h hl hn
    have := edges_sound h (j - lo) (by omega)
    rwa [show lo + (j - lo) = j by omega] at this
  rcases (show j < 92 ∨ (92 ≤ j ∧ j < 183) ∨ (183 ≤ j ∧ j < 274) ∨ (274 ≤ j ∧ j < 365) ∨
      (365 ≤ j ∧ j < 456) ∨ (456 ≤ j ∧ j < 547) ∨ (547 ≤ j ∧ j < 638) ∨ 638 ≤ j by omega) with
    h | h | h | h | h | h | h | h
  · exact e ch271035_e0 (by omega) (by omega)
  · exact e ch271035_e1 (by omega) (by omega)
  · exact e ch271035_e2 (by omega) (by omega)
  · exact e ch271035_e3' (by omega) (by omega)
  · exact e ch271035_e4 (by omega) (by omega)
  · exact e ch271035_e5 (by omega) (by omega)
  · exact e ch271035_e6 (by omega) (by omega)
  · exact e ch271035_e7 (by omega) (by omega)

theorem tree : ∀ j < 729, dataS (lS MSP j) = f4ThreeCert.tabArr.getD j 0 % 2 ^ 2704 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hj
  rcases Nat.eq_zero_or_pos j with rfl | hpos
  · have h := ch271035_one
    rw [Bool.and_eq_true, eqS_iff] at h
    have e0 : pathBits f4ThreeCert.gbList [] = oneBits := rfl
    have e1 : oneS = saltOf oneBits := rfl
    rw [h.2, tb_eq, tab_getD hf hj, hf.zero, e0, e1, dataS_saltOf]
  · have hp15 : Nat.land (l32 PW (l10 PAR j)) 15 < 15 := by
      obtain ⟨w1, w2, -⟩ := pw_eq (l10 PAR j)
      rw [w1, (pwOf_read w2).2]
      omega
    obtain ⟨g, hg8, hp, hlen, hcode, hdata⟩ := edge_sound (edge_all hpos hj) hp15
    set p := l10 PAR j with hpdef
    have hp729 : p < 729 := by omega
    obtain ⟨wj, lj, cj⟩ := pw_eq j
    obtain ⟨wp, lp, cp⟩ := pw_eq p
    obtain ⟨rj1, rj2⟩ := pwOf_read lj
    obtain ⟨rp1, rp2⟩ := pwOf_read lp
    rw [wj, wp, rj2, rp2] at hlen
    rw [wj, wp, rj1, rp1, rp2] at hcode
    have hpath : pth j = pth p ++ [g] := by
      refine enc8_inj _ _ (by rw [List.length_append, hlen]; rfl) cj ?_ ?_
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact cp x hx
        · rw [List.mem_singleton.1 hx]
          exact hg8
      · rw [hcode, enc8_append]
    have hg6 : g < 6 := path_lt6 hf hj g (by rw [hpath]; simp)
    have hs : sl j = sl p * f4ThreeCert.gen (X := ZMod 2) g := by
      change ((pth j).map (f4ThreeCert.gen (X := ZMod 2))).prod =
        ((pth p).map (f4ThreeCert.gen (X := ZMod 2))).prod * f4ThreeCert.gen (X := ZMod 2) g
      rw [hpath, List.map_append, List.prod_append]
      simp
    have H := (hasBits_tb hf hp729).mul (hasBits_gen (X := ZMod 2) f4ThreeCert g)
    rw [← hs] at H
    have e := (H.eq_iff (hasBits_tb hf hj)).1 rfl
    rw [hdata, ih p (by omega) hp729, (gen_lane hg6).2, mul_mod_left, mul_mod_right, e]

omit hf in
theorem foldr_mod (A : ℕ) : ∀ l : List ℕ, (∀ p ∈ l, p < 52) →
    l.foldr (fun p b => xor (A.testBit (52 * p + p)) b) false =
      l.foldr (fun p b => xor ((A % 2 ^ 2704).testBit (52 * p + p)) b) false
  | [], _ => rfl
  | p :: l, hl => by
    rw [List.foldr_cons, List.foldr_cons,
      foldr_mod A l (fun q hq => hl q (List.mem_cons_of_mem _ hq)), Nat.testBit_mod_two_pow]
    have := hl p List.mem_cons_self
    rw [decide_eq_true (by omega : 52 * p + p < 2704), Bool.true_and]

omit hf in
theorem trIB_mod (A : ℕ) : trIB A = trIB (A % 2 ^ 2704) := by
  have hpos : ∀ p ∈ f4ShortPos, p < 52 := by decide
  unfold trIB
  exact foldr_mod A _ hpos

omit hf in
theorem tr_lane {i : ℕ} (hi : i < 729) : bt TR i = trS f4ShortPos (lS MSP i) := by
  rcases (show i < 243 ∨ (243 ≤ i ∧ i < 486) ∨ 486 ≤ i by omega) with h | h | h
  · simpa using tr_sound ch271035_tr0 i h
  · have := tr_sound ch271035_tr1 (i - 243) (by omega)
    rwa [show 243 + (i - 243) = i by omega] at this
  · have := tr_sound ch271035_tr2 (i - 486) (by omega)
    rwa [show 486 + (i - 486) = i by omega] at this

theorem trace_of {A k : ℕ} (hk : k < 729) (h : HasBits (ZMod 2) (sl k) A) :
    trIB A = bt TR k := by
  have e := (h.eq_iff (hasBits_tb hf hk)).1 rfl
  rw [trIB_mod, e, ← tree hf k hk, ← trS_eq, tr_lane hk]

theorem trace_tb {i : ℕ} (hi : i < 729) : trIB (f4ThreeCert.tabArr.getD i 0) = bt TR i :=
  trace_of hf hi (hasBits_tb hf hi)

theorem wt_eq (w : List ℕ) (k : ℕ) (hb : bindB 2 (pk 2 w) w = true)
    (hw : wtB PW WT (pk 2 w) k = true) {i : ℕ} (hi : i < 729) :
    f4ThreeCert.wt w i = l2 WT i k := by
  obtain ⟨w1, w2, w3⟩ := pw_eq i
  obtain ⟨r1, r2⟩ := pwOf_read w2
  rw [wt_sound hw i hi, w1, r1, r2, wsum_eq _ _ w3]
  unfold F4SylowCert.wt
  congr 2
  refine List.map_congr_left fun g _ => ?_
  have := bind_sound hb g
  exact this.symm

theorem homOK_of (w : List ℕ) (k : ℕ) (hb : bindB 2 (pk 2 w) w = true)
    (hw : wtB PW WT (pk 2 w) k = true) (hh : homB RT WT (pk 2 w) k = true) :
    f4ThreeCert.homOK w = true := by
  rw [F4SylowCert.homOK_iff]
  intro i hi g hg
  rw [wt_eq hf w k hb hw (hf.rt i hi g hg).1, wt_eq hf w k hb hw hi, rtv_eq, hom_sound hh i hi g hg]
  have := bind_sound hb g
  rw [show Nat.land (Nat.shiftRight (pk 2 w) (2 * g)) 3 = w.getD g 0 from this]

omit hf in
theorem finite_adj : Finite (adjointGroup ReeTag.F4.tag (ZMod 2)) := by
  have : Finite (Module.End (ZMod 2) (RootModule ReeTag.F4.tag (ZMod 2))) :=
    Module.finite_of_finite (ZMod 2)
  infer_instance

theorem conj_sel {u x : ℕ} (hu : u < 729) (hx : x < 729) :
    sl u * sl x * (sl u)⁻¹ = sl (conjI RT PW INV u x) ∧ conjI RT PW INV u x < 729 := by
  obtain ⟨m1, l1⟩ := sel_mulI hf hu hx
  have hinv := (hf.inv u hu).1
  rw [invv_eq] at hinv
  obtain ⟨m2, l2⟩ := sel_mulI hf l1 hinv
  refine ⟨?_, l2⟩
  rw [conjI, ← m2, ← m1, ← invv_eq, sel_inv hf hu]

theorem uniq_ok {i : ℕ} (hi : i < 729) (hc : cubeI RT PW i = true)
    (hw : ¬ (l2 WT i 0 = 0 ∧ l2 WT i 3 = 0)) :
    uniqF (fun i => f4ThreeCert.tabArr.getD i 0)
      ((List.range 729).filter fun i => cubeF (fun i => f4ThreeCert.tabArr.getD i 0) i) i =
        true := by
  classical
  have := finite_adj
  set tb : ℕ → ℕ := fun i => f4ThreeCert.tabArr.getD i 0 with htb
  set C := ((List.range 729).filter fun i => cubeF tb i).filter fun j => commF tb j i with hCdef
  have hmemC : ∀ j, j ∈ C ↔ j < 729 ∧ cubeI RT PW j = true ∧ commI RT PW j i = true := by
    intro j
    simp only [hCdef, List.mem_filter, List.mem_range]
    constructor
    · rintro ⟨⟨hj, h1⟩, h2⟩
      exact ⟨hj, (cubeF_eq hf hj).symm.trans h1, (commF_eq hf hj hi).symm.trans h2⟩
    · rintro ⟨hj, h1, h2⟩
      exact ⟨⟨hj, (cubeF_eq hf hj).trans h1⟩, (commF_eq hf hj hi).trans h2⟩
  have hE3 : bt E3 i = true := by rw [e3_sound ch271035_e3 i hi]; exact hc
  obtain ⟨r, hr, rfl⟩ := cover_sound ch271035_cover i hi hE3 hw
  obtain ⟨hx, hus, hnd, hcase⟩ := wit_sound (wits_sound ch271035_wits r hr)
  obtain ⟨S, hS, hmem, -⟩ := table_subgroup (fun k : Fin 6 => f4ThreeCert.gen (X := ZMod 2) k)
    (f4ThreeCert.sel (X := ZMod 2)) (sel_zero hf) (fun i hi j hj h => sel_inj hf hi hj h)
    (fun i hi => sel_mem_closure hf hi)
    (fun i hi k => ⟨f4ThreeCert.rtv i k, (hf.rt i hi k k.2).1, sel_rt hf hi k.2⟩)
  have hS' : Nat.card S = 729 := by rw [hS]; norm_num
  have hd : ((r.2.1.map sl).map fun u => u * sl r.1 * u⁻¹).Nodup := by
    rw [List.map_map]
    have e : ∀ u ∈ r.2.1, ((fun u => u * sl r.1 * u⁻¹) ∘ sl) u =
        sl (conjI RT PW INV u r.1) := fun u hu => (conj_sel hf (hus u hu) hx).1
    have e2 : (r.2.1.map fun a => sl (conjI RT PW INV a r.1)) =
        (r.2.1.map fun a => conjI RT PW INV a r.1).map sl := by
      rw [List.map_map]
      rfl
    rw [List.map_congr_left e, e2]
    refine List.Nodup.map_on (fun a ha b hb h => ?_) hnd
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ha
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hb
    exact sel_inj hf (conj_sel hf (hus u hu) hx).2 (conj_sel hf (hus v hv) hx).2 h
  have hus' : ∀ u ∈ r.2.1.map sl, u ∈ S := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hu
    exact hmem v (hus v hv)
  have hCn : C.Nodup := ((List.nodup_range).filter _).filter _
  have hC' : ∀ y ∈ C.toFinset.image sl, y ∈ S ∧ y * sl r.1 = sl r.1 * y := by
    intro y hy
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨hj1, -, hj3⟩ := (hmemC j).1 (List.mem_toFinset.1 hj)
    exact ⟨hmem j hj1, (comm_sel_iff hf hj1 hx).1 hj3⟩
  obtain ⟨d, hd729, hCd, hdl⟩ := card_le_of_conjs S hS' (hmem _ hx) _ hus' hd _ hC'
  have hcard : (C.toFinset.image sl).card = C.length := by
    rw [Finset.card_image_of_injOn, List.toFinset_card_of_nodup hCn]
    intro a ha b hb h
    exact sel_inj hf ((hmemC a).1 (List.mem_toFinset.1 ha)).1
      ((hmemC b).1 (List.mem_toFinset.1 hb)).1 h
  rw [hcard] at hCd
  rw [List.length_map] at hdl
  obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
    (show d ∣ 3 ^ 6 by norm_num; exact hd729)
  unfold uniqF
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
    rw [commF_eq hf ha hb, hab]
    rfl

omit hf in
theorem nat_beq (a b : ℕ) : (a == b) = Nat.beq a b := by
  cases h : Nat.beq a b
  · have := Nat.ne_of_beq_eq_false h
    simp [this]
  · have := Nat.eq_of_beq_eq_true h
    simp [this]

omit hf in
theorem dec_ne (i : ℕ) : decide (i ≠ 0) = !Nat.beq i 0 := by
  cases h : Nat.beq i 0
  · have := Nat.ne_of_beq_eq_false h
    simp [this]
  · have := Nat.eq_of_beq_eq_true h
    simp [this]

omit hf in
theorem count_of {p q : ℕ → Bool} {n : ℕ} (hpq : ∀ i < 729, p i = q i) (h : Nat.beq (cnt q) n = true) :
    ((List.range 729).filter p).length = n := by
  rw [List.filter_congr (fun i hi => hpq i (List.mem_range.1 hi)), ← cnt_eq]
  exact Nat.eq_of_beq_eq_true h

theorem wtA {i : ℕ} (hi : i < 729) : f4ThreeCert.wt f4WA i = l2 WT i 0 :=
  wt_eq hf f4WA 0 (by decide) ch271035_wtA hi
theorem wtB' {i : ℕ} (hi : i < 729) : f4ThreeCert.wt f4WB i = l2 WT i 1 :=
  wt_eq hf f4WB 1 (by decide) ch271035_wtB hi
theorem wtC {i : ℕ} (hi : i < 729) : f4ThreeCert.wt f4WC i = l2 WT i 2 :=
  wt_eq hf f4WC 2 (by decide) ch271035_wtC hi
theorem wtY {i : ℕ} (hi : i < 729) : f4ThreeCert.wt f4WY2 i = l2 WT i 3 :=
  wt_eq hf f4WY2 3 (by decide) ch271035_wtY hi

theorem qF_eq {i : ℕ} (hi : i < 729) : qF (fun i => f4ThreeCert.tabArr.getD i 0) i =
    (!bt TR i && !bt TR (mulI RT PW i f4NaZ) &&
      !bt TR (mulI RT PW (mulI RT PW i f4NaZ) f4NaZ)) := by
  have hz : f4NaZ < 729 := by decide
  obtain ⟨m1, l1⟩ := sel_mulI hf hi hz
  obtain ⟨m2, l2⟩ := sel_mulI hf l1 hz
  have H1 := (hasBits_tb hf hi).mul (hasBits_tb hf hz)
  rw [m1] at H1
  have H2 := H1.mul (hasBits_tb hf hz)
  rw [m2] at H2
  unfold qF
  rw [trace_tb hf hi, trace_of hf l1 H1, trace_of hf l2 H2]

theorem cent_all {k z : ℕ} (hz : z < 729) (h : centB RT PW WT k z = true) (w : List ℕ)
    (hw : ∀ j < 729, f4ThreeCert.wt w j = l2 WT j k) :
    ((List.range 729).all fun j =>
      f4ThreeCert.wt w j != 0 || commF (fun i => f4ThreeCert.tabArr.getD i 0) z j) = true := by
  rw [List.all_eq_true]
  intro j hj
  have hj' := List.mem_range.1 hj
  rw [hw j hj', commF_eq hf hz hj', Bool.or_eq_true, bne_iff_ne, ne_eq]
  by_cases h0 : l2 WT j k = 0
  · exact Or.inr (cent_sound h j hj' h0)
  · exact Or.inl h0

theorem naCheck_true : f4ThreeCert.naCheck = true := by
  have hz : f4NaZ < 729 := by decide
  have zbf := ch271035_zbf
  simp only [Bool.and_eq_true, Nat.beq_eq] at zbf
  obtain ⟨⟨zb1, zb2⟩, zb3⟩ := zbf
  unfold F4SylowCert.naCheck F4SylowCert.naCheckWith
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  refine ⟨homOK_of hf f4WA 0 (by decide) ch271035_wtA ch271035_homA,
    homOK_of hf f4WB 1 (by decide) ch271035_wtB ch271035_homB,
    homOK_of hf f4WC 2 (by decide) ch271035_wtC ch271035_homC,
    homOK_of hf f4WY2 3 (by decide) ch271035_wtY ch271035_homY, ?_,
    count_of (fun i hi => by rw [wtA hf hi, nat_beq]) ch271035_cA,
    count_of (fun i hi => by rw [wtB' hf hi, nat_beq]) ch271035_cB,
    count_of (fun i hi => by rw [wtC hf hi, nat_beq]) ch271035_cC,
    count_of (fun i hi => by rw [wtA hf hi, wtY hf hi, nat_beq, nat_beq]) ch271035_cE0,
    by rw [wtB' hf hz, zb1]; rfl, by decide,
    by rw [cubeF_eq hf hz, ← e3_sound ch271035_e3 _ hz]; exact zb2,
    cent_all hf hz ch271035_zb f4WB (fun j hj => wtB' hf hj),
    by rw [trace_tb hf hz]; exact zb3,
    by decide, by decide, ?_, by decide, by decide, ?_,
    count_of (fun i hi => by rw [wtB' hf hi, nat_beq, qF_eq hf hi]) ch271035_cQ,
    count_of (fun i hi => by rw [wtA hf hi, wtY hf hi, nat_beq, nat_beq, dec_ne,
      trace_tb hf hi]) ch271035_cA0, ?_⟩
  · rw [List.all_eq_true]
    intro i hi
    have hi' := List.mem_range.1 hi
    rw [cubeF_eq hf hi', wtA hf hi', wtB' hf hi', wtC hf hi', ← e3_sound ch271035_e3 _ hi']
    rw [beq_iff_eq, Bool.eq_iff_iff, cubeWt_sound ch271035_cw i hi', Bool.or_eq_true,
      Bool.or_eq_true, beq_iff_eq, beq_iff_eq, beq_iff_eq, or_assoc]
  · rw [List.all_eq_true]
    intro z hz'
    have h1 := listAnd_sound (fun z => Nat.blt z 729 && Nat.beq (l2 WT z 0) 0) _ ch271035_zaw z hz'
    have h2 := listAnd_sound (fun z => centB RT PW WT 0 z) _ ch271035_za z hz'
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h1
    rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, wtA hf h1.1, h1.2]
    exact ⟨⟨h1.1, rfl⟩, cent_all hf h1.1 h2 f4WA (fun j hj => wtA hf hj)⟩
  · rw [List.all_eq_true]
    intro z hz'
    have h1 := listAnd_sound (fun z => Nat.blt z 729 && Nat.beq (l2 WT z 2) 0) _ ch271035_zcw z hz'
    have h2 := listAnd_sound (fun z => centB RT PW WT 2 z) _ ch271035_zc z hz'
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h1
    rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, wtC hf h1.1, h1.2]
    exact ⟨⟨h1.1, rfl⟩, cent_all hf h1.1 h2 f4WC (fun j hj => wtC hf hj)⟩
  · rw [List.all_eq_true]
    intro i hi
    have hi' := List.mem_range.1 hi
    rw [Bool.or_eq_true, Bool.or_eq_true]
    by_cases hc : cubeI RT PW i = true
    · by_cases hw : l2 WT i 0 = 0 ∧ l2 WT i 3 = 0
      · left; right
        rw [wtA hf hi', wtY hf hi', hw.1, hw.2]
        rfl
      · right
        exact uniq_ok hf hi' hc hw
    · left; left
      rw [cubeF_eq hf hi']
      simpa using hc

end Sel

end CFSG.KD.F4NA

end
