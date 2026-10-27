module

public import CFSG.YGroups.Y442Twist.Letters
public import CFSG.Certificates.Kernel.TwistDce.Orbit
public import Certificates.Kernel.YChain.Step
public import Certificates.Kernel.YChain.Tables.YCh10
public import Certificates.Kernel.Y442.Orb0
public import Certificates.Kernel.Y442.Orb1
public import Certificates.Kernel.Y442.Orb2

public section

namespace CertificateChecks.KernelY442

open CFSG.YGroups CFSG.YGroups.Y442Tw CFSG.KC CFSG.KC.YModel CFSG.KC.Benes CFSG.KC.MonsterConv.Perm
  CFSG.Certificates.TwDce CFSG.Certificates.CosetEnumeration CFSG.Certificates CFSG.Certificates.KB

theorem rho_yGen_apply {c : ℕ} (hc : c < 10) (x : Fin 31671) :
    (rho432F (yGen 4 3 2 c) x : ℕ) = fieldAt 32 (CFSG.KD.YM432P.F c) x := by
  rw [← rho432F_rep hc x, KernelYModel.y432F_arrays_eq, getElem_linesA' hc x.2]

theorem net_spec {c : ℕ} (hc : c < 10) :
    StagesValid 15 (CFSG.KD.YMY432F.Nf c) ∧
      (∀ x : Fin 31671, benesPerm 15 (CFSG.KD.YMY432F.Nf c) x = (rho432F (yGen 4 3 2 c) x : ℕ)) ∧
      ∀ p, 31671 ≤ p → p < 2 ^ 15 → benesPerm 15 (CFSG.KD.YMY432F.Nf c) p = p := by
  obtain ⟨-, hv, hent, hfix⟩ := Sem.letOK_spec (by decide) (KernelYModel.y432F_let c hc)
  exact ⟨hv, fun x => by rw [rho_yGen_apply hc, hent x x.2], hfix⟩

theorem rho_evalWord_apply :
    ∀ (w : List ℕ), (∀ c ∈ w, c < 10) → ∀ x : Fin 31671,
      (rho432F (evalWord (yGen 4 3 2) w) x : ℕ) = w.foldr (fun c p => fieldAt 32 (CFSG.KD.YM432P.F c) p) x
  | [], _, x => by simp
  | c :: w, hw, x => by
    rw [evalWord_cons, map_mul, Equiv.Perm.mul_apply, List.foldr_cons,
      ← rho_evalWord_apply w (fun c' hc' => hw c' (List.mem_cons_of_mem _ hc')) x,
      rho_yGen_apply (hw c List.mem_cons_self)]

theorem orb_card {L : List ℕ} (hL : ∀ c ∈ L, c < 10)
    {b R M o : ℕ} (hb : b < 31671) (h : orbitOK 15 (L.map CFSG.KD.YMY432F.Nf) b R M = true)
    (hp : Nat.beq (popc 15 M) o = true) :
    o ≤ (MulAction.orbit (lgen rho432F (yGen 4 3 2) L) (⟨b, hb⟩ : Fin 31671)).ncard := by
  rw [← Nat.eq_of_beq_eq_true hp]
  exact le_ncard_orbit_of_orbitOK (fun c hc => (net_spec (hL c hc)).1)
    (fun c hc => (net_spec (hL c hc)).2.1) (fun c hc => (net_spec (hL c hc)).2.2) hb (by norm_num) h

theorem orb_mem {L : List ℕ} (hL : ∀ c ∈ L, c < 10)
    {b R M : ℕ} (hb : b < 31671) (h : orbitOK 15 (L.map CFSG.KD.YMY432F.Nf) b R M = true) :
    ∀ p, M.testBit p = true → ∃ hp : p < 31671,
      (⟨p, hp⟩ : Fin 31671) ∈ MulAction.orbit (lgen rho432F (yGen 4 3 2) L) (⟨b, hb⟩ : Fin 31671) :=
  mem_orbit_of_orbitOK (fun c hc => (net_spec (hL c hc)).1)
    (fun c hc => (net_spec (hL c hc)).2.1) (fun c hc => (net_spec (hL c hc)).2.2) hb (by norm_num) h

theorem lgen_eq (L : List ℕ) :
    lgen rho432F (yGen 4 3 2) L = (lsub L).map rho432F := by
  rw [lgen, lsub, MonoidHom.map_closure, ← Set.image_comp]
  rfl

@[expose] def hLev : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [0, 1, 2, 3, 5, 6, 7, 8, 9], [0, 1, 2, 5, 6, 7, 8, 9],
    [0, 1, 5, 6, 7, 8, 9], [0, 5, 6, 7, 8, 9], [5, 6, 7, 8, 9], [6, 7, 8, 9], [7, 8, 9], [8, 9], [9]]

@[expose] def hPts : List ℕ := [0, 1, 2, 3, 4, 199, 55, 74, 5, 7]

@[expose] def hOrd : List ℕ := [31671, 28160, 3159, 288, 35, 4, 3, 2, 3, 2]

@[expose] def yLev : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 8, 9], [0, 1, 2, 3, 5, 6, 8, 9], [0, 1, 2, 5, 6, 8, 9], [0, 1, 5, 6, 8, 9],
    [0, 5, 6, 8, 9], [5, 6, 8, 9], [6, 8, 9], [8, 9], [9]]

@[expose] def yPts : List ℕ := [0, 1, 2, 3, 4, 92, 55, 5, 7]

@[expose] def yOrd : List ℕ := [1080, 728, 243, 72, 20, 3, 2, 3, 2]

theorem hLev_lt : ∀ l < 10, ∀ c ∈ hLev.getD l [], c < 10 := by decide
theorem yLev_lt : ∀ l < 9, ∀ c ∈ yLev.getD l [], c < 10 := by decide
theorem hPts_lt : ∀ l < 10, hPts.getD l 0 < 31671 := by decide
theorem yPts_lt : ∀ l < 9, yPts.getD l 0 < 31671 := by decide

theorem hChain_orb : ∀ l < 10, ∃ R M, orbitOK 15 ((hLev.getD l []).map CFSG.KD.YMY432F.Nf)
    (hPts.getD l 0) R M = true ∧ Nat.beq (popc 15 M) (hOrd.getD l 0) = true := by
  intro l hl
  interval_cases l
  · exact ⟨_, _, CFSG.KD.Y442D.orbH0, CFSG.KD.Y442D.popH0⟩
  · exact ⟨_, _, CFSG.KD.Y442D.orbH1, CFSG.KD.Y442D.popH1⟩
  · exact ⟨_, _, CFSG.KD.Y442D.orbH2, CFSG.KD.Y442D.popH2⟩
  · exact ⟨_, _, CFSG.KD.Y442D.orbH3, CFSG.KD.Y442D.popH3⟩
  · exact ⟨_, _, CFSG.KD.Y442D.orbH4, CFSG.KD.Y442D.popH4⟩
  · exact ⟨_, _, CFSG.KD.Y442D.orbH5, CFSG.KD.Y442D.popH5⟩
  · exact ⟨_, _, CFSG.KD.Y442D.orbH6, CFSG.KD.Y442D.popH6⟩
  · exact ⟨_, _, CFSG.KD.Y442D.orbH7, CFSG.KD.Y442D.popH7⟩
  · exact ⟨_, _, CFSG.KD.Y442D.orbH8, CFSG.KD.Y442D.popH8⟩
  · exact ⟨_, _, CFSG.KD.Y442D.orbH9, CFSG.KD.Y442D.popH9⟩

theorem yChain_orb : ∀ l < 9, ∃ R M, orbitOK 15 ((yLev.getD l []).map CFSG.KD.YMY432F.Nf)
    (yPts.getD l 0) R M = true ∧ Nat.beq (popc 15 M) (yOrd.getD l 0) = true := by
  intro l hl
  interval_cases l
  · exact ⟨_, _, CFSG.KD.Y442D.orbY0, CFSG.KD.Y442D.popY0⟩
  · exact ⟨_, _, CFSG.KD.Y442D.orbY1, CFSG.KD.Y442D.popY1⟩
  · exact ⟨_, _, CFSG.KD.Y442D.orbY2, CFSG.KD.Y442D.popY2⟩
  · exact ⟨_, _, CFSG.KD.Y442D.orbY3, CFSG.KD.Y442D.popY3⟩
  · exact ⟨_, _, CFSG.KD.Y442D.orbY4, CFSG.KD.Y442D.popY4⟩
  · exact ⟨_, _, CFSG.KD.Y442D.orbY5, CFSG.KD.Y442D.popY5⟩
  · exact ⟨_, _, CFSG.KD.Y442D.orbY6, CFSG.KD.Y442D.popY6⟩
  · exact ⟨_, _, CFSG.KD.Y442D.orbH8, CFSG.KD.Y442D.popH8⟩
  · exact ⟨_, _, CFSG.KD.Y442D.orbH9, CFSG.KD.Y442D.popH9⟩

theorem hChain_fix : ∀ l < 10, ∀ c ∈ hLev.getD l [], ∀ m < l,
    fieldAt 32 (CFSG.KD.YM432P.F c) (hPts.getD m 0) = hPts.getD m 0 := by
  decide +kernel

theorem yChain_fix : ∀ l < 9, ∀ c ∈ yLev.getD l [], ∀ m < l,
    fieldAt 32 (CFSG.KD.YM432P.F c) (yPts.getD m 0) = yPts.getD m 0 := by
  decide +kernel

theorem chain_card (k : ℕ) (lev : List (List ℕ)) (pts ord : List ℕ)
    (hlt : ∀ l < k, ∀ c ∈ lev.getD l [], c < 10) (hpt : ∀ l < k, pts.getD l 0 < 31671)
    (horb : ∀ l < k, ∃ R M, orbitOK 15 ((lev.getD l []).map CFSG.KD.YMY432F.Nf)
      (pts.getD l 0) R M = true ∧ Nat.beq (popc 15 M) (ord.getD l 0) = true)
    (hfix : ∀ l < k, ∀ c ∈ lev.getD l [], ∀ m < l,
      fieldAt 32 (CFSG.KD.YM432P.F c) (pts.getD m 0) = pts.getD m 0) :
    let β : ℕ → Fin 31671 := fun m => ⟨pts.getD m 0 % 31671, Nat.mod_lt _ (by norm_num)⟩
    let Y : ℕ → Set (Equiv.Perm (Fin 31671)) :=
      fun l => (fun c => rho432F (yGen 4 3 2 c)) '' {c | c ∈ lev.getD l []}
    (∀ l < k, ∀ y ∈ Y l, ∀ m < l, y (β m) = β m) ∧
      ∀ l < k, ord.getD l 0 ≤ (MulAction.orbit (Subgroup.closure (Y l)) (β l)).ncard := by
  intro β Y
  have hβ : ∀ m < k, (β m : ℕ) = pts.getD m 0 := fun m hm => Nat.mod_eq_of_lt (hpt m hm)
  refine ⟨?_, ?_⟩
  · rintro l hl _ ⟨c, hc, rfl⟩ m hm
    apply Fin.ext
    rw [rho_yGen_apply (hlt l hl c hc), hβ m (by omega)]
    exact hfix l hl c hc m hm
  · intro l hl
    obtain ⟨R, M, h1, h2⟩ := horb l hl
    have e : β l = ⟨pts.getD l 0, hpt l hl⟩ := Fin.ext (hβ l hl)
    rw [e]
    exact orb_card (hlt l hl) (hpt l hl) h1 h2

theorem rho_eq_one_of_base
    {g : Equiv.Perm (Fin 31671)} (hg : g ∈ rho432F.range)
    (hfix : ∀ m < 10, (g ⟨hPts.getD m 0 % 31671, Nat.mod_lt _ (by norm_num)⟩ : ℕ) =
      hPts.getD m 0) : g = 1 := by
  obtain ⟨h1, h2⟩ := chain_card 10 hLev hPts hOrd hLev_lt hPts_lt hChain_orb hChain_fix
  refine eq_one_of_chain rho432F.range 10 _ _ ?_ h1 _ h2 ?_ hg ?_
  · rintro l - _ ⟨c, -, rfl⟩
    exact ⟨_, rfl⟩
  · rw [card_range_rho432F]
    decide
  · intro m hm
    apply Fin.ext
    change (g ⟨hPts.getD m 0 % 31671, _⟩ : ℕ) = hPts.getD m 0 % 31671
    rw [hfix m hm, Nat.mod_eq_of_lt (hPts_lt m hm)]

theorem evalWord_eq_one_of_base
    (w : List ℕ) (hw : ∀ c ∈ w, c < 10) (he : Even w.length)
    (hb : ∀ m < 10, w.foldl (fun p c => fieldAt 32 (CFSG.KD.YM432P.F c) p) (hPts.getD m 0) =
      hPts.getD m 0) : evalWord (yGen 4 3 2) w = 1 := by
  have hrev : ∀ c ∈ w.reverse, c < 10 := fun c hc => hw c (List.mem_reverse.1 hc)
  have h1 : rho432F (evalWord (yGen 4 3 2) w.reverse) = 1 := by
    refine rho_eq_one_of_base ⟨_, rfl⟩ fun m hm => ?_
    rw [rho_evalWord_apply _ hrev]
    simp only [Fin.val_mk]
    rw [Nat.mod_eq_of_lt (hPts_lt m hm), List.foldr_reverse]
    exact hb m hm
  rw [evalWord_reverse (yGen_mul_self 4 3 2), map_inv, inv_eq_one] at h1
  refine eq_one_of_rho_par h1 ?_
  rw [par432_evalWord hw, ← ofAdd_zero]
  congr 1
  obtain ⟨k, hk⟩ := he
  rw [hk, Nat.cast_add, ← two_mul]
  exact mul_eq_zero_of_left (by decide) _

theorem swSp432_eq_one :
    evalWord (yGen 4 3 2) swSp432 = 1 :=
  evalWord_eq_one_of_base _ swSp432_lt (by decide) (by decide +kernel)

@[expose] def tL : List ℕ := [0, 1, 2, 3, 5, 6, 7, 8, 9]

@[expose] def yL : List ℕ := [0, 1, 2, 3, 4, 5, 6, 8, 9]

theorem rels_y332_y432 : ∀ w ∈ yRels 3 3 2, w.map (shiftAt 3) ∈ yRels 4 3 2 := by decide

theorem index_of_table {inv L eps nLab nT N RW RM nR nS nW nF : ℕ} {F D Wd Wd2 R S : ℕ → ℕ}
    {amap : ℕ} {walk cov : List ℕ} {rels words : List (List (ℕ × Bool))}
    (h : tableOk inv L eps nLab nT N RW RM nR nS nW nF F D Wd Wd2 R S amap rels words walk cov =
      true) (hrels : rels = (yRels 4 3 2).map KernelYChain.enc)
    (hwords : words = ((List.range (ngen 3 3 2)).map (shiftAt 3)).map fun c => [(c, true)])
    (htop : topOk amap (ngen 4 3 2) = true) :
    (Subgroup.closure (yGen 4 3 2 '' (shiftAt 3 '' Set.Iio (ngen 3 3 2)))).FiniteIndex ∧
      (Subgroup.closure (yGen 4 3 2 '' (shiftAt 3 '' Set.Iio (ngen 3 3 2)))).index ≤ N := by
  have := KernelYChain.index_le_of_table h hrels (by decide) htop
  rw [hwords, KernelYChain.wordSub_letters] at this
  exact this

theorem index_tL_le : (lsub tL).FiniteIndex ∧ (lsub tL).index ≤ 31671 := by
  have t := KernelYChain.YCh10.t1
  unfold CFSG.KBRoute.YCh10.T1.ok at t
  have h := index_of_table t (by decide +kernel) (by decide +kernel) CFSG.KBRoute.YCh10.top
  have e : shiftAt 3 '' Set.Iio (ngen 3 3 2) = {c | c ∈ tL} := by
    ext c
    simp only [Set.mem_image, Set.mem_Iio, ngen, Set.mem_setOf_eq, tL, List.mem_cons,
      List.not_mem_nil, or_false, shiftAt]
    constructor
    · rintro ⟨d, hd, rfl⟩
      split_ifs <;> omega
    · intro hc
      refine ⟨if c ≤ 3 then c else c - 1, by split_ifs <;> omega, ?_⟩
      split_ifs <;> omega
  rw [e] at h
  exact h

theorem tL_fix_zero :
    ∀ c ∈ tL, rho432F (yGen 4 3 2 c) 0 = 0 := by
  intro c hc
  apply Fin.ext
  rw [rho_yGen_apply (by simp only [tL] at hc; decide +revert)]
  revert c
  decide +kernel

@[expose] def fullPts : ℕ := 2 ^ 31671 - 1

theorem testBit_fullPts {p : ℕ} (hp : p < 31671) : fullPts.testBit p = true := by
  rw [fullPts, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hp

theorem cover_of_orbs {L : List ℕ} (hL : ∀ c ∈ L, c < 10)
    (bs : List ℕ) (Ms : List ℕ)
    (horb : ∀ i < bs.length, ∃ R, ∃ hb : bs.getD i 0 < 31671,
      orbitOK 15 (L.map CFSG.KD.YMY432F.Nf) (bs.getD i 0) R (Ms.getD i 0) = true)
    (hfull : Ms.foldr (· ||| ·) 0 = fullPts) (hlen : Ms.length = bs.length)
    (p : Fin 31671) : ∃ i < bs.length, ∃ hb : bs.getD i 0 < 31671,
      p ∈ MulAction.orbit (lgen rho432F (yGen 4 3 2) L) (⟨bs.getD i 0, hb⟩ : Fin 31671) := by
  have hbit : (Ms.foldr (· ||| ·) 0).testBit p = true := by rw [hfull]; exact testBit_fullPts p.2
  have key : ∀ (l : List ℕ), (l.foldr (· ||| ·) 0).testBit p = true →
      ∃ i < l.length, (l.getD i 0).testBit p = true := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      intro h
      rw [List.foldr_cons, Nat.testBit_or, Bool.or_eq_true] at h
      rcases h with h | h
      · exact ⟨0, by simp, by simpa using h⟩
      · obtain ⟨i, hi, h'⟩ := ih h
        exact ⟨i + 1, by simp; omega, by simpa using h'⟩
  obtain ⟨i, hi, hti⟩ := key Ms hbit
  rw [hlen] at hi
  obtain ⟨R, hb, h⟩ := horb i hi
  obtain ⟨hp, hmem⟩ := orb_mem hL hb h p hti
  exact ⟨i, hi, hb, hmem⟩

theorem transitive_zero (p : Fin 31671) :
    ∃ y : YGroup 4 3 2, rho432F y 0 = p := by
  obtain ⟨i, hi, hb, hmem⟩ := cover_of_orbs (L := allL) (by decide) [0] [CFSG.KD.Y442D.MH0]
    (fun i hi => by
      have : i = 0 := by simpa using hi
      subst this
      exact ⟨_, by decide, CFSG.KD.Y442D.orbH0⟩)
    (by decide +kernel) rfl p
  have hi0 : i = 0 := by simpa using hi
  subst hi0
  obtain ⟨⟨g, hg⟩, rfl⟩ := hmem
  rw [lgen_eq, lsub_all, ← MonoidHom.range_eq_map] at hg
  obtain ⟨y, rfl⟩ := hg
  exact ⟨y, rfl⟩

theorem stab_zero
    {y : YGroup 4 3 2} (hy : rho432F y 0 = 0) : y ∈ lsub tL := by
  have hfin := finite_y432
  let f : YGroup 4 3 2 ⧸ lsub tL → Fin 31671 := Quotient.lift (fun y => rho432F y 0) (by
    intro a b hab'
    have hab : a⁻¹ * b ∈ lsub tL := QuotientGroup.leftRel_apply.mp hab'
    have hT : ∀ z ∈ lsub tL, rho432F z 0 = 0 := by
      intro z hz
      induction hz using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨c, hc, rfl⟩ := hx
        exact tL_fix_zero c hc
      | one => simp
      | mul x z _ _ hx hz => rw [map_mul, Equiv.Perm.mul_apply, hz, hx]
      | inv x _ hx => rw [map_inv, Equiv.Perm.inv_eq_iff_eq, hx]
    have hfix : rho432F (a⁻¹ * b) 0 = 0 := hT _ hab
    change rho432F a 0 = rho432F b 0
    have e : b = a * (a⁻¹ * b) := by group
    rw [e, map_mul, Equiv.Perm.mul_apply, hfix])
  have hsurj : Function.Surjective f := by
    intro p
    obtain ⟨z, hz⟩ := transitive_zero p
    exact ⟨(z : YGroup 4 3 2 ⧸ lsub tL), hz⟩
  have hcard : Nat.card (YGroup 4 3 2 ⧸ lsub tL) ≤ Nat.card (Fin 31671) := by
    rw [← Subgroup.index_eq_card, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact index_tL_le.2
  have : Finite (YGroup 4 3 2 ⧸ lsub tL) := Finite.of_surjective _ (QuotientGroup.mk_surjective)
  have hinj := (hsurj.bijective_of_nat_card_le hcard).1
  have e : f (y : YGroup 4 3 2 ⧸ lsub tL) = f ((1 : YGroup 4 3 2) : YGroup 4 3 2 ⧸ lsub tL) := by
    change rho432F y 0 = rho432F 1 0
    rw [hy, map_one]
    rfl
  have := hinj e
  rw [QuotientGroup.eq, mul_one] at this
  exact (lsub tL).inv_mem_iff.1 this

theorem yLev_sub : ∀ l < 9, ∀ c ∈ yLev.getD l [], c ∈ yL := by decide

theorem index_yL_le :
    (lsub yL).index ≤ 825792 := by
  have hfin := finite_y432
  obtain ⟨h1, h2⟩ := chain_card 9 yLev yPts yOrd yLev_lt yPts_lt yChain_orb yChain_fix
  have hlow := card_ge_of_chain ((lsub yL).map rho432F) 9 _ _ (by
    rintro l hl _ ⟨c, hc, rfl⟩
    exact Subgroup.mem_map_of_mem _ (yGen_mem_lsub (yLev_sub l hl c hc))) h1 _ h2
  have hprod : ∏ l ∈ Finset.range 9, yOrd.getD l 0 = 9904359628800 := by decide
  rw [hprod] at hlow
  have hmap : Nat.card ((lsub yL).map rho432F) ≤ Nat.card (lsub yL) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd (lsub yL) rho432F)
  have hmul := (lsub yL).card_mul_index
  rw [card_y432] at hmul
  have hpos : 0 < (lsub yL).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  by_contra hc
  have : 9904359628800 * 825793 ≤ Nat.card (lsub yL) * (lsub yL).index :=
    Nat.mul_le_mul (hlow.trans hmap) (by omega)
  omega

@[expose] def cw : ℕ → List (List ℕ)
  | 0 => [[]]
  | 1 => [[], [4], [4, 3, 2, 1, 0, 8, 5, 0, 1, 2, 3, 4]]
  | _ => [[], [7, 6, 5, 0, 1, 2, 3, 4], [7, 6, 5, 0, 8, 9, 1, 0, 8, 5, 6, 2, 1, 0, 5, 3, 2, 1, 0,
      8, 9, 6, 0, 5, 2, 1, 0, 8, 7, 6, 5, 0, 1, 2, 3, 4]]

@[expose] def lt3 : ℕ → List ℕ
  | 0 => allL
  | 1 => tL
  | _ => yL

@[expose] def cp : ℕ → List ℕ
  | 0 => [0]
  | 1 => [0, 1, 52]
  | _ => [0, 11, 23116]

theorem cw_lt : ∀ t < 3, ∀ w ∈ cw t, ∀ c ∈ w, c < 10 := by decide

theorem lt3_lt : ∀ t < 3, ∀ c ∈ lt3 t, c < 10 := by decide

theorem cp_eq : ∀ t < 3, (cw t).length = (cp t).length ∧ ∀ i < (cw t).length,
    ((cw t).getD i []).foldr (fun c p => fieldAt 32 (CFSG.KD.YM432P.F c) p) 0 = (cp t).getD i 0 := by
  decide +kernel

theorem cover_orbs : ∀ t < 3, ∃ Ms : List ℕ, (∀ i < (cp t).length, ∃ R, ∃ hb : (cp t).getD i 0 < 31671,
      orbitOK 15 ((lt3 t).map CFSG.KD.YMY432F.Nf) ((cp t).getD i 0) R (Ms.getD i 0) = true) ∧
    Ms.foldr (· ||| ·) 0 = fullPts ∧ Ms.length = (cp t).length := by
  intro t ht
  interval_cases t
  · refine ⟨[CFSG.KD.Y442D.MH0], fun i hi => ?_, by decide +kernel, rfl⟩
    have : i = 0 := by simpa [cp] using hi
    subst this
    exact ⟨_, by decide, CFSG.KD.Y442D.orbH0⟩
  · refine ⟨[CFSG.KD.Y442D.MCT0, CFSG.KD.Y442D.MH1, CFSG.KD.Y442D.MCT2], fun i hi => ?_,
      by decide +kernel, rfl⟩
    have : i < 3 := by simpa [cp] using hi
    interval_cases i
    · exact ⟨_, by decide, CFSG.KD.Y442D.orbCT0⟩
    · exact ⟨_, by decide, CFSG.KD.Y442D.orbH1⟩
    · exact ⟨_, by decide, CFSG.KD.Y442D.orbCT2⟩
  · refine ⟨[CFSG.KD.Y442D.MY0, CFSG.KD.Y442D.MCY4221, CFSG.KD.Y442D.MCY4222],
      fun i hi => ?_, by decide +kernel, rfl⟩
    have : i < 3 := by simpa [cp] using hi
    interval_cases i
    · exact ⟨_, by decide, CFSG.KD.Y442D.orbY0⟩
    · exact ⟨_, by decide, CFSG.KD.Y442D.orbCY4221⟩
    · exact ⟨_, by decide, CFSG.KD.Y442D.orbCY4222⟩

theorem cover
    {t : ℕ} (ht : t < 3) (y : YGroup 4 3 2) :
    ∃ i < (cw t).length, ∃ ℓ ∈ lsub (lt3 t), ∃ z ∈ lsub tL,
      y = ℓ * evalWord (yGen 4 3 2) ((cw t).getD i []) * z := by
  obtain ⟨Ms, horb, hfull, hlen⟩ := cover_orbs t ht
  obtain ⟨i, hi, hb, ⟨⟨g, hg⟩, hgp⟩⟩ := cover_of_orbs (lt3_lt t ht) (cp t) Ms horb hfull hlen
    (rho432F y 0)
  obtain ⟨hl, hcp⟩ := cp_eq t ht
  rw [lgen_eq] at hg
  obtain ⟨ℓ, hℓ, rfl⟩ := hg
  have hi' : i < (cw t).length := by rw [hl]; exact hi
  have hmemw : (cw t).getD i [] ∈ cw t := by
    rw [List.getD_eq_getElem _ _ hi']
    exact List.getElem_mem hi'
  set w := evalWord (yGen 4 3 2) ((cw t).getD i [])
  have hw : rho432F w 0 = ⟨(cp t).getD i 0, hb⟩ := by
    apply Fin.ext
    rw [rho_evalWord_apply _ (fun c hc => cw_lt t ht _ hmemw c hc)]
    exact hcp i hi'
  refine ⟨i, hi', ℓ, hℓ, (ℓ * w)⁻¹ * y, stab_zero ?_, by simp [w, mul_assoc]⟩
  change rho432F ℓ ⟨(cp t).getD i 0, hb⟩ = rho432F y 0 at hgp
  have e1 : rho432F y 0 = rho432F (ℓ * w) 0 := by
    rw [map_mul, Equiv.Perm.mul_apply, hw]
    exact hgp.symm
  rw [map_mul, map_inv, Equiv.Perm.mul_apply, e1]
  simp

end CertificateChecks.KernelY442

end
