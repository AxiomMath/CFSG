module

public import Certificates.Kernel.G24B.Borel
public import Certificates.Kernel.G24B.Checks733011Z
public import CFSG.Quasithin.Recognition.St84.G24Table
import CFSG.GroupTheory.IndexFourQuotientKernel

public section

noncomputable section

set_option maxRecDepth 100000

namespace CFSG.KD.G24B

open CFSG.Fischer CFSG.Quasithin.F112R.St84.G24M CFSG.KC.Misc.Spec CFSG.KC.F2BfsRec
open CFSG.KC.Misc.G24 (mulF2 oneF2 wordF4 nthV nthL)
open CFSG.Quasithin.St84.G24Ident (k1 k2 xa xb pc1 pc2)
open CFSG.Quasithin.St84.G24Table (pcEltY pcEltY_def pcEltY_mem_closure)

open scoped commutatorElement


@[expose] def yAt (y : Fin 10 → Y) (m : ℕ) : Y := if h : m < 10 then y ⟨m, h⟩ else 1

theorem pcK_succ (G : List ℕ) (j n : ℕ) :
    (Nat.rec (motive := fun _ => ℕ) (oneF2 28)
      (fun m acc => Bool.rec (motive := fun _ => ℕ) acc (mulF2 28 acc (nthV G m))
        (CFSG.KLie.CT.bit j m)) (n + 1) : ℕ) =
    Bool.rec (motive := fun _ => ℕ)
      (Nat.rec (motive := fun _ => ℕ) (oneF2 28)
        (fun m acc => Bool.rec (motive := fun _ => ℕ) acc (mulF2 28 acc (nthV G m))
          (CFSG.KLie.CT.bit j m)) n)
      (mulF2 28 (Nat.rec (motive := fun _ => ℕ) (oneF2 28)
        (fun m acc => Bool.rec (motive := fun _ => ℕ) acc (mulF2 28 acc (nthV G m))
          (CFSG.KLie.CT.bit j m)) n) (nthV G n))
      (CFSG.KLie.CT.bit j n) := rfl

theorem psi_pcK_aux {y : Fin 10 → Y} {G : List ℕ}
    (hG : ∀ m : Fin 10, psi (y m) = pkMat 28 (nthV G m.val)) (j : ℕ) :
    ∀ n ≤ 10, pkMat 28 (Nat.rec (motive := fun _ => ℕ) (oneF2 28)
      (fun m acc => Bool.rec (motive := fun _ => ℕ) acc (mulF2 28 acc (nthV G m))
        (CFSG.KLie.CT.bit j m)) n) =
      psi ((((List.range n).filter fun m => j.testBit m).map (yAt y)).prod)
  | 0, _ => by
    change pkMat 28 (oneF2 28) = _
    rw [pkMat_oneF2]
    simp
  | n + 1, hn => by
    rw [pcK_succ, CFSG.KC.F2Mat.bit_eq_testBit, List.range_succ, List.filter_append]
    have ih := psi_pcK_aux hG j n (by omega)
    cases hb : j.testBit n
    · simp only [List.filter_cons, hb, List.filter_nil, Bool.false_eq_true, ↓reduceIte,
        List.append_nil]
      exact ih
    · simp only [List.filter_cons, hb, List.filter_nil, ↓reduceIte, List.map_append,
        List.map_cons, List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, mul_one,
        map_mul]
      change pkMat 28 (mulF2 28 _ _) = _
      rw [pkMat_mulF2, ih, yAt, dif_pos (by omega), hG ⟨n, by omega⟩]

theorem filter_range_finRange' (j : ℕ) :
    (List.range 10).filter (fun m => j.testBit m) =
      ((List.finRange 10).filter (fun m => j.testBit m.val)).map Fin.val := by
  rw [← List.map_coe_finRange_eq_range, List.filter_map]
  rfl

theorem psi_pcEltY {y : Fin 10 → Y} {G : List ℕ}
    (hG : ∀ m : Fin 10, psi (y m) = pkMat 28 (nthV G m.val)) (j : ℕ) :
    psi (pcEltY y j) = pkMat 28 (pcK G j) := by
  rw [pcK, psi_pcK_aux hG j 10 le_rfl, filter_range_finRange', List.map_map, pcEltY_def]
  congr 3
  funext m
  simp [yAt, m.2]

@[expose] def pcY (b : ℕ) : Fin 10 → Y := if b = 1 then pc1Y else pc2Y

theorem psi_pc1 (hC : ChevFacts) (m : Fin 10) : psi (pc1Y m) = pkMat 28 (nthV GQ1 m.val) := by
  rw [nthV_eq, GQ1, getD_map_lt (by rw [show wQ1.length = 10 from rfl]; exact m.2) 0 [],
    show pc1Y m = agY (wQ1.getD m.val []) from rfl, psi_agY hC]

theorem psi_pc2 (hC : ChevFacts) (m : Fin 10) : psi (pc2Y m) = pkMat 28 (nthV GQ2 m.val) := by
  rw [nthV_eq, GQ2, getD_map_lt (by rw [show wQ2.length = 10 from rfl]; exact m.2) 0 [],
    show pc2Y m = agY (wQ2.getD m.val []) from rfl, psi_agY hC]

theorem psi_pcY (hC : ChevFacts) {b : ℕ} (hb : b = 1 ∨ b = 2) (m : Fin 10) :
    psi (pcY b m) = pkMat 28 (nthV (selK b) m.val) := by
  rcases hb with rfl | rfl
  · exact psi_pc1 hC m
  · exact psi_pc2 hC m

theorem pcY_mem_T0 {b : ℕ} (hb : b = 1 ∨ b = 2) (hQ1T : Q1 ≤ T0) (hQ2T : Q2 ≤ T0) (j : ℕ) :
    pcEltY (pcY b) j ∈ T0 := by
  rcases hb with rfl | rfl
  · exact hQ1T (pcEltY_mem_closure pc1Y j)
  · exact hQ2T (pcEltY_mem_closure pc2Y j)

theorem okB_spec {b : ℕ} (h : okB b = true) : b = 1 ∨ b = 2 := by
  unfold okB at h
  cases h1 : Nat.beq b 1
  · rw [h1] at h
    exact Or.inr (beq_iff'.mp h)
  · exact Or.inl (beq_iff'.mp h1)

theorem lettersK_spec {X : ℕ} : ∀ {w : List (ℕ × (ℕ × ℕ))}, lettersK X w = true →
    ∀ l ∈ w, letterK X l = true
  | [], _ => by simp
  | l :: w, h => by
    obtain ⟨h1, h2⟩ := andB_iff.mp h
    intro l' hl'
    rcases List.mem_cons.mp hl' with rfl | hl'
    · exact h1
    · exact lettersK_spec h2 l' hl'

theorem psi_wordK (hC : ChevFacts) :
    ∀ w : List (ℕ × (ℕ × ℕ)), (∀ l ∈ w, l.1 = 1 ∨ l.1 = 2) →
      pkMat 28 (wordK w) = psi ((w.map fun l => pcEltY (pcY l.1) l.2.2).prod)
  | [], _ => by
    change pkMat 28 (oneF2 28) = _
    rw [pkMat_oneF2]
    simp
  | l :: w, hw => by
    change pkMat 28 (mulF2 28 (pcK (selK l.1) l.2.2) (wordK w)) = _
    rw [pkMat_mulF2, psi_wordK hC w (fun l' hl' => hw l' (by simp [hl'])),
      ← psi_pcEltY (psi_pcY hC (hw l (by simp))) l.2.2]
    simp [map_mul]

theorem mem_of_mul_eq' {h p q : Y} {N : Subgroup Y}
    (heq : p * q * h = h * p) (hpT : p ∈ T0)
    (hcomm : ∀ t ∈ T0, ⁅h, t⁆ ∈ N) : q ∈ N := by
  have hq : q = p⁻¹ * h * p * h⁻¹ := by
    calc q = p⁻¹ * (p * q * h) * h⁻¹ := by group
      _ = p⁻¹ * (h * p) * h⁻¹ := by rw [heq]
      _ = p⁻¹ * h * p * h⁻¹ := by group
  have hmem : ⁅h, p⁻¹⁆⁻¹ ∈ N := N.inv_mem (hcomm p⁻¹ (T0.inv_mem hpT))
  have hinv : ⁅h, p⁻¹⁆⁻¹ = p⁻¹ * h * p * h⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [hq, ← hinv]
  exact hmem

theorem Q1_le_or_Q2_le' (hC : ChevFacts) {N : Subgroup Y} {h : Y}
    (hhH : h ∈ CFSG.Quasithin.F112R.St84.G24M.H0) (hne : h ≠ 1)
    (hcomm : ∀ t ∈ T0, ⁅h, t⁆ ∈ N) (hQ1T : Q1 ≤ T0) (hQ2T : Q2 ≤ T0) :
    Q1 ≤ N ∨ Q2 ≤ N := by
  rw [H0_eq] at hhH
  obtain ⟨t, htN, hx⟩ := exists_entry_of_recOK (rH hC) hhH
  obtain ⟨s, hs, es⟩ := exists_sorted_of_entry (rH hC).h htN
  have htor := allN_iff'.mp ch733011_torus s hs
  rw [strictB_eq'] at htor
  cases hX : Nat.beq (sortedAt 28 12 6 2 EH.CF s) (oneF2 28)
  · rw [hX] at htor
    generalize tc.getD (nthV CFSG.KD.G24B.ht s) (0, []) = d at htor
    obtain ⟨hd1, hd2⟩ := andB_iff.mp htor
    have hb := okB_spec hd1
    have hpsi : psi h = pkMat 28 (sortedAt 28 12 6 2 EH.CF s) := by rw [hx, ← es]
    have hgen : ∀ m : Fin 10, pcY d.1 m ∈ N := by
      intro m
      obtain ⟨hl, hw⟩ := andB_iff.mp (allN_iff'.mp hd2 m.val m.2)
      have hlet := lettersK_spec hl
      have hb' : ∀ l ∈ d.2.getD m.val [], l.1 = 1 ∨ l.1 = 2 := fun l hl' =>
        okB_spec (andB_iff.mp (hlet l hl')).1
      have hprod : ((d.2.getD m.val []).map fun l => pcEltY (pcY l.1) l.2.2).prod = pcY d.1 m := by
        refine psi_injective hC ?_
        rw [← psi_wordK hC _ hb', beq_iff'.mp hw, psi_pcY hC hb m]
      rw [← hprod]
      apply Subgroup.list_prod_mem
      intro x hx'
      obtain ⟨l, hl', rfl⟩ := List.mem_map.mp hx'
      obtain ⟨-, hl2⟩ := andB_iff.mp (hlet l hl')
      rw [strictB_eq'] at hl2
      have heq : pcEltY (pcY l.1) l.2.1 * pcEltY (pcY l.1) l.2.2 * h =
          h * pcEltY (pcY l.1) l.2.1 := by
        refine psi_injective hC ?_
        rw [map_mul, map_mul, map_mul, hpsi, psi_pcEltY (psi_pcY hC (hb' l hl')),
          psi_pcEltY (psi_pcY hC (hb' l hl')), ← pkMat_mulF2, ← pkMat_mulF2, ← pkMat_mulF2,
          beq_iff'.mp hl2]
      exact mem_of_mul_eq' heq (pcY_mem_T0 (hb' l hl') hQ1T hQ2T _) hcomm
    rcases hb with h1 | h1
    · left
      refine (Subgroup.closure_le _).mpr ?_
      rintro x ⟨m, rfl⟩
      have := hgen m
      rwa [h1] at this
    · right
      refine (Subgroup.closure_le _).mpr ?_
      rintro x ⟨m, rfl⟩
      have := hgen m
      rwa [h1] at this
  · exfalso
    apply hne
    refine psi_injective hC ?_
    rw [hx, ← es, beq_iff'.mp hX, pkMat_oneF2, map_one]

theorem eq_Q1_or_eq_Q2' (hC : ChevFacts) (hH0 : CFSG.Quasithin.F112R.St84.G24M.H0 ≤ B0)
    (hcH0 : Nat.card CFSG.Quasithin.F112R.St84.G24M.H0 = 9)
    (hQ1T : Q1 ≤ T0) (hQ2T : Q2 ≤ T0) (hcQ1 : Nat.card Q1 = 1024) (hcQ2 : Nat.card Q2 = 1024)
    {N : Subgroup Y} (hNB : N ≤ B0) (hBN : B0 ≤ Subgroup.normalizer (N : Set Y))
    (hN : Nat.card N = 2 ^ 10) : N = Q1 ∨ N = Q2 := by
  classical
  have hT0N : T0 ≤ Subgroup.normalizer (N : Set Y) := hC.T0_le_B0.trans hBN
  have hH0T : CFSG.Quasithin.F112R.St84.G24M.H0 ≤ Subgroup.normalizer (T0 : Set Y) := by
    rw [hC.normalizer_T0]
    exact hH0
  have hH0N : CFSG.Quasithin.F112R.St84.G24M.H0 ≤ Subgroup.normalizer (N : Set Y) := hH0.trans hBN
  have hNT0 : N ≤ T0 := hC.le_T0_of_isPGroup hNB (isPGroup_of_card_two_pow hN)
  have hidx : (N.subgroupOf T0).index = 4 := by
    have hmul := Subgroup.card_mul_index (H := N.subgroupOf T0)
    have hcard : Nat.card (N.subgroupOf T0) = 1024 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNT0).toEquiv, hN]
      norm_num
    rw [hcard, hC.card_T0] at hmul
    omega
  obtain ⟨h, hhH0, hne, hcomm⟩ :=
    CFSG.GroupTheory.exists_ne_one_commutator_mem_of_index_four
      hNT0 hT0N hH0T hH0N hidx (by rw [hcH0]; norm_num)
  rcases Q1_le_or_Q2_le' hC hhH0 hne hcomm hQ1T hQ2T with hQ | hQ
  · left
    exact (Subgroup.eq_of_le_of_card_ge hQ (by rw [hN, hcQ1]; norm_num)).symm
  · right
    exact (Subgroup.eq_of_le_of_card_ge hQ (by rw [hN, hcQ2]; norm_num)).symm

theorem letters_rw : ∀ i < 36, ∀ c ∈ nthL rw i, c / 2 < 4 := by decide +kernel
theorem letters_rv : ∀ i < 36, ∀ c ∈ nthL rv i, c / 2 < 4 := by decide +kernel

@[expose] def rY (i : ℕ) : Y := yW gsB (nthL rw i)

@[expose] def rvY (i : ℕ) : Y := yW gsB (nthL rv i)

theorem psi_rY (hC : ChevFacts) {i : ℕ} (hi : i < 36) : psi (rY i) = pkMat 28 (repK rw i) :=
  (pk_wordF4 (pk_gK hC) _ (letters_rw i hi)).symm

theorem psi_rvY (hC : ChevFacts) {i : ℕ} (hi : i < 36) : psi (rvY i) = pkMat 28 (repK rv i) :=
  (pk_wordF4 (pk_gK hC) _ (letters_rv i hi)).symm

theorem psi_gB0 (hC : ChevFacts) (k : Fin 4) : psi (gB0 k) = pkMat 28 (nthV gK k.val) := by
  rw [nthV_eq, pk_gK hC k.val k.2, show gB0 k = gsB.getD k.val 1 by fin_cases k <;> rfl]

theorem psi_gB0_inv (hC : ChevFacts) (k : Fin 4) :
    psi (gB0 k)⁻¹ = pkMat 28 (nthV (gMiK 0) k.val) := by
  rw [nthV_eq]
  fin_cases k <;> simp only [gMiK, List.getD_cons_succ, List.getD_cons_zero]
  · change psi k1Y⁻¹ = _
    rw [inv_of_cube hC (psi_k1 hC) (ord3_spec gensParts.k1o).1, map_mul, psi_k1 hC, pkMat_mulF2]
  · change psi k2Y⁻¹ = _
    rw [inv_of_cube hC (psi_k2 hC) (ord3_spec gensParts.k2o).1, map_mul, psi_k2 hC, pkMat_mulF2]
  · change psi xaY⁻¹ = _
    rw [inv_of_sq hC (psi_xa hC) (ord2_spec gensParts.xao).1, psi_xa hC]
  · change psi xbY⁻¹ = _
    rw [inv_of_sq hC (psi_xb hC) (ord2_spec gensParts.xbo).1, psi_xb hC]

structure CosParts : Prop where
  r0 : repK rw 0 = oneF2 28
  r1 : repK rw 1 = blowW k2
  r2 : repK rw 2 = mulF2 28 (blowW k2) (blowW k2)
  inv : ∀ i < 36, mulF2 28 (repK rw i) (repK rv i) = oneF2 28
  cell : ∀ i < 36, ∀ k < 4, cellK rw i k (rt.getD (4 * i + k) (0, 0)) = true
  rc : ∀ i < 36, 3 ≤ i → (rc.getD i (0, 0)).1 < 4 ∧
    gapK 28 12 6 10 EQ2.CF 1024 (rc.getD i (0, 0)).2
      (mulF2 28 (mulF2 28 (mulF2 28 (repK rw i) (nthV gK (rc.getD i (0, 0)).1)) (repK rv i))
        (nthV (gMiK 0) (rc.getD i (0, 0)).1)) = true

theorem cosParts : CosParts := by
  have h := ch733011_cosets
  unfold cosetK at h
  obtain ⟨h0, h⟩ := andB_iff.mp h
  obtain ⟨h1, h⟩ := andB_iff.mp h
  obtain ⟨h2, h⟩ := andB_iff.mp h
  obtain ⟨h3, h4⟩ := andB_iff.mp h
  refine ⟨beq_iff'.mp h0, beq_iff'.mp h1, beq_iff'.mp h2,
    fun i hi => beq_iff'.mp (andB_iff.mp (allN_iff'.mp h3 i hi)).1,
    fun i hi k hk => allN_iff'.mp (andB_iff.mp (allN_iff'.mp h3 i hi)).2 k hk, fun i hi h3i => ?_⟩
  have e := allN_iff'.mp h4 i hi
  have hb : Nat.blt i 3 = false :=
    Bool.eq_false_iff.mpr fun hh => by
      have := Nat.le_of_ble_eq_true hh
      omega
  rw [hb, strictB_eq'] at e
  obtain ⟨e1, e2⟩ := andB_iff.mp e
  exact ⟨Nat.le_of_ble_eq_true e1, e2⟩

theorem rY_mul_rvY (hC : ChevFacts) {i : ℕ} (hi : i < 36) : rY i * rvY i = 1 :=
  psi_injective hC (by rw [map_mul, psi_rY hC hi, psi_rvY hC hi, ← pkMat_mulF2,
    cosParts.inv i hi, pkMat_oneF2, map_one])

theorem rY_zero (hC : ChevFacts) : rY 0 = 1 :=
  psi_injective hC (by rw [psi_rY hC (by norm_num), cosParts.r0, pkMat_oneF2, map_one])

theorem rY_one (hC : ChevFacts) : rY 1 = k2Y :=
  psi_injective hC (by rw [psi_rY hC (by norm_num), cosParts.r1, psi_k2 hC])

theorem rY_two (hC : ChevFacts) : rY 2 = k2Y * k2Y :=
  psi_injective hC (by rw [psi_rY hC (by norm_num), cosParts.r2, map_mul, psi_k2 hC, pkMat_mulF2])

@[expose] def InCos (x : Y) : Prop := ∃ i < 36, ∃ q ∈ Q2, x = q * rY i

theorem inCos_mul_gB0 (hC : ChevFacts) {x : Y} (hx : InCos x) (k : Fin 4) : InCos (x * gB0 k) := by
  obtain ⟨i, hi, q, hq, rfl⟩ := hx
  have hcell := cosParts.cell i hi k.val k.2
  unfold cellK at hcell
  obtain ⟨e1, e2⟩ := andB_iff.mp hcell
  obtain ⟨e3, e4⟩ := andB_iff.mp e2
  have hπ := Nat.le_of_ble_eq_true e1
  have hs := Nat.le_of_ble_eq_true e3
  obtain ⟨z, hz, hzpsi⟩ := exists_mem_of_sorted (rQ2 hC) hs
  refine ⟨_, hπ, q * z, Q2.mul_mem hq hz, ?_⟩
  have e : rY i * gB0 k = z * rY (rt.getD (4 * i + k.val) (0, 0)).1 := by
    refine psi_injective hC ?_
    rw [map_mul, map_mul, psi_rY hC hi, psi_rY hC hπ, hzpsi, psi_gB0 hC, ← pkMat_mulF2,
      ← pkMat_mulF2, beq_iff'.mp e4]
  rw [mul_assoc, e, ← mul_assoc]

theorem inCos_one (hC : ChevFacts) : InCos 1 := ⟨0, by norm_num, 1, Q2.one_mem, by rw [rY_zero hC, one_mul]⟩

theorem inCos_of_mem (hC : ChevFacts) {y : Y} (hy : y ∈ Subgroup.closure (Set.range gB0)) :
    InCos y := by
  suffices h : ∀ x, InCos x → InCos (x * y) by simpa using h 1 (inCos_one hC)
  induction hy using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨k, rfl⟩ := hg
    exact fun x hx => inCos_mul_gB0 hC hx k
  | one => simpa using fun x hx => hx
  | mul a b _ _ iha ihb =>
    intro x hx
    rw [← mul_assoc]
    exact ihb _ (iha x hx)
  | inv a _ iha =>
    intro x hx
    have hfin : (setOf InCos).Finite := Set.toFinite _
    have hinj : Set.InjOn (fun z => z * a) (setOf InCos) := fun z _ w _ h =>
      mul_right_cancel (h : z * a = w * a)
    obtain ⟨z, hz, hza⟩ :=
      ((hfin.injOn_iff_bijOn_of_mapsTo fun z hz => iha z hz).mp hinj).surjOn hx
    have hza' : z * a = x := hza
    rw [← hza', mul_assoc, mul_inv_cancel, mul_one]
    exact hz

theorem ord3GoK_spec : ∀ (L : List ℕ) (start : ℕ), ord3GoK L start = true →
    ∀ i < L.length, ord3StepK (start + i) (L.getD i 0) = true
  | [], _, _ => by simp
  | j :: L, start, h => by
    obtain ⟨h1, h2⟩ := andB_iff.mp h
    intro i hi
    rcases i with _ | i
    · simpa using h1
    · have := ord3GoK_spec L (start + 1) h2 i (by simpa using hi)
      rw [show start + (i + 1) = start + 1 + i by omega]
      simpa using this

theorem psi_pcEltY2 (hC : ChevFacts) (j : ℕ) : psi (pcEltY pc2Y j) = pkMat 28 (pcK GQ2 j) :=
  psi_pcEltY (psi_pc2 hC) j

theorem mem_Q2_normal (hNQ : B0 ≤ Subgroup.normalizer (Q2 : Set Y)) {g q : Y} (hg : g ∈ B0)
    (hq : q ∈ Q2) : g * q * g⁻¹ ∈ Q2 :=
  (Subgroup.mem_normalizer_iff.mp (hNQ hg) q).mp hq

theorem exists_conj_k2Y' (hC : ChevFacts) (hcl : Subgroup.closure (Set.range gB0) = B0)
    (hNQ : B0 ≤ Subgroup.normalizer (Q2 : Set Y)) {y : Y} (hy : y ∈ B0) (ho : orderOf y = 3)
    (hc : ∀ b ∈ B0, ⁅y, b⁆ ∈ Q2) :
    ∃ j < 1024, ∃ u : Y, (u = k2Y ∨ u = k2Y * k2Y) ∧ y * pcEltY pc2Y j = pcEltY pc2Y j * u := by
  obtain ⟨i, hi, q, hq, rfl⟩ := inCos_of_mem hC (hcl ▸ hy)
  have hi3 : i < 3 := by
    by_contra h3
    obtain ⟨hk, hg⟩ := cosParts.rc i hi (by omega)
    set k : Fin 4 := ⟨(rc.getD i (0, 0)).1, hk⟩ with hkdef
    have hnot : rY i * gB0 k * rvY i * (gB0 k)⁻¹ ∉ Q2 :=
      not_mem_of_gap (rQ2 hC) (mulF2_lt' _ _) (by
        rw [map_mul, map_mul, map_mul, psi_rY hC hi, psi_rvY hC hi, psi_gB0 hC, psi_gB0_inv hC,
          ← pkMat_mulF2, ← pkMat_mulF2, ← pkMat_mulF2]) hg
    apply hnot
    have hrv : rvY i = (rY i)⁻¹ := (inv_eq_of_mul_eq_one_right (rY_mul_rvY hC hi)).symm
    have hgB : gB0 k ∈ B0 := gB0_mem_B0' hC k
    have hcomm := hc _ hgB
    have hgq : gB0 k * q⁻¹ * (gB0 k)⁻¹ ∈ Q2 := mem_Q2_normal hNQ hgB (Q2.inv_mem hq)
    have e : rY i * gB0 k * rvY i * (gB0 k)⁻¹ =
        q⁻¹ * ⁅q * rY i, gB0 k⁆ * (gB0 k * q⁻¹ * (gB0 k)⁻¹)⁻¹ := by
      rw [hrv, commutatorElement_def]
      group
    rw [e]
    exact Q2.mul_mem (Q2.mul_mem (Q2.inv_mem hq) hcomm) (Q2.inv_mem hgq)
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [rY_zero hC, mul_one] at ho
    have hd := Subgroup.orderOf_dvd_natCard Q2 hq
    rw [ho, card_Q2' hC] at hd
    norm_num at hd
  obtain ⟨t, ht, hqt⟩ := exists_entry_of_recOK (rQ2 hC) hq
  obtain ⟨s, hs, es⟩ := exists_sorted_of_entry (rQ2 hC).h ht
  have hlen : o3.length = 2048 := by
    have h := ch733011_order3
    unfold ord3QK at h
    exact beq_iff'.mp (andB_iff.mp h).1
  have hgo : ord3GoK o3 0 = true := by
    have h := ch733011_order3
    unfold ord3QK at h
    exact (andB_iff.mp h).2
  have hstep := ord3GoK_spec o3 0 hgo (1024 * (i - 1) + s) (by omega)
  rw [zero_add] at hstep
  unfold ord3StepK at hstep
  have hmod : Nat.mod (1024 * (i - 1) + s) 1024 = s := by
    change (1024 * (i - 1) + s) % 1024 = s
    omega
  have hdiv : Nat.div (1024 * (i - 1) + s) 1024 = i - 1 := by
    change (1024 * (i - 1) + s) / 1024 = i - 1
    omega
  rw [hmod, hdiv, strictB_eq'] at hstep
  have hK : psi (rY i) = pkMat 28 (kPowK (i - 1)) := by
    rcases (by omega : i = 1 ∨ i = 2) with rfl | rfl
    · rw [rY_one hC, psi_k2 hC]
      rfl
    · rw [rY_two hC, map_mul, psi_k2 hC, ← pkMat_mulF2]
      rfl
  have hyp : psi (q * rY i) = pkMat 28 (mulF2 28 (sortedAt 28 12 6 10 EQ2.CF s) (kPowK (i - 1))) := by
    rw [map_mul, hqt, ← es, hK, pkMat_mulF2]
  have hcube : mulF2 28 (mulF2 28 (mulF2 28 (sortedAt 28 12 6 10 EQ2.CF s) (kPowK (i - 1)))
      (mulF2 28 (sortedAt 28 12 6 10 EQ2.CF s) (kPowK (i - 1))))
      (mulF2 28 (sortedAt 28 12 6 10 EQ2.CF s) (kPowK (i - 1))) = oneF2 28 := by
    have hy3 : (q * rY i) ^ 3 = 1 := by
      rw [← ho]
      exact pow_orderOf_eq_one _
    have hx3 : (q * rY i) * (q * rY i) * (q * rY i) = 1 := by
      rw [← pow_two, ← pow_succ]
      exact hy3
    refine eq_of_pk (mulF2_lt' _ _) oneF2_lt ?_
    rw [pkMat_mulF2, pkMat_mulF2, ← hyp, pkMat_oneF2, ← map_mul, ← map_mul, hx3, map_one]
  rw [hcube, Nat.beq_refl] at hstep
  obtain ⟨hj, hT⟩ := andB_iff.mp hstep
  rw [strictB_eq', strictB_eq'] at hT
  refine ⟨_, Nat.le_of_ble_eq_true hj, ?_⟩
  have hor : mulF2 28 (mulF2 28 (sortedAt 28 12 6 10 EQ2.CF s) (kPowK (i - 1)))
        (pcK GQ2 (o3.getD (1024 * (i - 1) + s) 0)) =
        mulF2 28 (pcK GQ2 (o3.getD (1024 * (i - 1) + s) 0)) (blowW k2) ∨
      mulF2 28 (mulF2 28 (sortedAt 28 12 6 10 EQ2.CF s) (kPowK (i - 1)))
        (pcK GQ2 (o3.getD (1024 * (i - 1) + s) 0)) =
        mulF2 28 (pcK GQ2 (o3.getD (1024 * (i - 1) + s) 0)) (mulF2 28 (blowW k2) (blowW k2)) := by
    unfold CFSG.KLie.CT.orB at hT
    cases h1 : Nat.beq (mulF2 28 (mulF2 28 (sortedAt 28 12 6 10 EQ2.CF s) (kPowK (i - 1)))
      (pcK GQ2 (o3.getD (1024 * (i - 1) + s) 0)))
      (mulF2 28 (pcK GQ2 (o3.getD (1024 * (i - 1) + s) 0)) (blowW k2))
    · rw [h1] at hT
      exact Or.inr (beq_iff'.mp hT)
    · exact Or.inl (beq_iff'.mp h1)
  rcases hor with h1 | h1
  · refine ⟨k2Y, Or.inl rfl, psi_injective hC ?_⟩
    rw [map_mul, hyp, map_mul, psi_pcEltY2 hC, psi_k2 hC, ← pkMat_mulF2, ← pkMat_mulF2, h1]
  · refine ⟨k2Y * k2Y, Or.inr rfl, psi_injective hC ?_⟩
    rw [map_mul, hyp, map_mul, map_mul, psi_pcEltY2 hC, psi_k2 hC, ← pkMat_mulF2, ← pkMat_mulF2,
      ← pkMat_mulF2, h1]

theorem k2Y_commute_Z2' (hC : ChevFacts)
    (hZ2 : Z2 = Subgroup.closure {pc2Y 6, pc2Y 7, pc2Y 8, pc2Y 9}) :
    ∀ z ∈ Z2, k2Y * z = z * k2Y := by
  have hcent := ch733011_cent
  unfold centK at hcent
  obtain ⟨-, h2⟩ := andB_iff.mp hcent
  obtain ⟨h3, -⟩ := andB_iff.mp h2
  have hk : ∀ r : Fin 4, k2Y * pc2Y ⟨r.val + 6, by omega⟩ = pc2Y ⟨r.val + 6, by omega⟩ * k2Y := by
    intro r
    have e := allN_iff'.mp h3 r.val r.2
    refine psi_injective hC ?_
    rw [map_mul, map_mul, psi_k2 hC, psi_pc2 hC, ← pkMat_mulF2, ← pkMat_mulF2]
    exact congrArg (pkMat 28) (beq_iff'.mp e)
  have hZ2C : Z2 ≤ Subgroup.centralizer ({k2Y} : Set Y) := by
    rw [hZ2]
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hk 0
    · exact hk 1
    · exact hk 2
    · exact hk 3
  intro z hz
  exact (Subgroup.mem_centralizer_iff.mp (hZ2C hz)) k2Y (Set.mem_singleton k2Y)

theorem zcGoK_spec : ∀ (L : List ℕ) (start : ℕ), zcGoK L start = true →
    ∀ i < L.length, zcStepK (start + i) (L.getD i 0) = true
  | [], _, _ => by simp
  | j :: L, start, h => by
    obtain ⟨h1, h2⟩ := andB_iff.mp h
    intro i hi
    rcases i with _ | i
    · simpa using h1
    · have := zcGoK_spec L (start + 1) h2 i (by simpa using hi)
      rw [show start + (i + 1) = start + 1 + i by omega]
      simpa using this

theorem mem_Z2_of_commute (hC : ChevFacts)
    (hZ2 : Z2 = Subgroup.closure {pc2Y 6, pc2Y 7, pc2Y 8, pc2Y 9}) {q : Y} (hq : q ∈ Q2)
    (hqk : Commute q k2Y) : q ∈ Z2 := by
  obtain ⟨t, ht, hqt⟩ := exists_entry_of_recOK (rQ2 hC) hq
  obtain ⟨s, hs, es⟩ := exists_sorted_of_entry (rQ2 hC).h ht
  have hzc := ch733011_zc
  unfold zcK at hzc
  obtain ⟨hl, hgo⟩ := andB_iff.mp hzc
  have hstep := zcGoK_spec zc 0 hgo s (by rw [beq_iff'.mp hl]; exact hs)
  rw [zero_add] at hstep
  unfold zcStepK at hstep
  rw [strictB_eq'] at hstep
  have hpsi : psi q = pkMat 28 (sortedAt 28 12 6 10 EQ2.CF s) := by rw [hqt, ← es]
  have hcomm : commK (sortedAt 28 12 6 10 EQ2.CF s) (blowW k2) = true := by
    unfold commK
    rw [beq_iff']
    refine eq_of_pk (mulF2_lt' _ _) (mulF2_lt' _ _) ?_
    rw [pkMat_mulF2, pkMat_mulF2, ← hpsi, ← psi_k2 hC, ← map_mul, ← map_mul, hqk.eq]
  rw [hcomm] at hstep
  obtain ⟨hj, hj2⟩ := andB_iff.mp hstep
  obtain ⟨hj64, hX⟩ := andB_iff.mp hj2
  have hqe : q = pcEltY pc2Y (zc.getD s 0) := by
    refine psi_injective hC ?_
    rw [hpsi, psi_pcEltY2 hC, beq_iff'.mp hX]
  rw [hqe, hZ2]
  have hdiv : 2 ^ 6 ∣ zc.getD s 0 := Nat.dvd_of_mod_eq_zero (beq_iff'.mp hj64)
  refine (Subgroup.closure_le _).mpr ?_ (CFSG.Quasithin.St84.G24Table.pcEltY_mem_closure_ge pc2Y hdiv)
  rintro x ⟨m, rfl⟩
  refine Subgroup.subset_closure ?_
  have hm : m.1.val = 6 ∨ m.1.val = 7 ∨ m.1.val = 8 ∨ m.1.val = 9 := by
    have := m.2
    have := m.1.isLt
    omega
  change pc2Y m.1 ∈ ({pc2Y 6, pc2Y 7, pc2Y 8, pc2Y 9} : Set Y)
  rcases hm with h | h | h | h
  · rw [show m.1 = (6 : Fin 10) from Fin.ext h]
    simp
  · rw [show m.1 = (7 : Fin 10) from Fin.ext h]
    simp
  · rw [show m.1 = (8 : Fin 10) from Fin.ext h]
    simp
  · rw [show m.1 = (9 : Fin 10) from Fin.ext h]
    simp

theorem comm_Z2_of_conj' {t u y : Y} (ht : t ∈ Q2) (hu : u = k2Y ∨ u = k2Y * k2Y)
    (heq : y * t = t * u) (hkZ : ∀ z ∈ Z2, k2Y * z = z * k2Y) :
    ∀ z ∈ Z2, y * z = z * y := by
  intro z hz
  have hzt : Commute z t := by
    have hzc : z ∈ Subgroup.centralizer (Q2 : Set Y) := (Subgroup.mem_inf.mp hz).2
    exact ((Subgroup.mem_centralizer_iff.mp hzc) t ht).symm
  have hzu : Commute z u := by
    rcases hu with rfl | h2
    · exact (hkZ z hz).symm
    · rw [h2]
      have hk : Commute z k2Y := (hkZ z hz).symm
      exact hk.mul_right hk
  have hy : y = t * u * t⁻¹ := by
    calc y = (y * t) * t⁻¹ := by group
      _ = (t * u) * t⁻¹ := by rw [heq]
      _ = t * u * t⁻¹ := rfl
  rw [hy]
  exact ((hzt.mul_right hzu).mul_right hzt.inv_right).eq.symm

theorem centralizer_eq_of_conj' (hC : ChevFacts)
    (hZ2 : Z2 = Subgroup.closure {pc2Y 6, pc2Y 7, pc2Y 8, pc2Y 9}) {t u y : Y}
    (ht : t ∈ Q2) (hu : u = k2Y ∨ u = k2Y * k2Y)
    (heq : y * t = t * u) (hky : ∀ z ∈ Z2, y * z = z * y) :
    Q2 ⊓ Subgroup.centralizer ({y} : Set Y) = Z2 := by
  have hk2Y3 : k2Y ^ 3 = 1 := by
    rw [← orderOf_k2Y' hC]
    exact pow_orderOf_eq_one _
  have hy_eq : y = t * u * t⁻¹ := by
    calc y = (y * t) * t⁻¹ := by group
      _ = (t * u) * t⁻¹ := by rw [heq]
      _ = t * u * t⁻¹ := rfl
  apply le_antisymm
  · intro q hq
    obtain ⟨hqQ, hqC⟩ := Subgroup.mem_inf.mp hq
    have hqy : Commute q y :=
      ((Subgroup.mem_centralizer_iff.mp hqC) y (Set.mem_singleton y)).symm
    have hq'Q : t⁻¹ * q * t ∈ Q2 := Q2.mul_mem (Q2.mul_mem (Q2.inv_mem ht) hqQ) ht
    have hq'u : Commute (t⁻¹ * q * t) u := by
      have h1 : t⁻¹ * y * t = u := by rw [hy_eq]; group
      have h : t⁻¹ * (y * q) * t = t⁻¹ * (q * y) * t :=
        congrArg (fun w => t⁻¹ * w * t) hqy.eq.symm
      have e1 : t⁻¹ * (y * q) * t = u * (t⁻¹ * q * t) := by
        rw [show t⁻¹ * (y * q) * t = (t⁻¹ * y * t) * (t⁻¹ * q * t) from by group, h1]
      have e2 : t⁻¹ * (q * y) * t = (t⁻¹ * q * t) * u := by
        rw [show t⁻¹ * (q * y) * t = (t⁻¹ * q * t) * (t⁻¹ * y * t) from by group, h1]
      rw [e1, e2] at h
      exact h.symm
    have hq'k : Commute (t⁻¹ * q * t) k2Y := by
      rcases hu with rfl | h2
      · exact hq'u
      · rw [h2] at hq'u
        have h4 := hq'u.pow_right 2
        have hk : (k2Y * k2Y) ^ 2 = k2Y := by
          have h5 : (k2Y * k2Y) ^ 2 = k2Y ^ 3 * k2Y := by
            rw [← pow_succ, ← pow_two, ← pow_mul]
          rw [h5, hk2Y3, one_mul]
        rw [hk] at h4
        exact h4
    have hq'Z : t⁻¹ * q * t ∈ Z2 := mem_Z2_of_commute hC hZ2 hq'Q hq'k
    have htq' : Commute (t⁻¹ * q * t) t := by
      have hz : t⁻¹ * q * t ∈ Subgroup.centralizer (Q2 : Set Y) :=
        (Subgroup.mem_inf.mp hq'Z).2
      exact ((Subgroup.mem_centralizer_iff.mp hz) t ht).symm
    have hqeq : q = t⁻¹ * q * t := by
      calc q = t * (t⁻¹ * q * t) * t⁻¹ := by group
        _ = (t⁻¹ * q * t) * t * t⁻¹ := by rw [htq'.eq]
        _ = t⁻¹ * q * t := by group
    rw [hqeq]
    exact hq'Z
  · refine le_inf inf_le_left ?_
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact hky z hz

@[expose] def gEY : Fin 2 → Y := ![xY 0 1, xY 0 F4.ω]

theorem psi_gEY (hC : ChevFacts) (j : Fin 2) : psi (gEY j) = pkMat 28 (nthV GE j.val) := by
  fin_cases j
  · change psi (xY 0 1) = pkMat 28 (bX 1)
    rw [psi_xY hC, ix_val, code_one]
    rfl
  · change psi (xY 0 F4.ω) = pkMat 28 (bX 2)
    rw [psi_xY hC, ix_val, code_omega]
    rfl

theorem rE (hC : ChevFacts) : RecOK gEY 6 EE.CF (genR 28 12 6 2 EE.CF) 4 :=
  ⟨fun j => by rw [psi_gEY hC, beq_iff'.mp (allN_iff'.mp ch733011_ePins j.val j.2)],
    by norm_num, by norm_num, ch733011_eHead, ch733011_eRecs⟩

theorem eParts : commK (blowW k2) (bX 1) = true ∧ commK (blowW k2) (bX 2) = true ∧
    ∀ s < 4, sortedAt 28 12 6 2 EE.CF s = oneF2 28 ∨
      gapK 28 12 6 10 EQ2.CF 1024 (nthV ej s) (sortedAt 28 12 6 2 EE.CF s) = true := by
  have h := ch733011_e
  unfold eK at h
  obtain ⟨h1, h⟩ := andB_iff.mp h
  obtain ⟨h2, h3⟩ := andB_iff.mp h
  refine ⟨h1, h2, fun s hs => ?_⟩
  have e := allN_iff'.mp h3 s hs
  rw [strictB_eq'] at e
  cases hX : Nat.beq (sortedAt 28 12 6 2 EE.CF s) (oneF2 28)
  · rw [hX] at e
    exact Or.inr e
  · exact Or.inl (beq_iff'.mp hX)

theorem E_inf_Q2 (hC : ChevFacts) {e : Y} (heE : e ∈ Subgroup.closure (Set.range gEY))
    (heQ : e ∈ Q2) : e = 1 := by
  obtain ⟨t, ht, hx⟩ := exists_entry_of_recOK (rE hC) heE
  obtain ⟨s, hs, es⟩ := exists_sorted_of_entry (rE hC).h ht
  rcases eParts.2.2 s hs with h1 | h1
  · refine psi_injective hC ?_
    rw [hx, ← es, h1, pkMat_oneF2, map_one]
  · exact absurd heQ (not_mem_of_gap (rQ2 hC) (es ▸ CFSG.KC.F2Mat.elemAt_lt _ _ _ _ _ _)
      (by rw [hx, ← es]) h1)

theorem gEY_commute_k2Y (hC : ChevFacts) (j : Fin 2) : Commute (gEY j) k2Y := by
  refine (commute_of_pk hC (psi_k2 hC) (psi_gEY hC j) ?_).symm
  fin_cases j
  · exact eParts.1
  · exact eParts.2.1

theorem fourGroup_exists' (hC : ChevFacts) (hQ2T : Q2 ≤ T0) {y : Y} {j : ℕ} {u : Y}
    (hu : u = k2Y ∨ u = k2Y * k2Y) (heq : y * pcEltY pc2Y j = pcEltY pc2Y j * u) :
    ∃ E : Subgroup Y, E ≤ B0 ⊓ Subgroup.centralizer ({y} : Set Y) ∧ Nat.card E = 4 ∧
      E ⊓ Z2 = ⊥ := by
  set t := pcEltY pc2Y j with htdef
  set K := Subgroup.closure (Set.range gEY) with hKdef
  have htj : t ∈ Q2 := pcEltY_mem_closure pc2Y j
  have htB0 : t ∈ B0 := hC.T0_le_B0 (hQ2T htj)
  have hy_eq : y = t * u * t⁻¹ := by
    calc y = (y * t) * t⁻¹ := by group
      _ = (t * u) * t⁻¹ := by rw [heq]
      _ = t * u * t⁻¹ := rfl
  have hKB0 : K ≤ B0 := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hC.xY_mem_B0 0 1
    · exact hC.xY_mem_B0 0 F4.ω
  have hxu : ∀ x ∈ K, Commute x u := by
    intro x hx
    have hKC : K ≤ Subgroup.centralizer ({u} : Set Y) := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨i, rfl⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      rcases hu with rfl | rfl
      · exact (gEY_commute_k2Y hC i).eq.symm
      · exact ((gEY_commute_k2Y hC i).mul_right (gEY_commute_k2Y hC i)).eq.symm
    exact ((Subgroup.mem_centralizer_iff.mp (hKC hx)) u (Set.mem_singleton u)).symm
  refine ⟨Subgroup.map (MulAut.conj t).toMonoidHom K, le_inf ?_ ?_, ?_, ?_⟩
  · intro z hz
    rw [Subgroup.mem_map] at hz
    obtain ⟨x, hxK, rfl⟩ := hz
    change t * x * t⁻¹ ∈ B0
    exact B0.mul_mem (B0.mul_mem htB0 (hKB0 hxK)) (B0.inv_mem htB0)
  · intro z hz
    rw [Subgroup.mem_map] at hz
    obtain ⟨x, hxK, rfl⟩ := hz
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    have hxy : Commute ((MulAut.conj t) x) ((MulAut.conj t) u) := (hxu x hxK).conj t
    rw [show y = (MulAut.conj t) u from by rw [MulAut.conj_apply]; exact hy_eq]
    exact hxy.eq.symm
  · rw [Subgroup.card_map_of_injective (MulAut.conj t).injective]
    exact card_of_recOK hC (rE hC)
  · rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzQ, hzZ⟩ := Subgroup.mem_inf.mp hz
    rw [Subgroup.mem_map] at hzQ
    obtain ⟨e, heK, hconj⟩ := hzQ
    have hzQ2 : z ∈ Q2 := (Subgroup.mem_inf.mp hzZ).1
    have hzT : Commute z t := by
      have hzc : z ∈ Subgroup.centralizer (Q2 : Set Y) := (Subgroup.mem_inf.mp hzZ).2
      exact ((Subgroup.mem_centralizer_iff.mp hzc) t htj).symm
    have hez : e = z := by
      have hconj' : (MulAut.conj t) e = z := hconj
      have h1 : z = t * e * t⁻¹ := by rw [← hconj', MulAut.conj_apply]
      calc e = t⁻¹ * (t * e * t⁻¹) * t := by group
        _ = t⁻¹ * z * t := by rw [← h1]
        _ = t⁻¹ * (z * t) := by group
        _ = t⁻¹ * (t * z) := by rw [hzT.eq]
        _ = z := by group
    have he1 : e = 1 := E_inf_Q2 hC heK (hez ▸ hzQ2)
    refine Subgroup.mem_bot.mpr ?_
    rw [← hconj, he1, map_one]

theorem central_mod_Q2' (hC : ChevFacts) (hcl : Subgroup.closure (Set.range gB0) = B0)
    (hQ2T : Q2 ≤ T0) (hNQ : M2 ≤ Subgroup.normalizer (Q2 : Set Y))
    (hZ2 : Z2 = Subgroup.closure {pc2Y 6, pc2Y 7, pc2Y 8, pc2Y 9})
    {y : Y} (hy : y ∈ B0) (ho : orderOf y = 3) (hc : ∀ b ∈ B0, ⁅y, b⁆ ∈ Q2) :
    (∀ z ∈ Z2, y * z = z * y) ∧ Q2 ⊓ Subgroup.centralizer ({y} : Set Y) = Z2 ∧
      ∃ E : Subgroup Y, E ≤ B0 ⊓ Subgroup.centralizer ({y} : Set Y) ∧ Nat.card E = 4 ∧
        E ⊓ Z2 = ⊥ := by
  obtain ⟨j, -, u, hu, heq⟩ := exists_conj_k2Y' hC hcl (hC.B0_le_M2.trans hNQ) hy ho hc
  have htj : pcEltY pc2Y j ∈ Q2 := pcEltY_mem_closure pc2Y j
  have hky := comm_Z2_of_conj' htj hu heq (k2Y_commute_Z2' hC hZ2)
  exact ⟨hky, centralizer_eq_of_conj' hC hZ2 htj hu heq hky, fourGroup_exists' hC hQ2T hu heq⟩

theorem normalFacts (hC : ChevFacts) : NormalFacts where
  eq_Q1_or_eq_Q2 := fun hH0 hcH0 hQ1T hQ2T hcQ1 hcQ2 _ hNB hBN hN =>
    eq_Q1_or_eq_Q2' hC hH0 hcH0 hQ1T hQ2T hcQ1 hcQ2 hNB hBN hN
  central_mod_Q2 := fun hcl hQ2T hNQ hZ2 _ hy ho hc => central_mod_Q2' hC hcl hQ2T hNQ hZ2 hy ho hc

end CFSG.KD.G24B
