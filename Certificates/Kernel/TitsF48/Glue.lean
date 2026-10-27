module

public import Certificates.Kernel.TitsF48.Checks
public import Certificates.Kernel.TitsD.Checks
public import Certificates.Kernel.TitsOct.Glue15080
public import Certificates.Certificate2270
public import CFSG.Certificates.Kernel.TitsF48Sound
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoLocLn
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoLocPtMain

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsF48

open CFSG.KC.Enum CFSG.KS CFSG.KC.TwoF4LieK CFSG.KC.TitsOctK CFSG.KC.TwoF4LieSound
  CFSG.KC.TitsOctSound CFSG.KC.TitsDK CFSG.KC.TitsF48K CFSG.KC.TitsF48Sound CFSG.KD.TitsF48
  CFSG.Sporadic.Schreier.Tits CFSG.Quasithin CFSG.Quasithin.H13.F45Ru CFSG.Quasithin.TitsGeo
  CertificateChecks.KernelMisc CertificateChecks.KernelTitsOct

open scoped Pointwise

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

@[expose] noncomputable def gH (j : ℕ) : Pm := genPerm titsHArrs j

theorem permOfArr_rep' {t : Array ℕ} {g : Pm} (h : CFSG.Monster.B.Co2.Rep 1755 t g) :
    CFSG.Monster.B.Co2.permOfArr 1755 t = g := by
  have hc : (∀ i < 1755, t[i]! < 1755) ∧ ∀ i < 1755, ∀ j < 1755, t[i]! = t[j]! → i = j :=
    ⟨fun i hi => h.lt hi, fun i hi j hj hij => by
      rw [h.apply hi, h.apply hj] at hij
      have := g.injective (Fin.ext hij)
      simpa using this⟩
  ext x
  rw [CFSG.Monster.B.Co2.permOfArr, dite_eq_left hc]
  change t[(x : ℕ)]! = _
  exact h x

theorem field_get {L₀ m j : ℕ} (hj : j < m) (h96 : L₀ + j < 96) :
    (titsField1755 L₀ m)[j]! = CFSG.KS.Raw.unpack 1755 11 (TitsText.F (L₀ + j)) := by
  rw [titsField1755, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn,
    TitsText.titsArr1755_eq h96]

theorem pr_field {L₀ m j : ℕ} (hj : j < m) (h96 : L₀ + j < 96) {I : ℕ}
    (h : permOK 1755 11 (mask 11) (1755 * 11) (TitsText.F (L₀ + j)) I = true) :
    PR (TitsText.F (L₀ + j)) (CFSG.Monster.B.Co2.permOfArr 1755 (titsField1755 L₀ m)[j]!) ∧
      PR I (CFSG.Monster.B.Co2.permOfArr 1755 (titsField1755 L₀ m)[j]!)⁻¹ := by
  obtain ⟨g, hg, hgi⟩ := CFSG.KC.EnumSound.permOK_perm h
  rw [field_get hj h96, permOfArr_rep' (CFSG.KS.Raw.Orb.rep_unpack hg)]
  exact ⟨hg, hgi⟩

theorem hHG {j : ℕ} (hj : j < 9) : PR (HG j) (gH j) ∧ PR (CFSG.KD.TitsD.HI j) (gH j)⁻¹ :=
  pr_field (L₀ := 43) (m := 9) hj (by omega) (allN_iff'.1 CertificateChecks.KernelTitsD.invH j hj)

theorem hQ0 : PR Q0 (genPerm titsNArrs 3) :=
  (pr_field (L₀ := 61) (m := 10) (j := 3) (by norm_num) (by norm_num)
    (allN_iff'.1 CertificateChecks.KernelTitsD.invN 3 (by norm_num))).1

theorem gH_mem {j : ℕ} (hj : j < 9) : gH j ∈ titsH := genH_mem hj

theorem q0_mem : genPerm titsNArrs 3 ∈ titsN := genN_mem (by norm_num)

theorem lett_eq' (F FI : ℕ → ℕ) (c : ℕ) :
    lett F FI c = if c % 2 = 0 then F (c / 2 - 1) else FI (c / 2 - 1) := by
  have h1 : Nat.land c 1 = c % 2 := Nat.and_one_is_mod c
  have h2 : Nat.shiftRight c 1 = c / 2 := by
    change c >>> 1 = c / 2
    rw [Nat.shiftRight_eq_div_pow, pow_one]
  unfold lett
  rw [nIf_d, beq_d, h1, h2]
  simp

theorem lett_prep9 {c : ℕ} (hc : 2 ≤ c) (hc' : c < 20) :
    PR (lett HG CFSG.KD.TitsD.HI c) (letP gH c) := by
  rw [lett_eq']
  unfold letP
  split_ifs
  · exact (hHG (by omega)).1
  · exact (hHG (by omega)).2

theorem wPt9 : ∀ wd : List ℕ, (∀ c ∈ wd, 2 ≤ c ∧ c < 20) →
    ∀ x : Fin 1755, wPt HG CFSG.KD.TitsD.HI wd x = (wordP gH wd x : ℕ)
  | [], _, x => by simp [wordP, wPt]
  | c :: wd, hw, x => by
    have h1 := lett_prep9 (hw c List.mem_cons_self).1 (hw c List.mem_cons_self).2
    have h2 := wPt9 wd (fun c' hc' => hw c' (List.mem_cons_of_mem _ hc')) x
    have e : wPt HG CFSG.KD.TitsD.HI (c :: wd) x =
        gp (lett HG CFSG.KD.TitsD.HI c) (wPt HG CFSG.KD.TitsD.HI wd x) := strictN_eq' _ _
    rw [e, h2, gp_eq h1 (wordP gH wd x)]
    simp [wordP, Equiv.Perm.mul_apply]

theorem word9_mem {wd : List ℕ} (hw : ∀ c ∈ wd, 2 ≤ c ∧ c < 20) : wordP gH wd ∈ titsH := by
  unfold wordP
  refine Subgroup.list_prod_mem (K := titsH) ?_
  intro x hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
  have h9 : c / 2 - 1 < 9 := by have := hw c hc; omega
  unfold letP
  split_ifs
  · exact gH_mem h9
  · exact Subgroup.inv_mem _ (gH_mem h9)

@[expose] noncomputable def fE (j : ℕ) : Pm := wordP gH (fws.getD j [])

@[expose] noncomputable def gE (i : ℕ) : Pm := wordP gH (gws.getD i [])

theorem fws_codes : ∀ j < 6, (fws.getD j []).length ≤ 3 ∧ ∀ c ∈ fws.getD j [], 2 ≤ c ∧ c < 20 := by
  rw [fwsEq]
  decide

theorem gws_codes : ∀ i < 4, ∀ c ∈ gws.getD i [], 2 ≤ c ∧ c < 20 := by
  rw [gwsEq]
  decide

theorem fE_pr {j : ℕ} (hj : j < 6) : PR (FA j) (fE j) := by
  intro x
  have hl : fws.length = 6 := by rw [fwsEq]; rfl
  have hj' : j < fws.length := by omega
  change gp (FA j) x = _
  rw [bindK_sound bindF j hj' x x.2, ← getD_eq [] hj', wPt9 _ (fws_codes j hj).2 x]
  rfl

theorem gE_pr {i : ℕ} (hi : i < 4) : PR (GG i) (gE i) := by
  intro x
  have hl : gws.length = 4 := by rw [gwsEq]; rfl
  have hi' : i < gws.length := by omega
  change gp (GG i) x = _
  rw [bindK_sound bindG i hi' x x.2, ← getD_eq [] hi', wPt9 _ (gws_codes i hi) x]
  rfl

theorem fE_mem {j : ℕ} (hj : j < 6) : fE j ∈ titsH := word9_mem (fws_codes j hj).2

theorem gE_mem {i : ℕ} (hi : i < 4) : gE i ∈ titsH := word9_mem (gws_codes i hi)

theorem ev_of_pr {P : ℕ} {g : Pm} (h : PR P g) : ∀ y < 1755, gp P y = ev g y :=
  fun _ hy => gp_ev h hy

theorem toTA_mem {x : Pm} (hx : x ∈ titsH) : x ∈ TA := titsD_le_titsA (titsH_le_titsD hx)

theorem memN_of {x : Pm} (hx : x ∈ titsH) {f : ℕ → ℕ} (hf : ∀ y < 1755, f y = ev x y)
    (h : lineMap lpF f 0 0 = true) : x ∈ titsN := by
  have hL := (lineMap_iff_smul (g := ⟨x, toTA_mem hx⟩) hf (by norm_num)).1 h
  exact RuType.J47.mem_titsN_of (titsH_le_titsD hx) hL

theorem near_iff {n : ℕ} (hn : n < 1755) :
    octGraph.dist (Sum.inl 0) (Sum.inl (⟨n, hn⟩ : Fin 1755)) = layAt LY n := by
  have hL := (lay_at lay0).1
  rw [ofCode_zero] at hL
  exact hL.dist_eq (Sum.inl ⟨n, hn⟩)

theorem itP_ev {N B : ℕ} {n β : Pm} (hN : PR N n) (hB : PR B β) {x : ℕ} (hx : x < 1755) :
    ∀ m, itP (fun y => gp N (gp B y)) m x = ev ((n * β) ^ m) x
  | 0 => by rw [itP_zero, pow_zero, ev_one]
  | m + 1 => by
    rw [itP_succ, itP_ev hN hB hx m, gp_ev hB (ev_lt _ hx), gp_ev hN (ev_lt _ (ev_lt _ hx)),
      pow_succ', ev_mul _ _ hx, ev_mul _ _ (ev_lt _ hx)]

theorem far2 : farK LY = true ∧ layAt LY 133 = 8 := by
  have := far
  rw [bAnd_eq', Bool.and_eq_true] at this
  exact ⟨this.1, Nat.eq_of_beq_eq_true this.2⟩

theorem rowsA : ∀ i < 1024, ∃ r, rowA FA FAI LY ORD PR LB PS (GG 0) Q0 (GG 2) (GG 3) S1 i r = true := by
  have hlen : WA.length = 1024 := by
    have := lens
    rw [bAnd_eq', Bool.and_eq_true] at this
    exact Nat.eq_of_beq_eq_true this.1
  intro i hi
  by_cases h5 : i < 512
  · have := rowsK_sound rowA0 i (by simp [hlen]; omega)
    exact ⟨_, by simpa using this⟩
  · have := rowsK_sound rowA1 (i - 512) (by simp [hlen]; omega)
    rw [show 512 + (i - 512) = i by omega] at this
    exact ⟨_, this⟩

theorem rowsB : ∀ i < 1024, ∃ r, rowB FA FAI LY ORD PR LB PS (GG 0) Q0 (GG 2) (GG 3) S2 i r = true := by
  have hlen : WB.length = 1024 := by
    have := lens
    rw [bAnd_eq', Bool.and_eq_true, bAnd_eq', Bool.and_eq_true] at this
    exact Nat.eq_of_beq_eq_true this.2.1
  intro i hi
  by_cases h5 : i < 512
  · have := rowsK_sound rowB0 i (by simp [hlen]; omega)
    exact ⟨_, by simpa using this⟩
  · have := rowsK_sound rowB1 (i - 512) (by simp [hlen]; omega)
    rw [show 512 + (i - 512) = i by omega] at this
    exact ⟨_, this⟩

theorem rowsC : ∀ i < 256, ∃ r, rowC FA LY ORD PR LB PS (GG 0) Q0 (GG 2) (GG 3) S1 S2 i r = true := by
  have hlen : WC.length = 256 := by
    have := lens
    rw [bAnd_eq', Bool.and_eq_true, bAnd_eq', Bool.and_eq_true] at this
    exact Nat.eq_of_beq_eq_true this.2.2
  intro i hi
  have := rowsK_sound rowC0 i (by omega)
  exact ⟨_, by simpa using this⟩

theorem facts4191 :
    (∀ p : Fin 1755, (∀ x ∈ titsH, x ∈ titsN → x p = p) → p = 0) ∧
    ∀ π : ↥titsH →* Equiv.Perm (Fin 1755),
      (∀ (x : Equiv.Perm (Fin 1755)) (hx : x ∈ titsH), x ∈ titsN → π ⟨x, hx⟩ = x) →
      (∀ (x : Equiv.Perm (Fin 1755)) (hx : x ∈ titsH) (p : Fin 1755),
        octGraph.dist (Sum.inl 0) (Sum.inl p) ≤ 6 → π ⟨x, hx⟩ p = x p) →
      (∀ (y : Equiv.Perm (Fin 1755)) (hy : y ∈ titsH) (q : Equiv.Perm (Fin 1755)), q ∈ titsN →
        (π ⟨y, hy⟩ * q) ^ 17971200 = 1) →
      ∀ y, π y = y := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9⟩ := smallF_sound small
  have hfN : ∀ j < 6, fE j ∈ titsN := fun j hj =>
    memN_of (fE_mem hj) (ev_of_pr (fE_pr hj)) (s2 j hj).1
  have htN : gE 1 ∈ titsN := memN_of (gE_mem (by norm_num)) (ev_of_pr (gE_pr (by norm_num))) s3
  have hb1N : gE 2 ∈ titsN := memN_of (gE_mem (by norm_num)) (ev_of_pr (gE_pr (by norm_num))) s4
  have hb2N : gE 3 ∈ titsN := memN_of (gE_mem (by norm_num)) (ev_of_pr (gE_pr (by norm_num))) s5
  have hnpr := gE_pr (i := 0) (by norm_num)
  have hnH : gE 0 ∈ titsH := gE_mem (by norm_num)
  have hnn : gE 0 * gE 0 = 1 := by
    apply ev_eq_one
    intro x hx
    rw [ev_mul _ _ hx, ← gp_ev hnpr hx, ← gp_ev hnpr (by rw [gp_ev hnpr hx]; exact ev_lt _ hx)]
    exact s1 x hx
  refine ⟨fun p hp => ?_, fun π hB hN hX y => ?_⟩
  ·
    by_contra hp0
    have ht : gp (GG 1) p = p := by
      rw [gp_ev (gE_pr (by norm_num)) p.2, ev_fin, hp _ (gE_mem (by norm_num)) htN]
    obtain ⟨j, hj, hjp⟩ := s9 p p.2 (fun h => hp0 (Fin.ext h)) ht
    apply hjp
    rw [gp_ev (fE_pr hj) p.2, ev_fin, hp _ (fE_mem hj) (hfN j hj)]
  ·
    set n := gE 0 with hn_def
    let nH : ↥titsH := ⟨n, hnH⟩
    have hnH2 : nH * nH = 1 := Subtype.ext hnn
    have hpn2 : π nH * π nH = 1 := by rw [← map_mul, hnH2, map_one]
    set σ : Pm := n * π nH with hσ
    have hπn : π nH = n * σ := by rw [hσ, ← mul_assoc, hnn, one_mul]
    have h6 : ∀ x < 1755, layAt LY x ≤ 6 → ev σ x = x := by
      intro x hx hl
      have h1 : π nH ⟨x, hx⟩ = n ⟨x, hx⟩ := hN n hnH ⟨x, hx⟩ (by rw [near_iff hx]; exact hl)
      have h2 : n (n ⟨x, hx⟩) = ⟨x, hx⟩ := by
        have := congrArg (fun g : Pm => g ⟨x, hx⟩) hnn
        simpa only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using this
      simp [ev, hx, hσ, Equiv.Perm.mul_apply, h1, h2]
    have hc : ∀ j < 6, σ * fE j = fE j * σ := by
      intro j hj
      have hcH : n * (fE j * n) ∈ titsH :=
        Subgroup.mul_mem _ hnH (Subgroup.mul_mem _ (fE_mem hj) hnH)
      have hf : ∀ y < 1755, (fun x => gp (GG 0) (gp (FA j) (gp (GG 0) x))) y =
          ev (n * (fE j * n)) y := by
        intro y hy
        have hy1 := ev_lt n hy
        have hy2 := ev_lt (fE j) hy1
        simp only
        rw [gp_ev hnpr hy, gp_ev (fE_pr hj) hy1, gp_ev hnpr hy2, ev_mul _ _ hy, ev_mul _ _ hy]
      have hcN : n * (fE j * n) ∈ titsN := memN_of hcH hf (s2 j hj).2
      have e1 : π ⟨fE j, fE_mem hj⟩ = fE j := hB _ (fE_mem hj) (hfN j hj)
      have e2 : π ⟨n * (fE j * n), hcH⟩ = n * (fE j * n) := hB _ hcH hcN
      have e3 : (⟨n * (fE j * n), hcH⟩ : ↥titsH) = nH * (⟨fE j, fE_mem hj⟩ * nH) := rfl
      have key : π nH * (fE j * π nH) = n * (fE j * n) := by
        rw [← e2, e3, map_mul, map_mul, e1]
      have key2 : π nH * fE j = n * (fE j * n) * π nH := by
        calc π nH * fE j = π nH * (fE j * (π nH * π nH)) := by rw [hpn2, mul_one]
          _ = (π nH * (fE j * π nH)) * π nH := by simp only [mul_assoc]
          _ = n * (fE j * n) * π nH := by rw [key]
      calc σ * fE j = n * (π nH * fE j) := by rw [hσ, mul_assoc]
        _ = n * (n * (fE j * n) * π nH) := by rw [key2]
        _ = (n * n) * (fE j * n) * π nH := by simp only [mul_assoc]
        _ = fE j * σ := by rw [hnn, one_mul, hσ]; simp only [mul_assoc]
    have h2 : (n * σ) ^ 2 = 1 := by rw [← hπn, sq, hpn2]
    have hrel : ∀ i, 2 ≤ i → i < 4 → ∀ m, (∀ x < 1755, itP (fun y => gp (GG 0) (gp (GG i) y)) m x = x) →
        (n * σ * gE i) ^ m = 1 := by
      intro i hi2 hi4 m hm
      have hbH := gE_mem (i := i) (by omega)
      have hbN : gE i ∈ titsN := by
        interval_cases i
        · exact hb1N
        · exact hb2N
      have hnb : (n * gE i) ^ m = 1 := by
        apply ev_eq_one
        intro x hx
        rw [← itP_ev hnpr (gE_pr (by omega)) hx]
        exact hm x hx
      have e : π ⟨gE i, hbH⟩ = gE i := hB _ hbH hbN
      have hprod : (nH * ⟨gE i, hbH⟩) ^ m = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_mul]
        exact hnb)
      rw [← hπn]
      have : π nH * gE i = π (nH * ⟨gE i, hbH⟩) := by rw [map_mul, e]
      rw [this, ← map_pow, hprod, map_one]
    have hr1 := hrel 2 (by norm_num) (by norm_num) 4 s6
    have hr2 := hrel 3 (by norm_num) (by norm_num) 5 s7
    have hXn : (n * σ * genPerm titsNArrs 3) ^ 17971200 = 1 := by
      rw [← hπn]
      exact hX n hnH _ q0_mem
    obtain ⟨hfar, h133⟩ := far2
    have hσ1 : σ = 1 := rigid2 (fun j hj => fE_pr hj) invFA recF half hfar h133 hnpr hQ0
      (gE_pr (by norm_num)) (gE_pr (by norm_num)) hnn rowsA rowsB rowsC h6 hc h2 hr1 hr2 hXn
    have hπn' : π nH = n := by rw [hπn, hσ1, mul_one]
    obtain ⟨x, hx⟩ := y
    have hxA := toTA_mem hx
    let g : ↥TA := ⟨x, hxA⟩
    have hx0 : x 0 = 0 := RuType.J47.fix_zero_of_mem_titsH hx
    have hw : x • titsLine 0 = titsLine (titsLineHom g 0) := (lineHom_eq_iff g 0 _).1 rfl
    have h0w : (0 : Fin 1755) ∈ titsLine (titsLineHom g 0) := by
      rw [← hw, ← hx0]
      exact Finset.smul_mem_smul_finset ((onLine_mem 0 0).1 onLine00)
    set v := titsLineHom g 0 with hv
    have hadj : adjK lpD 0 (1755 + v) = true := by
      have := (adj_iff (Sum.inl 0) (Sum.inr v)).1 (octGraph_adj_inl_inr.2 h0w)
      simpa [vCode] using this
    obtain ⟨k, hk, e⟩ := (nbOK.1 0 (by norm_num) _).1 hadj
    rw [degK_eq] at hk
    simp only [show (0 : ℕ) < 1755 by norm_num, if_true] at hk
    rw [nbK_pt (by norm_num)] at e
    have hpk : plK CFSG.KD.TitsOct.PL 0 k = v := by omega
    have htH := gE_mem (i := 1) (by norm_num)
    have hπt : π ⟨gE 1, htH⟩ = gE 1 := hB _ htH htN
    by_cases hv0 : (v : ℕ) = 0
    · have hL : x • titsLine 0 = titsLine 0 := by
        rw [hw]
        congr 1
        exact Fin.ext hv0
      exact hB x hx (RuType.J47.mem_titsN_of (titsH_le_titsD hx) hL)
    · obtain ⟨i, hi, hm⟩ := s8 k hk (by rw [hpk]; exact hv0)
      have hgi : gE 1 ^ i * n ∈ titsH := Subgroup.mul_mem _ (Subgroup.pow_mem _ htH i) hnH
      have hf : ∀ y < 1755, tn1 (GG 1) (GG 0) i y = ev (⟨_, toTA_mem hgi⟩ : ↥TA).1 y :=
        tn1_ev (gE_pr (by norm_num)) hnpr i
      have hwv : plK CFSG.KD.TitsOct.PL 0 k < 2925 := by rw [hpk]; exact v.2
      have hgiL := (lineMap_iff_smul hf hwv).1 hm
      have hgiL' : (gE 1 ^ i * n) • titsLine 0 = x • titsLine 0 := by
        rw [hgiL, hw]
        congr 1
        exact Fin.ext hpk
      let gi : ↥titsH := ⟨gE 1 ^ i * n, hgi⟩
      let b : ↥titsH := gi⁻¹ * ⟨x, hx⟩
      have hbL : b.1 • titsLine 0 = titsLine 0 := by
        change ((gE 1 ^ i * n)⁻¹ * x) • titsLine 0 = titsLine 0
        rw [mul_smul, ← hgiL', inv_smul_smul]
      have hbN : b.1 ∈ titsN := RuType.J47.mem_titsN_of (titsH_le_titsD b.2) hbL
      have e1 : π b = b := hB b.1 b.2 hbN
      have hπg : π gi = gE 1 ^ i * n := by
        have : gi = (⟨gE 1, htH⟩ : ↥titsH) ^ i * nH := rfl
        rw [this, map_mul, map_pow, hπt, hπn']
      have hgb : gi * b = ⟨x, hx⟩ := by rw [mul_inv_cancel_left]
      calc π ⟨x, hx⟩ = π (gi * b) := by rw [hgb]
        _ = π gi * π b := map_mul _ _ _
        _ = (gE 1 ^ i * n) * b.1 := by rw [hπg, e1]
        _ = x := congrArg Subtype.val hgb

end CertificateChecks.KernelTitsF48

end
