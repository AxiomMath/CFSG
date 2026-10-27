module

public import Certificates.Kernel.TitsOct.Glue

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsOct

open CFSG.KC.Enum CFSG.KS CFSG.KC.TwoF4LieK CFSG.KC.TitsOctK CFSG.KC.TwoF4LieSound
  CFSG.KC.TitsOctSound CFSG.KD.TitsOct CFSG.Sporadic.Schreier.Tits CFSG.Quasithin
  CFSG.Quasithin.H13.F45Ru

open scoped Pointwise

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

theorem lineMap_iff_smul {g : ↥TA} {f : ℕ → ℕ} (hf : ∀ y < 1755, f y = ev g.1 y) {w : ℕ}
    (hw : w < 2925) : lineMap lpD f 0 w = true ↔ g.1 • titsLine 0 = titsLine ⟨w, hw⟩ := by
  rw [lineMap_iff, ← line_iff hf 0 ⟨w, hw⟩]
  simp

theorem tn1_ev {T N : ℕ} {t n : Pm} (hT : PR T t) (hN : PR N n) :
    ∀ i, ∀ y < 1755, tn1 T N i y = ev (t ^ i * n) y
  | 0, y, hy => by
    change gp N y = _
    rw [gp_ev hN hy]
    simp
  | i + 1, y, hy => by
    change gp T (tn1 T N i y) = _
    rw [tn1_ev hT hN i y hy, gp_ev hT (ev_lt _ hy), pow_succ', mul_assoc, ev_mul t (t ^ i * n) hy]

theorem gen_ev {h : ℕ} (hh : h < 4) : ∀ y < 1755, gp (F h) y = ev (titsGen h) y :=
  fun _ hy => gp_ev (hF' h hh) hy

theorem genEl (h : ℕ) (hh : h < 4) : ∃ g : ↥TA, g.1 = titsGen h := ⟨⟨_, titsGen_mem_titsA hh⟩, rfl⟩

@[expose] noncomputable def aF (j : ℕ) : Pm := (wEl (fwPt.getD j [])).1

theorem aF_mem (j : ℕ) : aF j ∈ TA := (wEl (fwPt.getD j [])).2

theorem ev_zero' (g : Pm) : ev g 0 = (g 0 : ℕ) := by simp [ev]

theorem aF_prep {j : ℕ} (hj : j < 5) : PR (FP j) (aF j) := by
  intro x
  change gp (FP j) x = _
  obtain ⟨hl5, -, hc1, -⟩ := dWords
  have hj' : j < fwPt.length := by omega
  rw [bindK_sound bindP j hj' x x.2, wPt_ev (hc1 _ (List.getElem_mem hj')) x.2, ev_fin, aF,
    getD_eq _ hj']

theorem smul_zero_iff {g : ↥TA} : g • (Sum.inl 0 : Vtx) = Sum.inl 0 ↔ g.1 0 = 0 := by
  rw [smul_inl, Sum.inl.injEq]

theorem smul_line0_iff {g : ↥TA} : g • (Sum.inr 0 : Vtx) = Sum.inr 0 ↔ g.1 • titsLine 0 = titsLine 0 := by
  rw [smul_inr, Sum.inr.injEq, lineHom_eq_iff]

theorem nb0 : ∃ k < 5, nbK lpD PL 0 k = 1755 := by
  obtain ⟨k, hk, e⟩ := (nbOK.1 0 (by norm_num) 1755).1 (by decide +kernel)
  exact ⟨k, by rw [degK_eq] at hk; simpa using hk, e⟩

theorem aF_B {j : ℕ} (hj : j < 5) : aF j 0 = 0 ∧ aF j • titsLine 0 = titsLine 0 := by
  obtain ⟨h1, h2⟩ := fixV_sound (allN_iff'.1 fix0 j hj)
  have hf : ∀ y < 1755, gp (FP j) y = ev (wEl (fwPt.getD j [])).1 y :=
    fun y hy => by rw [gp_ev (aF_prep hj) hy]; rfl
  obtain ⟨k, hk, e⟩ := nb0
  have hk' : k < degK 0 := by rw [degK_eq]; simpa using hk
  have a1 := (actV_iff hf (by norm_num) (by norm_num)).1 h1
  have a2 := (actV_iff hf (by norm_num) (by norm_num)).1 (e ▸ h2 k hk')
  rw [ofCode_zero, smul_zero_iff] at a1
  rw [ofCode_1755, smul_line0_iff] at a2
  exact ⟨a1, a2⟩

theorem facts15080 :
    titsGen 3 * titsGen 3 = 1 ∧ titsGen 3 0 = 0 ∧ titsGen 1 0 = 0 ∧
    titsGen 1 • titsLine 0 = titsLine 0 ∧ titsGen 2 • titsLine 0 = titsLine 0 ∧
    (∀ v : Fin 2925, 0 ∈ titsLine v →
      v = 0 ∨ ∃ i < 4, (titsGen 1 ^ i * titsGen 3) • titsLine 0 = titsLine v) ∧
    (∀ p : Fin 1755, p ≠ 0 → ∃ b ∈ TA, (b 0 = 0 ∧ b • titsLine 0 = titsLine 0) ∧ b p ≠ p) ∧
    ∀ σ : Equiv.Perm (Fin 1755),
      (∀ p : Fin 1755, octGraph.dist (Sum.inl 0) (Sum.inl p) ≤ 6 → σ p = p) →
      (∀ b ∈ TA, b 0 = 0 → b • titsLine 0 = titsLine 0 → titsGen 3 * b * titsGen 3 ∈ TA →
        (titsGen 3 * b * titsGen 3) 0 = 0 →
        (titsGen 3 * b * titsGen 3) • titsLine 0 = titsLine 0 → σ * b = b * σ) →
      (titsGen 3 * σ) ^ 2 = 1 → (titsGen 3 * σ * titsGen 2) ^ 35942400 = 1 → σ = 1 := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ := smallK_sound small
  obtain ⟨g1, hg1⟩ := genEl 1 (by norm_num)
  obtain ⟨g2, hg2⟩ := genEl 2 (by norm_num)
  have hf1 : ∀ y < 1755, gp (F 1) y = ev g1.1 y := by rw [hg1]; exact gen_ev (by norm_num)
  have hf2 : ∀ y < 1755, gp (F 2) y = ev g2.1 y := by rw [hg2]; exact gen_ev (by norm_num)
  have n1sq : titsGen 3 * titsGen 3 = 1 := by
    apply ev_eq_one
    intro n hn
    rw [ev_mul _ _ hn, ← gen_ev (by norm_num) _ hn, ← gen_ev (by norm_num) _ (by
      rw [gen_ev (by norm_num) _ hn]; exact ev_lt _ hn)]
    exact s1 n hn
  have n10 : titsGen 3 0 = 0 := by
    have := gen_ev (h := 3) (by norm_num) 0 (by norm_num)
    rw [s2, ev_zero'] at this
    exact Fin.ext this.symm
  have t0 : titsGen 1 0 = 0 := by
    have := gen_ev (h := 1) (by norm_num) 0 (by norm_num)
    rw [s3, ev_zero'] at this
    exact Fin.ext this.symm
  have tl : titsGen 1 • titsLine 0 = titsLine 0 := by
    rw [← hg1]
    exact (lineMap_iff_smul hf1 (by norm_num)).1 s4
  have ql : titsGen 2 • titsLine 0 = titsLine 0 := by
    rw [← hg2]
    exact (lineMap_iff_smul hf2 (by norm_num)).1 s5
  refine ⟨n1sq, n10, t0, tl, ql, ?_, ?_, ?_⟩
  ·
    intro v hv
    have hadj : adjK lpD 0 (1755 + v) = true := by
      have := (adj_iff (Sum.inl 0) (Sum.inr v)).1 (octGraph_adj_inl_inr.2 hv)
      simpa [vCode] using this
    obtain ⟨k, hk, e⟩ := (nbOK.1 0 (by norm_num) _).1 hadj
    rw [degK_eq] at hk
    simp only [show (0 : ℕ) < 1755 by norm_num, if_true] at hk
    rw [nbK_pt (by norm_num)] at e
    have hpk : plK PL 0 k = v := by omega
    by_cases hv0 : v = 0
    · exact Or.inl hv0
    · right
      obtain ⟨i, hi, hm⟩ := s6 k hk (by rw [hpk]; exact fun h => hv0 (Fin.ext h))
      have hmem : titsGen 1 ^ i * titsGen 3 ∈ TA :=
        Subgroup.mul_mem _ (Subgroup.pow_mem _ (titsGen_mem_titsA (by norm_num)) _)
          (titsGen_mem_titsA (by norm_num))
      have hf : ∀ y < 1755, tn1 (F 1) (F 3) i y = ev (⟨_, hmem⟩ : ↥TA).1 y :=
        tn1_ev (hF' 1 (by norm_num)) (hF' 3 (by norm_num)) i
      have hw : plK PL 0 k < 2925 := by rw [hpk]; exact v.2
      have := (lineMap_iff_smul hf hw).1 hm
      refine ⟨i, hi, ?_⟩
      rw [this]
      congr 1
      exact Fin.ext hpk
  ·
    intro p hp
    by_cases htp : titsGen 1 p = p
    · have htp' : gp (F 1) p = p := by
        rw [gen_ev (by norm_num) _ p.2, ev_fin, htp]
      obtain ⟨j, hj, hjp⟩ := s8 p p.2 (fun h => hp (Fin.ext h)) htp'
      refine ⟨aF j, aF_mem j, aF_B hj, fun h => hjp ?_⟩
      rw [gp_ev (aF_prep hj) p.2, ev_fin, h]
    · exact ⟨titsGen 1, titsGen_mem_titsA (by norm_num), ⟨t0, tl⟩, htp⟩
  ·
    intro σ hnear hcomm h2 hq
    have hL := (lay_at lay0).1
    rw [ofCode_zero] at hL
    have h6 : ∀ n < 1755, layAt LAY0 n ≤ 6 → ev σ n = n := by
      intro n hn hl
      have e := hL.dist_eq (Sum.inl ⟨n, hn⟩)
      change _ = layAt LAY0 n at e
      have := hnear ⟨n, hn⟩ (by rw [e]; exact hl)
      simp [ev, hn, this]
    have hc : ∀ j < 5, σ * aF j = aF j * σ := by
      intro j hj
      obtain ⟨b1, b2⟩ := aF_B hj
      obtain ⟨c1, c2⟩ := s7 j hj
      have hmem : titsGen 3 * aF j * titsGen 3 ∈ TA :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (titsGen_mem_titsA (by norm_num)) (aF_mem j))
          (titsGen_mem_titsA (by norm_num))
      have hf : ∀ y < 1755, (fun x => gp (F 3) (gp (FP j) (gp (F 3) x))) y =
          ev (⟨_, hmem⟩ : ↥TA).1 y := by
        intro y hy
        have hy1 := ev_lt (titsGen 3) hy
        have hy2 := ev_lt (aF j) hy1
        simp only
        rw [gen_ev (by norm_num) _ hy, gp_ev (aF_prep hj) hy1, gen_ev (by norm_num) _ hy2,
          ev_mul (titsGen 3 * aF j) (titsGen 3) hy, ev_mul (titsGen 3) (aF j) hy1]
      refine hcomm _ (aF_mem j) b1 b2 hmem ?_ ((lineMap_iff_smul hf (by norm_num)).1 c2)
      have := hf 0 (by norm_num)
      simp only at this
      rw [c1, ev_zero'] at this
      exact Fin.ext this.symm
    have hwit : ∀ i < 1024, ∃ r, witRow FP LAY0 ORD0 PR0 LB0 PS0 (F 3) (F 2) i r = true := by
      have hlen : WIT.length = 1024 := Nat.eq_of_beq_eq_true witLen
      intro i hi
      by_cases h5 : i < 512
      · have := witK_sound wit0 i (by simp [hlen]; omega)
        exact ⟨_, by simpa using this⟩
      · have := witK_sound wit1 (i - 512) (by simp [hlen]; omega)
        rw [show 512 + (i - 512) = i by omega] at this
        exact ⟨_, this⟩
    exact rigid (a := aF) (fun j hj => aF_prep hj) rec0 far (hF' 3 (by norm_num))
      (hF' 2 (by norm_num)) hwit h6 hc h2 hq

end CertificateChecks.KernelTitsOct

end
