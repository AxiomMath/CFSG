module

public import Certificates.Kernel.Fi23T.Inst
public import Certificates.Kernel.Fi23T.TreeB
public import Certificates.Kernel.Fi23T.TreeC0
public import Certificates.Kernel.Fi23T.TreeC1
public import Certificates.Kernel.Fi23T.TreeD
public import Certificates.Kernel.Fi23T.TreeE
public import Certificates.Kernel.Fi23T.Tri

public section

set_option maxRecDepth 400000

open Pointwise

namespace CertificateChecks.KernelFi23T

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23T CFSG.KC.Fi23C CFSG.KD.Fi23K CFSG.KD.Fi23T
  CFSG.KS.PC CFSG.KS.Raw.Orb CertificateChecks.KernelFi23M

section


theorem tc_iff {x : Fin 31671} : domTc H x.val = true ↔ x ∉ T0 := by
  rw [notMem_T0 x.isLt, fp_of]

theorem nodesB : ∀ j, 0 ≤ j → j < 28431 → NodeOK 12 41 9 (domTc H) 0 j :=
  nodes_app (nodes_of b0) <| nodes_app (nodes_of b1) <| nodes_app (nodes_of b2) <|
    nodes_app (nodes_of b3) <| nodes_app (nodes_of b4) <| nodes_app (nodes_of b5) (nodes_of b6)

theorem cg_xi : ptSet cgL ⊆ ptSet xiL := fun x hx => by
  rw [mem_ptSet] at hx ⊢
  revert hx
  generalize x.val = v
  decide +revert

theorem hTc0 : ∀ f ∉ T0, f ∈ Orb tau (ptSet xiL) (fp 2) := by
  intro f hf
  have hd := tc_iff.2 hf
  obtain ⟨h1, h2⟩ := covK_spec b_cov f.isLt hd
  have h := orb_node (gens_ok cg_eq cg_lt) nodesB h2 (Nat.zero_le _) h1
  rw [root_eq root_12_0] at h
  exact orb_mono cg_xi h

theorem nodesC1 : ∀ j, 1 ≤ j → j < 22401 → NodeOK 16 42 5 (domTc H) 1 j :=
  nodes_app (nodes_of c1) <| nodes_app (nodes_of c2) <| nodes_app (nodes_of c3) <|
    nodes_app (nodes_of c4) <| nodes_app (nodes_of c5) (nodes_of c6)

theorem nodesC0 : ∀ j, 0 ≤ j → j < 1 → NodeOK 16 42 5 (domTc H) 0 j := nodes_of c0
theorem nodesC7 : ∀ j, 22401 ≤ j → j < 25551 → NodeOK 16 42 5 (domTc H) 22401 j := nodes_of c7
theorem nodesC8 : ∀ j, 25551 ≤ j → j < 28431 → NodeOK 16 42 5 (domTc H) 25551 j := nodes_of c8

theorem hF1_0 : ∀ e ∈ band 16 (domTc H) 1 22401, e ∉ T0 ∧ e ∈ Orb tau (ptSet kL) (fp 5) := by
  intro e he
  rw [mem_band] at he
  obtain ⟨hd, h1, h2⟩ := he
  refine ⟨tc_iff.1 hd, ?_⟩
  have h := orb_node (gens_ok k_eq k_lt) nodesC1 (covK_spec c_cov e.isLt hd).2 h1 h2
  rwa [root_eq root_16_1] at h

theorem hKR0 : ∀ e ∉ T0, e ∈ band 16 (domTc H) 1 22401 ∨ e ∈ Orb tau (ptSet kL) (fp 2) ∨
    e ∈ Orb tau (ptSet kL) (fp 3) ∨ e ∈ Orb tau (ptSet kL) (fp 8) := by
  intro e he
  have hd := tc_iff.2 he
  obtain ⟨hlt, hc⟩ := covK_spec c_cov e.isLt hd
  have hg := gens_ok k_eq k_lt
  by_cases h0 : tb H 19 e.val < 1
  · have h := orb_node hg nodesC0 hc (Nat.zero_le _) h0
    rw [root_eq root_16_0] at h
    exact Or.inr (Or.inl h)
  by_cases h1 : tb H 19 e.val < 22401
  · exact Or.inl (mem_band.2 ⟨hd, Nat.le_of_not_lt h0, h1⟩)
  by_cases h2 : tb H 19 e.val < 25551
  · have h := orb_node hg nodesC7 hc (Nat.le_of_not_lt h1) h2
    rw [root_eq root_16_22401] at h
    exact Or.inr (Or.inr (Or.inl h))
  · have h := orb_node hg nodesC8 hc (Nat.le_of_not_lt h2) hlt
    rw [root_eq root_16_25551] at h
    exact Or.inr (Or.inr (Or.inr h))

theorem F1_card : (band 16 (domTc H) 1 22401).card = 22400 :=
  band_card (by norm_num) (fun j h1 h2 => ⟨1, nodesC1 j h1 h2⟩)
    (fun x hx hd => (covK_spec c_cov hx hd).2)

theorem nodesD0 : ∀ j, 0 ≤ j → j < 2916 → NodeOK 20 43 5 (domTc H) 0 j := nodes_of d0
theorem nodesD1 : ∀ j, 2916 ≤ j → j < 22599 → NodeOK 20 43 5 (domTc H) 2916 j :=
  nodes_app (nodes_of d1) <| nodes_app (nodes_of d2) <| nodes_app (nodes_of d3) <|
    nodes_app (nodes_of d4) (nodes_of d5)
theorem nodesD6 : ∀ j, 22599 ≤ j → j < 25515 → NodeOK 20 43 5 (domTc H) 22599 j := nodes_of d6
theorem nodesD7 : ∀ j, 25515 ≤ j → j < 28431 → NodeOK 20 43 5 (domTc H) 25515 j := nodes_of d7

@[expose] noncomputable def M0 : Finset (Fin 31671) :=
  band 20 (domTc H) 0 2916 ∪ band 20 (domTc H) 22599 25515

theorem hM0 : ∀ g ∈ M0, g ∉ T0 ∧ (g ∈ Orb tau (ptSet kvL) (fp 2) ∨
    g ∈ Orb tau (ptSet kvL) (fp 8)) := by
  intro g hg
  have hgk := gens_ok kv_eq kv_lt
  rcases Finset.mem_union.1 hg with h | h
  · obtain ⟨hd, h1, h2⟩ := mem_band.1 h
    refine ⟨tc_iff.1 hd, Or.inl ?_⟩
    have h' := orb_node hgk nodesD0 (covK_spec d_cov g.isLt hd).2 h1 h2
    rwa [root_eq root_20_0] at h'
  · obtain ⟨hd, h1, h2⟩ := mem_band.1 h
    refine ⟨tc_iff.1 hd, Or.inr ?_⟩
    have h' := orb_node hgk nodesD6 (covK_spec d_cov g.isLt hd).2 h1 h2
    rwa [root_eq root_20_22599] at h'

theorem hMR0 : ∀ g ∉ T0, g ∈ M0 ∨ g ∈ Orb tau (ptSet kvL) (fp 3) ∨
    g ∈ Orb tau (ptSet kvL) (fp 17) := by
  intro g hg
  have hd := tc_iff.2 hg
  obtain ⟨hlt, hc⟩ := covK_spec d_cov g.isLt hd
  have hgk := gens_ok kv_eq kv_lt
  by_cases h0 : tb H 23 g.val < 2916
  · exact Or.inl (Finset.mem_union_left _ (mem_band.2 ⟨hd, Nat.zero_le _, h0⟩))
  by_cases h1 : tb H 23 g.val < 22599
  · have h := orb_node hgk nodesD1 hc (Nat.le_of_not_lt h0) h1
    rw [root_eq root_20_2916] at h
    exact Or.inr (Or.inl h)
  by_cases h2 : tb H 23 g.val < 25515
  · exact Or.inl (Finset.mem_union_right _ (mem_band.2 ⟨hd, Nat.le_of_not_lt h1, h2⟩))
  · have h := orb_node hgk nodesD7 hc (Nat.le_of_not_lt h2) hlt
    rw [root_eq root_20_25515] at h
    exact Or.inr (Or.inr h)

theorem M0_card : M0.card = 5832 := by
  have hcov : ∀ x < 31671, domTc H x = true → tb H 20 (tb H (20 + 3) x) = x :=
    fun x hx hd => (covK_spec d_cov hx hd).2
  rw [M0, Finset.card_union_of_disjoint, band_card (by norm_num) (fun j h1 h2 => ⟨0, nodesD0 j h1 h2⟩)
    hcov, band_card (by norm_num) (fun j h1 h2 => ⟨22599, nodesD6 j h1 h2⟩) hcov]
  rw [Finset.disjoint_left]
  intro x h1 h2
  have := (mem_band.1 h1).2.2
  have := (mem_band.1 h2).2.1
  omega

theorem w52_iff {x : Fin 31671} :
    domW G H [5, 2] x.val = true ↔ x ∉ tau (fp 2) • tau (fp 5) • T0 := by
  rw [domW_pts (by decide) x.isLt, fp_of, mem_tau, mem_tau]
  rfl

theorem nodesE0 : ∀ j, 0 ≤ j → j < 2916 → NodeOK 24 43 5 (domW G H [5, 2]) 0 j := nodes_of e0
theorem nodesE1 : ∀ j, 2916 ≤ j → j < 5832 → NodeOK 24 43 5 (domW G H [5, 2]) 2916 j :=
  nodes_of e1
theorem nodesE2 : ∀ j, 5832 ≤ j → j < 25515 → NodeOK 24 43 5 (domW G H [5, 2]) 5832 j :=
  nodes_app (nodes_of e2) <| nodes_app (nodes_of e3) <| nodes_app (nodes_of e4) <|
    nodes_app (nodes_of e5) (nodes_of e6)
theorem nodesE7 : ∀ j, 25515 ≤ j → j < 28431 → NodeOK 24 43 5 (domW G H [5, 2]) 25515 j :=
  nodes_of e7

theorem hedR0 : ∀ h ∉ tau (fp 2) • tau (fp 5) • T0, h ∈ Orb tau (ptSet kvL) (fp 2) ∨
    h ∈ Orb tau (ptSet kvL) (fp 8) ∨ h ∈ Orb tau (ptSet kvL) (fp 0) ∨
    h ∈ Orb tau (ptSet kvL) (fp 3) := by
  intro h hh
  have hd := w52_iff.2 hh
  obtain ⟨hlt, hc⟩ := covK_spec e_cov h.isLt hd
  have hgk := gens_ok kv_eq kv_lt
  by_cases h0 : tb H 27 h.val < 2916
  · have h' := orb_node hgk nodesE0 hc (Nat.zero_le _) h0
    rw [root_eq root_24_0] at h'
    exact Or.inr (Or.inr (Or.inl h'))
  by_cases h1 : tb H 27 h.val < 5832
  · have h' := orb_node hgk nodesE1 hc (Nat.le_of_not_lt h0) h1
    rw [root_eq root_24_2916] at h'
    exact Or.inl h'
  by_cases h2 : tb H 27 h.val < 25515
  · have h' := orb_node hgk nodesE2 hc (Nat.le_of_not_lt h1) h2
    rw [root_eq root_24_5832] at h'
    exact Or.inr (Or.inr (Or.inr h'))
  · have h' := orb_node hgk nodesE7 hc (Nat.le_of_not_lt h2) hlt
    rw [root_eq root_24_25515] at h'
    exact Or.inr (Or.inl h')

theorem reg_T0 {r c : ℕ} {L : List ℕ} (hL : hList H r 0 c = L)
    (h : ∀ l < c, tb H 1 (tb H r l) < 3240) : ptSet L ⊆ (T0 : Set (Fin 31671)) := by
  intro x hx
  obtain ⟨l, hl, e⟩ := mem_reg hL (mem_ptSet.1 hx)
  rw [Finset.mem_coe, mem_T0, ← e]
  exact h l hl

theorem hST0 : ptSet xiL ⊆ (T0 : Set (Fin 31671)) :=
  reg_T0 xi_eq fun l hl => (memS_iff.1 (allN_iff.1 xi_in l hl))

theorem hK0 : ptSet kL ⊆ (T0 : Set (Fin 31671)) :=
  reg_T0 k_eq fun l hl => (genK_spec k_gens hl).1

theorem hKf0 : ∀ k ∈ ptSet kL, tau k (fp 2) = fp 2 := by
  intro k hk
  obtain ⟨l, hl, e⟩ := mem_reg k_eq (mem_ptSet.1 hk)
  have h := (genK_spec k_gens hl).2.1 rfl
  have hlt := k_lt _ (reg_mem k_eq hl)
  have h2 := cJ_tau hlt (by norm_num : (2 : ℕ) < 31671)
  rw [h, e, fp_of] at h2
  exact h2.symm

theorem hKv0 : ∀ k ∈ ptSet kvL, k ∈ T0 ∧ k ∈ tau (fp 2) • tau (fp 5) • T0 := by
  intro k hk
  obtain ⟨l, hl, e⟩ := mem_reg kv_eq (mem_ptSet.1 hk)
  have h := genK_spec kv_gens hl
  refine ⟨?_, ?_⟩
  · rw [mem_T0, ← e]
    exact h.1
  · have h2 := h.2.2 rfl
    have hlt := kv_lt _ (reg_mem kv_eq hl)
    have h3 : domW G H [5, 2] (tb H 43 l) = false := by
      unfold domW
      rw [memS_iff.2 h2]
      rfl
    by_contra hn
    have hk : k = fp (tb H 43 l) := by rw [e, fp_of]
    rw [hk] at hn
    have h4 := w52_iff.2 hn
    rw [fp_val hlt, h3] at h4
    exact Bool.false_ne_true h4

theorem hmu0 : ∀ k ∈ ptSet kvL, k ∉ tau (fp 2) • T0 := by
  intro k hk
  obtain ⟨l, hl, e⟩ := mem_reg kv_eq (mem_ptSet.1 hk)
  have hlt := kv_lt _ (reg_mem kv_eq hl)
  have h := notW (w := [2]) (by decide) hlt (allN_iff.1 mu_gens l hl)
  rw [e, fp_of] at h
  exact fun hm => h (mem_tau.1 hm)

@[expose] noncomputable def cfg : Cfg (Fin 31671) where
  A := A0
  τ := tau
  T := T0
  S := ptSet xiL
  x0 := fp 0
  s1 := fp 1
  f0 := fp 2
  K := ptSet kL
  e1 := fp 5
  e2 := fp 3
  e3 := fp 8
  y2 := fp 6617
  y3 := fp 8
  F1 := band 16 (domTc H) 1 22401
  c1 := 360
  c2 := 324
  Kv := ptSet kvL
  d1 := fp 2
  d2 := fp 8
  d3 := fp 3
  d4 := fp 17
  z1 := fp 5
  z2 := fp 9702
  M := M0
  t := fp 27573
  a1 := fp 0
  a3 := fp 3
  Gab := {phiX wα, phiX wβ}

theorem adj_of {V W : Finset (Fin 31671)} {h : Fin 31671} (hV : W = tau h • V) (hh : h ∉ V) :
    Adj tau V W := ⟨h, hh, hV⟩

theorem cfg_ok : cfg.OK where
  sys := tsys
  hS := hS0
  h0 := h00
  hcov := hcov0
  hST := hST0
  hs1 := fp_ptSet xi_lt (by decide)
  hf0 := dom_facts.1
  hTc := hTc0
  hc1 := x0_card
  hc1T := by
    change 360 ≠ T0.card
    rw [T0_card]
    decide
  hK := hK0
  hKf := hKf0
  hF1 := hF1_0
  hKR := hKR0
  hc2 := v0_card
  hc2T := by
    change 324 ≠ T0.card
    rw [T0_card]
    decide
  hc21 := by decide
  hy2 := lab3
  hy3 := lab8
  hKv := hKv0
  hM := hM0
  hMR := hMR0
  hd1 := ⟨dom_facts.1, dom_facts.2, tsys.τ_τ _ _⟩
  hd2 := ⟨lab8.1, d8.1, d8.2⟩
  hd3 := d3_card
  hd4 := d17_card
  hmu := hmu0
  ht := mu_cross_facts
  hedR := hedR0
  hed1 := ⟨fp 8, lab8.1, fp 9702, d8.1, d8.2, adj_of (by
      change tau (fp 8) • T0 = tau (fp 2176) • tau (fp 0) • tau (fp 2) • tau (fp 5) • T0
      rw [ed0.2, tsys.τ_τ]) (by
      change fp 2176 ∉ tau (fp 0) • tau (fp 2) • tau (fp 5) • T0
      rw [ed0.2, tsys.mem_smul_self]
      exact ed0.1)⟩
  hed3 := ⟨fp 5, dom_facts.2, fp 3346, ed3m.1, ed3m.2, adj_of (by
      change tau (fp 5) • T0 = tau (fp 4776) • tau (fp 3) • tau (fp 2) • tau (fp 5) • T0
      rw [ed3.2, tsys.τ_τ]) (by
      change fp 4776 ∉ tau (fp 3) • tau (fp 2) • tau (fp 5) • T0
      rw [ed3.2, tsys.mem_smul_self]
      exact ed3.1)⟩
  hGab := rfl
  hgab := by
    rintro γ (rfl | rfl)
    · refine ⟨[fp 4600], ?_⟩
      rw [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      exact ga
    · refine ⟨[fp 7, fp 1558], ?_⟩
      rw [List.map_cons, List.map_cons, List.map_nil, List.prod_cons, List.prod_cons,
        List.prod_nil, mul_one, mul_smul]
      exact gb

theorem cfg_T : cfg.T = T0 := rfl
theorem cfg_F1 : cfg.F1 = band 16 (domTc H) 1 22401 := rfl
theorem cfg_M : cfg.M = M0 := rfl

theorem tc_card : cfg.Tᶜ.card = 28431 := by
  rw [Finset.card_compl, cfg_T, T0_card, Fintype.card_fin]

theorem card_N2 : cfg.N2.ncard = 109200 := by
  have h2 := cfg_ok.double_count
  rw [cfg_ok.nr_card_eq, tc_card, cfg_F1, F1_card, cfg_M, M0_card] at h2
  omega

theorem card_orbit : cfg.Vtx.ncard = 137632 := by
  rw [cfg_ok.card_vtx, tc_card, card_N2]

end

end CertificateChecks.KernelFi23T

end
