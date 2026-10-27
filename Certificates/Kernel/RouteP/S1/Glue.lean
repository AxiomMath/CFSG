module

public import Certificates.Kernel.RouteP.Geom.Trees
public import Certificates.Kernel.RouteP.S1.Cover
public import Certificates.Kernel.RouteP.S1.Hubs
public import Certificates.Kernel.RouteP.S1.Stab
public import CFSG.Certificates.Kernel.RouteP.S1Sound
public import CFSG.Certificates.Kernel.RouteP.MonoOrbit
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.Stage1Sem

public section

namespace CertificateChecks.KernelRouteP

open Equiv CFSG.KC CFSG.KC.RouteP CFSG.KS.RouteP CFSG.KD.RouteP CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.Native
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three
  CFSG.KC.Benes CFSG.KS.Fi24Net

section Letters


theorem s1_inv_act {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {g : Q3} {j : Nat}
    (hl : LOK NW KA KB (Int.ofNat (j + 1)))
    (h : ∀ y : Ω, (g • y).val = eL NW KA KB (Int.negSucc j) y.val) (y : Ω) :
    (g⁻¹ • y).val = eL NW KA KB (Int.ofNat (j + 1)) y.val := by
  have e : ∀ x : Ω, g • x = gT NW KA KB j x := fun x => Fin.ext (by rw [h, gT_apply hl])
  have e2 : g⁻¹ • y = (gT NW KA KB j)⁻¹ y := by
    apply smul_left_cancel g
    rw [smul_inv_smul, e]
    simp
  rw [e2, gT_inv_apply hl]

noncomputable def s1ρP (z : ℤ) : Q3 :=
  if z < 0 then genQ (z.natAbs - 29) else (genQ (z.natAbs - 29))⁻¹

noncomputable def s1ρO (z : ℤ) : Q3 :=
  if z < 0 then objElt (z.natAbs - 1) else (objElt (z.natAbs - 1))⁻¹

def s1PL (z : ℤ) : Prop := 29 ≤ z.natAbs ∧ z.natAbs - 29 ∈ zpLetters.toList

def s1OL (z : ℤ) : Prop := 1 ≤ z.natAbs ∧ z.natAbs - 1 ∈ geomA1Letters.toList

instance : DecidablePred s1PL := fun z =>
  inferInstanceAs (Decidable (29 ≤ z.natAbs ∧ z.natAbs - 29 ∈ zpLetters.toList))

instance : DecidablePred s1OL := fun z =>
  inferInstanceAs (Decidable (1 ≤ z.natAbs ∧ z.natAbs - 1 ∈ geomA1Letters.toList))

noncomputable def s1σ (ρ : ℤ → Q3) (w : List ℤ) : Q3 := (w.map ρ).prod

theorem s1σ_act {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {ρ : ℤ → Q3} : ∀ {w : List ℤ},
    (∀ z ∈ w, ∀ y : Ω, (ρ z • y).val = eL NW KA KB z y.val) →
      ∀ y : Ω, (s1σ ρ w • y).val = eW NW KA KB w y.val
  | [], _, y => by
    simp only [s1σ, List.map_nil, List.prod_nil, one_smul]
    rfl
  | z :: w, h, y => by
    have ih := s1σ_act (w := w) (fun z' hz' => h z' (List.mem_cons_of_mem z hz')) y
    simp only [s1σ, List.map_cons, List.prod_cons, mul_smul] at ih ⊢
    rw [eW_cons, h z List.mem_cons_self, ih]

theorem s1σ_mem {ρ : ℤ → Q3} {H : Subgroup Q3} {w : List ℤ} (h : ∀ z ∈ w, ρ z ∈ H) :
    s1σ ρ w ∈ H := by
  unfold s1σ
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
  exact h z hz

theorem s1_memS_img {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {ρ : ℤ → Q3} {w : List ℤ}
    (hρ : ∀ z ∈ w, ∀ y : Ω, (ρ z • y).val = eL NW KA KB z y.val)
    (hl : ∀ z ∈ w, LOK NW KA KB z) (s : Nat) (c : Ω) :
    memS (imgW NW KA KB w s) c.val = memS s ((s1σ ρ w)⁻¹ • c).val := by
  have e := memS_imgW w hl s ((s1σ ρ w)⁻¹ • c).isLt
  rwa [← s1σ_act hρ, smul_inv_smul] at e

theorem s1_pt {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {ρ : ℤ → Q3} {w : List ℤ}
    (hρ : ∀ z ∈ w, ∀ y : Ω, (ρ z • y).val = eL NW KA KB z y.val)
    (hl : ∀ z ∈ w, LOK NW KA KB z) {x y : Nat} (hx : x < 920808) (hy : y < 920808)
    (h : ptOK NW KA KB w x y = true) : (s1σ ρ w • (⟨x, hx⟩ : Ω)).val = y := by
  rw [s1σ_act hρ]
  exact ptOK_spec hl hx hy h

theorem s1_adj_inv (g : Q3) (a c : Ω) : Δ.Adj a (g⁻¹ • c) ↔ Δ.Adj (g • a) c := by
  rw [← Δ_adj_smul g a (g⁻¹ • c), smul_inv_smul]

theorem s1_cq {l : Nat} (hl : l ≤ 10) : cq ((l + 1 : Nat) : ℤ) = Int.negSucc (l + 28) := by
  interval_cases l <;> decide

theorem s1_genQ_act {l : Nat} (hl : l ∈ zpLetters) (y : Ω) :
    (genQ l • y).val = eL NWP KAP KBP (Int.negSucc (l + 28)) y.val := by
  have hl10 : l ≤ 10 := by simp [zpLetters] at hl; omega
  rw [smul_val_of_rep (rep_genQ (hzl l hl)) y, hapZ l hl y.val y.isLt, s1_cq hl10]

theorem s1_objElt_act {l : Nat} (hl : l ∈ geomA1Letters) (y : Ω) :
    (objElt l • y).val = eL NWO KAO KBO (Int.negSucc l) y.val := by
  rw [smul_val_of_rep (rep_objElt_of_mem hl) y]
  exact hapA l hl y.val y.isLt

theorem s1_actP {z : ℤ} (hz : s1PL z) (y : Ω) : (s1ρP z • y).val = eL NWP KAP KBP z y.val := by
  obtain ⟨h29, hl'⟩ := hz
  have hl : z.natAbs - 29 ∈ zpLetters := by simpa using hl'
  have hl10 : z.natAbs - 29 ≤ 10 := by simp [zpLetters] at hl; omega
  have hg := s1_genQ_act hl
  unfold s1ρP
  rcases Int.natAbs_eq z with e | e
  · rw [if_neg (by omega)]
    have ez : z = Int.ofNat (z.natAbs - 29 + 28 + 1) := by rw [Int.ofNat_eq_coe]; omega
    rw [s1_inv_act (lokP (by simp; omega)) hg y, ← ez]
  · rw [if_pos (by omega), hg]
    congr 1
    rw [Int.negSucc_eq]
    omega

theorem s1_actO {z : ℤ} (hz : s1OL z) (y : Ω) : (s1ρO z • y).val = eL NWO KAO KBO z y.val := by
  obtain ⟨h1, hl'⟩ := hz
  have hl : z.natAbs - 1 ∈ geomA1Letters := by simpa using hl'
  have hl8 : z.natAbs - 1 ≤ 8 := by simp [geomA1Letters] at hl; omega
  have hg := s1_objElt_act hl
  unfold s1ρO
  rcases Int.natAbs_eq z with e | e
  · rw [if_neg (by omega)]
    have ez : z = Int.ofNat (z.natAbs - 1 + 1) := by rw [Int.ofNat_eq_coe]; omega
    rw [s1_inv_act (lokO_reg (by omega)) hg y, ← ez]
  · rw [if_pos (by omega), hg]
    congr 1
    rw [Int.negSucc_eq]
    omega

theorem s1_lokP {z : ℤ} (hz : s1PL z) : LOK NWP KAP KBP z := by
  obtain ⟨h29, hl⟩ := hz
  have hl10 : z.natAbs - 29 ≤ 10 := by simp [zpLetters] at hl; omega
  exact lokP (by omega)

theorem s1_lokO {z : ℤ} (hz : s1OL z) : LOK NWO KAO KBO z := by
  obtain ⟨h1, hl⟩ := hz
  have hl8 : z.natAbs - 1 ≤ 8 := by simp [geomA1Letters] at hl; omega
  exact lokO (by omega)

theorem s1_memP {z : ℤ} (hz : s1PL z) : s1ρP z ∈ Zp := by
  have h : genQ (z.natAbs - 29) ∈ Zp := by
    rw [← lettersGroup_zpLetters]
    exact CFSG.Perm.lG_mem (by simpa using hz.2)
  unfold s1ρP
  split_ifs
  · exact h
  · exact inv_mem h

theorem s1_memO {z : ℤ} (hz : s1OL z) : s1ρO z ∈ A1gen := by
  have h : objElt (z.natAbs - 1) ∈ A1gen := CFSG.Perm.lG_mem (by simpa using hz.2)
  unfold s1ρO
  split_ifs
  · exact h
  · exact inv_mem h

theorem s1_wP {w : List ℤ} (h : ∀ z ∈ w, s1PL z) :
    (∀ z ∈ w, ∀ y : Ω, (s1ρP z • y).val = eL NWP KAP KBP z y.val) ∧
      (∀ z ∈ w, LOK NWP KAP KBP z) ∧ s1σ s1ρP w ∈ Zp :=
  ⟨fun z hz => s1_actP (h z hz), fun z hz => s1_lokP (h z hz),
    s1σ_mem fun z hz => s1_memP (h z hz)⟩

theorem s1_wO {w : List ℤ} (h : ∀ z ∈ w, s1OL z) :
    (∀ z ∈ w, ∀ y : Ω, (s1ρO z • y).val = eL NWO KAO KBO z y.val) ∧
      (∀ z ∈ w, LOK NWO KAO KBO z) ∧ s1σ s1ρO w ∈ A1gen :=
  ⟨fun z hz => s1_actO (h z hz), fun z hz => s1_lokO (h z hz),
    s1σ_mem fun z hz => s1_memO (h z hz)⟩

theorem s1_Zp_le : Zp ≤ Subgroup.closure {g | ∃ z ∈ k1Zp, s1ρP z = g} := by
  rw [← lettersGroup_zpLetters]
  unfold CFSG.Perm.lettersGroup
  rw [Subgroup.closure_le]
  rintro _ ⟨l, hl, rfl⟩
  apply Subgroup.subset_closure
  refine ⟨-((l + 29 : Nat) : ℤ), ?_, ?_⟩
  · simp [zpLetters] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · unfold s1ρP
    rw [if_pos (by omega)]
    congr 1

theorem s1_A1_le : A1gen ≤ Subgroup.closure {g | ∃ z ∈ k1A1, s1ρO z = g} := by
  unfold A1gen CFSG.Perm.lettersGroup
  rw [Subgroup.closure_le]
  rintro _ ⟨l, hl, rfl⟩
  apply Subgroup.subset_closure
  refine ⟨-((l + 1 : Nat) : ℤ), ?_, ?_⟩
  · simp [geomA1Letters] at hl
    rcases hl with rfl | rfl | rfl <;> decide
  · unfold s1ρO
    rw [if_pos (by omega)]
    congr 1

end Letters

noncomputable abbrev s1kG0 : Nat := closeS NWP KAP KBP k1Zp 33 (single 1479)

noncomputable abbrev s1kA : Nat := closeS NWO KAO KBO k1A1 10 (single 99705)

noncomputable abbrev s1kO : Nat := closeS NWO KAO KBO k1A1 12 (single k1Y)

noncomputable abbrev s1kBy : Nat := imgW NWP KAP KBP k1TY s1kA

noncomputable abbrev s1kB2 : Nat := imgW NWP KAP KBP k1T2 s1kA

@[expose] def s1kY : Ω := ⟨k1Y, by decide⟩

theorem s1_hgensP : ∀ z ∈ k1Zp, s1PL z := by decide

theorem s1_hgensO : ∀ z ∈ k1A1, s1OL z := by decide

theorem s1_hTY : ∀ z ∈ k1TY, s1PL z := by decide

theorem s1_hT2 : ∀ z ∈ k1T2, s1PL z := by decide

theorem s1_hubW : ∀ e ∈ k1Hubs, ∀ z ∈ e.2.2, s1OL z := by decide

theorem s1_hub_lt : ∀ e ∈ k1Hubs, e.1 < 920808 := by decide

theorem s1_stabW : ∀ s ∈ k1Stab, ∀ z ∈ s, s1OL z := by decide

theorem s1_cover : ptOK NWP KAP KBP k1TY 1479 k1Y = true ∧ memS s1kG0 k1Y = true ∧
    memS s1kA k1Y = false ∧ closedS NWO KAO KBO k1A1 s1kO = true ∧ Nat.land s1kA s1kO = 0 ∧
    memS s1kA 1479 = false ∧ memS s1kO 1479 = false ∧
    (∀ N, memS s1kA N = true → memS s1kG0 N = true) ∧
    (∀ N, memS s1kO N = true → memS s1kG0 N = true) ∧
    ∀ N, memS s1kG0 N = true →
      memS (single 1479) N = true ∨ memS s1kA N = true ∨ memS s1kO N = true :=
  s1CoverCore_spec (by
  have h := S1Ck.cover
  unfold s1CoverOK at h
  rw [s1_letB, s1_letB, s1_letB] at h
  exact h)

section Facts


theorem s1_G0 : (∀ c : Ω, memS s1kG0 c.val = true ↔ c ∈ MulAction.orbit Zp x1) ∧
    Nat.card (MulAction.orbit Zp x1) = 31671 :=
  orbOK_orbit (fun z hz => s1_lokP (s1_hgensP z hz)) s1ρP
    (fun z hz => s1_actP (s1_hgensP z hz)) (fun z hz => s1_memP (s1_hgensP z hz)) s1_Zp_le x1
    BridgeCk.zp

theorem s1_A : (∀ c : Ω, memS s1kA c.val = true ↔ c ∈ MulAction.orbit A1gen x2) ∧
    Nat.card (MulAction.orbit A1gen x2) = 3510 :=
  orbOK_orbit (fun z hz => s1_lokO (s1_hgensO z hz)) s1ρO
    (fun z hz => s1_actO (s1_hgensO z hz)) (fun z hz => s1_memO (s1_hgensO z hz)) s1_A1_le x2
    aOrb

theorem s1_memA (c : Ω) : memS s1kA c.val = true ↔ Δ.Adj x0 c ∧ Δ.Adj x1 c := by
  rw [s1_A.1 c, ← commonNeighbors_x0_x1_eq, SimpleGraph.mem_commonNeighbors]

theorem s1_memO' (c : Ω) : memS s1kO c.val = true ↔ c ∈ MulAction.orbit A1gen s1kY := by
  have hc : closedS NWO KAO KBO k1A1 s1kO = true := s1_cover.2.2.2.1
  constructor
  · exact mem_orbit_of_closeS (fun z hz => s1_lokO (s1_hgensO z hz)) s1ρO
      (fun z hz => s1_actO (s1_hgensO z hz)) (fun z hz => s1_memO (s1_hgensO z hz)) 12 s1kY c
  · exact mem_of_mem_orbit (fun z hz => s1_lokO (s1_hgensO z hz)) s1ρO
      (fun z hz => s1_actO (s1_hgensO z hz)) s1_A1_le hc (x := s1kY)
      (memS_closeS_of _ _ _ _ 12 _ _ (by
        rw [memS_single (by decide) (by decide)]
        exact decide_eq_true rfl)) c

theorem s1_memS_imgP {w : List ℤ} (hw : ∀ z ∈ w, s1PL z) (c : Ω) :
    memS (imgW NWP KAP KBP w s1kA) c.val = true ↔ Δ.Adj x0 c ∧ Δ.Adj (s1σ s1ρP w • x1) c := by
  obtain ⟨h1, h2, h3⟩ := s1_wP hw
  rw [s1_memS_img h1 h2, s1_memA, s1_adj_inv, s1_adj_inv, Zp_smul_x0 h3]

theorem s1_gY : s1σ s1ρP k1TY • x1 = s1kY :=
  Fin.ext (s1_pt (s1_wP s1_hTY).1 (s1_wP s1_hTY).2.1 (by decide) (by decide) s1_cover.1)

theorem s1_g2 : s1σ s1ρP k1T2 • x1 = x2 :=
  Fin.ext (s1_pt (s1_wP s1_hT2).1 (s1_wP s1_hT2).2.1 (by decide) (by decide)
    (s1HubsOK_spec S1Ck.hubs).1)

theorem s1_memBy (c : Ω) : memS s1kBy c.val = true ↔ Δ.Adj x0 c ∧ Δ.Adj s1kY c := by
  rw [s1_memS_imgP s1_hTY, s1_gY]

theorem s1_memB2 (c : Ω) : memS s1kB2 c.val = true ↔ Δ.Adj x0 c ∧ Δ.Adj x2 c := by
  rw [s1_memS_imgP s1_hT2, s1_g2]

theorem s1_memS_N {a : List ℤ} (ha : ∀ z ∈ a, s1OL z) (c : Ω) :
    memS (imgW NWO KAO KBO a s1kB2) c.val = true ↔ Δ.Adj x0 c ∧ Δ.Adj (s1σ s1ρO a • x2) c := by
  obtain ⟨h1, h2, h3⟩ := s1_wO ha
  rw [s1_memS_img h1 h2, s1_memB2, s1_adj_inv, s1_adj_inv, L0_smul_x0 (A1gen_le_L0 h3)]

theorem s1_card : Nat.card (MulAction.orbit A1gen s1kY) = 28160 := by
  obtain ⟨-, -, -, -, hland, hA1, hO1, hAG, hOG, hcov⟩ := s1_cover
  have hS : (MulAction.orbit Zp x1 : Set Ω) =
      {x1} ∪ (MulAction.orbit A1gen x2 ∪ MulAction.orbit A1gen s1kY) := by
    ext c
    simp only [Set.mem_union, Set.mem_singleton_iff]
    rw [← s1_G0.1 c, ← s1_A.1 c, ← s1_memO' c]
    constructor
    · intro h
      rcases hcov _ h with h1 | h1 | h1
      · left
        rw [memS_single (by decide) c.isLt] at h1
        exact Fin.ext (of_decide_eq_true h1)
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h1)
    · rintro (rfl | h | h)
      · exact (s1_G0.1 x1).2 (MulAction.mem_orbit_self x1)
      · exact hAG _ h
      · exact hOG _ h
  have hd2 : Disjoint (MulAction.orbit A1gen x2) (MulAction.orbit A1gen s1kY) := by
    rw [Set.disjoint_left]
    intro c h1 h2
    exact disj_memS hland c.val ⟨(s1_A.1 c).2 h1, (s1_memO' c).2 h2⟩
  have hd1 : Disjoint ({x1} : Set Ω) (MulAction.orbit A1gen x2 ∪ MulAction.orbit A1gen s1kY) := by
    rw [Set.disjoint_singleton_left, Set.mem_union, not_or]
    refine ⟨fun h => Bool.false_ne_true (hA1.symm.trans ((s1_A.1 x1).2 h)),
      fun h => Bool.false_ne_true (hO1.symm.trans ((s1_memO' x1).2 h))⟩
  have h1 := s1_G0.2
  rw [Nat.card_coe_set_eq, hS, Set.ncard_union_eq hd1, Set.ncard_union_eq hd2,
    Set.ncard_singleton] at h1
  have h2 := s1_A.2
  rw [Nat.card_coe_set_eq] at h2
  rw [Nat.card_coe_set_eq]
  omega

theorem s1_sem : ∃ y w : Ω, Stage1Sem y w := by
  classical
  obtain ⟨-, hG0y, hAy, -, -, -, -, -, -, hcov⟩ := s1_cover
  obtain ⟨-, hwA, hwB, hgo⟩ := s1HubsOK_spec S1Ck.hubs
  obtain ⟨hhub, V, hV, hfin⟩ := s1HubsGo_spec _ [] 0 hgo
  obtain ⟨hmu, hD⟩ := s1_and hfin
  have hy0 : Δ.Adj x0 s1kY := Δ_adj_x0_iff.2 ((s1_G0.1 s1kY).1 hG0y)
  let W : Ω := ⟨k1W, by decide⟩
  obtain ⟨hw0, hw1⟩ := (s1_memA W).1 hwA
  have hyw : Δ.Adj s1kY W := ((s1_memBy W).1 hwB).2
  let hp : ∀ i, i < k1Hubs.length → Ω := fun i hi => ⟨k1Hubs[i].1, s1_hub_lt _ (List.getElem_mem hi)⟩
  have hM : ∀ i (hi : i < k1Hubs.length),
      Δ.Adj x0 (hp i hi) ∧ Δ.Adj x1 (hp i hi) ∧ Δ.Adj s1kY (hp i hi) := by
    intro i hi
    obtain ⟨-, hA, hB, -⟩ := hhub i hi
    obtain ⟨a0, a1⟩ := (s1_memA (hp i hi)).1 hA
    exact ⟨a0, a1, ((s1_memBy (hp i hi)).1 hB).2⟩
  have hN : ∀ i (hi : i < k1Hubs.length) (c : Ω),
      memS (imgW NWO KAO KBO k1Hubs[i].2.2 s1kB2) c.val = true → Δ.Adj x0 c ∧ Δ.Adj (hp i hi) c := by
    intro i hi c hc
    have ha := s1_hubW _ (List.getElem_mem hi)
    have e : s1σ s1ρO k1Hubs[i].2.2 • x2 = hp i hi :=
      Fin.ext (s1_pt (s1_wO ha).1 (s1_wO ha).2.1 (by decide) (s1_hub_lt _ (List.getElem_mem hi))
        (hhub i hi).1)
    rw [← e]
    exact (s1_memS_N ha c).1 hc
  let Hb : Ω → Prop := fun v => ∃ i, ∃ hi : i < k1Hubs.length, k1Hubs[i].1 = v.val
  let Nb : Ω → Prop := fun v => ∃ j, ∃ hj : j < k1Hubs.length,
    memS (imgW NWO KAO KBO k1Hubs[j].2.2 s1kB2) v.val = true
  let rk : Ω → ℕ := fun v =>
    if h : Hb v then 2 * Nat.find h else if h' : Nb v then 2 * Nat.find h' + 1 else 0
  have hrkH : ∀ i (hi : i < k1Hubs.length), rk (hp i hi) ≤ 2 * i := by
    intro i hi
    have hH : Hb (hp i hi) := ⟨i, hi, rfl⟩
    have e : rk (hp i hi) = 2 * Nat.find hH := dif_pos hH
    have := Nat.find_min' hH ⟨hi, rfl⟩
    omega
  have h0 : 0 < k1Hubs.length := by decide
  refine ⟨s1kY, W, hy0, fun h => absurd (congrArg Fin.val h) (by decide),
    fun h => Bool.false_ne_true (hAy.symm.trans ((s1_memA s1kY).2 ⟨hy0, h⟩)), hw0, hw1, hyw,
    fun c hc => ?_, s1_card, ⟨hp 0 h0, rk, hM 0 h0, fun v hv0 hv1 hvy => ?_⟩, fun g hg0 hyg => ?_⟩
  · rcases hcov _ ((s1_G0.1 c).2 (Δ_adj_x0_iff.1 hc)) with h | h | h
    · left
      rw [memS_single (by decide) c.isLt] at h
      exact Fin.ext (of_decide_eq_true h)
    · exact Or.inr (Or.inl ((s1_memA c).1 h).2)
    · exact Or.inr (Or.inr ((s1_memO' c).1 h))
  · have hvmu : memS (Nat.land s1kA s1kBy) v.val = true := by
      rw [s1_memS_land, (s1_memA v).2 ⟨hv0, hv1⟩, (s1_memBy v).2 ⟨hv0, hvy⟩]
      rfl
    have hv := s1_subP hmu hvmu
    rw [memS_lor, Bool.or_eq_true] at hv
    by_cases hH : Hb v
    · obtain ⟨hi, hiv⟩ := Nat.find_spec hH
      have hrk : rk v = 2 * Nat.find hH := dif_pos hH
      revert hi hiv hrk
      generalize Nat.find hH = i
      intro hi hiv hrk
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · exact Or.inl (Fin.ext hiv.symm)
      · right
        obtain ⟨-, -, -, hpar⟩ := hhub i hi
        rcases hpar with hz | ⟨hplt, hpm⟩
        · simp at hz
          omega
        · simp only [List.length_nil, Nat.zero_add] at hplt
          have hpl : k1Hubs[i].2.1 < k1Hubs.length := lt_trans hplt hi
          rw [List.nil_append, List.getD_eq_getElem _ _ (by simpa using hpl),
            List.getElem_map] at hpm
          obtain ⟨-, hpv⟩ := hN _ hpl v (by rw [← hiv]; exact hpm)
          refine ⟨hp _ hpl, hM _ hpl, (Δ_adj_comm _ _).1 hpv, ?_⟩
          have := hrkH _ hpl
          rw [hrk]
          omega
    · rcases hv with hs | hU
      · exfalso
        apply hH
        rw [memS_single (by decide) v.isLt] at hs
        exact ⟨0, h0, (of_decide_eq_true hs).symm⟩
      · rcases hV _ hU with hz | ⟨e, he, hm⟩
        · rw [s1_memS_zero] at hz
          exact absurd hz Bool.false_ne_true
        · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 he
          have hNb : Nb v := ⟨j, hj, hm⟩
          have hrk : rk v = 2 * Nat.find hNb + 1 := (dif_neg hH).trans (dif_pos hNb)
          obtain ⟨hj', hjm⟩ := Nat.find_spec hNb
          obtain ⟨-, hpv⟩ := hN _ hj' v hjm
          refine Or.inr ⟨hp _ hj', hM _ hj', (Δ_adj_comm _ _).1 hpv, ?_⟩
          have := hrkH _ hj'
          rw [hrk]
          omega
  · have hgB : memS s1kBy g.val = true := (s1_memBy g).2 ⟨hg0, hyg⟩
    by_cases hgA : memS s1kA g.val = true
    · exact Or.inr (Or.inl ((s1_memA g).1 hgA).2)
    · have hgD : memS (Nat.xor s1kBy (Nat.land s1kA s1kBy)) g.val = true := by
        rw [s1_memS_xor, s1_memS_land, hgB, Bool.eq_false_iff.2 hgA]
        rfl
      rcases hV _ (s1_subP hD hgD) with hz | ⟨e, he, hm⟩
      · rw [s1_memS_zero] at hz
        exact absurd hz Bool.false_ne_true
      · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 he
        obtain ⟨-, hjg⟩ := hN j hj g hm
        exact Or.inr (Or.inr ⟨hp j hj, hM j hj, hjg⟩)

theorem s1_stab {c : Ω} (h0 : Δ.Adj x0 c) (h1 : Δ.Adj x1 c) (h2 : Δ.Adj x2 c) :
    ∃ h ∈ A1gen, h • x2 = x2 ∧ h • planePt 3 = c := by
  obtain ⟨-, hfix, hsub⟩ := s1StabOK_spec S1Ck.stab
  have hm := hsub c.val ((s1_memA c).2 ⟨h0, h1⟩) ((s1_memB2 c).2 ⟨h0, h2⟩)
  have hc0 : (planePt 3).val = k1C0 := by decide
  have hH : ∀ s ∈ k1Stab,
      s1σ s1ρO s ∈ (A1gen ⊓ MulAction.stabilizer Q3 x2 : Subgroup Q3) := fun s hs =>
    Subgroup.mem_inf.2 ⟨(s1_wO (s1_stabW s hs)).2.2, MulAction.mem_stabilizer_iff.2
      (Fin.ext (s1_pt (s1_wO (s1_stabW s hs)).1 (s1_wO (s1_stabW s hs)).2.1 (by decide)
        (by decide) (hfix s hs)))⟩
  have hc : c ∈ MulAction.orbit (A1gen ⊓ MulAction.stabilizer Q3 x2 : Subgroup Q3) (planePt 3) :=
    mem_orbit_of_closeW (fun s hs z hz => s1_lokO (s1_stabW s hs z hz)) (s1σ s1ρO)
      (fun s hs => s1σ_act (s1_wO (s1_stabW s hs)).1) hH 12 (planePt 3) c (by rw [hc0]; exact hm)
  obtain ⟨⟨h, hh⟩, rfl⟩ := hc
  exact ⟨h, (Subgroup.mem_inf.1 hh).1, MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 hh).2,
    rfl⟩

end Facts

end CertificateChecks.KernelRouteP

end
