module

public import Certificates.Kernel.RouteP.QCent.Check
public import Certificates.Kernel.RouteP.Geom.Trees
public import Certificates.Kernel.RouteP.Plane.Glue
public import CFSG.Certificates.Kernel.RouteP.QCentSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.QCentCount

public section

namespace CertificateChecks.KernelRouteP

open Equiv CFSG.KC CFSG.KC.RouteP CFSG.KS.RouteP CFSG.KD.RouteP CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.Native CFSG.Perm.Native CFSG.KC.Benes
  CFSG.KS.Fi24Net

theorem card_range_filter_eq {m N : Nat} (g : Nat → Nat) (q R : Nat → Bool)
    (hinj : ∀ a < m, ∀ b < m, g a = g b → a = b)
    (hmaps : ∀ k < m, q k = true → g k < N ∧ R (g k) = true)
    (hsurj : ∀ y < N, R y = true → ∃ k < m, q k = true ∧ g k = y) :
    ((Finset.range m).filter fun k => q k = true).card = ((List.range N).filter R).length := by
  have e : ((List.range N).filter R).length = ((Finset.range N).filter fun y => R y = true).card := by
    rw [← List.toFinset_card_of_nodup ((List.nodup_range).filter _)]
    congr 1
    ext y
    simp [List.mem_filter, Finset.mem_filter]
  rw [e]
  refine Finset.card_bij (fun k _ => g k) (fun k hk => ?_) (fun a ha b hb hab => ?_) (fun y hy => ?_)
  · simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    exact hmaps k hk.1 hk.2
  · simp only [Finset.mem_filter, Finset.mem_range] at ha hb
    exact hinj a ha.1 b hb.1 hab
  · simp only [Finset.mem_filter, Finset.mem_range] at hy
    obtain ⟨k, hk, hq, rfl⟩ := hsurj y hy.1 hy.2
    exact ⟨k, by simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨hk, hq⟩, rfl⟩

theorem pos_pts_of_treeOK {n r : Nat} {T : Tree} {letters : Array Table} {lv : Array Nat}
    (h : treeOK n r T letters lv = true) {j : Nat} (hj : j < T.pts.size) : ap T.pos (ap T.pts j) = j := by
  simp only [CFSG.Perm.Native.treeOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  have hat := (allIn_eq_true.1 h.2) j (Nat.zero_le _) hj
  simp only [treeAt, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hat
  exact hat.1.1.2

theorem pts_inj_of_treeOK {n r : Nat} {T : Tree} {letters : Array Table} {lv : Array Nat}
    (h : treeOK n r T letters lv = true) {a b : Nat} (ha : a < T.pts.size) (hb : b < T.pts.size)
    (hab : ap T.pts a = ap T.pts b) : a = b := by
  rw [← pos_pts_of_treeOK h ha, hab, pos_pts_of_treeOK h hb]

theorem ap_qcentGens {s : Nat} (hs : s < 14) {x : Nat} (hx : x < 920808) :
    ap (qcentGens (objRun ()).1)[s]! x = eL NWQ KAQ KBQ (zl s) x := by
  unfold qcentGens
  simp only
  rw [getElem!_pos _ s (by simp [planeGenCount]; omega), Array.getElem_map, Array.getElem_range]
  exact apG objRun_rep hs hx

theorem qcentGens_size : (qcentGens (objRun ()).1).size = 14 := by
  simp [qcentGens, planeGenCount]

theorem qTree (hcl : closedS NWQ KAQ KBQ ((List.range 14).map zl)
      (closeS NWQ KAQ KBQ ((List.range 14).map zl) 5 (single 749820)) = true)
    (hc : ((List.range 920808).filter (memS (closeS NWQ KAQ KBQ ((List.range 14).map zl) 5
      (single 749820)))).length = 693) :
    (treeBFS degree qcentRoot (qcentGens (objRun ()).1) (Array.range planeGenCount)).pts.size = 693 ∧
      treeOK degree qcentRoot (treeBFS degree qcentRoot (qcentGens (objRun ()).1)
        (Array.range planeGenCount)) (qcentGens (objRun ()).1) (Array.range planeGenCount) = true ∧
      ∀ x < 920808, (∃ j < (treeBFS degree qcentRoot (qcentGens (objRun ()).1)
          (Array.range planeGenCount)).pts.size,
        ap (treeBFS degree qcentRoot (qcentGens (objRun ()).1) (Array.range planeGenCount)).pts j = x) ↔
        memS (closeS NWQ KAQ KBQ ((List.range 14).map zl) 5 (single 749820)) x = true := by
  have horb : orbOK NWQ KAQ KBQ ((List.range 14).map zl) 749820 5 693 = true := by
    unfold orbOK
    rw [letB_eq']
    rw [hcl, pcount_pts, hc]
    rfl
  exact tree_of_orbOK (c := zl) (by decide) (by simp [planeGenCount, Array.toList_range])
    (fun z hz => by
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hz
      exact lokQ (zl_lok s (List.mem_range.1 hs)))
    (fun l hl x hx => ap_qcentGens (by simpa [planeGenCount] using hl) hx)
    (fun l hl => by simp [planeGenCount] at hl; omega) horb

theorem qcentOKAt_true : qcentOKAt (objRun ()).1 (genTabs ()) = true := by
  obtain ⟨hcl, hc1, hc2, hc3, hx2, hcov⟩ := qcentSetOK_spec QCentCk.qcentSet
  have hzp : ([-29, -30, -31, -32, -33, -34, -35, -36, -38, -39] : List Int) = zpL := rfl
  have hG0 : closeS NWP KAP KBP zpL 33 (single 1479) = gS 1 := rfl
  rw [hzp, hG0] at hc1 hc2 hcov
  obtain ⟨hTs, hTok, hTm⟩ := qTree hcl hc3
  have hok := (gTree (i := 1) (by decide)).2.1
  have hS1 := (gTree (i := 1) (by decide)).2.2
  rw [← geomTrees_get (i := 1) (by decide)] at hS1 hok
  have hlt : ∀ k < ((geomTrees (genTabs ()))[1]!).pts.size,
      ap ((geomTrees (genTabs ()))[1]!).pts k < 920808 := fun k hk => pts_lt_of_treeOK hok hk
  have hmem : ∀ k < ((geomTrees (genTabs ()))[1]!).pts.size,
      memS (gS 1) (ap ((geomTrees (genTabs ()))[1]!).pts k) = true :=
    fun k hk => (hS1 _ (hlt k hk)).1 ⟨k, hk, rfl⟩
  set T0 := (geomTrees (genTabs ()))[1]! with hT0
  set Tq := treeBFS degree qcentRoot (qcentGens (objRun ()).1) (Array.range planeGenCount) with hTq
  have l10 : LOK NWO KAO KBO (Int.ofNat (9 + 1)) := lokO_reg (by decide)
  have l48 : LOK NWO KAO KBO (Int.ofNat (47 + 1)) := lokO_reg (by decide)
  have hl10 : LOK NWO KAO KBO (-10) := lokO (by decide)
  have htau : ∀ x (hx : x < 920808), ap (objRun ()).1[tauReg]! x = (gO 9 ⟨x, hx⟩).val := by
    intro x hx
    rw [objRun_rep tauReg (by decide) x hx, idx_of_lt _ hx, Perm.smul_def]
    rfl
  have htauL : ∀ x (hx : x < 920808), ap (objRun ()).1[tauReg]! x = eL NWO KAO KBO (-10) x := by
    intro x hx
    rw [htau x hx]
    exact gT_apply l10 ⟨x, hx⟩
  have hfix : ∀ x (hx : x < 920808), (ap (objRun ()).1[epsReg qcentEps]! x == x) =
      memS (fixS NWO KAO KBO 48) x := by
    intro x hx
    have e : epsReg qcentEps = 47 := rfl
    rw [e, objRun_rep 47 (by decide) x hx, idx_of_lt _ hx, Perm.smul_def]
    have key : ((gO 47 ⟨x, hx⟩).val = x) ↔ ((gO 47)⁻¹ ⟨x, hx⟩).val = x := by
      constructor
      · intro h
        have h' : gO 47 ⟨x, hx⟩ = ⟨x, hx⟩ := Fin.ext h
        rw [Perm.inv_eq_iff_eq.2 h'.symm]
      · intro h
        have h' : (gO 47)⁻¹ ⟨x, hx⟩ = ⟨x, hx⟩ := Fin.ext h
        rw [← Perm.inv_eq_iff_eq.1 h']
    rw [gT_inv_apply l48 ⟨x, hx⟩] at key
    have e48 : (Int.ofNat (47 + 1)) = (48 : ℤ) := rfl
    rw [e48, ← memS_fixS (lokO (by decide)) hx] at key
    rw [Bool.eq_iff_iff, beq_iff_eq]
    exact key
  unfold qcentOKAt qcentCheck
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true']
  refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, qcentGens_size⟩, hTs⟩, hTok⟩, ?_⟩, ?_⟩
  ·
    rw [qcentCount_eq, Nat.zero_add, ← hc1]
    refine card_range_filter_eq (fun k => ap T0.pts k) _ _
      (fun a ha b hb hab => pts_inj_of_treeOK hok ha hb hab) (fun k hk hq => ?_) (fun y hy hR => ?_)
    · refine ⟨hlt k hk, ?_⟩
      rw [CFSG.KS.RouteP.memS_land, ← hfix _ (hlt k hk), hq, hmem k hk]
      rfl
    · rw [CFSG.KS.RouteP.memS_land, Bool.and_eq_true] at hR
      obtain ⟨k, hk, rfl⟩ := (hS1 y hy).2 hR.2
      refine ⟨k, hk, ?_, rfl⟩
      rw [hfix _ hy]
      exact hR.1
  ·
    rw [qcentCount_eq, Nat.zero_add, ← hc2]
    refine card_range_filter_eq (fun k => ap (objRun ()).1[tauReg]! (ap T0.pts k)) _ _
      (fun a ha b hb hab => ?_) (fun k hk hq => ?_) (fun y hy hR => ?_)
    · rw [htau _ (hlt a ha), htau _ (hlt b hb)] at hab
      have := (gO 9).injective (Fin.ext hab)
      exact pts_inj_of_treeOK hok ha hb (Fin.mk.inj this)
    · have hx := hlt k hk
      rw [htauL _ hx] at hq ⊢
      have hy := eL_lt hl10 hx
      refine ⟨hy, ?_⟩
      rw [CFSG.KS.RouteP.memS_land, ← hfix _ hy, hq, memS_imgS hl10 _ hx, hmem k hk]
      rfl
    · rw [CFSG.KS.RouteP.memS_land, Bool.and_eq_true] at hR
      obtain ⟨M, hM, hMG, rfl⟩ := memS_imgS_iff hl10 _ hy hR.2
      obtain ⟨k, hk, rfl⟩ := (hS1 M hM).2 hMG
      refine ⟨k, hk, ?_, ?_⟩
      · rw [htauL _ hM, hfix _ (eL_lt hl10 hM)]
        exact hR.1
      · rw [htauL _ hM]
  ·
    rw [Bool.eq_false_iff]
    intro h
    rw [memTree_iff hTok, hTm 99705 (by decide), hx2] at h
    exact Bool.false_ne_true h
  ·
    rw [allIn_eq_true]
    intro k _ hk
    have hx := hlt k hk
    rw [htauL _ hx]
    have hy := eL_lt hl10 hx
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, beq_iff_eq]
    by_cases hG : memTree T0 (eL NWO KAO KBO (-10) (ap T0.pts k)) = true
    · by_cases hF : ap (objRun ()).1[epsReg qcentEps]! (eL NWO KAO KBO (-10) (ap T0.pts k)) =
          eL NWO KAO KBO (-10) (ap T0.pts k)
      · have hF' := hfix _ hy
        rw [hF, beq_self_eq_true] at hF'
        have hG' : memS (gS 1) (eL NWO KAO KBO (-10) (ap T0.pts k)) = true := by
          rw [← (hS1 _ hy)]
          exact (memTree_iff hok _).1 hG
        have hT' : memS (imgS NWO KAO KBO (-10) (gS 1)) (eL NWO KAO KBO (-10) (ap T0.pts k)) = true := by
          rw [memS_imgS hl10 _ hx]
          exact hmem k hk
        rcases hcov _ hy hT' hG' hF'.symm with h | h
        · exact Or.inl (Or.inr h)
        · right
          rw [memTree_iff hTok, hTm _ hy]
          exact h
      · exact Or.inl (Or.inl (Or.inr (beq_eq_false_iff_ne.2 hF)))
    · exact Or.inl (Or.inl (Or.inl (by simpa using hG)))

theorem qcentOK_true : qcentOK () = true := qcentOKAt_true

end CertificateChecks.KernelRouteP

end
