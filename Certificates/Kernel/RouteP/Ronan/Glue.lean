module

public import Certificates.Kernel.RouteP.Ronan.Base
public import Certificates.Kernel.RouteP.Ronan.E0
public import Certificates.Kernel.RouteP.Ronan.E1
public import Certificates.Kernel.RouteP.Ronan.E2
public import Certificates.Kernel.RouteP.Ronan.E3
public import Certificates.Kernel.RouteP.Ronan.E4
public import Certificates.Kernel.RouteP.Ronan.E5
public import Certificates.Kernel.RouteP.Ronan.Grp
public import Certificates.Kernel.RouteP.Ronan.H4
public import Certificates.Kernel.RouteP.Ronan.Root
public import Certificates.Kernel.RouteP.Geom.Dist
public import CFSG.Certificates.Kernel.RouteP.RonanSound
public import CFSG.Certificates.Kernel.RouteP.RonanSpan
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.Spheres
import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.Kernel.RouteP.MemSBits
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Generic.Certificates
public import CFSG.GH74.Statements
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.PlaneAction
public import CFSG.LocalAnalysis.SectionRank.CentralLift
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.OrderCheckF
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.PrimaryCells
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs

public section

namespace CertificateChecks.KernelRouteP.Ronan

open Equiv CFSG.KC CFSG.KC.RouteP CFSG.KS.RouteP CFSG.KD.RouteP CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.Native
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom CFSG.Perm.Native
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three
  CFSG.KC.Benes CFSG.KS.Fi24Net CFSG.KS.Fi24NetPt CertificateChecks.KernelRouteP

#kc_forall_tree ent_all (fun e => CFSG.KD.RouteP.entCk e = true) 181 CFSG.KD.RouteP.entCk

theorem eL_negSucc_congr {NW NW' : Nat → Nat → Nat} {KA KB KA' KB' : Nat → Nat} {n n' : Nat}
    (h : NW n = NW' n') (ha : KA n = KA' n') (hb : KB n = KB' n') :
    eL NW KA KB (Int.negSucc n) = eL NW' KA' KB' (Int.negSucc n') := by
  funext N
  have e1 : fibF NW (Int.negSucc n) = pR (NW n) := rfl
  have e1' : fibF NW' (Int.negSucc n') = pR (NW' n') := rfl
  have e2 : lK NW KA KB (Int.negSucc n) = fun p => (2 * kv (KA n) (KB n) (pR (NW n) p)) % 3 := rfl
  have e2' : lK NW' KA' KB' (Int.negSucc n') =
      fun p => (2 * kv (KA' n') (KB' n') (pR (NW' n') p)) % 3 := rfl
  unfold eL
  rw [e1, e1', e2, e2', h, ha, hb]

theorem lok_negSucc_congr {NW NW' : Nat → Nat → Nat} {KA KB KA' KB' : Nat → Nat} {n n' : Nat}
    (h : NW n = NW' n') (ha : KA n = KA' n') (hb : KB n = KB' n')
    (hl : LOK NW' KA' KB' (Int.negSucc n')) : LOK NW KA KB (Int.negSucc n) := by
  unfold LOK at hl ⊢
  rw [Int.natAbs_negSucc, Nat.succ_sub_one] at hl ⊢
  have hk : kapOK KA KB n = kapOK KA' KB' n' := by
    unfold kapOK
    rw [ha, hb]
  rw [h, hk]
  exact hl

theorem NWC_lo {n : Nat} (hn : n < 58) : NWC n = NWO n := by
  funext l
  have hb : Nat.blt n 58 = true := by
    rw [Nat.blt_eq]
    exact hn
  unfold NWC
  rw [hb]

theorem NWC_hi (n : Nat) : NWC (n + 58) = NWP n := by
  funext l
  have hb : Nat.blt (n + 58) 58 = false := by
    rw [Bool.eq_false_iff]
    intro h
    rw [Nat.blt_eq] at h
    omega
  unfold NWC
  rw [hb]
  change NWP (n + 58 - 58) l = NWP n l
  rw [Nat.add_sub_cancel]


theorem mem_gS_iff {i : Nat} (hi : i < 7) (v : Ω) :
    memS (gS i) v.val = true ↔ v ∈ MulAction.orbit Zp (repPt ⟨i, hi⟩) := by
  have hF := CFSG.Perm.treeOK_facts (n := 920808)
    (fun _ hl => rep_genQ_of_mem_zpLetters hl) (gTree hi).2.1
  have e : repPt ⟨i, hi⟩ = ⟨gRoot i, hF.r_lt⟩ := Fin.ext (by rw [repPt_val, geomReps_get hi])
  rw [← (gTree hi).2.2 v.val v.isLt, e, ← lettersGroup_zpLetters]
  exact (hF.mem_orbit_iff v).symm

theorem pl0_eq : pl RN 0 = gS 1 :=
  (baseOK_spec (NW := NWP) (KA := KAP) (KB := KBP)
    (zg := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (R := RN) (i := 0) baseCk0).1
    (by decide)

theorem pl1_eq : pl RN 1 = gS 3 :=
  (baseOK_spec (NW := NWP) (KA := KAP) (KB := KBP)
    (zg := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (R := RN) (i := 1) baseCk1).1
    (by decide)

theorem pl2_eq : pl RN 2 = gS 4 :=
  (baseOK_spec (NW := NWP) (KA := KAP) (KB := KBP)
    (zg := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (R := RN) (i := 2) baseCk2).1
    (by decide)

theorem pl3_eq : pl RN 3 = imgW NWP KAP KBP (gMW 2) (pl RN 0) :=
  (baseOK_spec (NW := NWP) (KA := KAP) (KB := KBP)
    (zg := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (R := RN) (i := 3) baseCk3).2
    (by decide)

theorem pl4_eq : pl RN 4 = imgW NWP KAP KBP (gMW 3) (pl RN 0) :=
  (baseOK_spec (NW := NWP) (KA := KAP) (KB := KBP)
    (zg := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (R := RN) (i := 4) baseCk4).2
    (by decide)

theorem pl5_eq : pl RN 5 = imgW NWP KAP KBP (gMW 4) (pl RN 0) :=
  (baseOK_spec (NW := NWP) (KA := KAP) (KB := KBP)
    (zg := [-29, -30, -31, -32, -33, -34, -35, -36, -38, -39]) (R := RN) (i := 5) baseCk5).2
    (by decide)

theorem mem_pl0_iff (v : Ω) : memS (pl RN 0) v.val = true ↔ Δ.Adj x0 v := by
  rw [pl0_eq, mem_gS_iff (i := 1) (by decide), Δ_adj_x0_iff]
  have e : repPt ⟨1, by decide⟩ = x1 := repPt_one
  rw [e]

theorem lok_of_letters {w : List Int} (hw : ∀ z ∈ w, z = -1 ∨ z = -2) :
    ∀ z ∈ w, LOK NWP KAP KBP z := by
  intro z hz
  rcases hw z hz with rfl | rfl <;> exact lokP (by decide)

theorem mem_imgW_iff {w : List Int} (hw : ∀ z ∈ w, z = -1 ∨ z = -2) {u : Ω}
    (hu : eW NWP KAP KBP w 0 = u.val) (v : Ω) :
    memS (imgW NWP KAP KBP w (pl RN 0)) v.val = true ↔ Δ.Adj u v := by
  obtain ⟨h, hh⟩ := exists_wordQ w hw
  have hu' : h • x0 = u := Fin.ext (by rw [hh, x0_val, hu])
  have e : v = h • (h⁻¹ • v) := (smul_inv_smul h v).symm
  rw [e, hh, memS_imgW w (lok_of_letters hw) _ (h⁻¹ • v).isLt, mem_pl0_iff, ← hu', Δ_adj_smul]

theorem gMW_x0 {i : Nat} (hi : i < 7) : eW NWP KAP KBP (gMW i) 0 = (repPt ⟨i, hi⟩).val := by
  rw [repPt_val, geomReps_get hi]
  exact ptOK_spec (gMW_lok hi) (by decide) (gRoot_lt hi) (gFacts.root i hi)

theorem mem_gMW_iff {i : Nat} (hi : i < 7) (v : Ω) :
    memS (imgW NWP KAP KBP (gMW i) (pl RN 0)) v.val = true ↔ Δ.Adj (repPt ⟨i, hi⟩) v :=
  mem_imgW_iff (gMW_letters hi) (gMW_x0 hi) v

theorem mem_pl3_iff (v : Ω) : memS (pl RN 3) v.val = true ↔ Δ.Adj y2 v := by
  rw [pl3_eq]
  exact mem_gMW_iff (i := 2) (by decide) v

theorem mem_pl4_iff (v : Ω) : memS (pl RN 4) v.val = true ↔ Δ.Adj y3a v := by
  rw [pl4_eq]
  exact mem_gMW_iff (i := 3) (by decide) v

theorem mem_pl5_iff (v : Ω) : memS (pl RN 5) v.val = true ↔ Δ.Adj y3b v := by
  rw [pl5_eq]
  exact mem_gMW_iff (i := 4) (by decide) v

theorem mem_l3S_iff (v : Ω) : memS (l3S RN) v.val = true ↔ Δ.dist x0 v = 3 := by
  unfold l3S
  rw [memS_lor, pl1_eq, pl2_eq, Bool.or_eq_true, mem_gS_iff (i := 3) (by decide),
    mem_gS_iff (i := 4) (by decide), dist_x0_eq_three_iff]
  exact Iff.rfl

theorem mem_l2S_iff (v : Ω) : memS (l2S RN) v.val = true ↔ Δ.dist x0 v = 2 := by
  have key : memS (l2S RN) v.val = true ↔ ¬ (v.val = 0 ∨ v.val = 1 ∨ v.val = 2 ∨
      memS (pl RN 0) v.val = true ∨ memS (l3S RN) v.val = true) := by
    unfold l2S
    rw [memS_land, memS_xor, memS_land, memS_ptsS v.isLt, memS_lor, memS_lor, memS_lor, memS_lor,
      memS_single (by decide) v.isLt, memS_single (by decide) v.isLt,
      memS_single (by decide) v.isLt]
    cases memS (pl RN 0) v.val <;> cases memS (l3S RN) v.val <;> simp
  have h0 : v.val = 0 ↔ Δ.dist x0 v = 0 := by
    rw [dist_x0_eq_zero_iff]
    exact ⟨fun h => Fin.ext (h.trans x0_val.symm), fun h => h ▸ x0_val⟩
  have h12 : (v.val = 1 ∨ v.val = 2) ↔ Δ.dist x0 v = 4 := by
    rw [dist_x0_eq_four_iff]
    have e5 : y4a.val = 1 := rfl
    have e6 : y4b.val = 2 := rfl
    constructor
    · rintro (h | h)
      · exact Or.inl (Fin.ext (h.trans e5.symm))
      · exact Or.inr (Fin.ext (h.trans e6.symm))
    · rintro (h | h)
      · exact Or.inl (h ▸ e5)
      · exact Or.inr (h ▸ e6)
  have h1 : memS (pl RN 0) v.val = true ↔ Δ.dist x0 v = 1 := by
    rw [mem_pl0_iff, SimpleGraph.dist_eq_one_iff_adj]
  have h4 := Δ_dist_x0_le_four v
  rw [key, h1, mem_l3S_iff, h0]
  constructor
  · intro h
    by_contra hne
    apply h
    rcases (by omega : Δ.dist x0 v = 0 ∨ Δ.dist x0 v = 1 ∨ Δ.dist x0 v = 3 ∨
      Δ.dist x0 v = 4) with h' | h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h')))
    · rcases h12.2 h' with h'' | h''
      · exact Or.inr (Or.inl h'')
      · exact Or.inr (Or.inr (Or.inl h''))
  · intro h hc
    rcases hc with h' | h' | h' | h' | h'
    · omega
    · have := h12.1 (Or.inl h')
      omega
    · have := h12.1 (Or.inr h')
      omega
    · omega
    · omega

@[expose] noncomputable def entPt (e : Nat) : Ω := ⟨eU (RE e) % 920808, Nat.mod_lt _ (by decide)⟩

theorem entWord_letters (e : Nat) : ∀ z ∈ twd (eLen (RE e)) (eCode (RE e)), z = -1 ∨ z = -2 :=
  twd_letters _ _

theorem mem_ent_iff {e : Nat} (he : e < 181) :
    (entPt e).val = eU (RE e) ∧ ∀ v : Ω, memS (pl RN (e + 6)) v.val = true ↔
      Δ.Adj (entPt e) v ∧ memS (tgt RN (eGrp (RE e))) v.val = true := by
  obtain ⟨h1, h2⟩ := entOK_spec (NW := NWP) (KA := KAP) (KB := KBP) (R := RN) (E := RE) (ent_all e he)
  have hw := entWord_letters e
  rw [ptW_eq] at h1
  have hlt : eU (RE e) < 920808 := h1 ▸ eW_lt _ (lok_of_letters hw) (by decide)
  have hv : (entPt e).val = eU (RE e) := Nat.mod_eq_of_lt hlt
  refine ⟨hv, fun v => ?_⟩
  rw [h2, memS_land, Bool.and_eq_true, mem_imgW_iff hw (h1.trans hv.symm) v]

theorem tgt0 : tgt RN 0 = Nat.land (pl RN 0) (pl RN 3) := rfl
theorem tgt1 : tgt RN 1 = Nat.land (pl RN 3) (l2S RN) := rfl
theorem tgt2 : tgt RN 2 = Nat.land (pl RN 4) (l2S RN) := rfl
theorem tgt3 : tgt RN 3 = Nat.land (pl RN 4) (l3S RN) := rfl
theorem tgt4 : tgt RN 4 = Nat.land (pl RN 5) (l2S RN) := rfl
theorem tgt5 : tgt RN 5 = Nat.land (pl RN 5) (l3S RN) := rfl
theorem src1 : src RN 1 = Nat.land (pl RN 0) (pl RN 3) := rfl
theorem src3 : src RN 3 = Nat.land (pl RN 4) (l2S RN) := rfl
theorem src5 : src RN 5 = Nat.land (pl RN 5) (l2S RN) := rfl

theorem span_preconnected {g lo hi : Nat} (hg : g % 2 = 0) (hhi : hi ≤ 181) (hlo : lo < hi)
    (hgrp : grpOK RN RE g lo hi = true) (hroot : rootOK RE lo hi = true) {S : Set Ω}
    (hS : ∀ v : Ω, memS (tgt RN g) v.val = true ↔ v ∈ S) : (Δ.induce S).Preconnected := by
  obtain ⟨hA, hB⟩ := grpOK_spec hgrp
  have hr := rootOK_spec hroot
  have hent : ∀ e, lo ≤ e → e < hi → eGrp (RE e) = g ∧ (entPt e).val = eU (RE e) ∧
      ∀ v : Ω, memS (pl RN (e + 6)) v.val = true ↔ Δ.Adj (entPt e) v ∧ v ∈ S := by
    intro e h1 h2
    obtain ⟨hv, hm⟩ := mem_ent_iff (e := e) (by omega)
    have hgr := (hA e h1 h2).1
    refine ⟨hgr, hv, fun v => ?_⟩
    rw [hm, hgr, hS]
  refine preconnected_of_span (lo := lo) (hi := hi) entPt
    (fun e => {v | memS (pl RN (e + 6)) v.val = true})
    (fun e => ePar (RE e)) ?_ ?_ ?_ ?_
  · rcases (hA lo le_rfl hlo).2.2 hg with ⟨-, hm⟩ | ⟨hle, hlt, -⟩
    · rw [← hS, (hent lo le_rfl hlo).2.1]
      exact hm
    · omega
  · intro e h1 h2 v hv
    have := ((hent e h1 h2).2.2 v).1 hv
    exact ⟨this.2, this.1⟩
  · intro e h1 h2
    rcases (hA e (by omega) h2).2.2 hg with ⟨hp, -⟩ | ⟨hp1, hp2, hm⟩
    · have := hr e h1 h2
      omega
    · refine ⟨hp1, hp2, ?_⟩
      change memS (pl RN (ePar (RE e) + 6)) (entPt e).val = true
      rw [(hent e (by omega) h2).2.1]
      exact hm
  · intro v hv
    obtain ⟨e, h1, h2, hm⟩ := hB v.val ((hS v).2 hv)
    refine ⟨e, h1, h2, ?_⟩
    rcases hm with hm | ⟨-, hm⟩
    · exact Or.inl hm
    · right
      have hev := (hent e h1 h2).2.1
      rw [memS_single (hev ▸ (entPt e).isLt) v.isLt] at hm
      exact Fin.ext ((of_decide_eq_true hm).trans hev.symm)

theorem cover_witness {g lo hi : Nat} (hg : g % 2 = 1) (hhi : hi ≤ 181)
    (hgrp : grpOK RN RE g lo hi = true) {v : Ω} (hv : memS (tgt RN g) v.val = true) :
    ∃ e, Δ.Adj (entPt e) v ∧ memS (src RN g) (entPt e).val = true := by
  obtain ⟨hA, hB⟩ := grpOK_spec hgrp
  obtain ⟨e, h1, h2, hm⟩ := hB v.val hv
  obtain ⟨hev, hent⟩ := mem_ent_iff (e := e) (by omega)
  rcases hm with hm | ⟨hg', -⟩
  · refine ⟨e, ((hent v).1 hm).1, ?_⟩
    rw [hev]
    exact (hA e h1 h2).2.1 hg
  · omega

theorem ronan_Q_connected : (Δ.induce (Δ.commonNeighbors x0 y2)).Preconnected :=
  span_preconnected (g := 0) (lo := 0) (hi := 7) rfl (by decide) (by decide) grpCk0
    CFSG.KD.RouteP.RonanCk.root0 fun v => by
      rw [tgt0, memS_land, Bool.and_eq_true, mem_pl0_iff, mem_pl3_iff,
        SimpleGraph.mem_commonNeighbors]

theorem ronan_A3_connected_a :
    (Δ.induce {c | Δ.Adj y3a c ∧ Δ.dist x0 c = 2}).Preconnected :=
  span_preconnected (g := 2) (lo := 26) (hi := 71) rfl (by decide) (by decide) grpCk2
    CFSG.KD.RouteP.RonanCk.root2 fun v => by
      rw [tgt2, memS_land, Bool.and_eq_true, mem_pl4_iff, mem_l2S_iff]
      exact Iff.rfl

theorem ronan_A3_connected_b :
    (Δ.induce {c | Δ.Adj y3b c ∧ Δ.dist x0 c = 2}).Preconnected :=
  span_preconnected (g := 4) (lo := 105) (hi := 149) rfl (by decide) (by decide) grpCk4
    CFSG.KD.RouteP.RonanCk.root4 fun v => by
      rw [tgt4, memS_land, Bool.and_eq_true, mem_pl5_iff, mem_l2S_iff]
      exact Iff.rfl

theorem ronan_P_witness {y : Ω} (hy : Δ.dist x0 y = 2) (hadj : Δ.Adj y2 y) :
    ∃ c, Δ.Adj x0 c ∧ Δ.Adj c y2 ∧ Δ.Adj c y := by
  have hv : memS (tgt RN 1) y.val = true := by
    rw [tgt1, memS_land, Bool.and_eq_true, mem_pl3_iff, mem_l2S_iff]
    exact ⟨hadj, hy⟩
  obtain ⟨e, hA, hs⟩ := cover_witness (g := 1) (lo := 7) (hi := 26) rfl (by decide) grpCk1 hv
  rw [src1, memS_land, Bool.and_eq_true, mem_pl0_iff, mem_pl3_iff] at hs
  exact ⟨entPt e, hs.1, hs.2.symm, hA⟩

theorem ronan_Hp_witness_a {y : Ω} (hy : Δ.dist x0 y = 3) (hadj : Δ.Adj y3a y) :
    ∃ h, Δ.dist x0 h = 2 ∧ Δ.Adj h y3a ∧ Δ.Adj h y := by
  have hv : memS (tgt RN 3) y.val = true := by
    rw [tgt3, memS_land, Bool.and_eq_true, mem_pl4_iff, mem_l3S_iff]
    exact ⟨hadj, hy⟩
  obtain ⟨e, hA, hs⟩ := cover_witness (g := 3) (lo := 71) (hi := 105) rfl (by decide) grpCk3 hv
  rw [src3, memS_land, Bool.and_eq_true, mem_pl4_iff, mem_l2S_iff] at hs
  exact ⟨entPt e, hs.2, hs.1.symm, hA⟩

theorem ronan_Hp_witness_b {y : Ω} (hy : Δ.dist x0 y = 3) (hadj : Δ.Adj y3b y) :
    ∃ h, Δ.dist x0 h = 2 ∧ Δ.Adj h y3b ∧ Δ.Adj h y := by
  have hv : memS (tgt RN 5) y.val = true := by
    rw [tgt5, memS_land, Bool.and_eq_true, mem_pl5_iff, mem_l3S_iff]
    exact ⟨hadj, hy⟩
  obtain ⟨e, hA, hs⟩ := cover_witness (g := 5) (lo := 149) (hi := 181) rfl (by decide) grpCk5 hv
  rw [src5, memS_land, Bool.and_eq_true, mem_pl5_iff, mem_l2S_iff] at hs
  exact ⟨entPt e, hs.2, hs.1.symm, hA⟩

theorem ronan_dist_x0_eq_three_of_adj_y4a {y : Ω} (hadj : Δ.Adj y4a y) : Δ.dist x0 y = 3 :=
  (mem_l3S_iff y).1 (n4OK_spec CFSG.KD.RouteP.RonanCk.n4a y.val
    ((mem_gMW_iff (i := 5) (by decide) y).2 hadj))

theorem ronan_dist_x0_eq_three_of_adj_y4b {y : Ω} (hadj : Δ.Adj y4b y) : Δ.dist x0 y = 3 :=
  (mem_l3S_iff y).1 (n4OK_spec CFSG.KD.RouteP.RonanCk.n4b y.val
    ((mem_gMW_iff (i := 6) (by decide) y).2 hadj))

theorem letter_x0_x1 {z : Int} {s : Q3} (hs : ∀ y : Ω, (s • y).val = eL NWC KAC KBC z y.val)
    (h0 : eL NWC KAC KBC z 0 = 0)
    (h1 : eL NWC KAC KBC z 1479 = 1479 ∨
      memS (imgW NWP KAP KBP (gMW 1) (pl RN 0)) (eL NWC KAC KBC z 1479) = true) :
    s • x0 = x0 ∧ (s • x1 = x1 ∨ Δ.Adj x1 (s • x1)) := by
  refine ⟨Fin.ext (by rw [hs, x0_val, h0]), ?_⟩
  rcases h1 with h1 | h1
  · exact Or.inl (Fin.ext (by rw [hs, x1_val, h1]))
  · right
    have h := (mem_gMW_iff (i := 1) (by decide) (s • x1)).1 (by rw [hs, x1_val]; exact h1)
    have e : repPt ⟨1, by decide⟩ = x1 := repPt_one
    rwa [e] at h

@[expose] def H4Fix (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (z : Int) : Prop :=
  eLN NW KA KB z 0 = 0 ∧ (eLN NW KA KB z 1479 = 1479 ∨
    memS (pl RN 0) (eLN NW KA KB z 1479) = true ∧
    memS (imgW NWP KAP KBP (gMW 1) (pl RN 0)) (eLN NW KA KB z 1479) = true)

@[expose] def H4Letter (z : Int) : Prop :=
  LOK NWC KAC KBC z ∧ ∃ s : Q3, (∀ y : Ω, (s • y).val = eL NWC KAC KBC z y.val) ∧
    s • x0 = x0 ∧ (s • x1 = x1 ∨ Δ.Adj x1 (s • x1))

theorem h4Letter_of {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {z z' : Int}
    (hc : eL NWC KAC KBC z = eL NW KA KB z') (hl : LOK NWC KAC KBC z) {s : Q3}
    (hs : ∀ y : Ω, (s • y).val = eL NWC KAC KBC z y.val) (hf : H4Fix NW KA KB z') : H4Letter z := by
  obtain ⟨h0, h1⟩ := hf
  rw [eLN_eq, ← hc] at h0
  rw [eLN_eq, ← hc] at h1
  refine ⟨hl, s, hs, letter_x0_x1 hs h0 ?_⟩
  rcases h1 with h1 | ⟨-, h1⟩
  · exact Or.inl h1
  · exact Or.inr h1

theorem h4Letter_obj {n : Nat} (hn : n ∈ geomA1Letters) (hf : H4Fix NWO KAO KBO (Int.negSucc n)) :
    H4Letter (Int.negSucc n) := by
  have hn58 : n < 58 := by simp [geomA1Letters] at hn; omega
  have hN := NWC_lo hn58
  have ha : KAC n = KAO n := congrFun hN 37
  have hb : KBC n = KBO n := congrFun hN 38
  have hc : eL NWC KAC KBC (Int.negSucc n) = eL NWO KAO KBO (Int.negSucc n) :=
    eL_negSucc_congr hN ha hb
  have hl : LOK NWC KAC KBC (Int.negSucc n) :=
    lok_negSucc_congr hN ha hb (lokO (by simp; omega))
  refine h4Letter_of hc hl (s := objElt n) (fun y => ?_) hf
  rw [smul_val_of_rep (rep_objElt (by omega)) y, hc]
  exact hapA n hn y.val y.isLt

theorem h4Letter_pres {l : Nat} (hl : l ∈ zpLetters) (hl11 : l < 11)
    (hf : H4Fix NWP KAP KBP (Int.negSucc (28 + l))) : H4Letter (Int.negSucc (28 + l + 58)) := by
  have hN := NWC_hi (28 + l)
  have ha : KAC (28 + l + 58) = KAP (28 + l) := congrFun hN 37
  have hb : KBC (28 + l + 58) = KBP (28 + l) := congrFun hN 38
  have hc : eL NWC KAC KBC (Int.negSucc (28 + l + 58)) = eL NWP KAP KBP (Int.negSucc (28 + l)) :=
    eL_negSucc_congr hN ha hb
  have hcq : cq ((l + 1 : Nat) : ℤ) = Int.negSucc (28 + l) := by
    unfold cq
    rw [if_pos (by omega), if_pos (by omega), Int.negSucc_eq]
    omega
  have hlk : LOK NWC KAC KBC (Int.negSucc (28 + l + 58)) :=
    lok_negSucc_congr hN ha hb (lokP (by simp; omega))
  refine h4Letter_of hc hlk (s := genQ l) (fun y => ?_) hf
  rw [smul_val_of_rep (rep_genQ_of_mem_zpLetters hl) y, hc, ← hcq]
  exact hapZ l hl y.val y.isLt

theorem h4Letters : ∀ z ∈ h4L, H4Letter z := by
  obtain ⟨hO, hP, -⟩ := h4OK_spec CFSG.KD.RouteP.RonanCk.h4
  have hO' : ∀ n ∈ geomA1Letters, H4Letter (Int.negSucc n) := by
    intro n hn
    refine h4Letter_obj hn (hO _ ?_)
    simp [geomA1Letters] at hn
    rcases hn with rfl | rfl | rfl <;> decide
  have hP' : ∀ l ∈ ([1, 2, 3, 4, 5, 6, 7, 10] : List Nat), H4Letter (Int.negSucc (28 + l + 58)) := by
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    refine h4Letter_pres ?_ (by omega) (hP _ ?_)
    · rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [zpLetters]
    · rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  intro z hz
  simp only [h4L, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hO' 6 (by simp [geomA1Letters])
  · exact hO' 7 (by simp [geomA1Letters])
  · exact hO' 8 (by simp [geomA1Letters])
  · exact hP' 1 (by decide)
  · exact hP' 2 (by decide)
  · exact hP' 3 (by decide)
  · exact hP' 4 (by decide)
  · exact hP' 5 (by decide)
  · exact hP' 6 (by decide)
  · exact hP' 7 (by decide)
  · exact hP' 10 (by decide)

theorem ronan_H4_connected : (Δ.induce {c | Δ.Adj x0 c}).Preconnected := by
  obtain ⟨-, -, hcl⟩ := h4OK_spec CFSG.KD.RouteP.RonanCk.h4
  set S : Set Ω := {c | Δ.Adj x0 c}
  have hx1 : x1 ∈ S := Δ_adj_x0_x1
  let P : Nat → Prop := fun M => ∃ v : Ω, v.val = M ∧ ∃ hv : v ∈ S,
    (Δ.induce S).Reachable ⟨x1, hx1⟩ ⟨v, hv⟩
  have hstep : ∀ N, P N → ∀ z ∈ h4L, P (eL NWC KAC KBC z N) := by
    rintro N ⟨v, rfl, hv, hr⟩ z hz
    obtain ⟨-, s, hs, hs0, hs1⟩ := h4Letters z hz
    have hmap : ∀ c : Ω, c ∈ S → s • c ∈ S := fun c hc => by
      change Δ.Adj x0 (s • c)
      rw [← hs0, Δ_adj_smul]
      exact hc
    let φ : Δ.induce S →g Δ.induce S :=
      { toFun := fun c => ⟨s • c.1, hmap c.1 c.2⟩
        map_rel' := fun {a b} h => (Δ_adj_smul s a.1 b.1).2 h }
    have h1 : (Δ.induce S).Reachable ⟨x1, hx1⟩ ⟨s • x1, hmap x1 hx1⟩ := by
      rcases hs1 with e | hA
      · have e' : (⟨s • x1, hmap x1 hx1⟩ : S) = ⟨x1, hx1⟩ := Subtype.ext e
        rw [e']
      · have hA' : (Δ.induce S).Adj ⟨x1, hx1⟩ ⟨s • x1, hmap x1 hx1⟩ := hA
        exact hA'.reachable
    exact ⟨s • v, hs v, hmap v hv, h1.trans (hr.map φ)⟩
  have hbase : ∀ N < 920808, memS (single 1479) N = true → P N := by
    intro N hN hm
    rw [memS_single (by decide) hN] at hm
    exact ⟨x1, x1_val.trans (of_decide_eq_true hm).symm, hx1, SimpleGraph.Reachable.refl _⟩
  have hg : ∀ z ∈ h4L, LOK NWC KAC KBC z := fun z hz => (h4Letters z hz).1
  have reach : ∀ c : S, (Δ.induce S).Reachable ⟨x1, hx1⟩ c := by
    rintro ⟨c, hc⟩
    have hm : memS (closeS NWC KAC KBC h4L 7 (single 1479)) c.val = true := by
      rw [hcl]
      exact (mem_pl0_iff c).2 hc
    obtain ⟨v, hvc, hv, hr⟩ := closeS_min hg P hstep 7 _ hbase c.val c.isLt hm
    have e : v = c := Fin.ext hvc
    subst e
    exact hr
  intro a b
  exact (reach a).symm.trans (reach b)

end CertificateChecks.KernelRouteP.Ronan

end
