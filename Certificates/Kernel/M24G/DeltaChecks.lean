module

public import Certificates.Data.Kernel.M24G.Orbits
public import Certificates.Kernel.M24G.TrioData
public import Certificates.Kernel.M24G.TSData
public import Certificates.Kernel.M24G.OrbData
public import Certificates.Kernel.M24G.OrbitsQ

set_option maxRecDepth 400000

public section

namespace CFSG.KC.M24G.DeltaC

open CFSG.KC.M24G CFSG.Quasithin.H13.AS91.M24G LookQ OrbQ

set_option maxHeartbeats 0 in
theorem step0 : chkT (trioStepF TL (lookW 3795 72 Native.key3 dec3 TL) (Native.lTabs.getD 0 #[]))
    12 dT0 0 3795 = true := by
  rw [lookW_eq_P ptTL_eq]
  decide +kernel

set_option maxHeartbeats 0 in
theorem step1 : chkT (trioStepF TL (lookW 3795 72 Native.key3 dec3 TL) (Native.lTabs.getD 1 #[]))
    12 dT1 0 3795 = true := by
  rw [lookW_eq_P ptTL_eq]
  decide +kernel

set_option maxHeartbeats 0 in
theorem step2 : chkT (trioStepF TL (lookW 3795 72 Native.key3 dec3 TL) (Native.lTabs.getD 2 #[]))
    12 dT2 0 3795 = true := by
  rw [lookW_eq_P ptTL_eq]
  decide +kernel

set_option maxHeartbeats 0 in
theorem step3 : chkT (trioStepF TL (lookW 3795 72 Native.key3 dec3 TL) (Native.lTabs.getD 3 #[]))
    12 dT3 0 3795 = true := by
  rw [lookW_eq_P ptTL_eq]
  decide +kernel

set_option maxHeartbeats 0 in
theorem cls_eq : deltaCls (lookW 3795 72 Native.key3 dec3 TL) (lookW 3795 77 (packW 11) (decW 7 11) TS)
    = dCls := by
  unfold deltaCls
  rw [deltaBF_eq_Q, lookW_eq_P ptTL_eq, lookW_eq_P ptTS_eq]
  decide +kernel

set_option maxHeartbeats 0 in
theorem row0 : allR (deltaRow (lookW 3795 72 Native.key3 dec3 TL)
    (lookW 3795 77 (packW 11) (decW 7 11) TS)) 0 1000 = true := by
  unfold deltaRow
  rw [deltaBF_eq_Q, lookW_eq_P ptTL_eq, lookW_eq_P ptTS_eq]
  decide +kernel

set_option maxHeartbeats 0 in
theorem row1 : allR (deltaRow (lookW 3795 72 Native.key3 dec3 TL)
    (lookW 3795 77 (packW 11) (decW 7 11) TS)) 1000 1000 = true := by
  unfold deltaRow
  rw [deltaBF_eq_Q, lookW_eq_P ptTL_eq, lookW_eq_P ptTS_eq]
  decide +kernel

set_option maxHeartbeats 0 in
theorem row2 : allR (deltaRow (lookW 3795 72 Native.key3 dec3 TL)
    (lookW 3795 77 (packW 11) (decW 7 11) TS)) 2000 1000 = true := by
  unfold deltaRow
  rw [deltaBF_eq_Q, lookW_eq_P ptTL_eq, lookW_eq_P ptTS_eq]
  decide +kernel

set_option maxHeartbeats 0 in
theorem row3 : allR (deltaRow (lookW 3795 72 Native.key3 dec3 TL)
    (lookW 3795 77 (packW 11) (decW 7 11) TS)) 3000 795 = true := by
  unfold deltaRow
  rw [deltaBF_eq_Q, lookW_eq_P ptTL_eq, lookW_eq_P ptTS_eq]
  decide +kernel

theorem gens_ok : Native.lTabs.all (fun g => Native.imgTrio g Native.baseTrio == Native.baseTrio) = true := by
  decide +kernel

theorem rest_ok : deltaCkF (lookW 3795 72 Native.key3 dec3 TL)
    (lookW 3795 77 (packW 11) (decW 7 11) TS) (fun _ => true) = true := by
  rw [deltaCkF_rest, gens_ok, Bool.true_and, all_range_eq, Native.nTrio,
    allR_split _ 1000 2795 1000 rfl rfl, allR_split _ 1000 1795 2000 rfl rfl,
    allR_split _ 1000 795 3000 rfl rfl, row0, row1, row2, row3]
  rfl

@[expose] noncomputable def dSteps : List (Nat → Nat) :=
  [tabF 3795 12 dT0 (trioStepF TL (lookW 3795 72 Native.key3 dec3 TL) (Native.lTabs.getD 0 #[])),
    tabF 3795 12 dT1 (trioStepF TL (lookW 3795 72 Native.key3 dec3 TL) (Native.lTabs.getD 1 #[])),
    tabF 3795 12 dT2 (trioStepF TL (lookW 3795 72 Native.key3 dec3 TL) (Native.lTabs.getD 2 #[])),
    tabF 3795 12 dT3 (trioStepF TL (lookW 3795 72 Native.key3 dec3 TL) (Native.lTabs.getD 3 #[]))]

@[expose] noncomputable def dRun (k : Nat) : List Nat × List Nat × List Nat := dRuns.getD k ([], [], [])

@[expose] noncomputable def dChunk (k f a b a' b' : Nat) : Bool :=
  @ReplayQ.chunkB Nat decEqNQ id dSteps (posTreeB id (dRun k).1) (dRun k).1 (dRun k).2.1
    (dRun k).2.2 f a b a' b'

set_option maxHeartbeats 0 in
theorem part_ok : clsPartB Native.nTrio dCls [1, 42, 56, 1008, 2688] dRuns = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cls0_ok : clsOneB Native.nTrio dSteps (dCls.getD 0 []) 1 (dRun 0) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cls1_ok : clsOneB Native.nTrio dSteps (dCls.getD 1 []) 42 (dRun 1) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cls2_ok : clsOneB Native.nTrio dSteps (dCls.getD 2 []) 56 (dRun 2) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cls3_tests : (dCls.getD 3 []).isEmpty = false ∧ ((dCls.getD 3 []).length == 1008) = true ∧
    (dRun 3).1.all (fun x => Nat.blt x Native.nTrio) = true ∧
    (dCls.getD 3 []).all (fun q => (maskL (dRun 3).1).testBit q) = true ∧
    (sizeK (posTreeB id (dRun 3).1) == (dRun 3).1.length) = true ∧
    @ReplayQ.headB Nat decEqNQ ((dCls.getD 3 []).headD 0) (dRun 3).1 (dRun 3).2.1 (dRun 3).2.2 = true ∧
    posAllB id (posTreeB id (dRun 3).1) ((dRun 3).1.drop 0) 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cls3_run1 : dChunk 3 1008 0 1 1008 1008 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem cls3_end : @replayGoB Nat decEqNQ id dSteps (posTreeB id (dRun 3).1) 3992 ((dRun 3).1.drop 1008)
    1008 ((dRun 3).1.drop 1008) ((dRun 3).2.1.drop 1008) ((dRun 3).2.2.drop 1008) 1008 = true := by
  decide +kernel

theorem cls3_ok : clsOneB Native.nTrio dSteps (dCls.getD 3 []) 1008 (dRun 3) = true := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := cls3_tests
  refine clsOneB_of h1 h2 (@ReplayQ.replayOKB_of _ decEqNQ _ _ _ _ _ _ _ _ h5 h7 h6 ?_) h3 h4
  exact (@ReplayQ.replayGoB_chunk _ decEqNQ _ _ _ _ _ _ _ _ _ _ _ cls3_run1 3992).trans cls3_end

set_option maxHeartbeats 0 in
theorem cls4_tests : (dCls.getD 4 []).isEmpty = false ∧ ((dCls.getD 4 []).length == 2688) = true ∧
    (dRun 4).1.all (fun x => Nat.blt x Native.nTrio) = true ∧
    (dCls.getD 4 []).all (fun q => (maskL (dRun 4).1).testBit q) = true ∧
    (sizeK (posTreeB id (dRun 4).1) == (dRun 4).1.length) = true ∧
    @ReplayQ.headB Nat decEqNQ ((dCls.getD 4 []).headD 0) (dRun 4).1 (dRun 4).2.1 (dRun 4).2.2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cls4_pos1 : ReplayQ.posAllN id (posTreeB id (dRun 4).1) 1344 ((dRun 4).1.drop 0) 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cls4_pos2 : posAllB id (posTreeB id (dRun 4).1) ((dRun 4).1.drop 1344) 1344 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cls4_run1 : dChunk 4 1000 0 1 1000 2237 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem cls4_run2 : dChunk 4 1000 1000 2237 2000 2672 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem cls4_run3 : dChunk 4 688 2000 2672 2688 2688 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem cls4_end : @replayGoB Nat decEqNQ id dSteps (posTreeB id (dRun 4).1) 2312 ((dRun 4).1.drop 2688)
    2688 ((dRun 4).1.drop 2688) ((dRun 4).2.1.drop 2688) ((dRun 4).2.2.drop 2688) 2688 = true := by
  decide +kernel

theorem cls4_ok : clsOneB Native.nTrio dSteps (dCls.getD 4 []) 2688 (dRun 4) = true := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := cls4_tests
  refine clsOneB_of h1 h2 (@ReplayQ.replayOKB_of _ decEqNQ _ _ _ _ _ _ _ _ h5
    (ReplayQ.posAllB_chunk cls4_pos1 cls4_pos2) h6 ?_) h3 h4
  exact (@ReplayQ.replayGoB_chunk _ decEqNQ _ _ _ _ _ _ _ _ _ _ _ cls4_run1 4000).trans
    ((@ReplayQ.replayGoB_chunk _ decEqNQ _ _ _ _ _ _ _ _ _ _ _ cls4_run2 3000).trans
    ((@ReplayQ.replayGoB_chunk _ decEqNQ _ _ _ _ _ _ _ _ _ _ _ cls4_run3 2312).trans cls4_end))

theorem orb_ok : classOrbitKB Native.nTrio dCls [1, 42, 56, 1008, 2688] dSteps dRuns = true := by
  refine classOrbitKB_of part_ok fun k hk => ?_
  rcases k with _ | _ | _ | _ | _ | k
  · exact cls0_ok
  · exact cls1_ok
  · exact cls2_ok
  · exact cls3_ok
  · exact cls4_ok
  · exact absurd hk (by simp)

theorem ok : deltaCkF (lookW 3795 72 Native.key3 dec3 TL) (lookW 3795 77 (packW 11) (decW 7 11) TS)
    (fun cls => classOrbitK Native.nTrio cls [1, 42, 56, 1008, 2688]
      (trioStepsK TL (lookW 3795 72 Native.key3 dec3 TL) Native.lTabs) dRuns) = true := by
  rw [deltaCkF_split, rest_ok, Bool.true_and, cls_eq, trioStepsK_eq_B, lTabs_map, ← tabF_eq step0,
    ← tabF_eq step1, ← tabF_eq step2, ← tabF_eq step3, classOrbitK_eq_B]
  exact orb_ok

end CFSG.KC.M24G.DeltaC
