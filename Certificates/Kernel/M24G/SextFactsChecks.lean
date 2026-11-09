module

public import Certificates.Data.Kernel.M24G.Orbits
public import Certificates.Kernel.M24G.TrioData
public import Certificates.Kernel.M24G.SextData
public import Certificates.Kernel.M24G.TSData
public import Certificates.Kernel.M24G.OrbData
public import Certificates.Kernel.M24G.OrbitsQ

set_option maxRecDepth 400000

public section

namespace CFSG.KC.M24G.SextFactsC

open CFSG.KC.M24G CFSG.Quasithin.H13.AS91.M24G LookQ OrbQ

set_option maxHeartbeats 0 in
theorem tstep0 : chkT (trioStepF TL (lookW 3795 72 Native.key3 dec3 TL) (Native.uTabs.getD 0 #[]))
    12 uT0 0 3795 = true := by
  rw [lookW_eq_P ptTL_eq]
  decide +kernel

set_option maxHeartbeats 0 in
theorem tstep1 : chkT (trioStepF TL (lookW 3795 72 Native.key3 dec3 TL) (Native.uTabs.getD 1 #[]))
    12 uT1 0 3795 = true := by
  rw [lookW_eq_P ptTL_eq]
  decide +kernel

set_option maxHeartbeats 0 in
theorem tstep2 : chkT (trioStepF TL (lookW 3795 72 Native.key3 dec3 TL) (Native.uTabs.getD 2 #[]))
    12 uT2 0 3795 = true := by
  rw [lookW_eq_P ptTL_eq]
  decide +kernel

set_option maxHeartbeats 0 in
theorem tstep3 : chkT (trioStepF TL (lookW 3795 72 Native.key3 dec3 TL) (Native.uTabs.getD 3 #[]))
    12 uT3 0 3795 = true := by
  rw [lookW_eq_P ptTL_eq]
  decide +kernel

set_option maxHeartbeats 0 in
theorem sstep0 : chkT (sextStepF SL (lookW 1771 144 (packW 24) (decW 6 24) SL) (Native.uTabs.getD 0 #[]))
    11 uS0 0 1771 = true := by
  rw [lookW_eq_P ptSL_eq]
  decide +kernel

set_option maxHeartbeats 0 in
theorem sstep1 : chkT (sextStepF SL (lookW 1771 144 (packW 24) (decW 6 24) SL) (Native.uTabs.getD 1 #[]))
    11 uS1 0 1771 = true := by
  rw [lookW_eq_P ptSL_eq]
  decide +kernel

set_option maxHeartbeats 0 in
theorem sstep2 : chkT (sextStepF SL (lookW 1771 144 (packW 24) (decW 6 24) SL) (Native.uTabs.getD 2 #[]))
    11 uS2 0 1771 = true := by
  rw [lookW_eq_P ptSL_eq]
  decide +kernel

set_option maxHeartbeats 0 in
theorem sstep3 : chkT (sextStepF SL (lookW 1771 144 (packW 24) (decW 6 24) SL) (Native.uTabs.getD 3 #[]))
    11 uS3 0 1771 = true := by
  rw [lookW_eq_P ptSL_eq]
  decide +kernel

set_option maxHeartbeats 0 in
theorem xcls_eq : xiCls (lookW 1771 144 (packW 24) (decW 6 24) SL) = xCls := by
  rw [xiCls_eq_Q, lookW_eq_P ptSL_eq]
  decide +kernel

set_option maxHeartbeats 0 in
theorem kcls_eq : kappaCls (lookW 1771 144 (packW 24) (decW 6 24) SL) (lookW 3795 72 Native.key3 dec3 TL)
    (lookW 3795 77 (packW 11) (decW 7 11) TS) (fun q => (maskL (xCls.getD 1 [])).testBit q) = kCls := by
  rw [kappaCls_eq_Q, lookW_eq_P ptSL_eq, lookW_eq_P ptTL_eq, lookW_eq_P ptTS_eq]
  decide +kernel

theorem u0_ok : (Native.uTabs.all fun g => imgSextF g.toList Native.baseSext == Native.baseSext) = true := by
  decide +kernel

@[expose] noncomputable def xSteps : List (Nat → Nat) :=
  [tabF 1771 11 uS0 (sextStepF SL (lookW 1771 144 (packW 24) (decW 6 24) SL) (Native.uTabs.getD 0 #[])),
    tabF 1771 11 uS1 (sextStepF SL (lookW 1771 144 (packW 24) (decW 6 24) SL) (Native.uTabs.getD 1 #[])),
    tabF 1771 11 uS2 (sextStepF SL (lookW 1771 144 (packW 24) (decW 6 24) SL) (Native.uTabs.getD 2 #[])),
    tabF 1771 11 uS3 (sextStepF SL (lookW 1771 144 (packW 24) (decW 6 24) SL) (Native.uTabs.getD 3 #[]))]

@[expose] noncomputable def kSteps : List (Nat → Nat) :=
  [tabF 3795 12 uT0 (trioStepF TL (lookW 3795 72 Native.key3 dec3 TL) (Native.uTabs.getD 0 #[])),
    tabF 3795 12 uT1 (trioStepF TL (lookW 3795 72 Native.key3 dec3 TL) (Native.uTabs.getD 1 #[])),
    tabF 3795 12 uT2 (trioStepF TL (lookW 3795 72 Native.key3 dec3 TL) (Native.uTabs.getD 2 #[])),
    tabF 3795 12 uT3 (trioStepF TL (lookW 3795 72 Native.key3 dec3 TL) (Native.uTabs.getD 3 #[]))]

@[expose] noncomputable def xRun (k : Nat) : List Nat × List Nat × List Nat := xRuns.getD k ([], [], [])

@[expose] noncomputable def kRun (k : Nat) : List Nat × List Nat × List Nat := kRuns.getD k ([], [], [])

@[expose] noncomputable def xChunk (k f a b a' b' : Nat) : Bool :=
  @ReplayQ.chunkB Nat decEqNQ id xSteps (posTreeB id (xRun k).1) (xRun k).1 (xRun k).2.1
    (xRun k).2.2 f a b a' b'

@[expose] noncomputable def kChunk (k f a b a' b' : Nat) : Bool :=
  @ReplayQ.chunkB Nat decEqNQ id kSteps (posTreeB id (kRun k).1) (kRun k).1 (kRun k).2.1
    (kRun k).2.2 f a b a' b'

set_option maxHeartbeats 0 in
theorem xpart_ok : clsPartB Native.nSext xCls [1, 90, 240, 1440] xRuns = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem xcls0_ok : clsOneB Native.nSext xSteps (xCls.getD 0 []) 1 (xRun 0) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem xcls1_ok : clsOneB Native.nSext xSteps (xCls.getD 1 []) 90 (xRun 1) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem xcls2_ok : clsOneB Native.nSext xSteps (xCls.getD 2 []) 240 (xRun 2) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem xcls3_tests : (xCls.getD 3 []).isEmpty = false ∧ ((xCls.getD 3 []).length == 1440) = true ∧
    (xRun 3).1.all (fun x => Nat.blt x Native.nSext) = true ∧
    (xCls.getD 3 []).all (fun q => (maskL (xRun 3).1).testBit q) = true ∧
    (sizeK (posTreeB id (xRun 3).1) == (xRun 3).1.length) = true ∧
    @ReplayQ.headB Nat decEqNQ ((xCls.getD 3 []).headD 0) (xRun 3).1 (xRun 3).2.1 (xRun 3).2.2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem xcls3_pos1 : ReplayQ.posAllN id (posTreeB id (xRun 3).1) 720 ((xRun 3).1.drop 0) 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem xcls3_pos2 : posAllB id (posTreeB id (xRun 3).1) ((xRun 3).1.drop 720) 720 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem xcls3_run1 : xChunk 3 1000 0 1 1000 1429 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem xcls3_run2 : xChunk 3 440 1000 1429 1440 1440 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem xcls3_end : @replayGoB Nat decEqNQ id xSteps (posTreeB id (xRun 3).1) 3560 ((xRun 3).1.drop 1440)
    1440 ((xRun 3).1.drop 1440) ((xRun 3).2.1.drop 1440) ((xRun 3).2.2.drop 1440) 1440 = true := by
  decide +kernel

theorem xcls3_ok : clsOneB Native.nSext xSteps (xCls.getD 3 []) 1440 (xRun 3) = true := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := xcls3_tests
  refine clsOneB_of h1 h2 (@ReplayQ.replayOKB_of _ decEqNQ _ _ _ _ _ _ _ _ h5
    (ReplayQ.posAllB_chunk xcls3_pos1 xcls3_pos2) h6 ?_) h3 h4
  exact (@ReplayQ.replayGoB_chunk _ decEqNQ _ _ _ _ _ _ _ _ _ _ _ xcls3_run1 4000).trans
    ((@ReplayQ.replayGoB_chunk _ decEqNQ _ _ _ _ _ _ _ _ _ _ _ xcls3_run2 3560).trans xcls3_end)

theorem xorb_ok : classOrbitKB Native.nSext xCls [1, 90, 240, 1440] xSteps xRuns = true := by
  refine classOrbitKB_of xpart_ok fun k hk => ?_
  rcases k with _ | _ | _ | _ | k
  · exact xcls0_ok
  · exact xcls1_ok
  · exact xcls2_ok
  · exact xcls3_ok
  · exact absurd hk (by simp)

set_option maxHeartbeats 0 in
theorem kpart_ok : clsPartB Native.nTrio kCls [15, 180, 720, 2880] kRuns = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem kcls0_ok : clsOneB Native.nTrio kSteps (kCls.getD 0 []) 15 (kRun 0) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem kcls1_ok : clsOneB Native.nTrio kSteps (kCls.getD 1 []) 180 (kRun 1) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem kcls2_ok : clsOneB Native.nTrio kSteps (kCls.getD 2 []) 720 (kRun 2) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem kcls3_tests : (kCls.getD 3 []).isEmpty = false ∧ ((kCls.getD 3 []).length == 2880) = true ∧
    (kRun 3).1.all (fun x => Nat.blt x Native.nTrio) = true ∧
    (kCls.getD 3 []).all (fun q => (maskL (kRun 3).1).testBit q) = true ∧
    (sizeK (posTreeB id (kRun 3).1) == (kRun 3).1.length) = true ∧
    @ReplayQ.headB Nat decEqNQ ((kCls.getD 3 []).headD 0) (kRun 3).1 (kRun 3).2.1 (kRun 3).2.2 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem kcls3_pos1 : ReplayQ.posAllN id (posTreeB id (kRun 3).1) 1440 ((kRun 3).1.drop 0) 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem kcls3_pos2 : posAllB id (posTreeB id (kRun 3).1) ((kRun 3).1.drop 1440) 1440 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem kcls3_run1 : kChunk 3 1000 0 1 1000 2345 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem kcls3_run2 : kChunk 3 1000 1000 2345 2000 2850 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem kcls3_run3 : kChunk 3 880 2000 2850 2880 2880 = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem kcls3_end : @replayGoB Nat decEqNQ id kSteps (posTreeB id (kRun 3).1) 2120 ((kRun 3).1.drop 2880)
    2880 ((kRun 3).1.drop 2880) ((kRun 3).2.1.drop 2880) ((kRun 3).2.2.drop 2880) 2880 = true := by
  decide +kernel

theorem kcls3_ok : clsOneB Native.nTrio kSteps (kCls.getD 3 []) 2880 (kRun 3) = true := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := kcls3_tests
  refine clsOneB_of h1 h2 (@ReplayQ.replayOKB_of _ decEqNQ _ _ _ _ _ _ _ _ h5
    (ReplayQ.posAllB_chunk kcls3_pos1 kcls3_pos2) h6 ?_) h3 h4
  exact (@ReplayQ.replayGoB_chunk _ decEqNQ _ _ _ _ _ _ _ _ _ _ _ kcls3_run1 4000).trans
    ((@ReplayQ.replayGoB_chunk _ decEqNQ _ _ _ _ _ _ _ _ _ _ _ kcls3_run2 3000).trans
    ((@ReplayQ.replayGoB_chunk _ decEqNQ _ _ _ _ _ _ _ _ _ _ _ kcls3_run3 2120).trans kcls3_end))

theorem korb_ok : classOrbitKB Native.nTrio kCls [15, 180, 720, 2880] kSteps kRuns = true := by
  refine classOrbitKB_of kpart_ok fun k hk => ?_
  rcases k with _ | _ | _ | _ | k
  · exact kcls0_ok
  · exact kcls1_ok
  · exact kcls2_ok
  · exact kcls3_ok
  · exact absurd hk (by simp)

theorem ok : sextFactsF (lookW 1771 144 (packW 24) (decW 6 24) SL) (lookW 3795 72 Native.key3 dec3 TL)
    (lookW 3795 77 (packW 11) (decW 7 11) TS)
    (fun q => (maskL ((xiCls (lookW 1771 144 (packW 24) (decW 6 24) SL)).getD 1 [])).testBit q)
    (Native.uTabs.all fun g => imgSextF g.toList Native.baseSext == Native.baseSext)
    (fun cls => classOrbitK Native.nSext cls [1, 90, 240, 1440]
      (sextStepsK SL (lookW 1771 144 (packW 24) (decW 6 24) SL) Native.uTabs) xRuns)
    (fun cls => classOrbitK Native.nTrio cls [15, 180, 720, 2880]
      (trioStepsK TL (lookW 3795 72 Native.key3 dec3 TL) Native.uTabs) kRuns) = true := by
  rw [sextFactsF_eq, u0_ok, Bool.true_and, xcls_eq, kcls_eq, sextStepsK_eq_B, trioStepsK_eq_B,
    uTabs_map, uTabs_map, ← tabF_eq sstep0, ← tabF_eq sstep1, ← tabF_eq sstep2, ← tabF_eq sstep3,
    ← tabF_eq tstep0, ← tabF_eq tstep1, ← tabF_eq tstep2, ← tabF_eq tstep3, classOrbitK_eq_B,
    Bool.and_eq_true]
  exact ⟨xorb_ok, korb_ok⟩

end CFSG.KC.M24G.SextFactsC
