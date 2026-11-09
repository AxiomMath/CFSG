module

public import Certificates.Data.Kernel.M24G.Replay
public import Certificates.Data.Kernel.M24G.FixOct
public import Certificates.Kernel.M24G.FixOctData
import Certificates.Kernel.M24G.ReplayB
public import Certificates.Kernel.M24G.ReplayChunk
public import Certificates.Kernel.M24G.FixOctFast
public import Certificates.Kernel.M24G.FixOctPosData
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CFSG.KC.M24G.FixOctC

open CFSG.KC.M24G CFSG.Quasithin.H13.AS91.M24G
open scoped CFSG.KC.M24G.FixOctEq

noncomputable def fixOctChunkQ (f a b a' b' : Nat) : Bool :=
  @ReplayQ.chunkB _ ReplayQ.decEqQ FixOctQ.tabKeyQ
    [FixOctQ.mulPF FixOctQ.fixOctC1P Native.fixOctComm1,
      FixOctQ.mulPF FixOctQ.fixOctC2P Native.fixOctComm2]
    (ReplayQ.balK 15 10752 FixOctPD.SP).1 FixOctD.FL FixOctD.fPar FixOctD.fGen f a b a' b'

noncomputable def fixOctPosQ (n a : Nat) : Bool :=
  ReplayQ.posAllN FixOctQ.tabKeyQ (ReplayQ.balK 15 10752 FixOctPD.SP).1 n (FixOctD.FL.drop a) a

set_option maxHeartbeats 0 in
theorem fixOctChunk1 : fixOctChunkQ 1344 0 1 1344 2363 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem fixOctChunk2 : fixOctChunkQ 1344 1344 2363 2688 4389 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem fixOctChunk3 : fixOctChunkQ 1344 2688 4389 4032 6141 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem fixOctChunk4 : fixOctChunkQ 1344 4032 6141 5376 7663 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem fixOctChunk5 : fixOctChunkQ 1344 5376 7663 6720 8883 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem fixOctChunk6 : fixOctChunkQ 1344 6720 8883 8064 9838 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem fixOctChunk7 : fixOctChunkQ 1344 8064 9838 9408 10476 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem fixOctChunk8 : fixOctChunkQ 1344 9408 10476 10752 10752 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem fixOctGoEnd : @replayGoB _ ReplayQ.decEqQ FixOctQ.tabKeyQ
    [FixOctQ.mulPF FixOctQ.fixOctC1P Native.fixOctComm1,
      FixOctQ.mulPF FixOctQ.fixOctC2P Native.fixOctComm2]
    (ReplayQ.balK 15 10752 FixOctPD.SP).1 248 (FixOctD.FL.drop 10752) 10752 (FixOctD.FL.drop 10752)
    (FixOctD.fPar.drop 10752) (FixOctD.fGen.drop 10752) 10752 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem fixOctPos1 : fixOctPosQ 2688 0 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem fixOctPos2 : fixOctPosQ 2688 2688 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem fixOctPos3 : fixOctPosQ 2688 5376 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem fixOctPos4 : fixOctPosQ 2688 8064 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem fixOctPosEnd : posAllB FixOctQ.tabKeyQ (ReplayQ.balK 15 10752 FixOctPD.SP).1
    (FixOctD.FL.drop 10752) 10752 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem fixOctSize_ok :
    (sizeK (ReplayQ.balK 15 10752 FixOctPD.SP).1 == FixOctD.FL.length) = true := by quickRfl

theorem fixOctHead_ok :
    @ReplayQ.headB _ ReplayQ.decEqQ Native.fixOctIdTab FixOctD.FL FixOctD.fPar FixOctD.fGen = true := by
  quickRfl

theorem fixOctReplay_ok : replayOK tabKeyF fixOctStepsF Native.fixOctIdTab 11000 FixOctD.FL
    FixOctD.fPar FixOctD.fGen (ReplayQ.balK 15 10752 FixOctPD.SP).1 = true := by
  rw [replayOK_eq_B, ReplayQ.replayOKB_inst _ ReplayQ.decEqQ, FixOctQ.tabKeyF_eq_Q,
    FixOctQ.fixOctStepsF_eq_P]
  refine @ReplayQ.replayOKB_of _ ReplayQ.decEqQ _ _ _ _ _ _ _ _ fixOctSize_ok ?_ fixOctHead_ok ?_
  · exact ReplayQ.posAllB_chunk fixOctPos1 (ReplayQ.posAllB_chunk fixOctPos2
      (ReplayQ.posAllB_chunk fixOctPos3 (ReplayQ.posAllB_chunk fixOctPos4 fixOctPosEnd)))
  · exact (@ReplayQ.replayGoB_chunk _ ReplayQ.decEqQ _ _ _ _ _ _ _ _ _ _ _ fixOctChunk1 9656).trans
      ((@ReplayQ.replayGoB_chunk _ ReplayQ.decEqQ _ _ _ _ _ _ _ _ _ _ _ fixOctChunk2 8312).trans
      ((@ReplayQ.replayGoB_chunk _ ReplayQ.decEqQ _ _ _ _ _ _ _ _ _ _ _ fixOctChunk3 6968).trans
      ((@ReplayQ.replayGoB_chunk _ ReplayQ.decEqQ _ _ _ _ _ _ _ _ _ _ _ fixOctChunk4 5624).trans
      ((@ReplayQ.replayGoB_chunk _ ReplayQ.decEqQ _ _ _ _ _ _ _ _ _ _ _ fixOctChunk5 4280).trans
      ((@ReplayQ.replayGoB_chunk _ ReplayQ.decEqQ _ _ _ _ _ _ _ _ _ _ _ fixOctChunk6 2936).trans
      ((@ReplayQ.replayGoB_chunk _ ReplayQ.decEqQ _ _ _ _ _ _ _ _ _ _ _ fixOctChunk7 1592).trans
      ((@ReplayQ.replayGoB_chunk _ ReplayQ.decEqQ _ _ _ _ _ _ _ _ _ _ _ fixOctChunk8 248).trans fixOctGoEnd)))))))

theorem fixOctLen_ok : 10752 ≤ FixOctD.FL.length := by
  decide +kernel

theorem fixOctComm_ok : fixOctCommF = true := by
  decide +kernel

end CFSG.KC.M24G.FixOctC
