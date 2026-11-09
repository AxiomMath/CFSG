module

public import Certificates.Data.Kernel.M24G.Replay
public import Certificates.Data.Kernel.M24G.Steps
public import Certificates.Kernel.M24G.SextData
public import Certificates.Kernel.M24G.ReplayChunk
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CFSG.KC.M24G

open CFSG.Quasithin.H13.AS91.M24G

noncomputable def sextChunkQ (f a b a' b' : Nat) : Bool :=
  @ReplayQ.chunkB _ ReplayQ.decEqLQ Native.keyL sextStepsF (posTreeB Native.keyL SL) SL sPar sGen
    f a b a' b'

set_option maxHeartbeats 0 in
theorem sextChunk1 : sextChunkQ 600 0 1 600 745 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem sextChunk2 : sextChunkQ 600 600 745 1200 1395 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem sextChunk3 : sextChunkQ 571 1200 1395 1771 1771 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem sextGoEnd : @replayGoB _ ReplayQ.decEqLQ Native.keyL sextStepsF (posTreeB Native.keyL SL)
    1229 (SL.drop 1771) 1771 (SL.drop 1771) (sPar.drop 1771) (sGen.drop 1771) 1771 = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem sextPos1 : ReplayQ.posAllN Native.keyL (posTreeB Native.keyL SL) 900 (SL.drop 0) 0 = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem sextPos2 :
    ReplayQ.posAllN Native.keyL (posTreeB Native.keyL SL) 900 (SL.drop 900) 900 = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem sextPosEnd : posAllB Native.keyL (posTreeB Native.keyL SL) (SL.drop 1800) 1800 = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem sextSize_ok : (sizeK (posTreeB Native.keyL SL) == SL.length) = true := by quickRfl

theorem sextHead_ok : @ReplayQ.headB _ ReplayQ.decEqLQ Native.baseSext SL sPar sGen = true := by
  quickRfl

theorem sextReplay_ok : replayOK Native.keyL sextStepsF Native.baseSext 3000 SL sPar sGen
    (posTree Native.keyL SL) = true := by
  rw [replayOK_eq_B, posTree_eq_B, ReplayQ.replayOKB_inst _ ReplayQ.decEqLQ]
  refine @ReplayQ.replayOKB_of _ ReplayQ.decEqLQ _ _ _ _ _ _ _ _ sextSize_ok ?_ sextHead_ok ?_
  · exact ReplayQ.posAllB_chunk sextPos1 (ReplayQ.posAllB_chunk sextPos2 sextPosEnd)
  · exact (@ReplayQ.replayGoB_chunk _ ReplayQ.decEqLQ _ _ _ _ _ _ _ _ _ _ _ sextChunk1 2400).trans
      ((@ReplayQ.replayGoB_chunk _ ReplayQ.decEqLQ _ _ _ _ _ _ _ _ _ _ _ sextChunk2 1800).trans
      ((@ReplayQ.replayGoB_chunk _ ReplayQ.decEqLQ _ _ _ _ _ _ _ _ _ _ _ sextChunk3 1229).trans
        sextGoEnd))

end CFSG.KC.M24G
