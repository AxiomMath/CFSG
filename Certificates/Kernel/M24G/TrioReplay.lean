module

public import Certificates.Data.Kernel.M24G.Replay
public import Certificates.Data.Kernel.M24G.Steps
public import Certificates.Kernel.M24G.TrioData
public import Certificates.Kernel.M24G.ReplayChunk
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CFSG.KC.M24G

open CFSG.Quasithin.H13.AS91.M24G

noncomputable def trioChunkQ (f a b a' b' : Nat) : Bool :=
  ReplayQ.chunkB Native.key3 trioStepsF (posTreeB Native.key3 TL) TL tPar tGen f a b a' b'

set_option maxHeartbeats 0 in
theorem trioChunk1 : trioChunkQ 1000 0 1 1000 1299 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem trioChunk2 : trioChunkQ 1000 1000 1299 2000 2425 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem trioChunk3 : trioChunkQ 1000 2000 2425 3000 3415 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem trioChunk4 : trioChunkQ 795 3000 3415 3795 3795 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem trioGoEnd : replayGoB Native.key3 trioStepsF (posTreeB Native.key3 TL)
    1205 (TL.drop 3795) 3795 (TL.drop 3795) (tPar.drop 3795) (tGen.drop 3795) 3795 = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem trioPos1 : ReplayQ.posAllN Native.key3 (posTreeB Native.key3 TL) 1000 (TL.drop 0) 0 = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem trioPos2 :
    ReplayQ.posAllN Native.key3 (posTreeB Native.key3 TL) 1000 (TL.drop 1000) 1000 = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem trioPos3 :
    ReplayQ.posAllN Native.key3 (posTreeB Native.key3 TL) 1000 (TL.drop 2000) 2000 = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem trioPosEnd : posAllB Native.key3 (posTreeB Native.key3 TL) (TL.drop 3000) 3000 = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem trioSize_ok : (sizeK (posTreeB Native.key3 TL) == TL.length) = true := by quickRfl

theorem trioHead_ok : ReplayQ.headB Native.baseTrio TL tPar tGen = true := by
  quickRfl

theorem trioReplay_ok : replayOK Native.key3 trioStepsF Native.baseTrio 5000 TL tPar tGen
    (posTree Native.key3 TL) = true := by
  rw [replayOK_eq_B, posTree_eq_B]
  refine ReplayQ.replayOKB_of trioSize_ok ?_ trioHead_ok ?_
  · exact ReplayQ.posAllB_chunk trioPos1 (ReplayQ.posAllB_chunk trioPos2
      (ReplayQ.posAllB_chunk trioPos3 trioPosEnd))
  · exact (ReplayQ.replayGoB_chunk trioChunk1 4000).trans
      ((ReplayQ.replayGoB_chunk trioChunk2 3000).trans
      ((ReplayQ.replayGoB_chunk trioChunk3 2000).trans
      ((ReplayQ.replayGoB_chunk trioChunk4 1205).trans trioGoEnd)))

end CFSG.KC.M24G
