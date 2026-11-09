module

public import Certificates.Data.Kernel.M24G.FusePack
public import Certificates.Data.Kernel.M24G.FuseFast
public import Certificates.Data.Kernel.M24G.Replay
public import Certificates.Kernel.M24G.FuseData
public import Certificates.Kernel.M24G.FusePosData
public import Certificates.Kernel.M24G.ReplayChunk
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CFSG.KC.M24G.FuseC

open CFSG.KC.M24G


noncomputable def fuseBChunkQ (f a b a' b' : Nat) : Bool :=
  ReplayQ.chunkB (fun c => c) fuseStepsF (balTree FuseS.bS) FuseD.bL FuseD.bPar FuseD.bGen
    f a b a' b'

set_option maxHeartbeats 0 in
theorem fuseBChunk1 : fuseBChunkQ 2000 0 1 2000 2939 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem fuseBChunk2 : fuseBChunkQ 2000 2000 2939 4000 5598 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem fuseBChunk3 : fuseBChunkQ 2000 4000 5598 6000 7980 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem fuseBChunk4 : fuseBChunkQ 2000 6000 7980 8000 10525 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem fuseBChunk5 : fuseBChunkQ 2000 8000 10525 10000 12655 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem fuseBChunk6 : fuseBChunkQ 2000 10000 12655 12000 15803 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem fuseBChunk7 : fuseBChunkQ 2000 12000 15803 14000 17406 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem fuseBChunk8 : fuseBChunkQ 2000 14000 17406 16000 19235 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem fuseBChunk9 : fuseBChunkQ 2000 16000 19235 18000 22050 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem fuseBChunk10 : fuseBChunkQ 2000 18000 22050 20000 23804 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem fuseBChunk11 : fuseBChunkQ 2000 20000 23804 22000 25102 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem fuseBChunk12 : fuseBChunkQ 2000 22000 25102 24000 26974 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem fuseBChunk13 : fuseBChunkQ 2000 24000 26974 26000 28955 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem fuseBChunk14 : fuseBChunkQ 2000 26000 28955 28000 29873 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem fuseBChunk15 : fuseBChunkQ 2000 28000 29873 30000 31216 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem fuseBChunk16 : fuseBChunkQ 1878 30000 31216 31878 31878 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem fuseBGoEnd : replayGoB (fun c => c) fuseStepsF (balTree FuseS.bS) 122
    (FuseD.bL.drop 31878) 31878 (FuseD.bL.drop 31878) (FuseD.bPar.drop 31878)
    (FuseD.bGen.drop 31878) 31878 = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem fuseBPos1 : ReplayQ.posAllN (fun c => c) (balTree FuseS.bS) 4000
    (FuseD.bL.drop 0) 0 = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem fuseBPos2 : ReplayQ.posAllN (fun c => c) (balTree FuseS.bS) 4000
    (FuseD.bL.drop 4000) 4000 = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem fuseBPos3 : ReplayQ.posAllN (fun c => c) (balTree FuseS.bS) 4000
    (FuseD.bL.drop 8000) 8000 = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem fuseBPos4 : ReplayQ.posAllN (fun c => c) (balTree FuseS.bS) 4000
    (FuseD.bL.drop 12000) 12000 = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem fuseBPos5 : ReplayQ.posAllN (fun c => c) (balTree FuseS.bS) 4000
    (FuseD.bL.drop 16000) 16000 = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem fuseBPos6 : ReplayQ.posAllN (fun c => c) (balTree FuseS.bS) 4000
    (FuseD.bL.drop 20000) 20000 = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem fuseBPos7 : ReplayQ.posAllN (fun c => c) (balTree FuseS.bS) 4000
    (FuseD.bL.drop 24000) 24000 = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem fuseBPosEnd :
    posAllB (fun c => c) (balTree FuseS.bS) (FuseD.bL.drop 28000) 28000 = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem fuseBSize_ok : (sizeK (balTree FuseS.bS) == FuseD.bL.length) = true := by quickRfl

theorem fuseBHead_ok : ReplayQ.headB fusePiBP FuseD.bL FuseD.bPar FuseD.bGen = true := by
  quickRfl

theorem fuseOrbB_okF : replayOK (fun c => c) fuseStepsF fusePiBP 32000 FuseD.bL FuseD.bPar
    FuseD.bGen (balTree FuseS.bS) = true := by
  rw [replayOK_eq_B]
  refine ReplayQ.replayOKB_of fuseBSize_ok ?_ fuseBHead_ok ?_
  · exact (ReplayQ.posAllB_chunk fuseBPos1
      (ReplayQ.posAllB_chunk fuseBPos2
      (ReplayQ.posAllB_chunk fuseBPos3
      (ReplayQ.posAllB_chunk fuseBPos4
      (ReplayQ.posAllB_chunk fuseBPos5
      (ReplayQ.posAllB_chunk fuseBPos6
      (ReplayQ.posAllB_chunk fuseBPos7
      fuseBPosEnd)))))))
  · exact ((ReplayQ.replayGoB_chunk fuseBChunk1 30000).trans
      ((ReplayQ.replayGoB_chunk fuseBChunk2 28000).trans
      ((ReplayQ.replayGoB_chunk fuseBChunk3 26000).trans
      ((ReplayQ.replayGoB_chunk fuseBChunk4 24000).trans
      ((ReplayQ.replayGoB_chunk fuseBChunk5 22000).trans
      ((ReplayQ.replayGoB_chunk fuseBChunk6 20000).trans
      ((ReplayQ.replayGoB_chunk fuseBChunk7 18000).trans
      ((ReplayQ.replayGoB_chunk fuseBChunk8 16000).trans
      ((ReplayQ.replayGoB_chunk fuseBChunk9 14000).trans
      ((ReplayQ.replayGoB_chunk fuseBChunk10 12000).trans
      ((ReplayQ.replayGoB_chunk fuseBChunk11 10000).trans
      ((ReplayQ.replayGoB_chunk fuseBChunk12 8000).trans
      ((ReplayQ.replayGoB_chunk fuseBChunk13 6000).trans
      ((ReplayQ.replayGoB_chunk fuseBChunk14 4000).trans
      ((ReplayQ.replayGoB_chunk fuseBChunk15 2000).trans
      ((ReplayQ.replayGoB_chunk fuseBChunk16 122).trans
      fuseBGoEnd))))))))))))))))

end CFSG.KC.M24G.FuseC
