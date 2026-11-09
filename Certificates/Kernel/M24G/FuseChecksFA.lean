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


noncomputable def fuseAChunkQ (f a b a' b' : Nat) : Bool :=
  ReplayQ.chunkB (fun c => c) fuseStepsF (balTree FuseS.aS) FuseD.aL FuseD.aPar FuseD.aGen
    f a b a' b'

set_option maxHeartbeats 0 in
theorem fuseAChunk1 : fuseAChunkQ 2000 0 1 2000 2792 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem fuseAChunk2 : fuseAChunkQ 2000 2000 2792 4000 5085 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem fuseAChunk3 : fuseAChunkQ 2000 4000 5085 6000 7335 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem fuseAChunk4 : fuseAChunkQ 2000 6000 7335 8000 9348 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem fuseAChunk5 : fuseAChunkQ 2000 8000 9348 10000 10778 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem fuseAChunk6 : fuseAChunkQ 1385 10000 10778 11385 11385 = true := by quickRfl

set_option maxHeartbeats 0 in
theorem fuseAGoEnd : replayGoB (fun c => c) fuseStepsF (balTree FuseS.aS) 20615
    (FuseD.aL.drop 11385) 11385 (FuseD.aL.drop 11385) (FuseD.aPar.drop 11385)
    (FuseD.aGen.drop 11385) 11385 = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem fuseAPos1 : ReplayQ.posAllN (fun c => c) (balTree FuseS.aS) 4000
    (FuseD.aL.drop 0) 0 = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem fuseAPos2 : ReplayQ.posAllN (fun c => c) (balTree FuseS.aS) 4000
    (FuseD.aL.drop 4000) 4000 = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem fuseAPosEnd :
    posAllB (fun c => c) (balTree FuseS.aS) (FuseD.aL.drop 8000) 8000 = true := by
  quickRfl

set_option maxHeartbeats 0 in
theorem fuseASize_ok : (sizeK (balTree FuseS.aS) == FuseD.aL.length) = true := by quickRfl

theorem fuseAHead_ok : ReplayQ.headB fusePiAP FuseD.aL FuseD.aPar FuseD.aGen = true := by
  quickRfl

theorem fuseOrbA_okF : replayOK (fun c => c) fuseStepsF fusePiAP 32000 FuseD.aL FuseD.aPar
    FuseD.aGen (balTree FuseS.aS) = true := by
  rw [replayOK_eq_B]
  refine ReplayQ.replayOKB_of fuseASize_ok ?_ fuseAHead_ok ?_
  · exact (ReplayQ.posAllB_chunk fuseAPos1
      (ReplayQ.posAllB_chunk fuseAPos2
      fuseAPosEnd))
  · exact ((ReplayQ.replayGoB_chunk fuseAChunk1 30000).trans
      ((ReplayQ.replayGoB_chunk fuseAChunk2 28000).trans
      ((ReplayQ.replayGoB_chunk fuseAChunk3 26000).trans
      ((ReplayQ.replayGoB_chunk fuseAChunk4 24000).trans
      ((ReplayQ.replayGoB_chunk fuseAChunk5 22000).trans
      ((ReplayQ.replayGoB_chunk fuseAChunk6 20615).trans
      fuseAGoEnd))))))

end CFSG.KC.M24G.FuseC
