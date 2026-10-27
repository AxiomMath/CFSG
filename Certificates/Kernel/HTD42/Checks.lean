module

public import Certificates.Data.Kernel.HTD42Q
public import Certificates.Kernel.D4Plane.Checks
import all CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.D4TwoPlaneData
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.HTD42Q

open CFSG.KC.D4PlaneP CFSG.KC.HTD42Q CFSG.KD.D4Plane CFSG.AGLEmbedding.D4Two

theorem normA :
    eqQ (mulQ (wordQ ls xW) (wordP ls wordA, 0)) (mulQ (atP es 48, 0) (wordQ ls xW)) = true := by
  quickRfl

theorem normB :
    eqQ (mulQ (wordQ ls xW) (wordP ls wordB, 0)) (mulQ (atP es 54, 0) (wordQ ls xW)) = true := by
  quickRfl

theorem cubeX : cubeQ (wordQ ls xW) = true := by quickRfl

theorem frobX : Nat.beq (wordQ ls xW).2 2 = true := by quickRfl

theorem planesOK : planesQ (gensP es) = true := by quickRfl

theorem witA : witAll (wordQ ls xW) (gensP es) (es.take 40) = true := by quickRfl

theorem witB : witAll (wordQ ls xW) (gensP es) (es.drop 40) = true := by quickRfl

end CFSG.KD.HTD42Q

end
