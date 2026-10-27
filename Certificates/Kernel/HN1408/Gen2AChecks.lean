module

public import Certificates.Kernel.HN1408.Words
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CompatModel.Gen2ACheck
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.MulH CFSG.KS.Prim CFSG.EvenSporadicStandard.HNRecog
open CFSG.EvenSporadicStandard.HNRecog.CompatModel

@[expose] noncomputable def UL (l : Nat) : Nat := WK ((gen2aU ++ gen2aU.map List.reverse).getD (l - 1) [])

theorem k2a : bAnd(involK (WK gen2aC1), bAnd(involK (WK gen2aC2),
    bAnd(commP (WK gen2aC1) (WK wordB), bAnd(commP (WK gen2aC2) (WK wordB),
    bAnd(!Nat.beq (WK gen2aC1) (WK wordA),
    bAnd(!Nat.beq (WK gen2aC1) (WK wordB),
    bAnd(!Nat.beq (WK gen2aC1) (pc (WK wordA) (WK wordB)),
    bAnd(!Nat.beq (WK gen2aC2) (WK wordA),
    bAnd(!Nat.beq (WK gen2aC2) (WK wordB),
    bAnd(!Nat.beq (WK gen2aC2) (pc (WK wordA) (WK wordB)),
    bAnd(commP (WK gen2aG) (WK gen2aC1), bAnd(commP (WK gen2aG) (WK gen2aC2),
      !commP (WK gen2aG) (WK wordB))))))))))))) = true := by
  quickRfl

theorem k2u : allN 4 (fun k => bAnd(bIf(commP (WK (gen2aU.getD k [])) (WK gen2aC1), true,
      commP (WK (gen2aU.getD k [])) (WK gen2aC2)),
    bAnd(invEqK 1408 11 (mask 11) (1408 * 11) (WK (gen2aU.getD k [])) (WK (gen2aU.getD k []).reverse),
      invEqK 1408 11 (mask 11) (1408 * 11) (WK (gen2aU.getD k []).reverse)
        (WK (gen2aU.getD k []))))) = true := by
  quickRfl

theorem k2p : allN 7 (fun j => bAnd(Nat.blt (gen2aProd.getD j (0, [])).1 7,
    Nat.beq (wfoldK 1408 11 (mask 11) UL ((gen2aProd.getD j (0, [])).2) idK)
      (H8.F (gen2aProd.getD j (0, [])).1))) = true := by
  quickRfl

end CFSG.KD.HN1408

end
