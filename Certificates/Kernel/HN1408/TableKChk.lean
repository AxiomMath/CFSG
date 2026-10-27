module

public import Certificates.Kernel.HN1408.TableKDefs
public import Certificates.Kernel.HN1408.TableIDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.SylowData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.BindList

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.TK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.Blk CFSG.KD.HN1408
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.HaradaModel

theorem ch26773_hQ : headR (fun j => specK nK (qSpecK.getD j [])) 4 32 TKQ.G TKQ.GI TKQI
    TKQ.T TKQ.PL TKQ.cnt = true := by quickRfl

theorem ch26773_hE : headR (fun j => specK nK (eSpecK.getD j [])) 3 8 TKE.G TKE.GI TKEI
    TKE.T TKE.PL TKE.cnt = true := by quickRfl

theorem ch26773_hZ : headR (fun j => nIf(Nat.beq j 0, specK nK xSpecK, specK nK ySpecK))
    2 8 TKZ.G TKZ.GI TKZI TKZ.T TKZ.PL TKZ.cnt = true := by quickRfl

theorem ch26773_rQ : recK 4 TKQ.cnt TKQ.G TKQ.GI TKQI TKQ.T TKQ.PL TKQ.POS TKQ.SRT TKQ.SRI TKQ.HS
    TKQ.HSI TKQCl = true := by quickRfl

theorem ch26773_rE : recK 3 TKE.cnt TKE.G TKE.GI TKEI TKE.T TKE.PL TKE.POS TKE.SRT TKE.SRI TKE.HS
    TKE.HSI TKECl = true := by quickRfl

theorem ch26773_rZ : recK 2 TKZ.cnt TKZ.G TKZ.GI TKZI TKZ.T TKZ.PL TKZ.POS TKZ.SRT TKZ.SRI TKZ.HS
    TKZ.HSI TKZCl = true := by quickRfl

theorem ch26773_half : bAnd(allN 3 fun l => halvesK (kK l),
    bAnd(allN 3 fun l => halvesK (WK (tGens.getD l [])),
      bAnd(halvesK (uK 0), bAnd(swapsK (uK 1), swapsK (specK uK (nSpec1.getD 3 [])))))) = true := by
  quickRfl

theorem ch26773_blk : bAnd(allN 2 (fun j => blkTrivK 1408 11 4 (TB.F 0) (TKZ.GI j)),
    allN 4 fun j => blkTrivK 1408 11 4 (TB.F 0) (TKQ.GI j)) = true := by
  quickRfl

theorem ch26773_zc : strictB (TKZ.GI 0) (fun X => strictB (TKZ.GI 1) fun Y =>
    strictB (pc X X) fun X2 => strictB (pc X2 X) fun X3 =>
      bAnd(bIf(Nat.beq X2 idK, false, true), bAnd(Nat.beq (pc X2 X2) idK,
      bAnd(bIf(Nat.beq Y idK, false, true), bAnd(Nat.beq (pc Y Y) idK,
      bAnd(bIf(Nat.beq Y X, false, true), bAnd(bIf(Nat.beq Y X2, false, true),
      bAnd(bIf(Nat.beq Y X3, false, true), bAnd(commP X Y,
        allN 4 fun j => bAnd(commP X (TKQ.GI j), commP Y (TKQ.GI j))))))))))) = true := by
  quickRfl

theorem ch26773_c : strictB (TKQ.T (TKC 0)) (fun C =>
    bAnd(Nat.blt (TKC 0) 32, bAnd(Nat.beq C (specK nK cSpecK),
    bAnd(Nat.blt (TKC 1) 8, bAnd(Nat.beq (TKZ.T (TKC 1)) C,
    bAnd(bIf(Nat.beq C idK, false, true), bAnd(Nat.beq (pc C C) idK,
    bAnd(allN 3 (fun j => bAnd(Nat.blt (TKP j) 32, Nat.beq (TKQ.T (TKP j)) (TKE.GI j))),
    bAnd(allN 3 (fun j => allN 3 fun l => commP (TKE.GI j) (TKE.GI l)),
      allN 8 fun i => Nat.beq (pc (TKE.T i) (TKE.T i)) idK))))))))) = true := by
  quickRfl

theorem ch26773_qc : allN 32 (qCentK (TKQ.T (TKC 0))) = true := by quickRfl

theorem ch26773_qm : allN 32 (qCommK (TKQ.T (TKC 0))) = true := by quickRfl

theorem ch26773_qs : allN 32 (qSqK (TKQ.T (TKC 0))) = true := by quickRfl

end CFSG.KD.HN1408.TK

end
