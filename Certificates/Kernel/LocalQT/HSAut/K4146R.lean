module

public import Certificates.Kernel.LocalQT.HSAut.D4146
public import Certificates.Kernel.LocalQT.SV.C4126T
public import Certificates.Kernel.SporSch.PairHS.Tab
public import Certificates.Data.Kernel.LocalQT.HSAutR
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutNodesCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutOuter
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdInputs3
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19UHSFusion

public section

set_option maxRecDepth 400000

namespace CFSG.KD.LQT.HN

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.HSAutN
open CFSG.KD.LQT.C4126 CertificateChecks.KernelSporSch CFSG.QuasithinUnique.Id2519.HSAut
open CFSG.QuasithinUnique.Id2519.UHS

@[expose] noncomputable def la (l : Nat) : Nat := lt3 (HS.F 0) (HS.F 1) (HSI 1) l

@[expose] noncomputable def ly (l : Nat) : Nat := nIf(Nat.beq l (nat_lit 0), X 2, X 3)

@[expose] noncomputable def ls8 (l : Nat) : Nat := letterK PHSC.S PHSC.SI 8 l

@[expose] def wRU : List Nat := [9, 5, 15, 3, 0, 4, 5, 4, 5, 7, 4, 6]

@[expose] def wT : List Nat := [14, 12, 15, 13, 14, 12, 1, 12, 9, 11, 7]

theorem canon_ok : allN 5 (fun j => canonK 3850 12 (mask 12) (3850 * 12) (X j)) = true := by
  quickRfl

theorem x0_ok : Nat.beq (X 0) (wfoldR la gLetters) = true := by quickRfl

theorem x1_ok : invEqK 3850 12 (mask 12) (3850 * 12) (X 0) (X 1) = true := by quickRfl

theorem x2_ok : Nat.beq (X 2) (wfoldR la y1Letters) = true := by quickRfl

theorem x3_ok : Nat.beq (X 3) (wfoldR la y2Letters) = true := by quickRfl

theorem x4_ok : Nat.beq (X 4) (wfoldR la cLetters) = true := by quickRfl

theorem conj_ok : Nat.beq (pc (X 0) (HS.F 0)) (pc (wfoldR ly eLetters) (X 0)) = true := by
  quickRfl

theorem a_ok : bAnd(Nat.beq (A.G 0) (HC.F 6), bAnd(Nat.beq (A.G 1) (HC.F 7),
    bAnd(penumHdK idn A.cnt 7680 A.T A.PL, Nat.beq A.cnt 7680))) = true := by
  quickRfl

end CFSG.KD.LQT.HN

end
