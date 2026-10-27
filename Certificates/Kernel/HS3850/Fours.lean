module

public import Certificates.Kernel.HS3850.Fus
public import Certificates.Kernel.LocalQT.HSAut.K4146R
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.FoursInputs
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.FoursInputs
meta import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
meta import CFSG.Walter.JRFacts

public section

set_option maxRecDepth 400000

#ks_chars CFSG.KD.HS3850.FG CFSG.EvenSporadicStandard.HSStd.foursHex
#kmisc_hexflat CFSG.KD.HS3850.FG CFSG.EvenSporadicStandard.HSStd.foursHex 3 3850 12 2

namespace CFSG.KD.HS3850

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.HSAutN CFSG.KD.LQT.C4126 CFSG.KD.LQT.HN

@[expose] def fw0 : List Nat := [4, 0, 1, 7, 1, 5, 4, 7, 7, 3, 6]

@[expose] def fw1 : List Nat := [7, 0, 5, 7, 1, 0, 7, 7, 7, 5, 6, 4, 6]

@[expose] noncomputable def fourK (L R : Nat) (w : List Nat) : Bool :=
  strictB (pinvS 3850 12 (mask 12) L) (fun LI => strictB (pinvS 3850 12 (mask 12) R) (fun RI =>
    bAnd(Nat.beq L (wfoldR ls8 w), bAnd(canonK 3850 12 (mask 12) (3850 * 12) L,
    bAnd(canonK 3850 12 (mask 12) (3850 * 12) LI, bAnd(invEqK 3850 12 (mask 12) (3850 * 12) L LI,
    bAnd(canonK 3850 12 (mask 12) (3850 * 12) R, bAnd(canonK 3850 12 (mask 12) (3850 * 12) RI,
    bAnd(invEqK 3850 12 (mask 12) (3850 * 12) R RI, ordK (pc (pc (pc L R) LI) RI) 2)))))))))

theorem ok25370 : bAnd(fourK (FG.F 0) (HC.F 21) fw0, fourK (FG.F 1) (HC.F 34) fw1) = true := by
  quickRfl

end CFSG.KD.HS3850

end
