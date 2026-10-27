module

public import Certificates.Kernel.HS3850.Fours
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.CoverData
meta import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.CoverData
meta import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
meta import CFSG.Walter.JRFacts

public section

set_option maxRecDepth 400000

#ks_chars CFSG.KD.HS3850.CC CFSG.EvenSporadicStandard.TwoHS.coverHex
#kmisc_hexflat CFSG.KD.HS3850.CC CFSG.EvenSporadicStandard.TwoHS.coverHex 3 3850 12 2

namespace CFSG.KD.HS3850

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.HSAutN CFSG.KD.LQT.C4126 CFSG.KD.LQT.HN

@[expose] noncomputable def cvX : Nat :=
  wfoldR ls8 (CFSG.EvenSporadicStandard.TwoHS.coverXWord.map Int.toNat)

@[expose] noncomputable def cvN : Nat :=
  wfoldR ls8 (CFSG.EvenSporadicStandard.TwoHS.coverNWord.map Int.toNat)

@[expose] noncomputable def cvNI : Nat := pinvS 3850 12 (mask 12) cvN

@[expose] noncomputable def cvX2 : Nat := pc (pc cvN cvX) cvNI

@[expose] noncomputable def cvX3 : Nat := pc (pc cvN cvX2) cvNI

@[expose] noncomputable def cvC (p : Nat) : Bool := canonK 3850 12 (mask 12) (3850 * 12) p

theorem ok25552a : bAnd(cvC cvX, bAnd(cvC cvN, bAnd(cvC cvNI,
    bAnd(invEqK 3850 12 (mask 12) (3850 * 12) cvN cvNI,
    bAnd(bIf(Nat.beq cvX idn, false, true), bAnd(Nat.beq (pc cvX cvX) idn,
    bAnd(Nat.beq (pc cvX cvX2) (pc cvX2 cvX), bAnd(Nat.beq (pc cvX cvX3) (pc cvX3 cvX),
      Nat.beq (pc (pc cvN cvX3) cvNI) (pc cvX cvX2))))))))) = true := by
  quickRfl

@[expose] def cvW (k : Nat) : List Nat :=
  if k = 0 then [2, 1, 0, 9, 0, 15, 4, 5, 4, 2, 4, 6, 4] else [1, 1, 2, 0, 7, 7, 7, 4, 5, 6, 4]

@[expose] noncomputable def cvK (C L R : Nat) (w : List Nat) : Bool :=
  strictB (pinvS 3850 12 (mask 12) C) (fun CI =>
    bAnd(Nat.beq C (wfoldR ls8 w), bAnd(cvC C, bAnd(cvC CI,
    bAnd(invEqK 3850 12 (mask 12) (3850 * 12) C CI,
      Nat.beq (pc (pc (pc L R) (pinvS 3850 12 (mask 12) L)) (pinvS 3850 12 (mask 12) R))
        (pc (pc C cvX) CI))))))

theorem ok25552b : bAnd(cvK (CC.F 0) (FG.F 0) (HC.F 21) (cvW 0),
    cvK (CC.F 1) (FG.F 1) (HC.F 34) (cvW 1)) = true := by
  quickRfl

theorem neg25552 : bAnd(bIf(Nat.beq (pc cvX cvN) (pc cvN cvX), false, true),
    bIf(cvK (CC.F 0) (FG.F 1) (HC.F 34) (cvW 0), false, true)) = true := by
  quickRfl

end CFSG.KD.HS3850

end
