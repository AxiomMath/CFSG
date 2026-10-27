module

public import Certificates.Kernel.HS3850.Fus
public import Certificates.Kernel.LocalQT.HSAut.K4146R
public import Certificates.Kernel.LocalQT.Tc.Gen
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.FactsData
meta import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.FactsData
meta import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CFSG.KD.HS3850.FT CFSG.EvenSporadicStandard.HSStd.factsHex
#kmisc_hexflat CFSG.KD.HS3850.FT CFSG.EvenSporadicStandard.HSStd.factsHex 3 3850 12 2

namespace CFSG.KD.HS3850.D25371

meta def t0M : Array (Array Nat) := CFSG.EvenSporadicStandard.HSStd.hsT0Gens

meta def idM : Array Nat := CFSG.PSL3Four.Native.idTab 3850

end CFSG.KD.HS3850.D25371

#kpenum_d CFSG.KD.HS3850.ET0 3850 12 false CFSG.KD.HS3850.D25371.t0M CFSG.KD.HS3850.D25371.t0M
  CFSG.KD.HS3850.D25371.idM 512

namespace CFSG.KD.HS3850

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.HSAutN CFSG.KD.LQT.C4126 CFSG.KD.LQT.HN

@[expose] noncomputable def lc1 (j : Nat) : Nat := HC.F (Nat.add (nat_lit 6) j)

@[expose] noncomputable def cmK (a b : Nat) : Bool := Nat.beq (pc a b) (pc b a)

@[expose] noncomputable def sqK (a : Nat) : Bool := Nat.beq (pc a a) idn

@[expose] noncomputable def sqAt (w g0 g1 x : Nat) : Bool :=
  strictB (pc w x) (fun wx =>
    bAnd(bIf(bAnd(cmK x g0, cmK x g1), sqK x, true), bIf(bAnd(cmK wx g0, cmK wx g1), sqK wx, true)))

@[expose] def wZU : List Nat := [7, 5, 0, 1, 7, 6, 4, 7, 4, 5, 4, 6, 4, 6]

@[expose] def wH : List Nat := [6, 0, 1, 4, 0, 1, 4, 6, 5, 4, 2, 6, 4, 6, 4]

@[expose] def t1Pos : Nat := 4

@[expose] def t0Idx : List Nat := [0, 30]

@[expose] noncomputable def oddAK : Nat := wfoldR lc2 [2, 2]

@[expose] noncomputable def oddBK : Nat := wfoldR lc2 [1, 0]

@[expose] noncomputable def hInvK : Nat := pinvS 3850 12 (mask 12) (FT.F 1)

@[expose] noncomputable def oc0K : Nat := pc (pc hInvK oddAK) (FT.F 1)

@[expose] noncomputable def oc1K : Nat := pc (pc hInvK oddBK) (FT.F 1)

@[expose] noncomputable def ptF (i : Nat) : Bool :=
  strictB (A.T i) (fun x =>
    bAnd(sqAt (FT.F 0) (lc1 0) (lc1 1) x, bAnd(sqAt (FT.F 0) oc0K oc1K x,
      Bool.beq (bAnd(cmK x (ET0.G 0), bAnd(cmK x (ET0.G 1), cmK x (ET0.G 2)))) (t0Idx.elem i))))

@[expose] noncomputable def ckF (s : Nat) : Bool :=
  allN 32 (fun d => strictB (Nat.add (Nat.mul s (nat_lit 32)) d) (fun i =>
    bIf(Nat.blt i (nat_lit 7680), ptF i, true)))

@[expose] noncomputable def ckT0 (s : Nat) : Bool :=
  penumSlK 3850 12 (mask 12) (3850 * 12) false ET0.G ET0.GI 3 ET0.cnt ET0.T ET0.PL ET0.POS ET0.SRT
    ET0.SRI (Nat.mul s (nat_lit 32)) (nat_lit 32)

@[expose] noncomputable def commRelK (Q : Nat → Nat) (q : Nat) (X Y : List Nat) : Bool :=
  Nat.beq (pc (pc q (wfoldR Q Y)) (wfoldR Q X)) (pc (wfoldR Q X) (wfoldR Q Y))

@[expose] noncomputable def qPerf (i : Nat) : Nat :=
  nIf(Nat.beq i (nat_lit 0), wfoldR lc1 [0, 1, 0, 0, 0, 0, 0, 0, 1],
    wfoldR lc1 [0, 1, 1, 1, 0, 0, 1, 0, 0, 0])

theorem ok25371 : strictB (pinvS 3850 12 (mask 12) (FT.F 0)) (fun ZI =>
    bAnd(canonK 3850 12 (mask 12) (3850 * 12) (FT.F 0),
    bAnd(canonK 3850 12 (mask 12) (3850 * 12) ZI,
    bAnd(invEqK 3850 12 (mask 12) (3850 * 12) (FT.F 0) ZI,
    bAnd(allN 4 (fun b => Nat.beq (img (FT.F 0) b) b), bAnd((Nat.beq (img (FT.F 0) 5) 5).not,
    bAnd(Nat.beq (pc (FT.F 0) (HC.F 0)) (wfoldR ls8 wZU),
    bAnd(cmK (FT.F 0) (HC.F 5),
    bAnd(canonK 3850 12 (mask 12) (3850 * 12) (FT.F 1),
    bAnd(canonK 3850 12 (mask 12) (3850 * 12) hInvK,
    bAnd(Nat.beq (pc (FT.F 1) hInvK) idn,
    bAnd(Nat.beq (FT.F 1) (wfoldR ls8 wH),
    bAnd(Nat.beq (pc oddAK (pc oddAK (pc oddAK (pc oddAK (pc oddAK idn))))) idn,
    bAnd(Nat.beq (pc oddBK (pc oddBK (pc oddBK idn))) idn,
    bAnd(Nat.beq (pc (pc hInvK (pc oddBK (pc oddAK (pc oddBK (pc oddAK idn))))) (FT.F 1)) (HC.F 5),
    bAnd(Nat.beq ET0.cnt 512, bAnd(penumHdK idn ET0.cnt 512 ET0.T ET0.PL,
    bAnd(Nat.beq (ET0.G 0) (wfoldR lc1 [0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0]),
    bAnd(Nat.beq (ET0.G 1) (wfoldR lc1 [1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0]),
    bAnd(Nat.beq (ET0.G 2) (wfoldR lc1 [0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0]),
    bAnd(Nat.beq (ET0.T t1Pos) (HC.F 5),
    bAnd(commRelK qPerf (qPerf 0) [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1]
      [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0],
    bAnd(commRelK qPerf (qPerf 1) [0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0]
      [0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1],
    bAnd(Nat.beq (wfoldR qPerf [0, 0, 0, 0, 0, 0]) (HC.F 5),
      Nat.beq (foldN 7680 (fun x c => nIf(t0Idx.elem x, Nat.succ c, c)) 0) 2)))))))))))))))))))))))) =
      true := by
  quickRfl

end CFSG.KD.HS3850

end
