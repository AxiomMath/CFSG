module

public import Certificates.Kernel.TwoHS.HarSD
public import Certificates.Kernel.TwoHS.Four
public import Certificates.Data.Kernel.Spor.MulHF
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.HSAutN
open CFSG.KD.LQT.C4126 CFSG.KD.LQT.HN

@[expose] noncomputable def sComm (a b : Nat) : Nat := pc (pc a b) (pc (pinv a) (pinv b))

@[expose] noncomputable def sWd (wd : List Nat) : Nat := wfoldK 3850 12 (mask 12) HC.F wd idn

@[expose] noncomputable def sA (j : Nat) : Nat :=
  sWd (CFSG.EvenSporadicStandard.TwoHS.harSPairs.getD j ([], [])).1

@[expose] noncomputable def sB (j : Nat) : Nat :=
  sWd (CFSG.EvenSporadicStandard.TwoHS.harSPairs.getD j ([], [])).2

@[expose] noncomputable def DK (j : Nat) : Nat := sComm (sA j) (sB j)

@[expose] def sdW : List (List Nat) :=
  [[6, 5, 0, 1, 5, 7, 6, 5, 7],
    [5, 0, 6, 7, 7, 0, 3, 7, 2, 3, 5, 6],
    [0, 1, 4, 5, 0, 7, 6, 7, 7, 7, 4, 6],
    [5, 2, 1, 0, 6, 7, 7, 5, 4, 6],
    [4, 6, 3, 7, 3, 0, 3, 7, 5, 4, 2],
    [3, 6, 1, 6, 3, 0, 4, 6, 2, 4, 6, 4, 6],
    [0, 5, 2, 1, 0, 6, 7, 7, 5, 4, 6],
    [5, 3, 5, 7, 3, 0, 7, 6, 7, 5, 3, 2, 6, 4]]

@[expose] noncomputable def invSK (p r : Nat) : Bool :=
  bAnd(canonK 3850 12 (mask 12) (3850 * 12) p, bAnd(canonK 3850 12 (mask 12) (3850 * 12) r,
    invEqK 3850 12 (mask 12) (3850 * 12) p r))

theorem harS_base : bAnd(allN 4 (fun j => invK (HC.F (Nat.succ j))),
  bAnd(allN 4 (fun j => bAnd(Nat.beq (sA j) (wfoldR ls8 (sdW.getD (Nat.mul 2 j) [])),
    bAnd(Nat.beq (sB j) (wfoldR ls8 (sdW.getD (Nat.succ (Nat.mul 2 j)) [])),
    bAnd(invK (sA j), invK (sB j))))),
  bAnd(Nat.beq SD.k 4, bAnd(Nat.beq SD.cnt 64, bAnd(penumHdK idn SD.cnt 200 SD.T SD.PL,
  bAnd(allN 4 (fun j => bAnd(Nat.beq (SD.GI j) (DK j),
    bAnd(Nat.beq (SD.G j) idn, invSK (SD.GI j) (SDI j)))),
  allN 16 (fun c => strictB (r32 SDM c) (fun q => bAnd(Nat.blt q SD.cnt,
    Nat.beq (SD.T q) (sComm (HC.F (Nat.succ (Nat.div c 4))) (HC.F (Nat.succ (Nat.mod c 4))))))))))))) =
    true := by
  quickRfl

@[expose] noncomputable def peD (k : Nat) : Bool :=
  penumSlK 3850 12 (mask 12) (3850 * 12) true SD.G SD.GI 4 SD.cnt SD.T SD.PL SD.POS SD.SRT SD.SRI
    (Nat.mul 16 k) 16

@[expose] noncomputable def hsD (k : Nat) : Bool :=
  slK SD.cnt (hsortPtKF 3850 12 (mask 12) SD.cnt SD.T SD.HS SD.HSI) (Nat.mul 64 k) 64

theorem ch26132hsD_neg : hsortPtKF 3850 12 (mask 12) SD.cnt (fun _ => 0) SD.HS SD.HSI 0 = false := by
  decide +kernel

@[expose] noncomputable def clD (k : Nat) : Bool :=
  slK (Nat.mul SD.cnt 8) (findPtK SD.cnt SD.T (prodQK 3850 12 (mask 12) 8 SD.T (bothK 4 SD.GI SDI))
    SDCl) (Nat.mul 128 k) 128

@[expose] noncomputable def sG (j : Nat) : Nat := HC.F (Nat.succ j)

@[expose] noncomputable def sGI (j : Nat) : Nat := pinv (HC.F (Nat.succ j))

@[expose] noncomputable def nqD (k : Nat) : Bool :=
  slK (Nat.mul SD.cnt 4) (findPtK SD.cnt SD.T (conjQK 3850 12 (mask 12) 4 SD.T sG sGI) SDN)
    (Nat.mul 64 k) 64

end CFSG.KD.TwoHS

end

set_option maxRecDepth 400000
set_option Elab.async false

#kc_each CFSG.KD.TwoHS.peD 0 4
#kc_each CFSG.KD.TwoHS.hsD 0 1
#kc_each CFSG.KD.TwoHS.clD 0 4
#kc_each CFSG.KD.TwoHS.nqD 0 4
