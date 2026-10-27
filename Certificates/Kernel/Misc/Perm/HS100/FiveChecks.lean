module

public import Certificates.Kernel.Misc.Perm.HS100.Base
public import Certificates.Kernel.Misc.Perm.HS100.FiveData
public import Certificates.Data.Kernel.Misc.PermWit
public import Certificates.Data.Kernel.Misc.ChainTail
public import Certificates.Data.Kernel.Misc.ArrEnum
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.HS100.Five

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PermWit CFSG.KC.Misc.ChainTail
open CFSG.KC.Misc.ArrEnum (permB memK)
open CertificateChecks.KernelMisc.HS100
open CFSG.KLie.CT (fget)

@[expose] noncomputable def cuSK : List Nat := (List.range 2880).map CUK

@[expose] noncomputable def cfSK : List Nat := (List.range 300).map CFK

@[expose] noncomputable def aSK : List Nat := (List.range 60).map AAK

@[expose] noncomputable def sSK : List Nat := (List.range 9).map SSK

@[expose] noncomputable def fP (e : Nat) : Nat := ppow 100 7 (mask 7) (pidn 100 7) (FX.F 1) e

theorem fperm : allN 21 (fun k => permB 100 7 (FX.F k)) = true := by quickRfl

theorem hperm : allN 2 (fun k => permB 100 7 (HX.F k)) = true := by quickRfl

theorem fsift : allN 21 (fun k => siftR 100 7 C.LR C.TRI C.BP 5 (FX.F k)) = true := by quickRfl

theorem gU : allN 2 (fun k => Nat.beq (U.G k) (HX.F k)) = true := by quickRfl

theorem gCU : allN 3 (fun k => Nat.beq (CU.G k) (FX.F (Nat.add 2 k))) = true := by quickRfl

theorem gCF : allN 3 (fun k => Nat.beq (CF.G k) (FX.F (Nat.add 5 k))) = true := by quickRfl

theorem gAA : allN 2 (fun k => Nat.beq (AA.G k) (FX.F (Nat.add 8 k))) = true := by quickRfl

theorem gSS : allN 2 (fun k => Nat.beq (SS.G k) (FX.F (Nat.add 10 k))) = true := by quickRfl

theorem nums : (Nat.beq CU.ng 3 && Nat.beq CU.N 2880 && Nat.beq CF.ng 3 && Nat.beq CF.N 300 &&
    Nat.beq AA.ng 2 && Nat.beq AA.N 60 && Nat.beq SS.ng 2 && Nat.beq SS.N 9 && Nat.beq U.ng 2 &&
    Nat.beq U.N 15400 && Nat.beq U.r0 0) = true := by quickRfl

theorem rootU : Nat.beq (U.T U.r0) (FX.F 0) = true := by quickRfl

theorem kCU : keysSK 100 7 CFSG.EvenSporadicStandard.HSStd.Zassenhaus.HSFive.keys CU.N CU.T cuSK =
    true := by quickRfl

theorem kCF : keysSK 100 7 CFSG.EvenSporadicStandard.HSStd.Zassenhaus.HSFive.keys CF.N CF.T cfSK =
    true := by quickRfl

theorem kAA : keysSK 100 7 CFSG.EvenSporadicStandard.HSStd.Zassenhaus.HSFive.keys AA.N AA.T aSK =
    true := by quickRfl

theorem kSS : keysSK 100 7 CFSG.EvenSporadicStandard.HSStd.Zassenhaus.HSFive.keys SS.N SS.T sSK =
    true := by quickRfl

theorem prods : (Nat.beq (pcomp 100 7 (mask 7) (FX.F 0) (FX.F 0)) (pidn 100 7) &&
    !(Nat.beq (FX.F 0) (pidn 100 7)) && Nat.beq (fP 5) (pidn 100 7) &&
    !(Nat.beq (FX.F 1) (pidn 100 7)) &&
    Nat.beq (pcomp 100 7 (mask 7) (FX.F 1) (FX.F 0)) (pcomp 100 7 (mask 7) (FX.F 0) (FX.F 1)) &&
    Nat.beq (ppow 100 7 (mask 7) (pidn 100 7) (FX.F 12) 3) (pidn 100 7) &&
    !(Nat.beq (FX.F 12) (pidn 100 7)) && memK SS.N SS.T (FX.F 12) &&
    memK AA.N AA.T (FX.F 0)) = true := by quickRfl

theorem comms : (allN 3 (fun k => Nat.beq (pcomp 100 7 (mask 7) (FX.F (Nat.add 2 k)) (FX.F 0))
      (pcomp 100 7 (mask 7) (FX.F 0) (FX.F (Nat.add 2 k)))) &&
    allN 3 (fun k => Nat.beq (pcomp 100 7 (mask 7) (FX.F (Nat.add 5 k)) (FX.F 1))
      (pcomp 100 7 (mask 7) (FX.F 1) (FX.F (Nat.add 5 k)))) &&
    allN 2 (fun k => Nat.beq (pcomp 100 7 (mask 7) (FX.F (Nat.add 8 k)) (FX.F 1))
      (pcomp 100 7 (mask 7) (FX.F 1) (FX.F (Nat.add 8 k))))) = true := by quickRfl

theorem hW5 : allN CU.N (ordWitPt 100 7 5 (FX.F 1) CU.N CU.T W5) = true := by quickRfl

theorem hWF : allN CF.N (fun i => strictB (WF i) fun d => Nat.blt (Nat.mod d 8) 5 &&
    Nat.blt (Nat.div d 8) AA.N &&
    Nat.beq (CF.T i) (pcomp 100 7 (mask 7) (fP (Nat.mod d 8)) (AA.T (Nat.div d 8)))) = true := by
  quickRfl

theorem acnt : Nat.beq (cntK AA.N fun i => Nat.beq (pcomp 100 7 (mask 7) (FX.F 0) (AA.T i))
    (pcomp 100 7 (mask 7) (AA.T i) (FX.F 0))) 4 = true := by quickRfl

theorem hWS : allN SS.N (fun i => Nat.beq (SS.T i) (pidn 100 7) || strictB (WS i) fun c =>
    Nat.blt c 8 && Nat.beq (CFSG.KC.ConjOrb.pconj 100 7 (mask 7) (FX.F (Nat.add 13 c))
      (pinvS 100 7 (mask 7) (FX.F (Nat.add 13 c))) (FX.F 12)) (SS.T i)) = true := by quickRfl

theorem ctree : allN AA.N (fun k => Nat.beq (AA.T k) (pidn 100 7) ||
    allN AA.N (ctreePt 100 7 AA.N k AA.T (WT k))) = true := by quickRfl

theorem tperm : (allN CF.N (fun i => permB 100 7 (CF.T i)) &&
    allN AA.N (fun i => permB 100 7 (AA.T i))) = true := by quickRfl

theorem misc : (Nat.beq (AA.T 0) (pidn 100 7) && szOK 100 7 &&
    CFSG.KS.Prim.canonK 100 7 (mask 7) (100 * 7) (pidn 100 7)) = true := by quickRfl

theorem rc : Nat.beq (rcnt (C.LR 0)) 100 = true := by quickRfl

theorem br : allN 100 (ptailBranchK 100 7 C.LR C.TR C.BP (FX.F 1) fP
    CFSG.EvenSporadicStandard.HSStd.Zassenhaus.HSFive.rels CF.N CF.T 5) = true := by quickRfl

end CertificateChecks.KernelMisc.HS100.Five

end
