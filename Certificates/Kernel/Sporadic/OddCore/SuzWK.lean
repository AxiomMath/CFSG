module

public import Certificates.Kernel.Sporadic.OddCore.SuzW
public import Certificates.Data.Kernel.Spor.FpBfs
public import Certificates.Data.Kernel.B0SuzK
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSpor.SuzWK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.FpBfs CFSG.KC.B0SuzK
open CertificateChecks.KernelSpor CertificateChecks.KernelLC

@[expose] noncomputable def ptK (s : Nat) : Bool :=
  fpBfsPtSlK 1782 11 (mask 11) (1782 * 11) 2 343 SuzXS.F SuzWGI SuzWT SuzWV SuzWPL SuzWFP
    (Nat.mul (nat_lit 32) s) (nat_lit 32)

theorem hd : fpBfsHdK 1782 11 (mask 11) (1782 * 11) 2 2835 343 353 (SuzInvT1.F 0) SuzXS.F SuzWGI
    SuzWT SuzWPL SuzWFP = true := by
  quickRfl

theorem pt0 : ptK 0 = true := by quickRfl
theorem pt1 : ptK 1 = true := by quickRfl
theorem pt2 : ptK 2 = true := by quickRfl
theorem pt3 : ptK 3 = true := by quickRfl
theorem pt4 : ptK 4 = true := by quickRfl
theorem pt5 : ptK 5 = true := by quickRfl
theorem pt6 : ptK 6 = true := by quickRfl
theorem pt7 : ptK 7 = true := by quickRfl
theorem pt8 : ptK 8 = true := by quickRfl
theorem pt9 : ptK 9 = true := by quickRfl
theorem pt10 : ptK 10 = true := by quickRfl

theorem st : fpBfsStSlK 11 (mask 11) 2 343 353 SuzXS.F SuzWGI SuzWT SuzWPL SuzWPOS SuzWFP 0 353 =
    true := by
  quickRfl

theorem fpT : allN 343 (fun i => Nat.beq (SuzWFP i) (fpK 11 (mask 11) (SuzWT i))) = true := by
  quickRfl

@[expose] noncomputable def qPtK (Q : Nat → Nat) (v k : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun j ih x => ih (nIf(bitB v j, pg 11 (mask 11) (Q j) x, x))) k

theorem canQ : allN 6 (fun i => canonK 1782 11 (mask 11) (1782 * 11) (SuzB0Q.F i)) = true := by
  quickRfl

theorem canT : canonK 1782 11 (mask 11) (1782 * 11) (SuzInvT1.F 0) = true := by
  quickRfl

theorem qf : allN 64 (fun v => bAnd(Nat.beq (SuzWQF (Nat.mul 2 v)) (fpOf (qPtK SuzB0Q.F v 6)),
    Nat.beq (SuzWQF (Nat.succ (Nat.mul 2 v)))
      (fpOf (fun x => qPtK SuzB0Q.F v 6 (pg 11 (mask 11) (SuzInvT1.F 0) x))))) = true := by
  quickRfl

theorem p1K : bAnd(allN 342 (fun i => bIf(Nat.beq i 0, true,
    allN 128 (fun j => bIf(Nat.beq (SuzWFP i) (SuzWQF j), false, true)))),
    bAnd(Nat.blt (SuzWJ 0) 128, Nat.beq (SuzWFP 342) (SuzWQF (SuzWJ 0)))) = true := by
  quickRfl

theorem gi0 : invEqK 1782 11 (mask 11) (1782 * 11) (SuzXS.F 0) (SuzWGI 0) = true := by quickRfl
theorem gi1 : invEqK 1782 11 (mask 11) (1782 * 11) (SuzXS.F 1) (SuzWGI 1) = true := by quickRfl
theorem ci0 : invEqK 1782 11 (mask 11) (1782 * 11) (SuzInvT1.F 21) (SuzWCI 0) = true := by quickRfl
theorem ci1 : invEqK 1782 11 (mask 11) (1782 * 11) (SuzInvT1.F 24) (SuzWCI 1) = true := by quickRfl

theorem w0 : compEqK 1782 11 (mask 11) (1782 * 11) (SuzInvT1.F 0) (SuzWT 342) (SuzWC 0) = true := by
  quickRfl
theorem w1 : compEqK 1782 11 (mask 11) (1782 * 11) (SuzWCI 1) (SuzWCI 0) (SuzWC 1) = true := by
  quickRfl
theorem wq : compEqK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) (SuzB0Q.F 0) (SuzB0Q.F 0) =
    true := by
  quickRfl
theorem w2 : compEqK 1782 11 (mask 11) (1782 * 11) (SuzB0Q.F 0) (SuzWC 1) (SuzWC 2) = true := by
  quickRfl
theorem w3 : compEqK 1782 11 (mask 11) (1782 * 11) (SuzInvT1.F 24) (SuzWC 2) (SuzWC 3) = true := by
  quickRfl
theorem w4 : compEqK 1782 11 (mask 11) (1782 * 11) (SuzInvT1.F 21) (SuzWC 3) (SuzWC 4) = true := by
  quickRfl
theorem wE : Nat.beq (SuzWC 0) (SuzWC 4) = true := by quickRfl

theorem negPos : Bool.not (fpBfsStSlK 11 (mask 11) 2 343 353 SuzXS.F SuzWGI SuzWT SuzWPL
    (fun e => nIf(Nat.beq e 3, 342, SuzWPOS e)) SuzWFP 0 353) = true := by
  quickRfl

theorem negSwap : Bool.not (fpBfsPtK 1782 11 (mask 11) (1782 * 11) 2 343 SuzXS.F SuzWGI
    (fun i => nIf(Nat.beq i 5, SuzWT 6, nIf(Nat.beq i 6, SuzWT 5, SuzWT i))) SuzWV SuzWPL SuzWFP 5) =
    true := by
  quickRfl

theorem negDist : Bool.not (fpBfsHdK 1782 11 (mask 11) (1782 * 11) 2 2835 343 353 (SuzInvT1.F 0)
    SuzXS.F SuzWGI SuzWT SuzWPL (fun i => nIf(Nat.beq i 7, SuzWFP 3, SuzWFP i))) = true := by
  quickRfl

theorem negRounds : Bool.not (fpBfsHdK 1782 11 (mask 11) (1782 * 11) 2 176 343 353 (SuzInvT1.F 0)
    SuzXS.F SuzWGI SuzWT SuzWPL SuzWFP) = true := by
  quickRfl

theorem negP1 : Bool.not (allN 343 (fun i => bIf(Nat.beq i 0, true,
    allN 128 (fun j => bIf(Nat.beq (SuzWFP i) (SuzWQF j), false, true))))) = true := by
  quickRfl

end CertificateChecks.KernelSpor.SuzWK

end
