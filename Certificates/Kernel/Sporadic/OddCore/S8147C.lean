module

public import Certificates.Kernel.Sporadic.OddCore.S8147D
public import Certificates.Kernel.Sporadic.OddCore.S8147QD
public import Certificates.Kernel.Sporadic.OddCore.Suz2302
public import Certificates.Data.Kernel.Misc.ArrEnum
public import Certificates.Data.Kernel.B3S3K
public import Certificates.Data.Kernel.Spor.HNAOrb
public import Certificates.Data.Kernel.Spor.BaseEq
public import CFSG.Certificates.Kernel.PermToolSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S8147

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.BaseEq
open CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K CFSG.KS.HNA CFSG.KC.PermTool CFSG.KS.Mathieu
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.OddCore CertificateChecks.KernelSpor.Suz2306

@[expose] noncomputable def nB (b : Bool) : Bool := bIf(b, false, true)

@[expose] noncomputable def inTK (G : Nat) : Bool :=
  bIf(msift G, true, msift (pcomp 1782 11 (mask 11) V G))

@[expose] noncomputable def keyCommK (p d : Nat) : Bool :=
  allL [0, 1, 2, 3, 4, 8, 5, 6] fun b =>
    Nat.beq (pg 11 (mask 11) p (pg 11 (mask 11) d b)) (pg 11 (mask 11) d (pg 11 (mask 11) p b))

@[expose] noncomputable def inL (L : List Nat) (y : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => bIf(Nat.beq x y, true, ih)) L

@[expose] noncomputable def cnjK (g d : Nat) : Nat :=
  pcomp 1782 11 (mask 11) g (pcomp 1782 11 (mask 11) d (pinvS 1782 11 (mask 11) g))

@[expose] noncomputable def dChk (G0 G1 : Nat) (nd : Nat) (D : Nat → Nat) (Nd : Nat)
    (TD : Nat → Nat) (N : Nat) (TC : Nat → Nat) (cnt : Nat) : Bool :=
  bAnd(allN nd (fun l => bAnd(memK Nd TD (cnjK G0 (D l)), memK Nd TD (cnjK G1 (D l)))),
  bAnd(memK Nd TD (commP 1782 11 G0 G0), bAnd(memK Nd TD (commP 1782 11 G0 G1),
  bAnd(memK Nd TD (commP 1782 11 G1 G0), bAnd(memK Nd TD (commP 1782 11 G1 G1),
  bAnd(allN nd (fun l => msift (D l)),
  bAnd(nB (Nat.beq (pcomp 1782 11 (mask 11) (D 0) (D 1)) (pcomp 1782 11 (mask 11) (D 1) (D 0))),
    Nat.beq (cntN N fun k => allN nd fun l => keyCommK (TC k) (D l)) cnt)))))))

@[expose] noncomputable def powChk (nd : Nat) (D : Nat → Nat) (N : Nat) (TC : Nat → Nat)
    (X : Nat) : Bool :=
  allN N fun k => bIf(allN nd fun l => keyCommK (TC k) (D l),
    CFSG.KC.LQT.P.anyN 5 (fun e => Nat.beq (TC k) (pw 1782 11 X e)), true)

@[expose] noncomputable def oChk (L : List Nat) (nd : Nat) (D O : Nat → Nat) : Bool :=
  allN nd fun l => bAnd(allL L (fun x => inL L (pg 11 (mask 11) (D l) x)),
    Nat.beq (O l) (restrictK 11 3 L (D l)))

@[expose] noncomputable def preChk (G0 G1 : Nat) : Bool :=
  strictB (pinvS 1782 11 (mask 11) G0) fun I0 => strictB (pinvS 1782 11 (mask 11) G1) fun I1 =>
  strictB (pidn 1782 11) fun Z =>
    bAnd(nB (Nat.beq Z G0), bAnd(nB (Nat.beq Z G1), bAnd(nB (Nat.beq Z I0),
    bAnd(nB (Nat.beq Z I1), bAnd(nB (Nat.beq G0 G1), bAnd(nB (Nat.beq G0 I0),
    bAnd(nB (Nat.beq G0 I1), bAnd(nB (Nat.beq G1 I0), bAnd(nB (Nat.beq G1 I1),
      nB (Nat.beq I0 I1))))))))))

theorem fvP : allN 18 (fun k => permOK 1782 11 (mask 11) (1782 * 11) (SFvT.F k)
    (pinvS 1782 11 (mask 11) (SFvT.F k))) = true := by quickRfl

theorem gQ : allN 2 (fun k => Nat.beq (SFQ.G k) (SFvT.F k)) = true := by quickRfl
theorem gC0 : allN 2 (fun k => Nat.beq (SFC0.G k) (SFvT.F (Nat.add 6 k))) = true := by quickRfl
theorem gC1 : allN 2 (fun k => Nat.beq (SFC1.G k) (SFvT.F (Nat.add 8 k))) = true := by quickRfl
theorem gC2 : allN 2 (fun k => Nat.beq (SFC2.G k) (SFvT.F (Nat.add 10 k))) = true := by quickRfl
theorem gC3 : allN 2 (fun k => Nat.beq (SFC3.G k) (SFvT.F (Nat.add 12 k))) = true := by quickRfl
theorem gC4 : allN 2 (fun k => Nat.beq (SFC4.G k) (SFvT.F (Nat.add 14 k))) = true := by quickRfl
theorem gC5 : allN 2 (fun k => Nat.beq (SFC5.G k) (SFvT.F (Nat.add 16 k))) = true := by quickRfl

theorem qComm : Nat.beq (pcomp 1782 11 (mask 11) (SFvT.F 0) (SFvT.F 1))
    (pcomp 1782 11 (mask 11) (SFvT.F 1) (SFvT.F 0)) = true := by quickRfl

theorem qInM : bAnd(msift (SFvT.F 0), msift (SFvT.F 1)) = true := by quickRfl

theorem qPow : allN 25 (fun k => Nat.beq (pw 1782 11 (SFQ.T k) 5) (pidn 1782 11)) = true := by
  quickRfl

theorem qCover : allN 25 (fun k => strictB (r32 SFQW k) fun c =>
    bAnd(Nat.blt (Nat.div c 8) 6, bAnd(Nat.blt (Nat.mod c 8) 5,
      Nat.beq (SFQ.T k) (pw 1782 11 (SFvT.F (Nat.div c 8)) (Nat.mod c 8))))) = true := by quickRfl

theorem qDist : allN 6 (fun j' => allN 5 (fun e => strictB (pw 1782 11 (SFvT.F j') e) fun P =>
    allN 6 (fun j => bIf(Nat.beq j j', true, nB (Nat.beq (SFvT.F j) P))))) = true := by quickRfl

theorem qLines : allN 6 (fun j => bAnd(Nat.beq (pw 1782 11 (SFvT.F j) 5) (pidn 1782 11),
    bAnd(nB (Nat.beq (SFvT.F j) (pidn 1782 11)), memK 25 SFQ.T (SFvT.F j)))) = true := by
  quickRfl

theorem cGen0 : allN 2 (fun k => bAnd(Nat.beq (pcomp 1782 11 (mask 11) (SFvT.F (Nat.add 6 k))
    (SFvT.F 0)) (pcomp 1782 11 (mask 11) (SFvT.F 0) (SFvT.F (Nat.add 6 k))),
    inTK (SFvT.F (Nat.add 6 k)))) = true := by quickRfl
theorem cGen1 : allN 2 (fun k => bAnd(Nat.beq (pcomp 1782 11 (mask 11) (SFvT.F (Nat.add 8 k))
    (SFvT.F 1)) (pcomp 1782 11 (mask 11) (SFvT.F 1) (SFvT.F (Nat.add 8 k))),
    inTK (SFvT.F (Nat.add 8 k)))) = true := by quickRfl
theorem cGen2 : allN 2 (fun k => bAnd(Nat.beq (pcomp 1782 11 (mask 11) (SFvT.F (Nat.add 10 k))
    (SFvT.F 2)) (pcomp 1782 11 (mask 11) (SFvT.F 2) (SFvT.F (Nat.add 10 k))),
    inTK (SFvT.F (Nat.add 10 k)))) = true := by quickRfl
theorem cGen3 : allN 2 (fun k => bAnd(Nat.beq (pcomp 1782 11 (mask 11) (SFvT.F (Nat.add 12 k))
    (SFvT.F 3)) (pcomp 1782 11 (mask 11) (SFvT.F 3) (SFvT.F (Nat.add 12 k))),
    inTK (SFvT.F (Nat.add 12 k)))) = true := by quickRfl
theorem cGen4 : allN 2 (fun k => bAnd(Nat.beq (pcomp 1782 11 (mask 11) (SFvT.F (Nat.add 14 k))
    (SFvT.F 4)) (pcomp 1782 11 (mask 11) (SFvT.F 4) (SFvT.F (Nat.add 14 k))),
    inTK (SFvT.F (Nat.add 14 k)))) = true := by quickRfl
theorem cGen5 : allN 2 (fun k => bAnd(Nat.beq (pcomp 1782 11 (mask 11) (SFvT.F (Nat.add 16 k))
    (SFvT.F 5)) (pcomp 1782 11 (mask 11) (SFvT.F 5) (SFvT.F (Nat.add 16 k))),
    inTK (SFvT.F (Nat.add 16 k)))) = true := by quickRfl

theorem cX0 : memK 3600 SFC0.T (SFvT.F 0) = true := by quickRfl
theorem cX1 : memK 600 SFC1.T (SFvT.F 1) = true := by quickRfl
theorem cX2 : memK 600 SFC2.T (SFvT.F 2) = true := by quickRfl
theorem cX3 : memK 3600 SFC3.T (SFvT.F 3) = true := by quickRfl
theorem cX4 : memK 3600 SFC4.T (SFvT.F 4) = true := by quickRfl
theorem cX5 : memK 600 SFC5.T (SFvT.F 5) = true := by quickRfl

theorem pre0 : preChk (SFvT.F 6) (SFvT.F 7) = true := by quickRfl
theorem pre1 : preChk (SFvT.F 8) (SFvT.F 9) = true := by quickRfl
theorem pre2 : preChk (SFvT.F 10) (SFvT.F 11) = true := by quickRfl
theorem pre3 : bAnd(preChk (SFvT.F 12) (SFvT.F 13),
    strictB (pcomp 1782 11 (mask 11) (SFvT.F 12) (SFvT.F 12)) fun Q =>
      bAnd(nB (Nat.beq Q (pidn 1782 11)), bAnd(nB (Nat.beq Q (SFvT.F 12)),
      bAnd(nB (Nat.beq Q (SFvT.F 13)), bAnd(nB (Nat.beq Q (pinvS 1782 11 (mask 11) (SFvT.F 12))),
        nB (Nat.beq Q (pinvS 1782 11 (mask 11) (SFvT.F 13)))))))) = true := by quickRfl
theorem pre4 : preChk (SFvT.F 14) (SFvT.F 15) = true := by quickRfl
theorem pre5 : preChk (SFvT.F 16) (SFvT.F 17) = true := by quickRfl

theorem gD0 : bAnd(Nat.beq (SFD0.G 0) (commP 1782 11 (SFvT.F 7) (SFvT.F 6)),
    Nat.beq (SFD0.G 1) (commP 1782 11 (SFvT.F 7) (pinvS 1782 11 (mask 11) (SFvT.F 6)))) = true := by
  quickRfl
theorem gD1 : bAnd(Nat.beq (SFD1.G 0) (commP 1782 11 (SFvT.F 9) (SFvT.F 8)),
    Nat.beq (SFD1.G 1) (commP 1782 11 (SFvT.F 9) (pinvS 1782 11 (mask 11) (SFvT.F 8)))) = true := by
  quickRfl
theorem gD2 : bAnd(Nat.beq (SFD2.G 0) (commP 1782 11 (SFvT.F 11) (SFvT.F 10)),
    Nat.beq (SFD2.G 1) (commP 1782 11 (SFvT.F 11) (pinvS 1782 11 (mask 11) (SFvT.F 10)))) =
    true := by quickRfl
theorem gD3 : bAnd(Nat.beq (SFD3.G 0) (commP 1782 11 (SFvT.F 13) (SFvT.F 12)),
    bAnd(Nat.beq (SFD3.G 1) (commP 1782 11 (SFvT.F 13) (pinvS 1782 11 (mask 11) (SFvT.F 12))),
    bAnd(Nat.beq (SFD3.G 2) (commP 1782 11 (SFvT.F 12) (pinvS 1782 11 (mask 11) (SFvT.F 13))),
      Nat.beq (SFD3.G 3) (commP 1782 11 (SFvT.F 13)
        (pcomp 1782 11 (mask 11) (SFvT.F 12) (SFvT.F 12)))))) = true := by quickRfl
theorem gD4 : bAnd(Nat.beq (SFD4.G 0) (commP 1782 11 (SFvT.F 15) (SFvT.F 14)),
    Nat.beq (SFD4.G 1) (commP 1782 11 (SFvT.F 15) (pinvS 1782 11 (mask 11) (SFvT.F 14)))) =
    true := by quickRfl
theorem gD5 : bAnd(Nat.beq (SFD5.G 0) (commP 1782 11 (SFvT.F 17) (SFvT.F 16)),
    Nat.beq (SFD5.G 1) (commP 1782 11 (SFvT.F 17) (pinvS 1782 11 (mask 11) (SFvT.F 16)))) =
    true := by quickRfl

theorem dFacts0 : dChk (SFvT.F 6) (SFvT.F 7) 2 SFD0.G 360 SFD0.T 3600 SFC0.T 5 = true := by
  quickRfl
theorem dFacts1 : dChk (SFvT.F 8) (SFvT.F 9) 2 SFD1.G 60 SFD1.T 600 SFC1.T 10 = true := by
  quickRfl
theorem dFacts2 : dChk (SFvT.F 10) (SFvT.F 11) 2 SFD2.G 60 SFD2.T 600 SFC2.T 10 = true := by
  quickRfl
theorem dFacts3 : dChk (SFvT.F 12) (SFvT.F 13) 4 SFD3.G 360 SFD3.T 3600 SFC3.T 5 = true := by
  quickRfl
theorem dFacts4 : dChk (SFvT.F 14) (SFvT.F 15) 2 SFD4.G 360 SFD4.T 3600 SFC4.T 5 = true := by
  quickRfl
theorem dFacts5 : dChk (SFvT.F 16) (SFvT.F 17) 2 SFD5.G 60 SFD5.T 600 SFC5.T 10 = true := by
  quickRfl

theorem dPow0 : powChk 2 SFD0.G 3600 SFC0.T (SFvT.F 0) = true := by quickRfl
theorem dPow3 : powChk 4 SFD3.G 3600 SFC3.T (SFvT.F 3) = true := by quickRfl
theorem dPow4 : powChk 2 SFD4.G 3600 SFC4.T (SFvT.F 4) = true := by quickRfl

theorem pairs0 : bAnd(memK 3600 SFC0.T (SFvT.F 6), memK 3600 SFC0.T
    (pinvS 1782 11 (mask 11) (SFvT.F 6))) = true := by quickRfl
theorem pairs1 : bAnd(memK 600 SFC1.T (SFvT.F 8), memK 600 SFC1.T
    (pinvS 1782 11 (mask 11) (SFvT.F 8))) = true := by quickRfl
theorem pairs2 : bAnd(memK 600 SFC2.T (SFvT.F 10), memK 600 SFC2.T
    (pinvS 1782 11 (mask 11) (SFvT.F 10))) = true := by quickRfl
theorem pairs3 : bAnd(memK 3600 SFC3.T (SFvT.F 12), bAnd(memK 3600 SFC3.T
    (pinvS 1782 11 (mask 11) (SFvT.F 12)), bAnd(memK 3600 SFC3.T
    (pinvS 1782 11 (mask 11) (SFvT.F 13)), memK 3600 SFC3.T
    (pcomp 1782 11 (mask 11) (SFvT.F 12) (SFvT.F 12))))) = true := by quickRfl
theorem pairs4 : bAnd(memK 3600 SFC4.T (SFvT.F 14), memK 3600 SFC4.T
    (pinvS 1782 11 (mask 11) (SFvT.F 14))) = true := by quickRfl
theorem pairs5 : bAnd(memK 600 SFC5.T (SFvT.F 16), memK 600 SFC5.T
    (pinvS 1782 11 (mask 11) (SFvT.F 16))) = true := by quickRfl

theorem oFacts0 : oChk [0, 225, 211, 1263, 1557, 973] 2 SFD0.G SFO0.G = true := by quickRfl
theorem oFacts1 : oChk [10, 1781, 445, 248, 1052] 2 SFD1.G SFO1.G = true := by quickRfl
theorem oFacts2 : oChk [4, 730, 1579, 1514, 924] 2 SFD2.G SFO2.G = true := by quickRfl
theorem oFacts3 : oChk [211, 515, 714, 1336, 646, 1708] 4 SFD3.G SFO3.G = true := by quickRfl
theorem oFacts4 : oChk [211, 1678, 1279, 1158, 1211, 497] 2 SFD4.G SFO4.G = true := by quickRfl
theorem oFacts5 : oChk [16, 992, 1162, 240, 845] 2 SFD5.G SFO5.G = true := by quickRfl

end CertificateChecks.KernelSpor.S8147

end
