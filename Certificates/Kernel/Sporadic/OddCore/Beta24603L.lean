module

public import Certificates.Kernel.Sporadic.OddCore.Beta24603C
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.B24603

open CFSG.EvenSporadicStandard.Fin76b.Beta CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.PkPow
open CFSG.KS.ColH
open CertificateChecks.KernelSpor.J3BetaA5 (cK pc)
open CertificateChecks.KernelSporSch

@[expose] noncomputable def idK : Nat := pidn 6156 13

@[expose] noncomputable def j3W (wd : List Int) (p : Nat) : Bool :=
  wordEqK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI 5 wd p

@[expose] def bWord : List Int := [3, 4, 5, 3, 2, 2, 3, 4, 3, 1, 3, 1, 4, 5]

@[expose] def tWord : List Int := [1]

@[expose] def dWord : List Int := [3, 5, 3, 2, 1, 3, 5, 5, 3, 3, 1, 4, 5, 5]

theorem base_ok : bAnd(szOK 6156 13, bAnd(cK idK, bAnd(CFSG.KS.Prim.idK 6156 13 (mask 13),
    bAnd(cK (J3BetaP 7), bAnd(cK (B24603I 2),
    bAnd(invEqK 6156 13 (mask 13) (6156 * 13) (J3BetaP 7) (B24603I 2),
    bAnd(Nat.beq (pc (J3BetaP 7) (J3BetaP 7)) (B24603I 2),
    bAnd(allN 2 (fun j => bAnd(cK (J3BetaP (Nat.add j 8)), bAnd(cK (B24603I j),
      bAnd(invEqK 6156 13 (mask 13) (6156 * 13) (J3BetaP (Nat.add j 8)) (B24603I j),
      Nat.beq (pc (J3BetaP 7) (J3BetaP (Nat.add j 8))) (pc (J3BetaP (Nat.add j 8)) (J3BetaP 7)))))),
    bAnd(Nat.beq (ppw 6156 13 (J3BetaP 7) 3) idK,
    bAnd(bIf(Nat.beq (ppw 6156 13 (J3BetaP 7) 1) idK, false, true),
    bAnd(j3W tWord (J3BetaP 8), bAnd(j3W dWord (J3BetaP 9), bAnd(j3W bWord (J3BetaP 7),
      Nat.beq (J3BetaP 8) (J3CentP 9)))))))))))))) = true := by
  quickRfl

@[expose] noncomputable def piP (l : Nat) : Nat := nIf(Nat.beq l (nat_lit 0), nat_lit 173825, nat_lit 152601)

@[expose] noncomputable def inv6 (x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft i (Nat.mul (nat_lit 3) (pg 3 (mask 3) x i)))) (nat_lit 6)

@[expose] noncomputable def kerI (k : Nat) : Bool :=
  bIf(Nat.beq k (nat_lit 0), true, bIf(Nat.beq k (lane16 (B24603Bk 0) 0), true,
    Nat.beq k (lane16 (B24603Bk 0) 1)))

@[expose] noncomputable def cayP (k : Nat) : Bool :=
  (fun x => bAnd(canonK 6 3 (mask 3) (6 * 3) x, bAnd(invEqK 6 3 (mask 3) (6 * 3) x (inv6 x),
    bAnd(bIf(Nat.beq k (nat_lit 0), true, Nat.beq x (pcomp 6 3 (mask 3)
      (B24603L (lane16 (B24603Tr 0) k)) (piP (lane16 (B24603Tr 1) k)))),
    bAnd(allN 2 (fun l => Nat.beq (B24603L (lane16 (B24603Tr 2) (Nat.add (Nat.mul 2 k) l)))
      (pcomp 6 3 (mask 3) x (piP l))),
      bIf(Nat.beq x (nat_lit 181896), kerI k, bIf(kerI k, false, true)))))))
    (B24603L k)

@[expose] noncomputable def cayG : Bool :=
  bAnd(Nat.beq (B24603L 0) (nat_lit 181896), bAnd(Nat.blt (lane16 (B24603Bk 0) 0) 1080,
    bAnd(Nat.blt (lane16 (B24603Bk 0) 1) 1080, allN 2 (fun l => bAnd(canonK 6 3 (mask 3) (6 * 3) (piP l),
      invEqK 6 3 (mask 3) (6 * 3) (piP l) (inv6 (piP l)))))))

theorem cay24603 : bAnd(cayG, allN 1080 cayP) = true := by
  quickRfl

end CertificateChecks.KernelSpor.B24603

end
