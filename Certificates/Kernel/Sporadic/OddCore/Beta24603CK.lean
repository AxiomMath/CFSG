module

public import Certificates.Kernel.Sporadic.OddCore.Beta24603C
public import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.B24603

open CFSG.KC.Enum CFSG.KS.ColH CertificateChecks.KernelSpor

@[expose] noncomputable def netL (l : Nat) : Nat := nIf(Nat.beq l (nat_lit 0), B24603N0, B24603N1)

@[expose] noncomputable def x24603 (i : Nat) : Bool :=
  colSlK (nat_lit 15) (netL (Nat.div i (nat_lit 6))) (nat_lit 13) (nat_lit 8191)
    (J3BetaP (Nat.add (nat_lit 8) (Nat.div i (nat_lit 6)))) B24603Col
    (Nat.mul (nat_lit 1026) (Nat.mod i (nat_lit 6))) (nat_lit 1026)

@[expose] noncomputable def hashRec : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun r acc => Nat.lor acc (Nat.shiftLeft (B24603Hx r) (Nat.mul (nat_lit 17280) r))) (nat_lit 8)

theorem x24603pin0 : pinK 11 B24603N0 (B24603Pi 0) = true := by quickRfl

theorem x24603pin1 : pinK 11 B24603N1 (B24603Pi 1) = true := by quickRfl

end CertificateChecks.KernelSpor.B24603

#kc_each CertificateChecks.KernelSpor.B24603.x24603 0 12

namespace CertificateChecks.KernelSpor.B24603

open CFSG.KC.Enum CFSG.KS.ColH CertificateChecks.KernelSpor

theorem x24603idx :
    allN 1080 (idxK 1080 (B24603Tr 0) (B24603Tr 1) (B24603Tr 2) B24603Pi) = true := by quickRfl

theorem x24603root : rootK B24603Col 6156 = true := by quickRfl

theorem x24603beta : bAnd(laneEqK B24603Col 6156 13 8191 (lane16 (B24603Bk 0) 0) (J3BetaP 7),
    laneEqK B24603Col 6156 13 8191 (lane16 (B24603Bk 0) 1) (B24603I 2)) = true := by quickRfl

theorem x24603hash : Nat.beq (hashColK 135 6156 B24603Col) hashRec = true := by quickRfl

theorem x24603sort :
    allN 1080 (hsortK 135 hashRec 1080 (B24603Hs 0) (B24603Hs 1)) = true := by quickRfl

theorem x24603neg : bIf(colSlK 15 B24603N1 13 8191 (J3BetaP 8) B24603Col 0 4, false, true) = true := by
  quickRfl

theorem x24603negS : bIf(allN 1080 (hsortK 135 hashRec 1080 (B24603Tr 0) (B24603Tr 0)), false,
    true) = true := by
  quickRfl

end CertificateChecks.KernelSpor.B24603

end
