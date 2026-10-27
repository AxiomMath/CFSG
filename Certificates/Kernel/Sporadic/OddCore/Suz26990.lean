module

public import Certificates.Kernel.Sporadic.OddCore.Suz2302
public import Certificates.Kernel.LocalQT.PEnumD
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzPinCheck
public import CFSG.Certificates.Kernel.Common.Loop
meta import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzPinCheck
import CFSG.Certificates.Kernel.Common.Harness

namespace CertificateChecks.KernelSpor.S26990

meta def abM : Array (Array Nat) := CFSG.EvenSporadicStandard.Solomon78.suzArrAB

meta def idM : Array Nat := CFSG.PSL3Four.Native.idTab 1782

end CertificateChecks.KernelSpor.S26990

public section

set_option maxRecDepth 400000

#kpenum_d CertificateChecks.KernelSpor.S26990.PK 1782 11 false
  CertificateChecks.KernelSpor.S26990.abM CertificateChecks.KernelSpor.S26990.abM
  CertificateChecks.KernelSpor.S26990.idM 20160

namespace CertificateChecks.KernelSpor.S26990

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum
open CertificateChecks.KernelSpor.OddCore CFSG.EvenSporadicStandard.Solomon78
open CFSG.EvenSporadicStandard.Induction
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 1782 11 (mask 11) p q

@[expose] noncomputable def pinv (p : Nat) : Nat := pinvS 1782 11 (mask 11) p

@[expose] noncomputable def cn (p : Nat) : Bool := canonK 1782 11 (mask 11) (1782 * 11) p

@[expose] noncomputable def e : Nat := pidn 1782 11

@[expose] noncomputable def ok (p : Nat) : Bool :=
  andB (cn p) (andB (cn (pinv p)) (permOK 1782 11 (mask 11) (1782 * 11) p (pinv p)))

@[expose] noncomputable def W3 (w : List Int) : Nat := wordK 1782 11 (mask 11) e triS triSI w

@[expose] noncomputable def PA : Nat := W3 suzWordA
@[expose] noncomputable def PB : Nat := W3 suzWordB

@[expose] noncomputable def sel2 (a b j : Nat) : Nat := nIf(Nat.beq j 0, a, b)

@[expose] noncomputable def WK (w : List Int) : Nat :=
  wordK 1782 11 (mask 11) e (sel2 PA PB) (sel2 (pinv PA) (pinv PB)) w

@[expose] noncomputable def CA (u v : Nat) : Nat := pc (pc (pc u v) (pinv u)) (pinv v)

theorem kInv : andB (ok PA) (andB (ok PB) (andB (ok (WK suzWordU1)) (andB (ok (WK suzWordV1))
    (andB (ok (WK suzWordU2)) (andB (ok (WK suzWordV2)) (andB (ok (W3 suzWordC))
    (andB (ok (W3 suzWordD)) (andB (cn (WK suzWordE1)) (andB (cn (WK suzWordE2))
    (andB (cn (WK suzWordE3)) (cn (SuzTP 0)))))))))))) = true := by
  quickRfl

theorem kE8 : strictB (WK suzWordE1) fun a => strictB (WK suzWordE2) fun b =>
    strictB (WK suzWordE3) fun c =>
    andB (Nat.beq (pc a a) e) (andB (Nat.beq (pc b b) e) (andB (Nat.beq (pc c c) e)
    (andB (Nat.beq (pc a b) (pc b a)) (andB (Nat.beq (pc a c) (pc c a))
    (andB (Nat.beq (pc b c) (pc c b)) (andB (notB (Nat.beq a e)) (andB (notB (Nat.beq b e))
    (andB (notB (Nat.beq b a)) (andB (notB (Nat.beq c e)) (andB (notB (Nat.beq c a))
    (andB (notB (Nat.beq c b)) (notB (Nat.beq c (pc a b)))))))))))))) = true := by
  quickRfl

theorem kPerf : andB (Nat.beq (CA (WK suzWordU1) (WK suzWordV1)) PA)
    (Nat.beq (CA (WK suzWordU2) (WK suzWordV2)) PB) = true := by
  quickRfl

theorem kComm : andB (Nat.beq (pc (W3 suzWordC) (SuzTP 0)) (pc (SuzTP 0) (W3 suzWordC)))
    (andB (Nat.beq (pc (W3 suzWordD) (SuzTP 0)) (pc (SuzTP 0) (W3 suzWordD)))
      (Nat.beq (CA (W3 suzWordC) (W3 suzWordD)) (SuzTP 0))) = true := by
  quickRfl

theorem kHd : andB (Nat.beq PK.cnt 20160) (andB (Nat.beq PK.k 2)
    (andB (penumHdK e PK.cnt 20160 PK.T PK.PL)
      (andB (Nat.beq (PK.G 0) PA) (Nat.beq (PK.G 1) PB)))) = true := by
  quickRfl

theorem kNeg : notB (Nat.beq (CA (WK suzWordU1) (WK suzWordV1)) PB) = true := by quickRfl

@[expose] noncomputable def kSl (s : Nat) : Bool :=
  penumSlK 1782 11 (mask 11) (1782 * 11) false PK.G PK.GI 2 PK.cnt PK.T PK.PL PK.POS PK.SRT PK.SRI
    (Nat.mul s (nat_lit 32)) (nat_lit 32)

end CertificateChecks.KernelSpor.S26990

end
