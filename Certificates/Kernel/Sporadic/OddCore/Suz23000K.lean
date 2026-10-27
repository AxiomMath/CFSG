module

public import Certificates.Kernel.Sporadic.OddCore.SuzCTF0
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Certificates.Kernel.Common.Lce
public import Certificates.Data.GSThmBCatalog7SuzCS
public meta import Certificates.Data.GSThmBCatalog7SuzCS
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Suz23000

open CFSG.PSL3Four.Native CFSG.Sporadic.SuzOddCore CFSG.ComponentClassification.CatFactsL4U4.SuzCS

meta def ogM : Array Nat := restrictArr (fixList 0) outerArr

meta def ogiM : Array Nat := invTab 42 ogM

end CertificateChecks.KernelSpor.Suz23000

#ks_perm CertificateChecks.KernelSpor.Suz23000.OG 6 CertificateChecks.KernelSpor.Suz23000.ogM
#ks_perm CertificateChecks.KernelSpor.Suz23000.OGI 6 CertificateChecks.KernelSpor.Suz23000.ogiM

namespace CertificateChecks.KernelSpor.Suz23000

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.BfsPin
open CFSG.KC CFSG.KS.Mathieu CertificateChecks.KernelSpor CertificateChecks.KernelSpor.SuzCT
open CertificateChecks.KernelSpor.OddCore CFSG.ComponentClassification.CatFactsL4U4.SuzCS

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "cn" => canonK 1782 11 (mask 11) (1782 * 11)

@[expose] noncomputable def GH (h : Nat) : Nat := SuzInvT0.F (Nat.add 31 h)

@[expose] noncomputable def BK : Nat := wordTabK 1782 11 (mask 11) (pidn 1782 11) GH betaWord

@[expose] noncomputable def OK7 : Nat := SuzInvT0.F 7

@[expose] noncomputable def PW (w : List Nat) : Nat := wordTabK 42 6 (mask 6) (pidn 42 6) DE.G w

theorem betaK : bAnd(allN 23 (fun h => cn (GH h)), bAnd(cn BK,
    bAnd(allN 42 (fun a => Nat.beq (pg 11 (mask 11) BK (nget fix0L a)) (nget fix0L a)),
    bAnd(notB (Nat.beq BK (pidn 1782 11)), bAnd(notB (Nat.beq BK (SuzTP 0)),
    bAnd(allN 22 (fun k => strictB (pc (GH (k + 1)) BK) (fun L =>
      bIf(Nat.beq L (pc BK (GH (k + 1))), true,
        Nat.beq L (pc (pc (SuzTP 0) BK) (GH (k + 1)))))),
    notB (Nat.beq (pc (GH 5) BK) (pc BK (GH 5))))))))) = true := by
  quickRfl

theorem outerK : bAnd(cn OK7, bAnd(notB (msift OK7), sigK 42 fix0L OK7 OG OGI)) = true := by
  quickRfl

@[expose] noncomputable def notInSl (s : Nat) : Bool :=
  allN 5040 (fun k => notB (Nat.beq (K0E.T (Nat.add (Nat.mul 5040 s) k)) OG))

theorem notIn0 : notInSl 0 = true := by quickRfl
theorem notIn1 : notInSl 1 = true := by quickRfl
theorem notIn2 : notInSl 2 = true := by quickRfl
theorem notIn3 : notInSl 3 = true := by quickRfl
theorem notIn4 : notInSl 4 = true := by quickRfl
theorem notIn5 : notInSl 5 = true := by quickRfl
theorem notIn6 : notInSl 6 = true := by quickRfl
theorem notIn7 : notInSl 7 = true := by quickRfl

theorem pinK : bAnd(Nat.beq pinWords.length 42, allN 42 (fun p =>
    bAnd((pinWords.getD p []).all (fun w => bAnd(w.all (fun j => Nat.blt j 5),
      Nat.beq (pg 6 (mask 6) (PW w) p) p)),
    allN 42 (fun q => bIf(Nat.beq q p, true,
      (pinWords.getD p []).any (fun w => notB (Nat.beq (pg 6 (mask 6) (PW w) q) q))))))) = true := by
  quickRfl

theorem betaNeg : notB (allN 42 (fun a =>
    Nat.beq (pg 11 (mask 11) OK7 (nget fix0L a)) (nget fix0L a))) = true := by
  quickRfl

theorem notInNeg : notB (allN 5040 (fun k => notB (Nat.beq (K0E.T k) (K0E.T 17)))) = true := by
  quickRfl

theorem pinNeg : notB (allN 42 (fun q => bIf(Nat.beq q 1, true,
    (pinWords.getD 0 []).any (fun w => notB (Nat.beq (pg 6 (mask 6) (PW w) q) q))))) = true := by
  quickRfl

end CertificateChecks.KernelSpor.Suz23000

end
