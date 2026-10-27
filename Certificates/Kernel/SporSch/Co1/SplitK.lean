module

public import Certificates.Kernel.SporSch.Co1.ElemDag
public import CFSG.Certificates.Kernel.SporSch.Co1SplitSound
public import CFSG.Sporadic.Schreier.Co1SplitCheckInputs
public meta import Certificates.Kernel.SporSch.Co1.GenDag
public meta import Certificates.Kernel.SporSch.GenPerms
public meta import CFSG.Sporadic.Schreier.Co1SplitCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.GenPerms

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co1Split

open CFSG.Sporadic.Co1Schreier.Native

meta def ABA : Array (Array Nat) := #[aR, bR]

meta def ABIA : Array (Array Nat) := #[inv aR, inv bR]

meta def GA : Array (Array Nat) := #[gRows 0, gRows 1, gRows 2]

meta def GIA : Array (Array Nat) := #[inv (gRows 0), inv (gRows 1), inv (gRows 2)]

meta def XIA : Array (Array Nat) := ((List.range 6).map (fun i => inv (aRows i)) ++
  (List.range 3).map (fun i => inv (gRows i))).toArray

meta def ZQA : Array (Array Nat) := zqT.map fun v => #[v]

end CertificateChecks.KernelSporSch.Co1Split

#kss_perms CertificateChecks.KernelSporSch.Co1Split.AB 24 CertificateChecks.KernelSporSch.Co1Split.ABA
#kss_perms CertificateChecks.KernelSporSch.Co1Split.ABI 24 CertificateChecks.KernelSporSch.Co1Split.ABIA
#kss_perms CertificateChecks.KernelSporSch.Co1Split.GG 24 CertificateChecks.KernelSporSch.Co1Split.GA
#kss_perms CertificateChecks.KernelSporSch.Co1Split.GGI 24 CertificateChecks.KernelSporSch.Co1Split.GIA
#kss_perms CertificateChecks.KernelSporSch.Co1Split.XI 24 CertificateChecks.KernelSporSch.Co1Split.XIA
#kss_perms CertificateChecks.KernelSporSch.Co1Split.ZQ 24 CertificateChecks.KernelSporSch.Co1Split.ZQA
#kss_co1dag CertificateChecks.KernelSporSch.Co1Split.SG CFSG.Sporadic.Co1Schreier.Native.strongDag

namespace CertificateChecks.KernelSporSch.Co1Split

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch.M24 CFSG.KS.SporSch.Orb CFSG.KS.Mathieu
open CFSG.Sporadic.Co1Schreier CertificateChecks.KernelSporSch.Co1Packed
open CertificateChecks.KernelSporSch.Co1Elem

@[expose] noncomputable def GV (i : Nat) : Nat :=
  gValK AB ABI SG.M SG.MI (Data.topWords.getD i []) (Data.lowerWords.getD i [])

@[expose] noncomputable def GF (i : Nat) : Nat := nIf(Nat.blt i 3, GG i, GV i)

theorem kAB0 : Nat.beq (AB 0) PA = true := by quickRfl
theorem kAB1 : Nat.beq (AB 1) PB = true := by quickRfl
theorem kab : bAnd(invOKK PA (ABI 0), invOKK PB (ABI 1)) = true := by quickRfl
theorem kNb : Nat.beq Data.ambWords.length 2 = true := by quickRfl
theorem kAmb : allN 2 (fun i => bAnd(CFSG.KS.SporSch.M24.lettersK 2 (ngetL Data.ambWords i),
    Nat.beq (wordSK AB ABI (ngetL Data.ambWords i)) (SG.M i))) = true := by quickRfl
theorem kSD : dagK SG.M SG.MI 2 SG.N Data.strongWords = true := by quickRfl
theorem kG : allN 3 (fun i => bAnd(gLettersK SG.N (Data.topWords.getD i [])
    (Data.lowerWords.getD i []), Nat.beq (GV i) (GG i))) = true := by quickRfl
theorem kLR0 : bindListK 24 24 (GF 0) (Data.liftRows.getD 0 []) = true := by quickRfl
theorem kLR1 : bindListK 24 24 (GF 1) (Data.liftRows.getD 1 []) = true := by quickRfl
theorem kLR2 : bindListK 24 24 (GF 2) (Data.liftRows.getD 2 []) = true := by quickRfl
theorem kZ : zqOK (E.M 2) Data.f4vecs ZQ = true := by quickRfl
theorem kGens : gensK ZQ AF GF XI = true := by quickRfl
theorem kData : dataK ZQ AF GF Data.liftPerms Data.liftSigns = true := by quickRfl
theorem kConj : conjK AF GF GGI Data.conjExps Data.corrExps = true := by quickRfl
theorem kZD : zqDistK ZQ = true := by quickRfl

end CertificateChecks.KernelSporSch.Co1Split

end
