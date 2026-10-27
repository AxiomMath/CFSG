module

public import Certificates.Kernel.Sporadic.Fi22.X2069PT
public import Certificates.Kernel.Sporadic.ON.Gen
public import Certificates.Kernel.MonsterB.IndOrbData
public import Certificates.Kernel.MonsterB.IndTransData
public import Certificates.Kernel.MonsterB.IndCentral
public import Certificates.Data.Kernel.Misc.ArrEnum
public import CFSG.Monster.B.Fischer.PinnedBridgeChecksInputs
meta import CFSG.Monster.B.Fischer.InducedData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.Fi22PXT CFSG.Monster.B.Fischer.pinXiHex
#kmisc_hexflat CertificateChecks.KernelSpor.Fi22PXT CFSG.Monster.B.Fischer.pinXiHex 3 3510 12 1

namespace CertificateChecks.KernelSpor.Fi22F1B

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum
open CertificateChecks.KernelSpor CertificateChecks.KernelMonB

@[expose] noncomputable def XP : Nat := Fi22PXT.F 0

@[expose] noncomputable def candP (k : Nat) : Nat :=
  Bool.rec (Bool.rec (ICe.F 0) (ITr.F (Nat.sub k 2)) (Nat.blt k 12)) (IG.F k) (Nat.blt k 2)

@[expose] noncomputable def SIP (j : Nat) : Nat := pinvS 3510 12 (mask 12) (Fi22ChT.F j)

@[expose] noncomputable def wordOK (k : Nat) : Bool :=
  Nat.beq (wordK 3510 12 (mask 12) (pidn 3510 12) Fi22ChT.F SIP
      (CFSG.Monster.B.Fischer.pinWord k))
    (pcomp 3510 12 (mask 12) (pcomp 3510 12 (mask 12) XP (candP k)) (pinvS 3510 12 (mask 12) XP))

theorem permX : permB 3510 12 XP = true := by quickRfl
theorem permC : allN 13 (fun k => permB 3510 12 (candP k)) = true := by quickRfl
theorem permS : allN 19 (fun j => permB 3510 12 (Fi22ChT.F j)) = true := by quickRfl

end CertificateChecks.KernelSpor.Fi22F1B

#kon_slices CertificateChecks.KernelSpor.Fi22F1B.wordOK 0 13

#kon_join CertificateChecks.KernelSpor.Fi22F1B.wordAll CertificateChecks.KernelSpor.Fi22F1B.wordOK 13

end
