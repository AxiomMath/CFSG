module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Sporadic.SuzRecog.ModelGroupsChecks
meta import CFSG.Sporadic.SuzRecog.ModelGroupsChecks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.SuzMGS1 CFSG.Sporadic.SuzRecog.ModelGroupsData.s1Hex
#kmisc_hexflat CertificateChecks.KernelSpor.SuzMGS1 CFSG.Sporadic.SuzRecog.ModelGroupsData.s1Hex
  3 1782 11 1
#ks_chars CertificateChecks.KernelSpor.SuzMGS2 CFSG.Sporadic.SuzRecog.ModelGroupsData.s2Hex
#kmisc_hexflat CertificateChecks.KernelSpor.SuzMGS2 CFSG.Sporadic.SuzRecog.ModelGroupsData.s2Hex
  3 1782 11 1
#ks_chars CertificateChecks.KernelSpor.SuzMGC1S
  CFSG.Sporadic.SuzRecog.ModelGroupsData.c1StrongHex
#kmisc_hexflat CertificateChecks.KernelSpor.SuzMGC1S
  CFSG.Sporadic.SuzRecog.ModelGroupsData.c1StrongHex 3 1782 11 11

namespace CertificateChecks.KernelSpor.SuzMG

open CFSG.Sporadic.SuzRecog.ModelGroupsCheck CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.SuzRecog.ModelGroupsData CFSG.Sporadic.SuzRecog.LevelTwoData

meta def gM : Array (Array Nat) := #[aA, bA, s1Arr, s2Arr, tauA, rho2A]

meta def aM : Array (Array Nat) := (Array.range 12).map a4A

meta def eM : Array (Array Nat) := (Array.range 8).map e8A

meta def cM : Array (Array Nat) :=
  ((Array.range 12).map fun i => #[conjA (a4A i) rhoArr, conjA (a4A i) rho2A]).flatten

meta def ecM : Array (Array Nat) := (Array.range 8).map fun i => conjA (e8A i) rhoArr

meta def gIM : Array (Array Nat) := gM.map (invCand 1782)
meta def aIM : Array (Array Nat) := aM.map (invCand 1782)
meta def eIM : Array (Array Nat) := eM.map (invCand 1782)

end CertificateChecks.KernelSpor.SuzMG

#kmisc_packarrs CertificateChecks.KernelSpor.SuzMGG CertificateChecks.KernelSpor.SuzMG.gM 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzMGGI CertificateChecks.KernelSpor.SuzMG.gIM 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzMGA CertificateChecks.KernelSpor.SuzMG.aM 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzMGAI CertificateChecks.KernelSpor.SuzMG.aIM 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzMGC CertificateChecks.KernelSpor.SuzMG.cM 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzMGE CertificateChecks.KernelSpor.SuzMG.eM 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzMGEI CertificateChecks.KernelSpor.SuzMG.eIM 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzMGEC CertificateChecks.KernelSpor.SuzMG.ecM 11

end
