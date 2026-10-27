module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Sporadic.SuzRecog.RootTwistChecks
meta import CFSG.Sporadic.SuzRecog.RootTwistChecks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.SuzRKA CFSG.Sporadic.SuzRecog.RootTwistData.kGenAHex

#kmisc_hexflat CertificateChecks.KernelSpor.SuzRKA CFSG.Sporadic.SuzRecog.RootTwistData.kGenAHex
  3 1782 11 1

#ks_chars CertificateChecks.KernelSpor.SuzRKB CFSG.Sporadic.SuzRecog.RootTwistData.kGenBHex

#kmisc_hexflat CertificateChecks.KernelSpor.SuzRKB CFSG.Sporadic.SuzRecog.RootTwistData.kGenBHex
  3 1782 11 1

namespace CertificateChecks.KernelSpor.SuzRK

open CFSG.Sporadic.SuzRecog.RootTwistCheck CFSG.Monster.B.Co2.Native

meta def gM : Array (Array Nat) := kGens

meta def tM : Array (Array Nat) := kEls

meta def tiM : Array (Array Nat) := kEls.map (invCand 1782)

meta def plM : Array (Array Nat) :=
  (Array.range kEls.size).map fun i => #[2 * kPar[i]! + kLab[i]!]

meta def fpM : Array (Array Nat) := kEls.map fun a => #[CFSG.Sporadic.SuzRecog.LevelTwo.fp a]

meta def posM : Array (Array Nat) :=
  (Array.range (4 * kEls.size)).map fun e =>
    #[kTab.getD (CFSG.Sporadic.SuzRecog.LevelTwo.fp (compA 1782 kGens[e % 4]! kEls[e / 4]!)) 3456]

meta def srtL : Array Nat :=
  (Array.range kEls.size).qsort fun x y =>
    CFSG.Sporadic.SuzRecog.LevelTwo.fp kEls[x]! < CFSG.Sporadic.SuzRecog.LevelTwo.fp kEls[y]!

meta def srtM : Array (Array Nat) := srtL.map fun x => #[x]

meta def sriM : Array (Array Nat) :=
  (Array.range kEls.size).map fun i => #[(srtL.findIdx? (· == i)).getD 0]

end CertificateChecks.KernelSpor.SuzRK

#kmisc_packarrs CertificateChecks.KernelSpor.SuzRKG CertificateChecks.KernelSpor.SuzRK.gM 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzRKT CertificateChecks.KernelSpor.SuzRK.tM 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzRKTI CertificateChecks.KernelSpor.SuzRK.tiM 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzRKPL CertificateChecks.KernelSpor.SuzRK.plM 32
#kmisc_packarrs CertificateChecks.KernelSpor.SuzRKFP CertificateChecks.KernelSpor.SuzRK.fpM 32
#kmisc_packarrs CertificateChecks.KernelSpor.SuzRKPOS CertificateChecks.KernelSpor.SuzRK.posM 32
#kmisc_packarrs CertificateChecks.KernelSpor.SuzRKSRT CertificateChecks.KernelSpor.SuzRK.srtM 32
#kmisc_packarrs CertificateChecks.KernelSpor.SuzRKSRI CertificateChecks.KernelSpor.SuzRK.sriM 32

end
