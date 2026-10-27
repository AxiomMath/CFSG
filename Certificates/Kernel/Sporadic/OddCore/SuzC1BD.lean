module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import CFSG.Sporadic.SuzRecog.C1ModelTests
import CFSG.Open.LocalVocabulary

namespace CertificateChecks.KernelSpor.SuzC1B

open CFSG.Sporadic.SuzRecog.C1Model CFSG.ComponentClassification.AS81.SuzB0

meta def tM : Array (Array Nat) :=
  #[l4T, gcT, gcI, rhoDecT, bgT, bgI, bwT, bwI, cwT, zT, hT, r1T, r2T]

meta def rM : Array (Array Nat) := #[resTab tTab, resTab zT, resTab tauT]

meta def gM : Array (Array Nat) := CFSG.PSL3Four.Native.gTabs

end CertificateChecks.KernelSpor.SuzC1B

public section

#kmisc_packarrs CertificateChecks.KernelSpor.SuzC1BT CertificateChecks.KernelSpor.SuzC1B.tM 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzC1BR CertificateChecks.KernelSpor.SuzC1B.rM 6
#kmisc_packarrs CertificateChecks.KernelSpor.SuzC1BG CertificateChecks.KernelSpor.SuzC1B.gM 6

end
