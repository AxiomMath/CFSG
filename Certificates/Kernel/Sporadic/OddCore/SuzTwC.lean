module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Sporadic.SuzRecog.B0TwistChecks
meta import CFSG.Sporadic.SuzRecog.B0TwistChecks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.SuzTwH1 CFSG.Sporadic.SuzRecog.B0TwistData.h1Hex
#kmisc_hexflat CertificateChecks.KernelSpor.SuzTwH1 CFSG.Sporadic.SuzRecog.B0TwistData.h1Hex
  3 1782 11 1
#ks_chars CertificateChecks.KernelSpor.SuzTwH2 CFSG.Sporadic.SuzRecog.B0TwistData.h2Hex
#kmisc_hexflat CertificateChecks.KernelSpor.SuzTwH2 CFSG.Sporadic.SuzRecog.B0TwistData.h2Hex
  3 1782 11 1
#ks_chars CertificateChecks.KernelSpor.SuzTwA CFSG.Sporadic.SuzRecog.B0TwistData.aHex
#kmisc_hexflat CertificateChecks.KernelSpor.SuzTwA CFSG.Sporadic.SuzRecog.B0TwistData.aHex
  3 1782 11 1
#ks_chars CertificateChecks.KernelSpor.SuzTwB CFSG.Sporadic.SuzRecog.B0TwistData.bHex
#kmisc_hexflat CertificateChecks.KernelSpor.SuzTwB CFSG.Sporadic.SuzRecog.B0TwistData.bHex
  3 1782 11 1
#ks_chars CertificateChecks.KernelSpor.SuzTwTau CFSG.Sporadic.SuzRecog.B0TwistData.tauHex
#kmisc_hexflat CertificateChecks.KernelSpor.SuzTwTau CFSG.Sporadic.SuzRecog.B0TwistData.tauHex
  3 1782 11 1
#ks_chars CertificateChecks.KernelSpor.SuzTwRho CFSG.Sporadic.SuzRecog.LevelTwoData.rhoHex
#kmisc_hexflat CertificateChecks.KernelSpor.SuzTwRho CFSG.Sporadic.SuzRecog.LevelTwoData.rhoHex
  3 1782 11 1
#ks_chars CertificateChecks.KernelSpor.SuzTwW0 CFSG.Sporadic.SuzRecog.LevelTwoData.w0Hex
#kmisc_hexflat CertificateChecks.KernelSpor.SuzTwW0 CFSG.Sporadic.SuzRecog.LevelTwoData.w0Hex
  3 1782 11 1

namespace CertificateChecks.KernelSpor.SuzTwC

open CFSG.Sporadic.SuzRecog.B0TwistCheck CFSG.Monster.B.Co2.Native

meta def gM : Array (Array Nat) := twGens.push twGensT[5]!

meta def giM : Array (Array Nat) := gM.map (invCand 1782)

end CertificateChecks.KernelSpor.SuzTwC

#kmisc_packarrs CertificateChecks.KernelSpor.SuzTwG CertificateChecks.KernelSpor.SuzTwC.gM 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzTwGI CertificateChecks.KernelSpor.SuzTwC.giM 11

end
