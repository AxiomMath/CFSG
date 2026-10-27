module

public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import CFSG.Sporadic.SuzRecog.SuzL34Cert.CheckClosure
import CFSG.Open.LocalVocabulary

namespace CertificateChecks.KernelSpor.SuzClD

open CFSG.PSL3Four.Native CFSG.Sporadic.SuzRecog.SuzL34Cert

meta def idR : Array Nat := idTab 1782

meta def l1R : Array (Array Nat) := l1Tabs ()
meta def m21R : Array (Array Nat) := m21Tabs ()

meta def kG : Array (Array Nat) := decs l1CompDecs

end CertificateChecks.KernelSpor.SuzClD

public section

set_option maxRecDepth 400000

#kmisc_packarrs CertificateChecks.KernelSpor.SuzClL CertificateChecks.KernelSpor.SuzClD.l1R 11
#kmisc_packarrs CertificateChecks.KernelSpor.SuzClM CertificateChecks.KernelSpor.SuzClD.m21R 11

#kpenum CertificateChecks.KernelSpor.SuzClK 1782 11 false CertificateChecks.KernelSpor.SuzClD.kG
  CertificateChecks.KernelSpor.SuzClD.kG CertificateChecks.KernelSpor.SuzClD.idR 4

end
