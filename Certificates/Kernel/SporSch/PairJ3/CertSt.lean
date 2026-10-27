module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.SporSch.PairJ3.GenCert
public import Certificates.Data.Kernel.SporSch.PairJ3Cert
public import Certificates.Data.Kernel.SporSch.J4STok
public import CFSG.Sporadic.Schreier.PairJ3CertInputs
public meta import CFSG.Sporadic.Schreier.PairJ3CertInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSporSch.PJ3St CFSG.Sporadic.Schreier.j3StabText

#kss_pomdata CertificateChecks.KernelSporSch.PJ3St CFSG.Sporadic.Schreier.j3StabData

namespace CertificateChecks.KernelSporSch.PJ3Cert

open CFSG.KS.SporSch CertificateChecks.KernelSporSch

theorem tok : tokK PJ3St.chars (encOM PJ3St.R) = true := by quickRfl

theorem stab : stabK 6156 6154 [1, 1360, 2040, 1360, 510, 680, 120, 85] [1, 4, 7, 8, 26, 47, 205]
    PJ3St.R = true := by
  quickRfl

end CertificateChecks.KernelSporSch.PJ3Cert

end
