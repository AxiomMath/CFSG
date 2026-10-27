module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Monster.B.Fischer.Fi22OuterData
public meta import CFSG.Monster.B.Fischer.Fi22OuterData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.Fi22O693T CFSG.Monster.B.Fischer.fi22Outer693Text
#ks_hexlines CertificateChecks.KernelSpor.Fi22O693T CFSG.Monster.B.Fischer.fi22Outer693Text 3 693 10

#ks_chars CertificateChecks.KernelSpor.Fi22O256T CFSG.Monster.B.Fischer.fi22Outer256Text
#ks_hexlines CertificateChecks.KernelSpor.Fi22O256T CFSG.Monster.B.Fischer.fi22Outer256Text 2 256 9

#ks_chars CertificateChecks.KernelSpor.Fi22OMP CFSG.Monster.B.Fischer.fi22OuterMPointsHex
#kmisc_hexflat CertificateChecks.KernelSpor.Fi22OMP CFSG.Monster.B.Fischer.fi22OuterMPointsHex 3 693 12 1

#ks_chars CertificateChecks.KernelSpor.Fi22OTP CFSG.Monster.B.Fischer.fi22OuterTPointsHex
#kmisc_hexflat CertificateChecks.KernelSpor.Fi22OTP CFSG.Monster.B.Fischer.fi22OuterTPointsHex 3 256 12 1

#ks_chars CertificateChecks.KernelSpor.Fi22OWO CFSG.Monster.B.Fischer.fi22OuterWitnessOrbitsHex
#kmisc_hexflat CertificateChecks.KernelSpor.Fi22OWO CFSG.Monster.B.Fischer.fi22OuterWitnessOrbitsHex 3 693 12 1

#ks_chars CertificateChecks.KernelSpor.Fi22OUP CFSG.Monster.B.Fischer.fi22OuterUnitaryPoints

#ks_chars CertificateChecks.KernelSpor.Fi22OTV CFSG.Monster.B.Fischer.fi22OuterTransvectionVectors

end
