module

public import Certificates.Kernel.U52.Defs
public import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.U52.Defs
public meta import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.BorelTits.CompleteFlag

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelU52.CP1 462 9 16 CertificateChecks.KernelU52.u52SP1
  CertificateChecks.KernelU52.u52BP1 3 CertificateChecks.KernelU52.u52DP1

#ks_rawchain CertificateChecks.KernelU52.CP2 462 9 16 CertificateChecks.KernelU52.u52SP2
  CertificateChecks.KernelU52.u52BP2 3 CertificateChecks.KernelU52.u52DP2

#ks_rawchain CertificateChecks.KernelU52.CB 462 9 16 CertificateChecks.KernelU52.u52SB
  CertificateChecks.KernelU52.u52BB 2 CertificateChecks.KernelU52.u52DB

#ks_rawchain CertificateChecks.KernelU52.CS0 462 9 16 CertificateChecks.KernelU52.u52SS0
  CertificateChecks.KernelU52.u52BS0 4 CertificateChecks.KernelU52.u52DS0

#ks_rawchain CertificateChecks.KernelU52.CK 462 9 16 CertificateChecks.KernelU52.u52SK
  CertificateChecks.KernelU52.u52BK 2 CertificateChecks.KernelU52.u52DK
