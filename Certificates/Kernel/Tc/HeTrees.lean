module

public import Certificates.Kernel.Tc.HeSrc
public import Certificates.Kernel.HeLoc.TreeCmd
public import Certificates.Kernel.B3S3.Gen
public import Certificates.Data.Kernel.TcK
public meta import Certificates.Kernel.Tc.HeSrc
public meta import Certificates.Kernel.B3S3.Gen

set_option maxRecDepth 400000

#kh_tree CertificateChecks.KernelTc.He.TQ CertificateChecks.KernelTc.He.cQ 8330
  CFSG.Sporadic.HeldB.heBase
#kh_tree CertificateChecks.KernelTc.He.TK CertificateChecks.KernelTc.He.cK 8330
  CFSG.Sporadic.HeldB.heBase
#kh_tree CertificateChecks.KernelTc.He.TY CertificateChecks.KernelTc.He.cY 8330
  CFSG.Sporadic.HeldB.heBase
#kb3_enum CertificateChecks.KernelTc.He.ES CertificateChecks.KernelTc.He.sig
  CertificateChecks.KernelTc.He.keys7 7 4
