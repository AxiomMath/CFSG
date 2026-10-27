module

public import Certificates.Kernel.LocalComp.L39Arrs
public import Certificates.Kernel.Sporadic.RawGen
meta import Certificates.Kernel.LocalComp.L39Arrs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelLC.L39.LT1 91 7 16 CFSG.EvenSmallLie.Child3.SelL39.t1S
  CertificateChecks.KernelLC.L39.t1BaseArr 2 CFSG.EvenSmallLie.Child3.SelL39.tWords

#ks_rawchain CertificateChecks.KernelLC.L39.LT 182 8 16 CFSG.EvenSmallLie.Child3.SelL39.tS
  CertificateChecks.KernelLC.L39.tBaseArr 2 CFSG.EvenSmallLie.Child3.SelL39.tWords

#ks_rawchain CertificateChecks.KernelLC.L39.LA 182 8 16 CFSG.EvenSmallLie.Child3.SelL39.autS
  CertificateChecks.KernelLC.L39.autBaseArr 4 CFSG.EvenSmallLie.Child3.SelL39.autWords

#ks_rawchain CertificateChecks.KernelLC.L39.LS 182 8 16 CFSG.EvenSmallLie.Child3.SelL39.sylowS
  CertificateChecks.KernelLC.L39.sylowBaseArr 4 CFSG.EvenSmallLie.Child3.SelL39.sylowWords

end
