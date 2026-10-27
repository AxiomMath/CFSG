module

public import Certificates.Data.Kernel.HM22Flag
import all Certificates.Data.SmithB45HM22Flag
import all Certificates.Data.SmithB45HM22Std
import all CFSG.Quasithin.Background.SmithB45HM22Comp
import all CFSG.Quasithin.Background.SmithB45HM22Pack
public import CFSG.Certificates.Kernel.Common.EachTrue
public import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace CertificateChecks.HM22Flag

open CFSG.KC.HM22Flag

#kc_each CertificateChecks.HM22Flag ch260415i (chunk idCol9 33) 0 6

#kc_each CertificateChecks.HM22Flag ch260415a (chunk blk1Col9 18) 0 11

#kc_each CertificateChecks.HM22Flag ch260415b (chunk blk2Col9 18) 0 11

#kc_forall_tree ch260415iAll (fun k => chunk idCol9 33 k = true) 6
  CertificateChecks.HM22Flag.ch260415i

#kc_forall_tree ch260415aAll (fun k => chunk blk1Col9 18 k = true) 11
  CertificateChecks.HM22Flag.ch260415a

#kc_forall_tree ch260415bAll (fun k => chunk blk2Col9 18 k = true) 11
  CertificateChecks.HM22Flag.ch260415b

end CertificateChecks.HM22Flag
