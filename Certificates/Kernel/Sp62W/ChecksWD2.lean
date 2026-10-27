module

public import Certificates.Data.Kernel.Sp62W.Defs
public import Certificates.Kernel.Sp62W.DataWD
import CFSG.Certificates.Kernel.Common.EachTrue

public section

namespace CertificateChecks.KernelSp62W

open CFSG.KD.Sp62W

#kc_each CertificateChecks.KernelSp62W ch9441wdS (fun j => stepSl WD 16 51840 7 j) 45 89

end CertificateChecks.KernelSp62W

end
