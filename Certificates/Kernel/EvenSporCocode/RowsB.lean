module

public import Certificates.Kernel.EvenSporCocode.RowsK
public meta import CFSG.Certificates.Kernel.Common.Each
public meta import CFSG.Certificates.Kernel.Common.ForallTreeFrom
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallTreeFrom

public section

namespace CertificateChecks.KernelCocode

set_option maxHeartbeats 0 in
#kc_each CertificateChecks.KernelCocode.rowCR 512 1024

#kc_forall_tree_from rowsB_all (fun k => rowCR k = true) 512 512 CertificateChecks.KernelCocode.rowCR

end CertificateChecks.KernelCocode

end
