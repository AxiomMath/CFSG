module

public import Certificates.Kernel.EvenSporCocode.RowsK
public meta import CFSG.Certificates.Kernel.Common.Each
public meta import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace CertificateChecks.KernelCocode

set_option maxHeartbeats 0 in
#kc_each CertificateChecks.KernelCocode.rowCR 0 512

#kc_forall_tree rowsA_all (fun k => rowCR k = true) 512 CertificateChecks.KernelCocode.rowCR

end CertificateChecks.KernelCocode

end
