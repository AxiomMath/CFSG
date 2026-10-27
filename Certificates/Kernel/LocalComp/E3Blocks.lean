
module

public import Certificates.Kernel.LocalComp.E3Checks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#lc_blocks CertificateChecks.KernelLC.Co3Id.BD CertificateChecks.KernelLC.Co3Id.ddK 4608 4608
#lc_blocks CertificateChecks.KernelLC.Co3Id.B1 CertificateChecks.KernelLC.Co3Id.l1K 4608 128
#lc_blocks CertificateChecks.KernelLC.Co3Id.BP CertificateChecks.KernelLC.Co3Id.cdPos 576 64
#lc_blocks CertificateChecks.KernelLC.Co3Id.BM CertificateChecks.KernelLC.Co3Id.cdMem 4608 1152
#lc_blocks CertificateChecks.KernelLC.Co3Id.BH CertificateChecks.KernelLC.Co3Id.leafH 16 1
#lc_blocks CertificateChecks.KernelLC.Co3Id.BC CertificateChecks.KernelLC.Co3Id.leafC 2048 16

end
