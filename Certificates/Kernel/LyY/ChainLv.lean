module

public import Certificates.Kernel.LyY.ChainData
public import Certificates.Kernel.Sporadic.RawGenSplitP
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_lvp CertificateChecks.KernelLyY.YC 0 0 9
#ks_rawchain_sl2_lvp CertificateChecks.KernelLyY.YC 1 0 9
#ks_rawchain_sl2_lvp CertificateChecks.KernelLyY.YC 2 0 9

end
