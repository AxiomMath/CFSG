module

public import Certificates.Data.Kernel.SmithD6.WtCheck
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000

open CFSG.KD.SmithD6

#kc_each CertificateChecks.SmithD6Wt d6cl (fun i => d6CloseOK (i / 13) (i % 13)) 130 260
