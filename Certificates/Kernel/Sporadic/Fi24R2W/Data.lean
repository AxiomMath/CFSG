module

public import Certificates.Kernel.Sporadic.HexNumsGen
public import CFSG.Sporadic.FischerOddCore.Fi24R2Data

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.Fi24R2W.FP CFSG.Sporadic.FischerOddCore.fi24FPtsText
#ks_hexnums CertificateChecks.KernelSpor.Fi24R2W.FP CFSG.Sporadic.FischerOddCore.fi24FPtsText 5 19

namespace CertificateChecks.KernelSpor.Fi24R2W

open CFSG.KS.Raw CFSG.KS.HexNums CFSG.Sporadic.FischerOddCore

theorem fp_eq : fi24FPts = unpack 504 19 FP.F := hexNums_of FP.eq FP.ok

end CertificateChecks.KernelSpor.Fi24R2W

end
