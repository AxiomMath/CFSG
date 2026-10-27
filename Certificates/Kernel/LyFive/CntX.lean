module

public import Certificates.Kernel.LyFive.Data
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLyFive

open CFSG.KC.LyG2 CertificateChecks.KernelLyFive.D

@[expose] noncomputable def cX0 (k : Nat) : Bool := cntChk CC TT [packCols RX] x0_fixed x0_ins x0_cnt k

@[expose] noncomputable def cX1 (k : Nat) : Bool := cntChk CC TT [packCols RX] x1_fixed x1_ins x1_cnt k

end CertificateChecks.KernelLyFive

#kc_slices CertificateChecks.KernelLyFive.X0 CertificateChecks.KernelLyFive.cX0 25
#kc_slices CertificateChecks.KernelLyFive.X1 CertificateChecks.KernelLyFive.cX1 25

end
