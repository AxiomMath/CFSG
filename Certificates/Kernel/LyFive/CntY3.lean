module

public import Certificates.Kernel.LyFive.Data
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLyFive

open CFSG.KC.LyG2 CertificateChecks.KernelLyFive.D

@[expose] noncomputable def cY3 (k : Nat) : Bool :=
  cntChk CC TT [packCols RY3] y3_fixed y3_ins y3_cnt k

@[expose] noncomputable def wY3 (k : Nat) : Bool := witBlk CC (packCols RY3) y3_wit k

end CertificateChecks.KernelLyFive

#kc_slices CertificateChecks.KernelLyFive.Y3 CertificateChecks.KernelLyFive.cY3 25
#kc_slices CertificateChecks.KernelLyFive.W3 CertificateChecks.KernelLyFive.wY3 25

end
