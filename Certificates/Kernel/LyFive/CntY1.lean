module

public import Certificates.Kernel.LyFive.Data
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLyFive

open CFSG.KC.LyG2 CertificateChecks.KernelLyFive.D

@[expose] noncomputable def cY1 (k : Nat) : Bool :=
  cntChk CC TT [packCols RY1] y1_fixed y1_ins y1_cnt k

end CertificateChecks.KernelLyFive

#kc_slices CertificateChecks.KernelLyFive.Y1 CertificateChecks.KernelLyFive.cY1 25

end
