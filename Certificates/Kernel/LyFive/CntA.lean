module

public import Certificates.Kernel.LyFive.Data
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLyFive

open CFSG.KC.LyG2 CertificateChecks.KernelLyFive.D

@[expose] noncomputable def cA0 (k : Nat) : Bool := cntChk CC TT [] a0_fixed a0_ins a0_cnt k

@[expose] noncomputable def cA1 (k : Nat) : Bool := cntChk CC TT [] a1_fixed a1_ins a1_cnt k

@[expose] noncomputable def cA2 (k : Nat) : Bool := cntChk CC TT [] a2_fixed a2_ins a2_cnt k

end CertificateChecks.KernelLyFive

#kc_slices CertificateChecks.KernelLyFive.A0 CertificateChecks.KernelLyFive.cA0 25
#kc_slices CertificateChecks.KernelLyFive.A1 CertificateChecks.KernelLyFive.cA1 25
#kc_slices CertificateChecks.KernelLyFive.A2 CertificateChecks.KernelLyFive.cA2 25

end
