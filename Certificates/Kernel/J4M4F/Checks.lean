module

public import Certificates.Data.Kernel.J4M4F.Defs
public import Certificates.Kernel.J4NPVerdict.Defs
public import CFSG.Quasithin.Vol2.KGFactC31J4M4Native
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4M4F

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KD.J4NPV CFSG.KD.J4M4F CFSG.Quasithin.KGC31.J4M4
  CFSG.Sporadic.J4.Native

@[expose] noncomputable def FMs : List Nat := [FM_0, FM_1, FM_2, FM_3, FM_4, FM_5, FM_6, FM_7, FM_8, FM_9]

theorem m4i_ok : andB (Nat.beq (wordJ c rm one [A, B] [Ai, Bi] (invW w1Word)) W1i)
    (Nat.beq (wordJ c rm one [A, B] [Ai, Bi] (invW w2Word)) W2i) = true := by quickRfl

theorem fa_ok : chkA c rm one FMs = true := by quickRfl

theorem fb_ok0 : chkB rm one FMs (v2N rootV) 0 128 = true := by quickRfl
theorem fb_ok1 : chkB rm one FMs (v2N rootV) 128 128 = true := by quickRfl
theorem fb_ok2 : chkB rm one FMs (v2N rootV) 256 128 = true := by quickRfl
theorem fb_ok3 : chkB rm one FMs (v2N rootV) 384 128 = true := by quickRfl
theorem fb_ok4 : chkB rm one FMs (v2N rootV) 512 128 = true := by quickRfl
theorem fb_ok5 : chkB rm one FMs (v2N rootV) 640 128 = true := by quickRfl
theorem fb_ok6 : chkB rm one FMs (v2N rootV) 768 128 = true := by quickRfl
theorem fb_ok7 : chkB rm one FMs (v2N rootV) 896 128 = true := by quickRfl

theorem fc_ok : chkC c rm one FMs [W1, W2] [W1i, W2i] cTab = true := by quickRfl

theorem kw_ok : chkK c rm one [A, B] [Ai, Bi] gWord (v2N rootV) [W1i, W2i, W1, W2]
    (kwVecs.map v2N) kwSig = true := by quickRfl

end CertificateChecks.KernelJ4M4F

end
