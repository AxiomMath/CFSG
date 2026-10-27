module

public import Certificates.Kernel.J4NPVerdict.Defs
public import CFSG.Quasithin.Vol2.KGFactC31J4M4Native
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4NPV

open CFSG.KC.J4Q CFSG.KC.J4NPV CFSG.KD.J4Q CFSG.KD.J4NPV CFSG.Quasithin.KGC31.J4M4

theorem vj79_ginv : invsK c rm one pad vjT.ge vjT.gei = true := by quickRfl

theorem vj79_ucomm : commK c rm vjT.us = true := by quickRfl

theorem vj79_w : andB (wordsK c rm one [A, B] [Ai, Bi] [W1, W2] [w1Word, w2Word])
    (invsK c rm one pad [W1, W2] [W1i, W2i]) = true := by quickRfl

theorem vj79_f : wordsK c rm one [W1, W2] [W1i, W2i] vjT.fm fWords = true := by quickRfl

end CertificateChecks.KernelJ4NPV

end
