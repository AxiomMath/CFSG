module

public import Certificates.Data.Kernel.G2Three.Sec1T3A
public import Certificates.Kernel.G2Three.Sec1T3Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.G2Three.Sec1T3

open CFSG.KC.Loop

theorem s3a_f11 : f11K PT PC IV SQ 1 2 3 4 5 6 5 = true := by quickRfl

theorem s3a_f12 : f12K PT PC IV SQ 1 2 3 4 5 5 = true := by quickRfl

theorem s3a_f13 : f13K PT PC IV SQ 1 2 3 4 5 6 5 = true := by quickRfl

end CFSG.KD.G2Three.Sec1T3

end
