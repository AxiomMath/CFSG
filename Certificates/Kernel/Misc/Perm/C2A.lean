module

public import Certificates.Kernel.Misc.Perm.C2K
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.NativeSchreierCard

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.Co2K

open CFSG.KC.Enum CFSG.RankThree.Native.F2

theorem vec_ok : vecK = true := by quickRfl

theorem span_ok : spanK = true := by quickRfl

theorem strong_ok : strongK = true := by quickRfl

end CertificateChecks.KernelMisc.Co2K

end
