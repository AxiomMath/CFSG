module

public import Certificates.Kernel.Misc.Perm.C2K
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.NativeSchreierCard

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.Co2K

open CFSG.KC.Enum CFSG.RankThree.Native.F2

theorem q_ok : qK = true := by quickRfl

theorem c0_ok : c0K = true := by quickRfl

theorem c1_ok : c1K = true := by quickRfl

end CertificateChecks.KernelMisc.Co2K

end
