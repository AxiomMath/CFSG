module

public import Certificates.Kernel.Misc.Perm.C2K
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.NativeSchreierCard

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.Co2K

open CFSG.KC.Enum CFSG.RankThree.Native.F2

theorem sift_ok : siftK = true := by quickRfl

theorem fix_ok : fixK = true := by quickRfl

theorem tail_ok : tailK = true := by quickRfl

theorem rels_ok : relsK = true := by quickRfl

theorem se_ok : seK = true := by quickRfl

end CertificateChecks.KernelMisc.Co2K

end
