module

public import Certificates.Data.Kernel.S97RYK
public import CFSG.LargeExtraspecial.S97RYData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelS97RY

open CFSG.KC.S97RYK CFSG.LargeExtraspecial.S11.PairCheck CFSG.CGT.Timmesfeld75.WCCheck
  CFSG.Sporadic.Th.Native

theorem a9_ok : pairCheckK a9PData = true := by quickRfl

theorem m22_ok : pairCheckK m22PData = true := by quickRfl

theorem a9_gens : [a9tA, a9tAi, a9tB, a9tBi, idT 9].all (validT 9) = true := by decide +kernel

theorem m22_gens : [m22tA, m22tAi, m22tB, m22tBi, idT 22].all (validT 22) = true := by
  decide +kernel

end CertificateChecks.KernelS97RY

end
