module

public import Certificates.Data.Kernel.WCK2
public import CFSG.CGT.Timmesfeld75.ListWCMathieuData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelWCK2

open CFSG.KC.WCK CFSG.KC.S97RYK CFSG.CGT.Timmesfeld75.WCCheck CFSG.Sporadic.Th.Native

theorem m22_ok : wcCheckK2 m22Data [0, 1, 2] = true := by quickRfl

theorem m23_ok : wcCheckK2 m23Data [0, 1, 2] = true := by quickRfl

theorem m24_ok : wcCheckK2 m24Data [0, 1, 3] = true := by quickRfl

theorem m22_gens : [m22tA, m22tAi, m22tB, m22tBi, idT 22].all (validT 22) = true := by
  decide +kernel

theorem m23_gens : [m23tA, m23tAi, m23tB, m23tBi, idT 23].all (validT 23) = true := by
  decide +kernel

theorem m24_gens : [m24tA, m24tAi, m24tB, m24tBi, idT 24].all (validT 24) = true := by
  decide +kernel

end CertificateChecks.KernelWCK2

end
