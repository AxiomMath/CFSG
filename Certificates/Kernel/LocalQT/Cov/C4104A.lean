module

public import Certificates.Data.Kernel.LocalQT.CovT
public import Certificates.Kernel.LocalQT.Cov.D4104
public import Certificates.Kernel.LocalQT.Cov.T4104
public import Certificates.Kernel.Misc.Tits.Text
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CFSG.KD.LQT.C4104

open CFSG.KC.LQT.Cov CFSG.KS CertificateChecks.KernelMisc.TitsText

@[expose] noncomputable def SG (j : Nat) : Nat := F (Nat.add 18 j)

@[expose] noncomputable def SGI (j : Nat) : Nat := pinvS 1755 11 (mask 11) (F (Nat.add 18 j))

theorem kA : covTA 1755 11 13 SG SGI CT.chars P 2048 = true := by quickRfl

end CFSG.KD.LQT.C4104

end
