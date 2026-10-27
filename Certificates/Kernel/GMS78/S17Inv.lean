module

public import Certificates.Kernel.GMS78.S95Data
public import Certificates.Kernel.GMS78.P117Data
public import Certificates.Data.Kernel.GMS78RuCzJ
public import Certificates.Data.Kernel.GMS78RuSCent
public import Certificates.Data.GMS78RuSModelCheck
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelGMS78.SD

open CFSG.KC.GMS CFSG.KLie.CT CFSG.GMS78RuS

@[expose] noncomputable def m17f : Nat → Nat → Nat := mul17K GT DPR LIN DM DO0

@[expose] noncomputable def m17t : Nat → Nat → Nat := mul17K GT DPR LIN DM DO1

theorem i17f : czListEq I170 (sInvs m17f 8192) = true := by quickRfl

theorem i17t : czListEq I171 (sInvs m17t 8192) = true := by quickRfl

theorem f17f : kFin17 m17f inX17 I170 K170 = true := by quickRfl

theorem f17t : kFin17 m17t inX17 I171 K171 = true := by quickRfl

end CertificateChecks.KernelGMS78.SD

end
