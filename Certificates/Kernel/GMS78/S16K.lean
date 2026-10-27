module

public import Certificates.Kernel.GMS78.S95Data
public import Certificates.Kernel.GMS78.P117Data
public import Certificates.Data.Kernel.GMS78RuCzJ
public import Certificates.Data.Kernel.GMS78RuSCent16
public import Certificates.Kernel.LocalComp.BlockGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelGMS78.SK

open CFSG.KC.GMS CFSG.KLie.CT CertificateChecks.KernelGMS78.SD

@[expose] noncomputable def n16f : Nat → Nat → Nat := mul16K GT DPR LIN DM DO0

@[expose] noncomputable def n16t : Nat → Nat → Nat := mul16K GT DPR LIN DM DO1

theorem j16f : czListEq I160 (sInvs n16f 2048) = true := by quickRfl

theorem j16t : czListEq I161 (sInvs n16t 2048) = true := by quickRfl

@[expose] noncomputable def c16fF (i : Nat) : Bool :=
  kKey16 GT DPR LIN DM DO0 (neGet 0 I160 i) (neGet 0 K160 i)

@[expose] noncomputable def c16tF (i : Nat) : Bool :=
  kKey16 GT DPR LIN DM DO1 (neGet 0 I161 i) (neGet 0 K161 i)

#lc_blocks c16fB c16fF 366 8

#lc_blocks c16tB c16tF 366 8

theorem g16f : kFin16 n16f I160 K160 = true := by quickRfl

theorem g16t : kFin16 n16t I161 K161 = true := by quickRfl

end CertificateChecks.KernelGMS78.SK

end
