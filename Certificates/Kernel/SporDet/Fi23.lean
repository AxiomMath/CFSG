module

public import Certificates.Kernel.SporDet.Fi23Data
public import Certificates.Data.Kernel.Spor.F3LaneId
public import Certificates.Data.Kernel.Spor.F3LaneRows
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelDet.Fi23

open CFSG.F3.Native CFSG.KS.F3L

set_option Elab.async false

theorem seedA_ok : seedRowsK (nat_lit 253) LA SeedA.chars = true := by quickRfl
theorem seedB_ok : seedRowsK (nat_lit 253) LB SeedB.chars = true := by quickRfl

theorem id_ok : idOK 253 LI = true := by decide +kernel

@[expose] noncomputable def LE : V :=
  mulF (powF (mulF LA LB) (nat_lit 5)) (powF (mulF LA (mulF LB LB)) (nat_lit 2))

theorem b3_ok : (powF LB 3).beq LI = true := by quickRfl
theorem e5_ok : (powF LE 5).beq LI = true := by quickRfl

end CertificateChecks.KernelDet.Fi23

end
