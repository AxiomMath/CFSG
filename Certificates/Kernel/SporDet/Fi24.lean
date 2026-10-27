module

public import Certificates.Kernel.SporDet.Fi24Data
public import Certificates.Kernel.Sporadic.Fi24Br.Seed
public import Certificates.Data.Kernel.Spor.F3LaneId
public import Certificates.Data.Kernel.Spor.F3LaneRows
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelDet.Fi24

open CFSG.F3.Native CFSG.KS.F3L

set_option Elab.async false

theorem seedA_ok : seedRowsK (nat_lit 781) LA CFSG.KD.BrFi24.SA.chars = true := by quickRfl
theorem seedB_ok : seedRowsK (nat_lit 781) LB CFSG.KD.BrFi24.SB.chars = true := by quickRfl

theorem id_ok : idOK 781 LI = true := by decide +kernel

theorem b3_ok : (powF LB 3).beq LI = true := by quickRfl
theorem ab29_ok : (powF (mulF LA LB) 29).beq LI = true := by quickRfl

end CertificateChecks.KernelDet.Fi24

end
