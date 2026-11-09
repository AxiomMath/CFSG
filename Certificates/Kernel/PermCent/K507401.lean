module

public import Certificates.Data.Kernel.PermCent.Sp6BTwin
public import Certificates.Kernel.PermCent.Sp6BLay

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelPermCent

open CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.Sp6B

@[expose] noncomputable def twinP (a b : CV 36) : Bool :=
  decide (a = b) || (List.range wsC.length).any fun k =>
    commAllC a (memberElemsC L0C (wsC.getD k 1)) &&
      (memberElemsC L0C (wsC.getD k 1)).any fun z => ordThreeC (z * b * z⁻¹ * b⁻¹)

theorem kTwin : (layR.all fun a => layR.all fun b => twinP a b) = true := by decide +kernel

theorem k507401 : twinLayC = true := all2_layC kTwin

end CertificateChecks.KernelPermCent
