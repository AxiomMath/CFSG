
module

public import Certificates.Data.Kernel.Parrott946.O3C

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.Parrott946

open CFSG.KC.Parrott946 CFSG.Certificates.Kernel.PkCV CFSG.RankThree.GF2n.Parrott

theorem o3c_facts : O3C.Nodup ∧ O3C.length = 27 ∧ (1 : CV 45) ∈ O3C ∧
    O3C.all (fun a => O3C.all fun b => decide (a * b ∈ O3C)) = true ∧
    O3C.all (fun a => decide (a⁻¹ ∈ O3C)) = true ∧ closeStepC O3C o3StepsC = O3C ∧
    cOf sigma1 ∈ O3C ∧ cOf o3b ∈ O3C ∧ cOf o3c ∈ O3C ∧ cOf (sigma1 * sigma2⁻¹) ∉ O3C ∧
    O3C.all (fun a => powOneC a 3) = true ∧
    O3C.any (fun a => O3C.any fun b => !eq22C a b b a) = true ∧
    O3C.all (fun a => eq22C a (cOf sigma1) (cOf sigma1) a) = true := by
  decide +kernel

end CertificateChecks.Parrott946

end
