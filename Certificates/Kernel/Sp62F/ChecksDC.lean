module

public import Certificates.Data.Kernel.Sp62F.Cosets
public import Certificates.Kernel.Sp62F.DataN
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CertificateChecks.KernelSp62F.DC
  "Certificates/Kernel/Sp62F/data/dc.json.gz" 8579 11154273989494448450
  (DC : List (Nat × Nat))

namespace CertificateChecks.KernelSp62F

open CFSG.KD.Sp62F CFSG.KD.Sp62W CFSG.KGroups.Sp6 CFSG.AGLEmbedding.KFactProofs.Sp62Local

theorem ch9453dc : dcCheck NR 15 DC.DC = true := by decide +kernel

theorem ch9453cz : czCheck2 = true := by decide +kernel

theorem ch9453dc_n1 : incKeys (dcKeyB NR 15) (DC.DC.head! :: DC.DC) 0 = false := by
  decide +kernel

theorem ch9453cz_n1 :
    ((List.range 64).all fun v => qv v == bf v (mulVecC cW0 v)) = false := by decide +kernel

theorem ch9453dc_n2 : permS cGD = false := by decide +kernel

end CertificateChecks.KernelSp62F

end
