module

public import Certificates.Kernel.LocalComp.ThOrder
public import CFSG.Certificates.Kernel.M1F2Sound

public section

namespace CertificateChecks.KernelLC

open CFSG.KC.M1F2

open CFSG.EvenSmallLie.CatalogOrders CFSG.SectionRank.Native in
theorem cert3005 : prodOrderOK (ops2 248) thData.seedA thData.seedB 19 0 = true := by
  have h := prodOrder_sound (by decide) (by decide) ThA.bind ThB.bind kThOrder
  rw [← ThA.eq, ← ThB.eq] at h
  exact h

end CertificateChecks.KernelLC

end
