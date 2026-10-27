module

public import Certificates.Kernel.KGC31M23.Defs
public import Certificates.Kernel.SporSch.Mathieu.M23Facts
public import CFSG.Certificates.Kernel.SporSch.ClsMem

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKGC31M23

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.MOC CFSG.Quasithin.KGC31.M23
open CertificateChecks.KernelSporSch

theorem mem_invs : ∀ t ∈ invs, ∃ k < D.c, t = CFSG.KC.Child3.tabP 23 5 (D.ST k) := by
  intro t ht
  obtain ⟨j, hj, k, hk, e⟩ := mem_orderTables_cls M23OC.chainQ (by decide) (by decide)
    M23OC.tA_eq M23OC.tB_eq M23OC.clsOK2 (fun j hj => M23OC.siftR j hj) (by norm_num)
    M23OC.hX t ht
  have hj0 : j = 0 := by simpa [M23CK] using hj
  subst hj0
  exact ⟨k, hk, e⟩

end CertificateChecks.KernelKGC31M23

end
