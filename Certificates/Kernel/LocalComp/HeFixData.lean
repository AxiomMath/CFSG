module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CertificateChecks.KernelLC.HeFix

#kc_repo #kc_nat_items_gz CertificateChecks.KernelLC.HeFix
  "Certificates/Kernel/LocalComp/data/HeFixData.items.gz" 131406 4674645406482070778
  PC1_[9] Q[6]

#kc_repo #kc_json_gz CertificateChecks.KernelLC.HeFix
  "Certificates/Kernel/LocalComp/data/HeFixData.json.gz" 245789 7098172062745226998
  (PT1 : Nat) (PU : Nat) (PX : Nat) (G0I : Nat) (G1I : Nat) (T1I : Nat) (UI : Nat)

@[expose] noncomputable def PC1 (j : Nat) : Nat :=
  [PC1_0, PC1_1, PC1_2, PC1_3, PC1_4, PC1_5, PC1_6, PC1_7, PC1_8].getD j 0

@[expose] noncomputable def Q (j : Nat) : Nat := [Q0, Q1, Q2, Q3, Q4, Q5].getD j 0

end CertificateChecks.KernelLC.HeFix

end
