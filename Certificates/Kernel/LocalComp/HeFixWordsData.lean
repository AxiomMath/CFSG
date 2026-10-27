module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CertificateChecks.KernelLC.HeFix

#kc_repo #kc_nat_items_gz CertificateChecks.KernelLC.HeFix
  "Certificates/Kernel/LocalComp/data/HeFixWordsData.items.gz" 524948 17942095412061356704
  XR[16] C3R[5] C7R[8] C8R[7]

#kc_repo #kc_json_gz CertificateChecks.KernelLC.HeFix
  "Certificates/Kernel/LocalComp/data/HeFixWordsData.json.gz" 421369 14790322425027700373
  (C0R0 : Nat) (C0R1 : Nat) (C1R0 : Nat) (C1R1 : Nat) (C2R0 : Nat) (C2R1 : Nat) (C4R0 : Nat)
  (C4R1 : Nat) (C5R0 : Nat) (C5R1 : Nat) (C6R0 : Nat) (C6R1 : Nat)

@[expose] noncomputable def XR (i : Nat) : Nat :=
  [XR0, XR1, XR2, XR3, XR4, XR5, XR6, XR7, XR8, XR9, XR10, XR11, XR12, XR13, XR14, XR15].getD i 0

@[expose] noncomputable def C0R (i : Nat) : Nat :=
  [C0R0, C0R1].getD i 0

@[expose] noncomputable def C1R (i : Nat) : Nat :=
  [C1R0, C1R1].getD i 0

@[expose] noncomputable def C2R (i : Nat) : Nat :=
  [C2R0, C2R1].getD i 0

@[expose] noncomputable def C3R (i : Nat) : Nat :=
  [C3R0, C3R1, C3R2, C3R3, C3R4].getD i 0

@[expose] noncomputable def C4R (i : Nat) : Nat :=
  [C4R0, C4R1].getD i 0

@[expose] noncomputable def C5R (i : Nat) : Nat :=
  [C5R0, C5R1].getD i 0

@[expose] noncomputable def C6R (i : Nat) : Nat :=
  [C6R0, C6R1].getD i 0

@[expose] noncomputable def C7R (i : Nat) : Nat :=
  [C7R0, C7R1, C7R2, C7R3, C7R4, C7R5, C7R6, C7R7].getD i 0

@[expose] noncomputable def C8R (i : Nat) : Nat :=
  [C8R0, C8R1, C8R2, C8R3, C8R4, C8R5, C8R6].getD i 0

end CertificateChecks.KernelLC.HeFix

end
