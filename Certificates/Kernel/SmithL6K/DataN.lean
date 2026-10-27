module

public import Init
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CertificateChecks.KernelSmithL6K
  "Certificates/Kernel/SmithL6K/data/l6n.json.gz" 14492 14051539917506608098
  (prt : List Nat) (prc : List (Nat × Nat × Nat)) (frt : Nat)

#kc_repo #kc_nat_items_gz CertificateChecks.KernelSmithL6K
  "Certificates/Kernel/SmithL6K/data/l6n.items.gz" 164205 16680381500053603375
  fpk[21] frp[21] fgm

namespace CertificateChecks.KernelSmithL6K

@[expose] noncomputable def fpkL : List Nat :=
  [fpk0, fpk1, fpk2, fpk3, fpk4, fpk5, fpk6, fpk7, fpk8, fpk9, fpk10, fpk11, fpk12, fpk13, fpk14,
    fpk15, fpk16, fpk17, fpk18, fpk19, fpk20]

@[expose] noncomputable def frpL : List Nat :=
  [frp0, frp1, frp2, frp3, frp4, frp5, frp6, frp7, frp8, frp9, frp10, frp11, frp12, frp13, frp14,
    frp15, frp16, frp17, frp18, frp19, frp20]

end CertificateChecks.KernelSmithL6K

end
