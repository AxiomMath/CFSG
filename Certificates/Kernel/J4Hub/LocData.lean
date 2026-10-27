module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CertificateChecks.KernelJ4Hub

#kc_repo #kc_nat_items_gz CertificateChecks.KernelJ4Hub
  "Certificates/Kernel/J4Hub/data/LocData.items.gz" 75287 15337747970071606245
  (LG 1 7)

#kc_repo #kc_json_gz CertificateChecks.KernelJ4Hub
  "Certificates/Kernel/J4Hub/data/LocData.json.gz" 6659 17969106154432458445
  (lw0 : List (Nat × Bool)) (lw1 : List (Nat × Bool)) (lw2 : List (Nat × Bool))
  (xW : List (Nat × Bool)) (yW : List (Nat × Bool)) (zW : List (Nat × Bool))

@[expose] noncomputable def LG (r : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun k _ => Nat.rec (motive := fun _ => Nat) LG1
    (fun k _ => Nat.rec (motive := fun _ => Nat) LG2 (fun k _ => Nat.rec (motive := fun _ => Nat) LG3
      (fun k _ => Nat.rec (motive := fun _ => Nat) LG4 (fun k _ => Nat.rec (motive := fun _ => Nat) LG5
        (fun _ _ => LG6) k) k) k) k) k) r

end CertificateChecks.KernelJ4Hub

end
