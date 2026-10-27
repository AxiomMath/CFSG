module

public import Init
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CertificateChecks.KernelGMS78.W

#kc_repo #kc_nat_items_gz CertificateChecks.KernelGMS78.W
  "Certificates/Kernel/GMS78/data/WData.items.gz" 10642 15209434539921388483
  (G 1 19)

#kc_repo #kc_json_gz CertificateChecks.KernelGMS78.W
  "Certificates/Kernel/GMS78/data/WData.json.gz" 34441 13167091832285816563
  (RI : List (List (Nat × Bool))) (RC : List (List (Nat × Bool))) (RA : List (List (Nat × Bool)))
  (RE : List (List (Nat × Bool))) (RS : List (List (Nat × Bool)))

@[expose] noncomputable def RG (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (G18) (G17) (Nat.blt k (nat_lit 18))) (G16) (Nat.blt k (nat_lit 17))) (Bool.rec (motive := fun _ => Nat) (G15) (G14) (Nat.blt k (nat_lit 15))) (Nat.blt k (nat_lit 16))) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (G13) (G12) (Nat.blt k (nat_lit 13))) (G11) (Nat.blt k (nat_lit 12))) (Bool.rec (motive := fun _ => Nat) (G10) (G9) (Nat.blt k (nat_lit 10))) (Nat.blt k (nat_lit 11))) (Nat.blt k (nat_lit 14))) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (G8) (G7) (Nat.blt k (nat_lit 8))) (G6) (Nat.blt k (nat_lit 7))) (Bool.rec (motive := fun _ => Nat) (G5) (G4) (Nat.blt k (nat_lit 5))) (Nat.blt k (nat_lit 6))) (Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (G3) (G2) (Nat.blt k (nat_lit 3))) (Bool.rec (motive := fun _ => Nat) (G1) (nat_lit 0) (Nat.blt k (nat_lit 1))) (Nat.blt k (nat_lit 2))) (Nat.blt k (nat_lit 4))) (Nat.blt k (nat_lit 9))) (Nat.blt k (nat_lit 19))

end CertificateChecks.KernelGMS78.W

end
