module

public import Certificates.Data.Kernel.Misc.PermM22
public import Certificates.Data.Kernel.Misc.PermU33B
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json_gz CertificateChecks.KernelMisc.U33B "Certificates/Kernel/Misc/Perm/U33B/data/u33b.json.gz" 1945 8231367165467438952
  (genL : List Nat) (tWords : List (List Nat)) (tL : List Nat) (kWords : List (List Nat))
  (kL : List Nat) (ixL : List Nat) (iz : Nat) (ixx : Nat) (iyy : Nat)

#kc_repo #kc_ktree_gz CertificateChecks.KernelMisc.U33B E "Certificates/Kernel/Misc/Perm/U33B/data/u33b_eP.bin.gz" 18 4 3888 2397848533003110519
#kc_repo #kc_ktree_gz CertificateChecks.KernelMisc.U33B PA "Certificates/Kernel/Misc/Perm/U33B/data/u33b_paP.bin.gz" 4 4 864 12528654331605002757
#kc_repo #kc_ktree_gz CertificateChecks.KernelMisc.U33B SG "Certificates/Kernel/Misc/Perm/U33B/data/u33b_sgP.bin.gz" 4 4 864 6323301893803471130
#kc_repo #kc_ktree_gz CertificateChecks.KernelMisc.U33B CT "Certificates/Kernel/Misc/Perm/U33B/data/u33b_ctP.bin.gz" 4 4 1728 2744026085898145681

public section

namespace CertificateChecks.KernelMisc.U33B

open CFSG.KC.Misc.M22 CFSG.KC.Misc.U33B

@[expose] noncomputable def AG (a : Nat) : Nat := nthL genL a
@[expose] noncomputable def T (j : Nat) : Nat := nthL tL j
@[expose] noncomputable def TW (j : Nat) : List Nat := nthW tWords j
@[expose] noncomputable def KG (j : Nat) : Nat := nthL kL j
@[expose] noncomputable def KW (j : Nat) : List Nat := nthW kWords j
@[expose] noncomputable def IX (i : Nat) : Nat := nthL ixL i
@[expose] noncomputable def cubeAt (k : Nat) : Bool := cubeOne (E k)

end CertificateChecks.KernelMisc.U33B

end
