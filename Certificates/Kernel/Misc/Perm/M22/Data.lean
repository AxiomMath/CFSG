module

public import Certificates.Data.Kernel.Misc.PermM22
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json_gz CertificateChecks.KernelMisc.M22 "Certificates/Kernel/Misc/Perm/M22/data/m22.json.gz" 1693 13718293265045208003
  (genL : List Nat) (tWords : List (List Nat)) (tL : List Nat) (kWords : List (List Nat))
  (kL : List Nat) (ixL : List Nat) (wL : List Nat) (xC : Nat) (yC : Nat)

#kc_repo #kc_ktree_gz CertificateChecks.KernelMisc.M22 E "Certificates/Kernel/Misc/Perm/M22/data/m22_eP.bin.gz" 14 4 282240 2335193889603519183
#kc_repo #kc_ktree_gz CertificateChecks.KernelMisc.M22 PA "Certificates/Kernel/Misc/Perm/M22/data/m22_paP.bin.gz" 4 4 80640 9687271123121582669
#kc_repo #kc_ktree_gz CertificateChecks.KernelMisc.M22 SG "Certificates/Kernel/Misc/Perm/M22/data/m22_sgP.bin.gz" 4 4 80640 11355990155945215156
#kc_repo #kc_ktree_gz CertificateChecks.KernelMisc.M22 CT "Certificates/Kernel/Misc/Perm/M22/data/m22_ctP.bin.gz" 4 4 161280 9802474027486990170

public section

namespace CertificateChecks.KernelMisc.M22

open CFSG.KC.Misc.M22

@[expose] noncomputable def AG (a : Nat) : Nat := nthL genL a
@[expose] noncomputable def T (j : Nat) : Nat := nthL tL j
@[expose] noncomputable def TW (j : Nat) : List Nat := nthW tWords j
@[expose] noncomputable def KG (j : Nat) : Nat := nthL kL j
@[expose] noncomputable def KW (j : Nat) : List Nat := nthW kWords j
@[expose] noncomputable def IX (i : Nat) : Nat := nthL ixL i
@[expose] noncomputable def WC (k : Nat) : Nat := nthL wL k
@[expose] def q8L : List Nat := [35, 22, 49, 69, 88, 98, 116, 135]
@[expose] noncomputable def badAt (k : Nat) : Bool := noBadK xC yC WC q8L (E k)

end CertificateChecks.KernelMisc.M22

end
