module

public import Certificates.Data.Kernel.Misc.PermFuse
public import Certificates.Data.Kernel.Misc.PermClos
public import Certificates.Data.Kernel.Misc.PermM22
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json_gz CertificateChecks.KernelMisc.Fuse "Certificates/Kernel/Misc/Perm/Fuse/data/fuse.json.gz" 117251 13013292556499836633
  (gL : List Nat)
  (kW2 : List (List Nat)) (kL2 : List Nat) (eL2 : List Nat) (paL2 : List Nat) (sgL2 : List Nat)
  (ctL2 : List Nat) (oL2 : List Nat) (opL2 : List Nat) (osL2 : List Nat) (wW2 : List (List Nat))
  (wL2 : List Nat)
  (kW3 : List (List Nat)) (kL3 : List Nat) (eL3 : List Nat) (paL3 : List Nat) (sgL3 : List Nat)
  (ctL3 : List Nat) (oL3 : List Nat) (opL3 : List Nat) (osL3 : List Nat) (wW3 : List (List Nat))
  (wL3 : List Nat)
  (kW4 : List (List Nat)) (kL4 : List Nat) (eL4 : List Nat) (paL4 : List Nat) (sgL4 : List Nat)
  (ctL4 : List Nat) (oL4 : List Nat) (opL4 : List Nat) (osL4 : List Nat) (wW4 : List (List Nat))
  (wL4 : List Nat)

public section

namespace CertificateChecks.KernelMisc.Fuse

open CFSG.KC.Misc.M22 (nthL nthW)

@[expose] noncomputable def KG2 (j : Nat) : Nat := nthL kL2 j
@[expose] noncomputable def KW2 (j : Nat) : List Nat := nthW kW2 j
@[expose] noncomputable def E2 (j : Nat) : Nat := nthL eL2 j
@[expose] noncomputable def PA2 (j : Nat) : Nat := nthL paL2 j
@[expose] noncomputable def SG2 (j : Nat) : Nat := nthL sgL2 j
@[expose] noncomputable def CT2 (j : Nat) : Nat := nthL ctL2 j
@[expose] noncomputable def O2 (j : Nat) : Nat := nthL oL2 j
@[expose] noncomputable def OP2 (j : Nat) : Nat := nthL opL2 j
@[expose] noncomputable def OS2 (j : Nat) : Nat := nthL osL2 j
@[expose] noncomputable def SW2 (j : Nat) : List Nat := nthW wW2 j
@[expose] noncomputable def SC2 (j : Nat) : Nat := nthL wL2 j

@[expose] noncomputable def KG3 (j : Nat) : Nat := nthL kL3 j
@[expose] noncomputable def KW3 (j : Nat) : List Nat := nthW kW3 j
@[expose] noncomputable def E3 (j : Nat) : Nat := nthL eL3 j
@[expose] noncomputable def PA3 (j : Nat) : Nat := nthL paL3 j
@[expose] noncomputable def SG3 (j : Nat) : Nat := nthL sgL3 j
@[expose] noncomputable def CT3 (j : Nat) : Nat := nthL ctL3 j
@[expose] noncomputable def O3 (j : Nat) : Nat := nthL oL3 j
@[expose] noncomputable def OP3 (j : Nat) : Nat := nthL opL3 j
@[expose] noncomputable def OS3 (j : Nat) : Nat := nthL osL3 j
@[expose] noncomputable def SW3 (j : Nat) : List Nat := nthW wW3 j
@[expose] noncomputable def SC3 (j : Nat) : Nat := nthL wL3 j

@[expose] noncomputable def KG4 (j : Nat) : Nat := nthL kL4 j
@[expose] noncomputable def KW4 (j : Nat) : List Nat := nthW kW4 j
@[expose] noncomputable def E4 (j : Nat) : Nat := nthL eL4 j
@[expose] noncomputable def PA4 (j : Nat) : Nat := nthL paL4 j
@[expose] noncomputable def SG4 (j : Nat) : Nat := nthL sgL4 j
@[expose] noncomputable def CT4 (j : Nat) : Nat := nthL ctL4 j
@[expose] noncomputable def O4 (j : Nat) : Nat := nthL oL4 j
@[expose] noncomputable def OP4 (j : Nat) : Nat := nthL opL4 j
@[expose] noncomputable def OS4 (j : Nat) : Nat := nthL osL4 j
@[expose] noncomputable def SW4 (j : Nat) : List Nat := nthW wW4 j
@[expose] noncomputable def SC4 (j : Nat) : Nat := nthL wL4 j

end CertificateChecks.KernelMisc.Fuse

end
