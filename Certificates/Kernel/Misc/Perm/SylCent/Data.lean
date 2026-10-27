module

public import Certificates.Data.Kernel.Misc.PermCent
public import Certificates.Data.Kernel.Misc.PermM22
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json_gz CertificateChecks.KernelMisc.SylCent "Certificates/Kernel/Misc/Perm/SylCent/data/sylcent.json.gz" 11458 1157151589773877762
  (gL : List Nat) (pL : List Nat) (pWords : List (List Nat)) (eL : List Nat) (paL : List Nat)
  (sgL : List Nat) (ctL : List Nat) (repL : List Nat) (orbits : List (List Nat)) (uL : List Nat)
  (uWords : List (List Nat)) (adjL : List Nat)

public section

namespace CertificateChecks.KernelMisc.SylCent

open CFSG.KC.Misc.M22 (nthL nthW)
open CFSG.KC.Misc.Cent (presE)
open CFSG.KC.LQT.P (anyN impB)

@[expose] noncomputable def GC (j : Nat) : Nat := nthL gL j
@[expose] noncomputable def PC (j : Nat) : Nat := nthL pL j
@[expose] noncomputable def PW (j : Nat) : List Nat := nthW pWords j
@[expose] noncomputable def E (k : Nat) : Nat := nthL eL k
@[expose] noncomputable def PA (k : Nat) : Nat := nthL paL k
@[expose] noncomputable def SG (k : Nat) : Nat := nthL sgL k
@[expose] noncomputable def CT (k : Nat) : Nat := nthL ctL k
@[expose] noncomputable def RR (k : Nat) : Nat := nthL repL k
@[expose] noncomputable def OO (k : Nat) : List Nat := nthW orbits k
@[expose] noncomputable def UU (q : Nat) : Nat := nthL uL q
@[expose] noncomputable def UW (q : Nat) : List Nat := nthW uWords q
@[expose] noncomputable def AA (a : Nat) : Nat := nthL adjL a
@[expose] noncomputable def leaf (X : Nat) : Bool :=
  impB (presE 42 6 AA X) (anyN 64 fun k => Nat.beq X (E k))

end CertificateChecks.KernelMisc.SylCent

end
