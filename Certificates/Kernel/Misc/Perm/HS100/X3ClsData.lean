module

public import Certificates.Data.Kernel.PCent
public import Certificates.Kernel.Misc.Perm.HS100.Base
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.HS100.X3Cls

#kc_repo #kc_json CertificateChecks.KernelMisc.HS100.X3Cls
  "Certificates/Kernel/Misc/Perm/HS100/data/x3cls.json" 2803387 11184465463479532910
  (G : List Nat) (GI : List Nat) (W : List (List Nat)) (p : Nat) (v : Nat)
  (R : List (Nat × Nat × Nat × Nat))

#kc_repo #kc_json CertificateChecks.KernelMisc.HS100.X3Cls
  "Certificates/Kernel/Misc/Perm/HS100/data/x3cent.json" 4811 12058007959493435142
  (C : List Nat) (CW : List (List Nat))
  (L : List (Nat × List Nat × List (List Nat) × List (Nat × Nat × Nat × Nat)))
  (PO : List (Nat × Nat × Nat × Nat))

open CFSG.KS (mask pinvS)

@[expose] noncomputable def pG (k : Nat) : Nat := G.getD k (nat_lit 0)

@[expose] noncomputable def pGI (k : Nat) : Nat := GI.getD k (nat_lit 0)

@[expose] noncomputable def pC (k : Nat) : Nat := C.getD k (nat_lit 0)

@[expose] noncomputable def hsW (k : Nat) : Nat :=
  [HX.F 0, HX.F 1, HX.F 15, pinvS 100 7 (mask 7) (HX.F 0), pinvS 100 7 (mask 7) (HX.F 1),
    pinvS 100 7 (mask 7) (HX.F 15)].getD k (nat_lit 0)

end CertificateChecks.KernelMisc.HS100.X3Cls

end
