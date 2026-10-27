module

public import Certificates.Data.Kernel.J4Q.CovTab
public import Certificates.Kernel.J4Q.MatData
public import Certificates.Data.CFSGNative.J4.Data
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json_gz CFSG.KD.J4Cov3 "Certificates/Kernel/J4Cov3/data/covtab.json.gz" 3747 11727996718121256989
    (prg : List (Nat × Nat)) (rp : List Nat) (cj : List (List Nat)) (cw : List (List Nat))
    (fu : List Nat) (prg2 : List (Nat × Nat)) (xr : List Nat)

public section

namespace CFSG.KD.J4Cov3

open CFSG.KD.J4Q

@[expose] noncomputable def mats : List Nat := [L0, L1, L2, A, B]

@[expose] noncomputable def invs : List Nat := [L0i, L1i, L2i, Ai, Bi]

@[expose] noncomputable def chkW (prg : List (Nat × Nat)) (rp : List Nat) (cj cw : List (List Nat))
    (fu : List Nat) (prg2 : List (Nat × Nat)) (xr : List Nat) : Bool :=
  CFSG.KC.J4Q.CovTab.chk c rm one (CFSG.KC.J4Q.v2N CFSG.Sporadic.J4.Native.rootV) mats invs prg rp
    cj cw fu prg2 xr

end CFSG.KD.J4Cov3

end
