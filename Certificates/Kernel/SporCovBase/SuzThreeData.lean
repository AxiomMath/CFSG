module

public import Init
public import Certificates.Data.Kernel.Spor.PEnum
import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_ktree_gz CFSG.KD.SporCovBase.SuzThree TBF "Certificates/Kernel/SporCovBase/data/suz3tb.bin.gz" 64 4 31616 7780746356388481390

#kc_repo #kc_ktree_gz CFSG.KD.SporCovBase.SuzThree LGF "Certificates/Kernel/SporCovBase/data/suz3lg.bin.gz" 64 4 2432 11286595673470940521

#kc_repo #kc_json_gz CFSG.KD.SporCovBase.SuzThree.F "Certificates/Kernel/SporCovBase/data/suz3.json.gz"
  37102 7967462996525682375
  (bs : List Nat) (gw : List Nat) (Rg : List (List Nat)) (H : List (List Nat)) (R : List (List Nat))
  (P : List Nat) (T : List (List Nat)) (Rp : List (List Nat)) (Gs : List (List Nat))
  (RCc : List Nat) (RCg : List (List Nat))
  (t0 : List Nat) (M0 : List (List Nat)) (nL0 : Nat) (Y0 : List (List Nat)) (H0 : List (List Nat))
  (Yc0 : List (List Nat)) (K0 : List Nat) (nE0 : Nat) (C0 : List (List Nat))
  (t1 : List Nat) (M1 : List (List Nat)) (nL1 : Nat) (Y1 : List (List Nat)) (H1 : List (List Nat))
  (Yc1 : List (List Nat)) (K1 : List Nat) (nE1 : Nat) (C1 : List (List Nat))
  (t2 : List Nat) (M2 : List (List Nat)) (nL2 : Nat) (Y2 : List (List Nat)) (H2 : List (List Nat))
  (Yc2 : List (List Nat)) (K2 : List Nat) (nE2 : Nat) (C2 : List (List Nat))

public section

namespace CFSG.KD.SporCovBase.SuzThree

open CFSG.KS.Row

@[expose] noncomputable def tb (i j : Nat) : Nat :=
  rg (nat_lit 16) (nat_lit 65535) TBF (Nat.mul (nat_lit 38) i) j

@[expose] noncomputable def lg (j : Nat) : Nat :=
  rg (nat_lit 16) (nat_lit 65535) LGF (nat_lit 0) j

end CFSG.KD.SporCovBase.SuzThree

end
