module

public import Certificates.Data.Kernel.TcRes.Plane
public import Certificates.Kernel.TcRes.ForestData
import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_nat_items_gz CFSG.KD.TcRes.C1P "Certificates/Kernel/TcRes/data/c1plane.bin.gz"
  13019 10844681761422634765 START PW U[6] RC[6] L[6] M[6]

#kc_repo #kc_ktree_gz CFSG.KD.TcRes.C1P LF "Certificates/Kernel/TcRes/data/c1planes.bin.gz"
  1094 4 127998 2932202142854823132

#kc_select CFSG.KD.TcRes.C1P uS U 6
#kc_select CFSG.KD.TcRes.C1P rcS RC 6
#kc_select CFSG.KD.TcRes.C1P lS L 6
#kc_select CFSG.KD.TcRes.C1P mS M 6

namespace CFSG.KD.TcRes

open CFSG.TcRes.TK

@[expose] noncomputable def C1P.tab (i : Nat) : Bool := tabsOK C1P.uS C1P.lS C1P.mS i

@[expose] noncomputable def C1P.rc (g : Nat) : Bool := rcOK C1P.rcS E6.V g

@[expose] noncomputable def C1P.pw (k : Nat) : Bool := pwOK E6.RT C1.REPS E6.PAR C1P.PW k

@[expose] noncomputable def C1P.sw (q : Nat) : Bool :=
  swOK C1P.uS C1P.rcS C1P.lS C1P.mS C1P.LF C1.REPS C1P.START q

@[expose] noncomputable def C1P.leaf (L : Nat) : Bool :=
  pleaf C1P.rcS C1P.LF E6.ADJ C1P.PW E6.NEG C1P.START L

end CFSG.KD.TcRes

end
