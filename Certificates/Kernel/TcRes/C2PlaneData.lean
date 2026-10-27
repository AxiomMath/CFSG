module

public import Certificates.Data.Kernel.TcRes.C2Plane
public import Certificates.Kernel.TcRes.TransData
import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_nat_items_gz CFSG.KD.TcRes.C2P "Certificates/Kernel/TcRes/data/c2plane.bin.gz"
  7448 14361977687976289916 PW B0 PV0 MW0 B1 PV1 MW1 U[4] RC[8] L[4] M[4]

#kc_repo #kc_ktree_gz CFSG.KD.TcRes.C2P LF "Certificates/Kernel/TcRes/data/c2planes.bin.gz"
  896 4 90496 6329575052299725584

#kc_select CFSG.KD.TcRes.C2P uS U 4
#kc_select CFSG.KD.TcRes.C2P rcS RC 8
#kc_select CFSG.KD.TcRes.C2P lS L 4
#kc_select CFSG.KD.TcRes.C2P mS M 4
#kc_select CFSG.KD.TcRes.C2P bS B 2

namespace CFSG.KD.TcRes

open CFSG.TcRes.TK

@[expose] noncomputable def C2P.tab (i : Nat) : Bool := tabs5OK C2P.uS C2P.lS C2P.mS i

@[expose] noncomputable def C2P.rc (g : Nat) : Bool := rc5OK C2P.rcS E8.V g

@[expose] noncomputable def C2P.pw : Bool := pw8OK E8.RTs E8T.T0 E8.PAR C2P.PW

@[expose] noncomputable def C2P.k0 : Bool := kOK C2P.rcS E8T.T0 C2P.B0 C2P.PV0 C2P.MW0 (nat_lit 2)

@[expose] noncomputable def C2P.k1 : Bool := kOK C2P.rcS E8T.T0 C2P.B1 C2P.PV1 C2P.MW1 (nat_lit 3)

@[expose] noncomputable def C2P.sw (s : Nat) : Bool := sw5OK C2P.lS C2P.mS C2P.LF s

@[expose] noncomputable def C2P.leaf (L : Nat) : Bool :=
  pleaf5 C2P.rcS C2P.bS C2P.LF E8.ADJ C2P.PW L

end CFSG.KD.TcRes

end
