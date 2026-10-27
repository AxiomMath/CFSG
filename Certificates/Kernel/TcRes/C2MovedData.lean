module

public import Certificates.Data.Kernel.TcRes.C2Moved
public import Certificates.Kernel.TcRes.C2PlaneData
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_nat_items_gz CFSG.KD.TcRes.C2M "Certificates/Kernel/TcRes/data/c2moved.bin.gz"
  226882 11219785741879709977 POS DEC LT[1038] A[1360]

#kc_select CFSG.KD.TcRes.C2M LS LT 1038
#kc_select CFSG.KD.TcRes.C2M AS A 1360

namespace CFSG.KD.TcRes

open CFSG.TcRes.TK

@[expose] noncomputable def C2M.pos (g : Nat) : Bool := pos8OK E8.V C2M.POS g

@[expose] noncomputable def C2M.dec (g : Nat) : Bool :=
  dec8OK E8T.QS E8T.MVS E8.V C2M.POS C2M.DEC g

@[expose] noncomputable def C2M.line (l : Nat) : Bool :=
  line8OK E8.ADJ C2M.POS C2M.DEC C2P.PW C2P.rcS C2P.bS (C2M.LS l)

@[expose] noncomputable def C2M.leaf (L : Nat) : Bool :=
  mleaf8 E8.ADJ C2M.POS C2M.DEC C2P.PW C2P.rcS C2P.bS C2M.LS C2P.LF C2M.AS L

end CFSG.KD.TcRes

end
