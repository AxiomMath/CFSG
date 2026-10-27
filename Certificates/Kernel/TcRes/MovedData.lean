module

public import Certificates.Data.Kernel.TcRes.Moved
public import Certificates.Kernel.TcRes.PlaneData
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_nat_items_gz CFSG.KD.TcRes.C1M "Certificates/Kernel/TcRes/data/c1moved.bin.gz"
  95447 13187498005453342238 POS DEC LT[234] A[222]

#kc_select CFSG.KD.TcRes.C1M LS LT 234
#kc_select CFSG.KD.TcRes.C1M AS A 222

namespace CFSG.KD.TcRes

open CFSG.TcRes.TK

@[expose] noncomputable def C1M.pos (g : Nat) : Bool := posOK E6.V C1M.POS g

@[expose] noncomputable def C1M.dec (g : Nat) : Bool := decOK E6.RT E6.X E6.Y C1M.POS C1M.DEC g

@[expose] noncomputable def C1M.line (l : Nat) : Bool :=
  lineOK E6.RT E6.X E6.Y E6.ADJ C1M.POS C1M.DEC E6.NEG C1P.PW C1P.rcS (C1M.LS l)

@[expose] noncomputable def C1M.leaf (L : Nat) : Bool :=
  mleaf E6.RT E6.X E6.Y E6.ADJ C1M.POS C1M.DEC E6.NEG C1P.PW C1P.rcS C1M.LS C1P.LF C1M.AS
    C1P.START L

end CFSG.KD.TcRes

end
