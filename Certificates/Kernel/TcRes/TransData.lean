module

public import Certificates.Data.Kernel.TcRes.Trans
public import Certificates.Kernel.TcRes.Data
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_nat_items_gz CFSG.KD.TcRes.E8T "Certificates/Kernel/TcRes/data/e8trans.bin.gz"
  543528 16658699900848419516 T0 BT Q[8] MV[240] ND

#kc_select CFSG.KD.TcRes.E8T QS Q 8
#kc_select CFSG.KD.TcRes.E8T MVS MV 240

namespace CFSG.KD.TcRes

open CFSG.TcRes.TK

@[expose] noncomputable def E8T.q (i : Nat) : Bool := qOK E8T.QS E8.V i

@[expose] noncomputable def E8T.mv (x : Nat) : Bool := mvOK E8T.QS E8.Y E8T.MVS x

@[expose] noncomputable def E8T.bt : Bool := btOK E8.RTs E8.ADJ E8T.BT E8T.T0

@[expose] noncomputable def E8T.nd (j : Nat) : Bool := ndOK E8.X E8.Y E8.RTs E8T.MVS E8T.ND E8T.T0 j

@[expose] noncomputable def E8T.nd0 : Bool := nd0OK E8T.ND E8T.T0

end CFSG.KD.TcRes

end
