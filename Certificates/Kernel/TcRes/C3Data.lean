module

public import Certificates.Data.Kernel.TcRes.C3
public import Certificates.Kernel.TcRes.C2MovedData
import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_nat_items_gz CFSG.KD.TcRes.C3 "Certificates/Kernel/TcRes/data/c3.bin.gz"
  2952 9101851116379602981 TG[3] PG[3] ZL COLS XM DD SG KE REPS CM[12] LC[13] LP[13]

#kc_repo #kc_ktree_gz CFSG.KD.TcRes.C3 LF "Certificates/Kernel/TcRes/data/c3tree.bin.gz"
  320 4 38400 34109054361760600

#kc_select CFSG.KD.TcRes.C3 TGs TG 3
#kc_select CFSG.KD.TcRes.C3 PGs PG 3
#kc_select CFSG.KD.TcRes.C3 CMs CM 12
#kc_select CFSG.KD.TcRes.C3 LCs LC 13
#kc_select CFSG.KD.TcRes.C3 LPs LP 13

namespace CFSG.KD.TcRes

open CFSG.TcRes.TK

@[expose] noncomputable def C3.gen (k : Nat) : Bool :=
  genOK E8.RTs E8.X E8.Y E8.PAR C2P.PW (C3.TGs k) (C3.PGs k)

@[expose] noncomputable def C3.zl : Bool := zlOK E8T.MVS C2P.PW C3.ZL

@[expose] noncomputable def C3.cnt : Bool := cntOK E8T.MVS C2P.PW C3.ZL

@[expose] noncomputable def C3.leaf (L : Nat) : Bool :=
  tleaf E8T.MVS C3.PGs C3.LF C2P.PW C3.ZL (fld C3.COLS (nat_lit 8) (nat_lit 0))
    (fld C3.COLS (nat_lit 8) (nat_lit 2)) L

@[expose] noncomputable def C3.cols : Bool := colsOK C2P.PW C3.COLS

@[expose] noncomputable def C3.bx : Bool := bxOK E8.V C3.COLS C3.XM C3.DD

@[expose] noncomputable def C3.root (i : Nat) : Bool :=
  pbW C3.CMs E8.V C3.XM C3.SG C3.KE C3.REPS i

@[expose] noncomputable def C3.sig : Bool := sigOK E8.RTs E8.NEG C2P.PW C3.COLS C3.SG

@[expose] noncomputable def C3.cls : Bool := clsOK C3.CMs E8.V C3.XM C3.SG C3.REPS

@[expose] noncomputable def C3.line (k : Nat) : Bool :=
  lnOK C3.CMs C3.LCs C3.LPs E8.ADJ C2M.POS C2M.DEC C2P.PW C3.COLS C3.SG k

@[expose] noncomputable def C3.lineJ : Bool :=
  lnJ E8.RTs C3.LCs C3.LPs E8.ADJ C2M.POS C2M.DEC E8.NEG C2P.PW C3.COLS C3.SG

@[expose] noncomputable def C3.jok : Bool := jok3 C3.LPs

end CFSG.KD.TcRes

end
