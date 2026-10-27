module

public import Certificates.Data.Kernel.TcRes.Defs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatItemsGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_nat_items_gz CFSG.KD.TcRes.E6 "Certificates/Kernel/TcRes/data/e6.bin.gz"
  9937 8041291004203825057 YC[6] V X Y NEG PAR SRT ADJ RT

#kc_repo #kc_nat_items_gz CFSG.KD.TcRes.E8 "Certificates/Kernel/TcRes/data/e8.bin.gz"
  86163 3739864336902232551 YC[8] V X Y NEG PAR SRT ADJ RT[240]

#kc_select CFSG.KD.TcRes.E6 yc YC 6
#kc_select CFSG.KD.TcRes.E8 yc YC 8
#kc_select CFSG.KD.TcRes.E8 RTs RT 240

namespace CFSG.KD.TcRes

open CFSG.TcRes.TK

@[expose] noncomputable def E6.rt (g : Nat) : Nat := fld E6.RT (nat_lit 504) g

@[expose] noncomputable def E6.root (i : Nat) : Bool :=
  rootOK (nat_lit 6) (nat_lit 72) (nat_lit 7) E6.yc E6.rt E6.V E6.X E6.Y E6.NEG E6.PAR i

@[expose] noncomputable def E6.row (g : Nat) : Bool :=
  rowOK (nat_lit 6) (nat_lit 72) (nat_lit 7) E6.rt E6.V E6.X E6.Y E6.ADJ g

@[expose] noncomputable def E6.srt : Bool :=
  srtOK (nat_lit 6) (nat_lit 72) (nat_lit 7) E6.yc E6.V E6.SRT

@[expose] noncomputable def E8.root (i : Nat) : Bool :=
  rootOK (nat_lit 8) (nat_lit 240) (nat_lit 8) E8.yc E8.RTs E8.V E8.X E8.Y E8.NEG E8.PAR i

@[expose] noncomputable def E8.row (g : Nat) : Bool :=
  rowOK (nat_lit 8) (nat_lit 240) (nat_lit 8) E8.RTs E8.V E8.X E8.Y E8.ADJ g

@[expose] noncomputable def E8.srt : Bool :=
  srtOK (nat_lit 8) (nat_lit 240) (nat_lit 8) E8.yc E8.V E8.SRT

end CFSG.KD.TcRes

end
