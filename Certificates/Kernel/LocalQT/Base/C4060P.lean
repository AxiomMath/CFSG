module

public import Certificates.Kernel.LocalQT.Base.C4060D
public import Certificates.Kernel.LocalQT.Base.C4060T
public import Certificates.Kernel.LocalQT.Base.C4060U
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import Certificates.Data.Kernel.LocalQT.RankO

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.C4060

@[expose] noncomputable def famRQ (j : Nat) : Bool :=
  CFSG.KC.LQT.PP.allR (Nat.mul j 64) 64 (CFSG.KC.LQT.RB.rowRQ 9 3 512 PT CT MQT)

@[expose] noncomputable def famEQ (j : Nat) : Bool :=
  CFSG.KC.LQT.PP.allR (Nat.mul j 64) 64 (CFSG.KC.LQT.RB.eqvRU 9 3 512 CT MQT TUPT TUIT)

@[expose] noncomputable def famZQ (_ : Nat) : Bool :=
  CFSG.KC.Ord.andB
    (Nat.ble (CFSG.KC.LQT.L.lenA (CFSG.KC.LQT.RB.invsB 512 (CFSG.KC.LQT.RB.mulRQ 9 MQT)))
      (Nat.mul 87 1))
    (Nat.beq (CFSG.KC.LQT.RB.mulRQ 9 MQT 10 10) 0)

@[expose] noncomputable def fam (j : Nat) : Bool :=
  CFSG.KC.LQT.RB.rankBO 9 512 MQT 3 10 (Nat.mul j 1) 1

end CFSG.KD.LQT.C4060

#kss_each CFSG.KD.LQT.C4060.Q CFSG.KD.LQT.C4060.famRQ 8

#kss_each CFSG.KD.LQT.C4060.EQ CFSG.KD.LQT.C4060.famEQ 8

#kss_each CFSG.KD.LQT.C4060.ZQ CFSG.KD.LQT.C4060.famZQ 1

#kss_each CFSG.KD.LQT.C4060.P CFSG.KD.LQT.C4060.fam 87

end
