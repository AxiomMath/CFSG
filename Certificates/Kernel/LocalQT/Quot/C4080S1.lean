module

public import Certificates.Kernel.LocalQT.Quot.D4080
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import Certificates.Data.Kernel.LocalQT.QuotS

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.C4080

@[expose] noncomputable def famS1 (c : Nat) : Bool :=
  CFSG.KC.LQT.QS.setQ 12 [0, 1, 2, 3, 4] 2 64 RT 122880 17 E PG (Nat.mul (Nat.add c 15) 1024) 1024

end CFSG.KD.LQT.C4080

#kss_each CFSG.KD.LQT.C4080.S1 CFSG.KD.LQT.C4080.famS1 15

end
