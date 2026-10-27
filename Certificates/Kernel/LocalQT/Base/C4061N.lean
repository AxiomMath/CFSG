module

public import Certificates.Kernel.LocalQT.Base.C4061D
public import Certificates.Kernel.LocalQT.Base.C4061L
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import Certificates.Data.Kernel.LocalQT.BaseT

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.C4061

@[expose] noncomputable def famN (c : Nat) : Bool :=
  CFSG.KC.LQT.BT.nodesT 4060 12 P2 TF (Nat.mul c 8) 8

end CFSG.KD.LQT.C4061

#kss_each CFSG.KD.LQT.C4061.N CFSG.KD.LQT.C4061.famN 67

end
