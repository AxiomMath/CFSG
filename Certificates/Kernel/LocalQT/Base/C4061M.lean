module

public import Certificates.Kernel.LocalQT.Base.C4061E
public import Certificates.Kernel.LocalQT.Base.C4061L
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import Certificates.Data.Kernel.LocalQT.BaseT

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.C4061

@[expose] noncomputable def famM (c : Nat) : Bool :=
  CFSG.KC.LQT.BT.nodesT 4060 12 WP Wp.TF (Nat.mul c 16) 16

end CFSG.KD.LQT.C4061

#kss_each CFSG.KD.LQT.C4061.M CFSG.KD.LQT.C4061.famM 324

end
