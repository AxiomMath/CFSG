module

public import Certificates.Kernel.LocalQT.Base.C7145D
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import Certificates.Data.Kernel.LocalQT.BaseT
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieuInputs
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Schreier.M23

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.C7145

@[expose] noncomputable def famN (c : Nat) : Bool :=
  CFSG.KC.LQT.BT.nodesT 24 5 CFSG.QuasithinUnique.K1.SporadicPerm.m24Prog TF (Nat.mul c 8) 8

end CFSG.KD.LQT.C7145

#kss_each CFSG.KD.LQT.C7145.N CFSG.KD.LQT.C7145.famN 29

end
