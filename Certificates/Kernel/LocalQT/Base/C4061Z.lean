module

public import Certificates.Kernel.LocalQT.Base.C4061D
public import Certificates.Kernel.LocalQT.Base.C4076D
public import Certificates.Kernel.LocalQT.Base.C4143D
public import Certificates.Kernel.LocalQT.Base.C4143E
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import Certificates.Data.Kernel.LocalQT.X1R
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1RuData
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRuInputs

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.C4061

@[expose] noncomputable def famZ (c : Nat) : Bool :=
  CFSG.KC.LQT.XR.zcS 4060 12 CFSG.QuasithinUnique.K1.SporadicPerm.ruB
    CFSG.QuasithinUnique.K1.SporadicPerm.ruQp C4143.TF C4143.E C4076.BO 16384 TF
    CFSG.QuasithinUnique.Setup.X1.ruNodes1 CFSG.QuasithinUnique.Setup.X1.ruNodes2
    CFSG.QuasithinUnique.Setup.X1.ruNodes3 (Nat.mul c 512) 512

end CFSG.KD.LQT.C4061

#kss_each CFSG.KD.LQT.C4061.Z CFSG.KD.LQT.C4061.famZ 32

end
