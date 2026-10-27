module

public import Certificates.Data.Kernel.P0VisBd
public import CFSG.Monster.B.TwoA.Sp8.P0RankInputs

public section

namespace CFSG.KD.P0Vis

open CFSG.KC.P0Vis CFSG.Monster.B.TwoA.Sp8.WordRel

theorem bd : bdOK p0Data = true := by decide +kernel

theorem bdNeg : bdOK ⟨[[512]], [], [], [], []⟩ = false := by decide +kernel

end CFSG.KD.P0Vis

end
