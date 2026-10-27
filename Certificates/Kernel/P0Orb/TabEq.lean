module

public import Certificates.Kernel.P0Orb.Tab
public import CFSG.Monster.B.TwoA.Sp8.P0StructInputs

public section

namespace CFSG.KD.P0Orb

open CFSG.Monster.B.TwoA.Sp8.WordRel

theorem gc_eq : GC = uConjLN.map (·.map (·.1)) := by decide +kernel

theorem beta_eq : beta = lCommN := by decide +kernel

end CFSG.KD.P0Orb

end
