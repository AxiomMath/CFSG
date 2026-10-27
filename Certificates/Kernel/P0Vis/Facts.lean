module

public import Certificates.Kernel.P0Vis.Tab
public import CFSG.Monster.B.TwoA.Sp8.P0RankInputs
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000

public section

namespace CFSG.KD.P0Vis

open CFSG.KC.P0Vis CFSG.Monster.B.TwoA.Sp8.WordRel

@[expose] noncomputable def factsOK (i : Nat) : Bool :=
  (List.range 6).all fun t => factOK p0Data FK FC (6 * i + t)

#kc_each CFSG.KD.P0Vis fc812462_ (fun i => factsOK i) 0 59

end CFSG.KD.P0Vis

end
