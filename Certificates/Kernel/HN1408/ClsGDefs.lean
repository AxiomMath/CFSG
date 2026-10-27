module

public import Certificates.Kernel.HN1408.ClsRDefs
public import Certificates.Kernel.HN1408.ClsGData

public section

namespace CFSG.KD.HN1408.ClsR

@[expose] noncomputable def gRep (s : Nat) : Bool := repSl ClsG.R ClsG.P 2800 (Nat.mul 100 s) 100

@[expose] noncomputable def gSort (s : Nat) : Bool :=
  sortSl ClsG.R ClsG.S 2800 30800 (Nat.mul 2200 s) 2200

end CFSG.KD.HN1408.ClsR

end
