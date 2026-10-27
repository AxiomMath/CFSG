module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM22Orb
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspM23Data

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.C4088

open scoped Pointwise
open CFSG.QuasithinUnique.Vol2Native.L239 CFSG.QuasithinUnique.Vol2Native.L239.M23Insp
  CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1

theorem H_closed : ClosedUnder data.gens data.H := by decide +kernel

end CFSG.KD.LQT.C4088

end
