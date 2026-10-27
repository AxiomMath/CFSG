module

public import Certificates.Data.Kernel.M24G.Img
public import Certificates.Data.Kernel.M24G.ListChecks
public import Certificates.Kernel.M24G.OctData

set_option maxRecDepth 100000

public section

namespace CFSG.KC.M24G.OctC

open CFSG.KC.M24G CFSG.KC.ONanSmall CFSG.Quasithin.H13.AS91.M24G

theorem tabs_eq : [imgTab Native.pATab.toList, imgTab Native.pBTab.toList,
    imgTab Native.pBiTab.toList] = [OctD.bA, OctD.bB, OctD.bBi] := by
  decide +kernel

theorem replay : replayOK id [imgF OctD.bA, imgF OctD.bB, imgF OctD.bBi] 255 1000 OctD.O OctD.par
    OctD.gen (posTree id OctD.O) = true := by
  decide +kernel

theorem length : OctD.O.length = 759 := by decide +kernel

theorem items : OctD.O.all octItem = true := by decide +kernel

theorem base : baseOK (posTree id OctD.O) = true := by decide +kernel

end CFSG.KC.M24G.OctC
