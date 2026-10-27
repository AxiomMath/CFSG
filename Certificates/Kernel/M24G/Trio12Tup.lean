module

public import Certificates.Data.Kernel.M24G.Trio12
public import Certificates.Kernel.M24G.OctData
public import Certificates.Kernel.M24G.SextData
public import Certificates.Kernel.M24G.Trio12Data

set_option maxRecDepth 400000

public section

namespace CFSG.KC.M24G.T12C

open CFSG.KC.M24G CFSG.Quasithin.H13.AS91.M24G

set_option maxHeartbeats 0 in
theorem tup_ok : tupOK OctD.O (posTree id OctD.O) SL (posTree Native.keyL SL) T12D.lB T12D.U
    T12D.uPar T12D.uGen = true := by
  decide +kernel

end CFSG.KC.M24G.T12C
