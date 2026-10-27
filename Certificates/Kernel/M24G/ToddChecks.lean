module

public import Certificates.Data.Kernel.M24G.Todd
public import Certificates.Kernel.M24G.TrioData
public import Certificates.Kernel.M24G.SextData

set_option maxRecDepth 400000

public section

namespace CFSG.KC.M24G

set_option maxHeartbeats 0 in
theorem toddUniq_ok : toddUniqF = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem toddInt_ok : toddIntCk TL.toArray SL.toArray = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem toddSext_ok : toddSextCk SL = true := by decide +kernel

end CFSG.KC.M24G
