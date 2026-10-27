module

public import Certificates.Data.Kernel.Fi23Frame.Defs
public import Certificates.Kernel.Fi23K.Tabs

public section

namespace CFSG.KD.Fi23Frame

open CFSG.KC.Fi23Frame CFSG.KD.Fi23K

@[expose] noncomputable def c24670comm : Bool := frComm G frPts
@[expose] noncomputable def c24670trip0 : Bool := frTrip G frPts 0 12
@[expose] noncomputable def c24670trip1 : Bool := frTrip G frPts 12 11
@[expose] noncomputable def c24670rows : Bool := frRows G frPts frMasks

end CFSG.KD.Fi23Frame

end
