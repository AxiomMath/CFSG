module

public import Certificates.Kernel.J2Dc.Defs
public import Certificates.Kernel.SporSch.Ru.RowsGen

set_option maxRecDepth 100000

public noncomputable section

namespace CFSG.KD.J2Dc

@[expose] def ptc (i : Nat) : Bool := CFSG.KC.SLDc.ptChunk C D i

end CFSG.KD.J2Dc

#kss_each CFSG.KD.J2Dc.PtK CFSG.KD.J2Dc.ptc 97

end
