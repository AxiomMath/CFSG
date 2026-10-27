module

public meta import Lean
meta import Certificates.Kernel.Misc.OmegaSix.MaxGen
public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Certificates.Kernel.Misc.OmegaSix.MaxGen

namespace CFSG.KD.OmegaSix.GenX

open CFSG.CGT.Foote82.OmegaSix

meta def recM1 : List Nat := recTX [numX cr1Mat, numX cr2Mat, numX dc1Mat] 25920

end CFSG.KD.OmegaSix.GenX

#kss_ntree CFSG.KD.OmegaSix.RM1 CFSG.KD.OmegaSix.GenX.recM1
