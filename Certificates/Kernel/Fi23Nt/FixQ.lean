module

public import Certificates.Data.Kernel.Fi23Nt.FixQDefs
public import Certificates.Kernel.Fi23K.Tabs
public import Certificates.Kernel.Fi23Nt.DataE
import CFSG.Certificates.Kernel.BabyMonster.Load

public section

namespace CFSG.KD.Fi23Nt

open CFSG.KC.Fi23Nt

@[expose] noncomputable def fixQB : Bool := fixQK CFSG.KD.Fi23K.G eBW

@[expose] noncomputable def negFixQ : Bool := Bool.not (fixQK CFSG.KD.Fi23K.G eCW)

end CFSG.KD.Fi23Nt

#bm_bool CFSG.KD.Fi23Nt tw101701fq (fixQB)

#bm_bool CFSG.KD.Fi23Nt tw101701negFq (negFixQ)
