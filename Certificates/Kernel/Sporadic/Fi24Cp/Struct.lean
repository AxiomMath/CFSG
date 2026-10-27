module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi24ThreeData
public import Certificates.Kernel.Sporadic.Fi24Cp.Data
public import Certificates.Data.Kernel.Ssa3Free

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.Fi24Cp

open CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.Fi24Three CFSG.KC.Ssa3

theorem ssa_ok : ssaOK SD cpProg cpNregs = true := by decide +kernel

theorem struct_ok : structS SD = true := by decide +kernel

theorem cmps_ok : cmpsS SD cpNregs cpSpec.facts = true := by decide +kernel

theorem cover_ok : coverS SD cpNregs 2000 cpSpec.facts = true := by decide +kernel

theorem nchunks : SD.cb.length = 79 + 1 := by decide +kernel

theorem wf_ok : cpSpec.wf = true := by decide +kernel

theorem fv0 : SD.fv.getD cpSpec.rA 0 = 0 := by decide +kernel

theorem fv1 : SD.fv.getD cpSpec.rB 0 = 1 := by decide +kernel

end CFSG.KD.Fi24Cp

end
