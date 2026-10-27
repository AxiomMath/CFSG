module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi24ThreeData
public import Certificates.Kernel.Sporadic.Fi24Tc.Data
public import Certificates.Data.Kernel.Ssa3Free

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.Fi24Tc

open CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.Fi24Three CFSG.KC.Ssa3

theorem ssa_ok : ssaOK SD tcProg tcNregs = true := by decide +kernel

theorem struct_ok : structS SD = true := by decide +kernel

theorem cmps_ok : cmpsS SD tcNregs tcSpec.facts = true := by decide +kernel

theorem cover_ok : coverS SD tcNregs 2000 tcSpec.facts = true := by decide +kernel

theorem nchunks : SD.cb.length = 239 + 1 := by decide +kernel

theorem wf_ok : tcSpec.wf = true := by decide +kernel

theorem fv0 : SD.fv.getD tcSpec.rA 0 = 0 := by decide +kernel

theorem fv1 : SD.fv.getD tcSpec.rB 0 = 1 := by decide +kernel

end CFSG.KD.Fi24Tc

end
