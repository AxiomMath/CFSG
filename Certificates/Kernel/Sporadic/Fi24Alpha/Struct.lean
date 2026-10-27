module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaFi24Data
public import Certificates.Kernel.Sporadic.Fi24Alpha.Data
public import Certificates.Data.Kernel.Ssa3Free
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaWordDefs

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.Fi24Alpha

open CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaFi24 CFSG.KC.Ssa3

theorem ssa_ok : ssaOK SD fi24Prog fi24Nregs = true := by decide +kernel

theorem struct_ok : structS SD = true := by decide +kernel

theorem cmps_ok : cmpsS SD fi24Nregs (fi24Mod.modFactsW 3 fi24Tops) = true := by decide +kernel

theorem cover_ok : coverS SD fi24Nregs 2000 (fi24Mod.modFactsW 3 fi24Tops) = true := by
  decide +kernel

theorem nchunks : SD.cb.length = 110 + 1 := by decide +kernel

end CFSG.KD.Fi24Alpha

end
