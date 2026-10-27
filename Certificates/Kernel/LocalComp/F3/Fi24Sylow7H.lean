module

public import Certificates.Kernel.LocalComp.F3.Fi24Sylow7H.P3
import Certificates.Kernel.LocalQT.Cmd
import Certificates.Kernel.LocalComp.PartsCmd
import all CFSG.Blueprint.NativeSporadic
public meta import Certificates.Data.Kernel.LocalComp.CubParts
public meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi24SevenData
public import CFSG.Certificates.Kernel.LocalQT.Steps

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LC.F3

@[expose] def fi24Sylow7HAs : CFSG.SectionRank.Native.Data :=
  CFSG.AGLEmbedding.SporCubic.fi24Sylow7HData.asData

end CFSG.KD.LC.F3

end

public meta section

meta def CFSG.KD.LC.F3.fi24Sylow7HM : CFSG.SectionRank.Native.CubData :=
  CFSG.AGLEmbedding.SporCubic.fi24Sylow7HData

end

#lqt_sr_cubx CFSG.KD.LC.F3.Fi24Sylow7H CFSG.KD.LC.F3.fi24Sylow7HM CFSG.KD.LC.F3.fi24Sylow7HAs 3 781
  CFSG.Blueprint.NativeSporadic.Fi24primeSeed1 CFSG.Blueprint.NativeSporadic.Fi24primeSeed2
