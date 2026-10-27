module

public import Certificates.Data.Kernel.LocalComp.CubParts
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi24SevenData
import Certificates.Kernel.LocalQT.Cmd
import Certificates.Kernel.LocalComp.PartsCmd
import all CFSG.Blueprint.NativeSporadic
public meta import Certificates.Data.Kernel.LocalComp.CubParts
public meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi24SevenData

set_option maxRecDepth 100000

public meta section

meta def CFSG.KD.LC.F3.fi24Sylow7HE : CFSG.SectionRank.Native.Data :=
  CFSG.AGLEmbedding.SporCubic.fi24Sylow7HData.extData

end

#lqt_prog_part CFSG.KD.LC.F3.Fi24Sylow7H CFSG.KD.LC.F3.fi24Sylow7HE 3 781
  CFSG.Blueprint.NativeSporadic.Fi24primeSeed1 CFSG.Blueprint.NativeSporadic.Fi24primeSeed2 0 4
