module

public meta import Certificates.Kernel.SporSch.Co1.GenDag
meta import Certificates.Kernel.SporSch.Co1Rank.InGen
public import Certificates.Kernel.SporSch.Co1.GenDag
import CFSG.Assembly.Defs

public section

set_option maxRecDepth 400000

#kss_co1dag CFSG.KD.Co1RankGen.RB CFSG.KD.Co1RankGen.dagB

#kss_co1dag CFSG.KD.Co1RankGen.C1 CFSG.KD.Co1RankGen.dagC1

#kss_co1dag CFSG.KD.Co1RankGen.C2 CFSG.KD.Co1RankGen.dagC2

end
