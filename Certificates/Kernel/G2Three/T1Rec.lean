module

public meta import Lean
meta import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.T1Data
public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import CFSG.Assembly.LowTwoRankDefs
meta import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FactsL

namespace CFSG.KD.G2Three.T1W.Gen

open CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.Tab

meta def rtV : List Nat := ((t1G ()).rt.toList.map Array.toList).flatten
meta def paV : List Nat := (t1G ()).par.toList.map (·.1)
meta def pbV : List Nat := (t1G ()).par.toList.map (·.2)

end CFSG.KD.G2Three.T1W.Gen

#kss_ntree CFSG.KD.G2Three.T1W.RT CFSG.KD.G2Three.T1W.Gen.rtV
#kss_ntree CFSG.KD.G2Three.T1W.PA CFSG.KD.G2Three.T1W.Gen.paV
#kss_ntree CFSG.KD.G2Three.T1W.PB CFSG.KD.G2Three.T1W.Gen.pbV
