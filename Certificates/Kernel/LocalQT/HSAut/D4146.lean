module

public import Certificates.Kernel.LocalQT.PEnumD
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.LocalQT.HSAutN
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutNodesCheckInputs
public import CFSG.Assembly.LowTwoRankDefs
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutOuter
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdInputs3
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19UHSFusion

public section

set_option maxRecDepth 400000

namespace CFSG.KD.LQT.HN

open CFSG.PSL3Four.Native CFSG.QuasithinUnique.Id2519.HSAut

meta def gM : Array (Array Nat) := gensA0

meta def idM : Array Nat := idTab 3850

meta def xM : Array (Array Nat) := #[gTab, giTab, y1Tab, y2Tab, cTab]

end CFSG.KD.LQT.HN

#kpenum_d CFSG.KD.LQT.HN.A 3850 12 false CFSG.KD.LQT.HN.gM CFSG.KD.LQT.HN.gM CFSG.KD.LQT.HN.idM
  7680
#kmisc_packarrs CFSG.KD.LQT.HN.X CFSG.KD.LQT.HN.xM 12

end
