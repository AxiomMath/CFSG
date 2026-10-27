module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4Aff2A
public import CFSG.Sporadic.J4.QTRankInvData
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4Aff2A.Data.w "Certificates/Kernel/J4Aff2A/data/w.items" 2100 16648722588124304797

namespace CFSG.KC.J4Aff2A

open CFSG.KC.J4TreeN CFSG.Sporadic.J4.QT

set_option maxRecDepth 400000 in
theorem ch7853_all : allOK tabs invData Data.w = true := by quickRfl

end CFSG.KC.J4Aff2A
