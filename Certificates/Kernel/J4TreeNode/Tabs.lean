module

public import Certificates.Data.Kernel.J4TreeNode
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_blocked_root CFSG.KC.J4TreeN.Data.eta "Certificates/Kernel/J4TreeNode/data/eta.bin" 4 8 22300745198530623141535718272648361505980415 65536 2944043283121724651
#kc_repo #kc_blocked_root CFSG.KC.J4TreeN.Data.kel "Certificates/Kernel/J4TreeNode/data/kel.bin" 4 8 22300745198530623141535718272648361505980415 32768 7265395972540808222
#kc_repo #kc_blocked_root CFSG.KC.J4TreeN.Data.w4 "Certificates/Kernel/J4TreeNode/data/w4.bin" 4 8 22300745198530623141535718272648361505980415 131072 11287902186285986862
#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.sx "Certificates/Kernel/J4TreeNode/data/sext.items" 260 11932754894820958184

namespace CFSG.KC.J4TreeN

@[expose] noncomputable def tabs : Tabs := ⟨Data.eta, Data.kel, Data.w4, Data.sx 0⟩

set_option maxRecDepth 400000 in
theorem tabs_ok : tabsOK tabs = true := by quickRfl

end CFSG.KC.J4TreeN
