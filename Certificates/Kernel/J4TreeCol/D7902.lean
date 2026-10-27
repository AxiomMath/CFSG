module

public import Certificates.Kernel.J4TreeCol.Mats
public import Certificates.Kernel.J4TreeNode.Tabs
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeCol.Data.col2 "Certificates/Kernel/J4TreeCol/data/col2.items" 125030 18014381383584741971
#kc_repo #kc_items_root CFSG.KC.J4TreeCol.Data.colq2 "Certificates/Kernel/J4TreeCol/data/colq2.items" 2556 15860399130520801803

namespace CFSG.KC.J4TreeCol

@[expose] noncomputable def rec7902 (j : Nat) : CRec := parseCol (decG 4096 (Data.col2 j))

@[expose] noncomputable def pit7902 (p : Nat) : List Nat := decG 3 (Data.colq2 p)

end CFSG.KC.J4TreeCol
