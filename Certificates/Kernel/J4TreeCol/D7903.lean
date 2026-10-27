module

public import Certificates.Kernel.J4TreeCol.Mats
public import Certificates.Kernel.J4TreeNode.Tabs
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeCol.Data.col3 "Certificates/Kernel/J4TreeCol/data/col3.items" 99284 14932523335927528835
#kc_repo #kc_items_root CFSG.KC.J4TreeCol.Data.colq3 "Certificates/Kernel/J4TreeCol/data/colq3.items" 2268 16617743154467829076

namespace CFSG.KC.J4TreeCol

@[expose] noncomputable def rec7903 (j : Nat) : CRec := parseCol (decG 4096 (Data.col3 j))

@[expose] noncomputable def pit7903 (p : Nat) : List Nat := decG 3 (Data.colq3 p)

end CFSG.KC.J4TreeCol
