module

public import Certificates.Kernel.J4TreeCol.Mats
public import Certificates.Kernel.J4TreeNode.Tabs
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeCol.Data.col1 "Certificates/Kernel/J4TreeCol/data/col1.items" 122900 2087298120695169712
#kc_repo #kc_items_root CFSG.KC.J4TreeCol.Data.colq1 "Certificates/Kernel/J4TreeCol/data/colq1.items" 2513 8004776893638956883

namespace CFSG.KC.J4TreeCol

@[expose] noncomputable def rec7901 (j : Nat) : CRec := parseCol (decG 4096 (Data.col1 j))

@[expose] noncomputable def pit7901 (p : Nat) : List Nat := decG 3 (Data.colq1 p)

end CFSG.KC.J4TreeCol
