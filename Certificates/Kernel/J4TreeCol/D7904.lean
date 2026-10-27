module

public import Certificates.Kernel.J4TreeCol.Mats
public import Certificates.Kernel.J4TreeNode.Tabs
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeCol.Data.col4 "Certificates/Kernel/J4TreeCol/data/col4.items" 58563 7856991092936206193
#kc_repo #kc_items_root CFSG.KC.J4TreeCol.Data.colq4 "Certificates/Kernel/J4TreeCol/data/colq4.items" 1879 4825722668597613754

namespace CFSG.KC.J4TreeCol

@[expose] noncomputable def rec7904 (j : Nat) : CRec := parseCol (decG 4096 (Data.col4 j))

@[expose] noncomputable def pit7904 (p : Nat) : List Nat := decG 3 (Data.colq4 p)

end CFSG.KC.J4TreeCol
