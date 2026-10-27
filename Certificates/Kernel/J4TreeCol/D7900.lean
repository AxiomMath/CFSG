module

public import Certificates.Kernel.J4TreeCol.Mats
public import Certificates.Kernel.J4TreeNode.Tabs
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeCol.Data.col0 "Certificates/Kernel/J4TreeCol/data/col0.items" 139175 15811686049207301983
#kc_repo #kc_items_root CFSG.KC.J4TreeCol.Data.colq0 "Certificates/Kernel/J4TreeCol/data/colq0.items" 2784 7621474494011941339

namespace CFSG.KC.J4TreeCol

@[expose] noncomputable def rec7900 (j : Nat) : CRec := parseCol (decG 4096 (Data.col0 j))

@[expose] noncomputable def pit7900 (p : Nat) : List Nat := decG 3 (Data.colq0 p)

end CFSG.KC.J4TreeCol
