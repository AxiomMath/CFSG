module

public import Certificates.Kernel.J4TreeNode.Tabs
public import Certificates.Data.Kernel.J4TreeNodeChunk
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c05f "Certificates/Kernel/J4TreeNode/data/c05.fld.items" 197220 1158758866845312380
#kc_repo #kc_items_root CFSG.KC.J4TreeN.Data.c05o "Certificates/Kernel/J4TreeNode/data/c05.off.items" 737 15456633716578086546

namespace CFSG.KC.J4TreeN

@[expose] noncomputable def rec05 (j : Nat) : NRec := parseRec (nodeFlds Data.c05f (Data.c05o j))

@[expose] noncomputable def chk05 (j : Nat) : Bool := chunkNodeOK tabs 5 rec05 j

set_option maxRecDepth 400000

#kc_each chk05 0 100

#kc_forall_tree chk05_all (fun j => chk05 j = true) 100 CFSG.KC.J4TreeN.chk05

@[expose] noncomputable def edgeN05 (j : Nat) : Bool := edgeNodeChk 5 rec05 j

#kc_each edgeN05 0 100

#kc_forall_tree edgeN05_all (fun j => edgeN05 j = true) 100 CFSG.KC.J4TreeN.edgeN05

theorem edge05 : edgeChk 5 rec05 = true := edgeChk_of_nodes edgeN05_all

end CFSG.KC.J4TreeN
