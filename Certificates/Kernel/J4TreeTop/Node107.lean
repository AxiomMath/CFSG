module

public import Certificates.Kernel.J4TreeTop.NodeGlue
public import Certificates.Kernel.J4TreeTop.Cover107
public import Certificates.Kernel.J4TreeNode.Facts
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.J4TreeNode.Glue

public section

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4Tree CFSG.KC.J4TreeN CFSG.KC.J4TreeS CFSG.J4Tree.Native CFSG.ASVolI
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT


theorem cov107 :
    TopCover (burnsideJ4NP_Rep 107)
      (topNode107.children.map fun c => burnsideJ4NP_treeElt c.y) := by
  have e : (treeBasis 107).map (ccT tabs) = wB107 := by rw [wC107_eq]; rfl
  refine walk_topCover (H := hd107) (D := fun e => decF 4096 (Data.w107 e)) (R := cv107Rec)
    (cg := cv107G) tabs_ok sx_ok (by rw [wC107_eq]; quickRfl) ?_ ?_ ?_ ?_ <;> rw [e]
  · exact hd107_ok
  · exact w107_all
  · exact cv107_glob
  · exact cv107_all


theorem top107_facts : burnsideJ4NP_TopNodeFacts 107 :=
  burnsideJ4NP_topNodeFacts_of (kids := topNode107.kids) (by decide +kernel)
    (top_facts (i := 5) (d := topNode107) (by norm_num) rfl (by quickRfl) cov107)

end CFSG.KC.J4TreeT
