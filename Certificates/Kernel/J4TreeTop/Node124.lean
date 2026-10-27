module

public import Certificates.Kernel.J4TreeTop.NodeGlue
public import Certificates.Kernel.J4TreeTop.Cover124
public import Certificates.Kernel.J4TreeNode.Facts
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.J4TreeNode.Glue

public section

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4Tree CFSG.KC.J4TreeN CFSG.KC.J4TreeS CFSG.J4Tree.Native CFSG.ASVolI
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT


theorem cov124 :
    TopCover (burnsideJ4NP_Rep 124)
      (topNode124.children.map fun c => burnsideJ4NP_treeElt c.y) := by
  have e : (treeBasis 124).map (ccT tabs) = wB124 := by rw [wC124_eq]; rfl
  refine walk_topCover (H := hd124) (D := fun e => decF 4096 (Data.w124 e)) (R := cv124Rec)
    (cg := cv124G) tabs_ok sx_ok (by rw [wC124_eq]; quickRfl) ?_ ?_ ?_ ?_ <;> rw [e]
  · exact hd124_ok
  · exact w124_all
  · exact cv124_glob
  · exact cv124_all


theorem top124_facts : burnsideJ4NP_TopNodeFacts 124 :=
  burnsideJ4NP_topNodeFacts_of (kids := topNode124.kids) (by decide +kernel)
    (top_facts (i := 6) (d := topNode124) (by norm_num) rfl (by quickRfl) cov124)

end CFSG.KC.J4TreeT
