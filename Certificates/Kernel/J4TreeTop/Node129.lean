module

public import Certificates.Kernel.J4TreeTop.NodeGlue
public import Certificates.Kernel.J4TreeTop.Cover129
public import Certificates.Kernel.J4TreeNode.Facts
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.J4TreeNode.Glue

public section

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4Tree CFSG.KC.J4TreeN CFSG.KC.J4TreeS CFSG.J4Tree.Native CFSG.ASVolI
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT


theorem cov129 :
    TopCover (burnsideJ4NP_Rep 129)
      (topNode129.children.map fun c => burnsideJ4NP_treeElt c.y) := by
  have e : (treeBasis 129).map (ccT tabs) = wB129 := by rw [wC129_eq]; rfl
  refine walk_topCover (H := hd129) (D := fun e => decF 4096 (Data.w129 e)) (R := cv129Rec)
    (cg := cv129G) tabs_ok sx_ok (by rw [wC129_eq]; quickRfl) ?_ ?_ ?_ ?_ <;> rw [e]
  · exact hd129_ok
  · exact w129_all
  · exact cv129_glob
  · exact cv129_all


theorem top129_facts : burnsideJ4NP_TopNodeFacts 129 :=
  burnsideJ4NP_topNodeFacts_of (kids := topNode129.kids) (by decide +kernel)
    (top_facts (i := 7) (d := topNode129) (by norm_num) rfl (by quickRfl) cov129)

end CFSG.KC.J4TreeT
