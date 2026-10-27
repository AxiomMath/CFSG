module

public import Certificates.Kernel.J4TreeTop.NodeGlue
public import Certificates.Kernel.J4TreeTop.Cover7
public import Certificates.Kernel.J4TreeNode.Facts
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.J4TreeNode.Glue

public section

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4Tree CFSG.KC.J4TreeN CFSG.KC.J4TreeS CFSG.J4Tree.Native CFSG.ASVolI
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

theorem cov7 :
    TopCover (burnsideJ4NP_Rep 7) (topNode7.children.map fun c => burnsideJ4NP_treeElt c.y) := by
  have e : (treeBasis 7).map (ccT tabs) = wB7 := by rw [wC7_eq]; rfl
  refine walk_topCover (H := hd7) (D := fun e => decF 4096 (Data.w7 e)) (R := cv7Rec)
    (cg := cv7G) tabs_ok sx_ok (by rw [wC7_eq]; quickRfl) ?_ ?_ ?_ ?_ <;> rw [e]
  · exact hd7_ok
  · exact w7_all
  · exact cv7_glob
  · exact cv7_all

theorem top7_facts : burnsideJ4NP_TopNodeFacts 7 :=
  burnsideJ4NP_topNodeFacts_of (kids := topNode7.kids) (by decide +kernel)
    (top_facts (i := 4) (d := topNode7) (by norm_num) rfl (by quickRfl) cov7)

end CFSG.KC.J4TreeT
