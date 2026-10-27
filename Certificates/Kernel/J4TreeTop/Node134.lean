module

public import Certificates.Kernel.J4TreeTop.NodeGlue
public import Certificates.Kernel.J4TreeTop.Cover134
public import Certificates.Kernel.J4TreeNode.Facts
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.J4TreeNode.Glue

public section

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4Tree CFSG.KC.J4TreeN CFSG.KC.J4TreeS CFSG.J4Tree.Native CFSG.ASVolI
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT


theorem cov134 :
    TopCover (burnsideJ4NP_Rep 134)
      (topNode134.children.map fun c => burnsideJ4NP_treeElt c.y) := by
  have e : (treeBasis 134).map (ccT tabs) = wB134 := by rw [wC134_eq]; rfl
  refine walk_topCover (H := hd134) (D := fun e => decF 4096 (Data.w134 e)) (R := cv134Rec)
    (cg := cv134G) tabs_ok sx_ok (by rw [wC134_eq]; quickRfl) ?_ ?_ ?_ ?_ <;> rw [e]
  · exact hd134_ok
  · exact w134_all
  · exact cv134_glob
  · exact cv134_all


theorem top134_facts : burnsideJ4NP_TopNodeFacts 134 :=
  burnsideJ4NP_topNodeFacts_of (kids := topNode134.kids) (by decide +kernel)
    (top_facts (i := 8) (d := topNode134) (by norm_num) rfl (by quickRfl) cov134)

end CFSG.KC.J4TreeT
