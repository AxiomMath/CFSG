module

public import Certificates.Kernel.J4TreeTop.Tgts
public import Certificates.Kernel.J4TreeTop.Cover3
public import Certificates.Kernel.J4TreeNode.Facts
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.J4TreeNode.Glue

public section

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4Tree CFSG.KC.J4TreeN CFSG.KC.J4TreeS CFSG.J4Tree.Native CFSG.ASVolI
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT


theorem cov3 :
    TopCover (burnsideJ4NP_Rep 3) (topNode3.children.map fun c => burnsideJ4NP_treeElt c.y) := by
  have e : (treeBasis 3).map (ccT tabs) = wB3 := by rw [wC3_eq]; rfl
  refine walk_topCover (H := hd3) (D := fun e => decF 4096 (Data.w3 e)) (R := cv3Rec)
    (cg := cv3G) tabs_ok sx_ok (by rw [wC3_eq]; quickRfl) ?_ ?_ ?_ ?_ <;> rw [e]
  · exact hd3_ok
  · exact w3_all
  · exact cv3_glob
  · exact cv3_all


theorem top3_facts : burnsideJ4NP_TopNodeFacts 3 :=
  burnsideJ4NP_topNodeFacts_of (kids := topNode3.kids) (by decide +kernel)
    (top_facts_ts (i := 2) (d := topNode3) (ts := [7, 107]) (by norm_num) rfl
      (by simp [topTgt7, topTgt107]) (by quickRfl) cov3)

end CFSG.KC.J4TreeT
