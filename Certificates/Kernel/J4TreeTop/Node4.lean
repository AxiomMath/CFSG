module

public import Certificates.Kernel.J4TreeTop.Tgts
public import Certificates.Kernel.J4TreeTop.Cover4
public import Certificates.Kernel.J4TreeNode.Facts
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.J4TreeNode.Glue

public section

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4Tree CFSG.KC.J4TreeN CFSG.KC.J4TreeS CFSG.J4Tree.Native CFSG.ASVolI
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT


theorem cov4 :
    TopCover (burnsideJ4NP_Rep 4) (topNode4.children.map fun c => burnsideJ4NP_treeElt c.y) := by
  have e : (treeBasis 4).map (ccT tabs) = wB4 := by rw [wC4_eq]; rfl
  refine walk_topCover (H := hd4) (D := fun e => decF 4096 (Data.w4 e)) (R := cv4Rec)
    (cg := cv4G) tabs_ok sx_ok (by rw [wC4_eq]; quickRfl) ?_ ?_ ?_ ?_ <;> rw [e]
  · exact hd4_ok
  · exact w4_all
  · exact cv4_glob
  · exact cv4_all


theorem top4_facts : burnsideJ4NP_TopNodeFacts 4 :=
  burnsideJ4NP_topNodeFacts_of (kids := topNode4.kids) (by decide +kernel)
    (top_facts_ts (i := 3) (d := topNode4) (ts := [7, 134]) (by norm_num) rfl
      (by simp [topTgt7, topTgt134]) (by quickRfl) cov4)

end CFSG.KC.J4TreeT
