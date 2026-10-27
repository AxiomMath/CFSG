module

public import Certificates.Kernel.J4TreeTop.Tgts
public import Certificates.Kernel.J4TreeTop.Cover2
public import Certificates.Kernel.J4TreeNode.Facts
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.J4TreeNode.Glue

public section

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4Tree CFSG.KC.J4TreeN CFSG.KC.J4TreeS CFSG.J4Tree.Native CFSG.ASVolI
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT


theorem cov2 :
    TopCover (burnsideJ4NP_Rep 2) (topNode2.children.map fun c => burnsideJ4NP_treeElt c.y) := by
  have e : (treeBasis 2).map (ccT tabs) = wB2 := by rw [wC2_eq]; rfl
  refine walk_topCover (H := hd2) (D := fun e => decF 4096 (Data.w2 e)) (R := cv2Rec)
    (cg := cv2G) tabs_ok sx_ok (by rw [wC2_eq]; quickRfl) ?_ ?_ ?_ ?_ <;> rw [e]
  · exact hd2_ok
  · exact w2_all
  · exact cv2_glob
  · exact cv2_all


theorem top2_facts : burnsideJ4NP_TopNodeFacts 2 :=
  burnsideJ4NP_topNodeFacts_of (kids := topNode2.kids) (by decide +kernel)
    (top_facts_ts (i := 1) (d := topNode2) (ts := [124, 129]) (by norm_num) rfl
      (by simp [topTgt124, topTgt129]) (by quickRfl) cov2)

end CFSG.KC.J4TreeT
