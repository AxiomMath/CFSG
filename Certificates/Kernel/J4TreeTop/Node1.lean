module

public import Certificates.Kernel.J4TreeTop.Tgts
public import Certificates.Kernel.J4TreeTop.Cover1
public import Certificates.Kernel.J4TreeNode.Facts
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.J4TreeNode.Glue

public section

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4Tree CFSG.KC.J4TreeN CFSG.KC.J4TreeS CFSG.J4Tree.Native CFSG.ASVolI
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

theorem cov1 :
    TopCover (burnsideJ4NP_Rep 1) (topNode1.children.map fun c => burnsideJ4NP_treeElt c.y) :=
  node1_topCover (z := 1131) (D := ecRec) (R := c1Rec) tabs_ok sx_ok (by decide) c1_glob ec_all
    c1_all (by decide +kernel)

theorem top1_facts : burnsideJ4NP_TopNodeFacts 1 :=
  burnsideJ4NP_topNodeFacts_of (kids := topNode1.kids) (by decide +kernel)
    (top_facts_ts (i := 0) (d := topNode1) (ts := [2, 3, 4, 7]) (by norm_num) rfl
      (by simp [topTgt2, topTgt3, topTgt4, topTgt7]) (by quickRfl) cov1)

end CFSG.KC.J4TreeT
