module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.Fi24Seven.Data
public import Certificates.Data.Kernel.Spor.SlpPlan
public import CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K.Data
public import CFSG.Certificates.Kernel.Orders.He.Rels

public section

set_option maxRecDepth 400000

namespace CFSG.KD.F24S

open CFSG.KC.SlpM CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K

@[expose] noncomputable def wc (j : Nat) : Nat := Nat.mul (nat_lit 2) (Nat.add j (nat_lit 3))

@[expose] noncomputable def pureEqs (p : PureSec) : List (List Nat × List Nat) :=
  [([wc p.oX], [wc 64]), ([wc p.oY], [wc 66]),
    (wc p.oh :: wc 64 :: List.replicate p.lam (wc 66), [wc 67, wc p.oh])]

@[expose] noncomputable def eqsK : List (List Nat × List Nat) :=
  [([wc 1085, wc 67], [wc 67, wc 1085]), ([wc 1086, wc 67], [wc 67, wc 1086]),
    ([wc 1082, wc 66], [wc 66, wc 1082]), ([wc 1083, wc 66], [wc 66, wc 1083]),
    ([wc 1084, wc 66], [wc 66, wc 1084])] ++
  (mixedSecs.map fun m => [([wc m.ia], [wc 0]), ([wc m.ib], [wc 1])]).flatten ++
  (pureSecs.map pureEqs).flatten

theorem eqsK_ok : allL eqsK (hasEq lyK eqK nK 2) = true := by quickRfl

theorem relsK_ok : allL pureSecs (fun p => allL CFSG.KD.OrdHe.rels
    fun v => hasEq lyK eqK nK 2 (relC p.ix p.iy v, [])) = true := by quickRfl

theorem nesK_ok : allL pureSecs (fun p => hasEq lyK neK nK 2 ([wc p.ix], [])) = true := by quickRfl

@[expose] noncomputable def pureDataC (p : PureSec) : Bool :=
  secC (WL 2) (pureGens p.lam) p.lo p.hi && secC (WL 2) [p.ix, p.iy] p.hi p.hi2 &&
    decide (p.lo ≤ p.ix) && decide (p.ix < p.hi) && decide (p.lo ≤ p.iy) && decide (p.iy < p.hi) &&
    decide (p.hi ≤ p.oX) && decide (p.oX < p.hi2) && decide (p.hi ≤ p.oY) &&
    decide (p.oY < p.hi2) && decide (p.hi ≤ p.oh) && decide (p.oh < p.hi2) && decide (p.hi2 ≤ 3820)

@[expose] noncomputable def mixedDataC (m : MixedSec) : Bool :=
  secC (WL 2) m.gs m.lo m.hi && decide (m.lo ≤ m.ia) && decide (m.ia < m.hi) &&
    decide (m.lo ≤ m.ib) && decide (m.ib < m.hi) && decide (m.hi ≤ 3820)

theorem pureDataC_ok : allL pureSecs pureDataC = true := by quickRfl

theorem mixedDataC_ok : allL mixedSecs mixedDataC = true := by quickRfl

end CFSG.KD.F24S

end
