module

public import Certificates.Data.Kernel.M24G.Trio12
public import Certificates.Kernel.M24G.OctData
public import Certificates.Kernel.M24G.SextData
public import Certificates.Kernel.M24G.Trio12Data
public import Certificates.Data.Kernel.M24G.StmtB
import CFSG.Certificates.Kernel.M24G.StmtBSound
public import Certificates.Kernel.M24G.ReplayB
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CFSG.KC.M24G.T12C

open CFSG.KC.M24G CFSG.KC.ONanSmall CFSG.Quasithin.H13.AS91.M24G

@[expose] def stepTupT (OT : IxTree Nat) (posO : KTree (Nat × Nat)) (ST : IxTree (List Nat))
    (posS : KTree (Nat × Nat)) (b : Nat × Nat × Nat) (c : Nat) : Nat :=
  let a := idxK posO 759 (imgF b (getT OT (c % 759)))
  let a' := idxK posO 759 (imgF b (getT OT (c / 759 % 759)))
  let u := idxK posS 1771 (Native.keyL (sortN ((getT ST (c / 759 / 759 % 1771)).map (imgF b))))
  let v := idxK posS 1771
    (Native.keyL (sortN ((getT ST (c / 759 / 759 / 1771 % 1771)).map (imgF b))))
  let w := idxK posS 1771
    (Native.keyL (sortN ((getT ST (c / 759 / 759 / 1771 / 1771 % 1771)).map (imgF b))))
  if a < 759 && a' < 759 && u < 1771 && v < 1771 && w < 1771 then Native.encTup a a' u v w
  else Native.nTup

@[expose] def tupOKT (OT : IxTree Nat) (posO : KTree (Nat × Nat)) (ST : IxTree (List Nat))
    (posS : KTree (Nat × Nat)) (bs : List (Nat × Nat × Nat)) (U uPar uGen : List Nat) : Bool :=
  decide (1008 ≤ U.length) && U.all (fun q => decide (q < Native.nTup)) &&
    replayOKB (fun i => i) (bs.map fun b => stepTupT OT posO ST posS b) (x0F posO posS) 5000 U
      uPar uGen (posTreeB (fun i => i) U)

private theorem getD0_T (L : List Nat) (i : Nat) : L.getD i 0 = getT (treeOf L) i :=
  (getT_treeOf L i).symm

private theorem getDnil_T (L : List (List Nat)) (i : Nat) : L.getD i [] = getT (treeOf L) i :=
  (getT_treeOf L i).symm

theorem stepTupF_eqT (O : List Nat) (posO : KTree (Nat × Nat)) (SL : List (List Nat))
    (posS : KTree (Nat × Nat)) (b : Nat × Nat × Nat) :
    stepTupF O posO SL posS b = stepTupT (treeOf O) posO (treeOf SL) posS b := by
  funext c
  simp only [stepTupF, stepTupT, getD0_T, getDnil_T]

theorem tupOK_eqT (O : List Nat) (posO : KTree (Nat × Nat)) (SL : List (List Nat))
    (posS : KTree (Nat × Nat)) (bs : List (Nat × Nat × Nat)) (U uPar uGen : List Nat) :
    tupOK O posO SL posS bs U uPar uGen = tupOKT (treeOf O) posO (treeOf SL) posS bs U uPar uGen := by
  simp only [tupOK, tupOKT, tupStepsF, stepTupF_eqT, replayOK_eq_B, posTree_eq_B]

set_option maxHeartbeats 0 in
theorem tup_ok : tupOK OctD.O (posTree id OctD.O) SL (posTree Native.keyL SL) T12D.lB T12D.U
    T12D.uPar T12D.uGen = true := by
  rw [tupOK_eqT]
  quickRfl

end CFSG.KC.M24G.T12C
