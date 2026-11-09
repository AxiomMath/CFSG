module

public import Certificates.Data.Kernel.M24G.Trio12
public import Certificates.Kernel.M24G.TrioData
public import Certificates.Kernel.M24G.Trio12Data
public import Certificates.Kernel.M24G.SliceIdx
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CFSG.KC.M24G.T12C

open CFSG.KC.M24G CFSG.Quasithin.H13.AS91.M24G

theorem close_ok_p0 : allIdx
    (fun i t => allIdx (fun k b => decide (field12 (T12D.PI.getD k 0) i < 3795) &&
      idxK (posTree Native.key3 TL) 3795 (Native.key3 (imgTrioB b t)) == field12 (T12D.PI.getD k 0) i)
      T12D.tB 0)
    (SliceGlue.slice TL (0 * 759) 759) (0 + 0 * 759) = true := by
  quickRfl

theorem close_ok_p1 : allIdx
    (fun i t => allIdx (fun k b => decide (field12 (T12D.PI.getD k 0) i < 3795) &&
      idxK (posTree Native.key3 TL) 3795 (Native.key3 (imgTrioB b t)) == field12 (T12D.PI.getD k 0) i)
      T12D.tB 0)
    (SliceGlue.slice TL (1 * 759) 759) (0 + 1 * 759) = true := by
  quickRfl

theorem close_ok_p2 : allIdx
    (fun i t => allIdx (fun k b => decide (field12 (T12D.PI.getD k 0) i < 3795) &&
      idxK (posTree Native.key3 TL) 3795 (Native.key3 (imgTrioB b t)) == field12 (T12D.PI.getD k 0) i)
      T12D.tB 0)
    (SliceGlue.slice TL (2 * 759) 759) (0 + 2 * 759) = true := by
  quickRfl

theorem close_ok_p3 : allIdx
    (fun i t => allIdx (fun k b => decide (field12 (T12D.PI.getD k 0) i < 3795) &&
      idxK (posTree Native.key3 TL) 3795 (Native.key3 (imgTrioB b t)) == field12 (T12D.PI.getD k 0) i)
      T12D.tB 0)
    (SliceGlue.slice TL (3 * 759) 759) (0 + 3 * 759) = true := by
  quickRfl

theorem close_ok_p4 : allIdx
    (fun i t => allIdx (fun k b => decide (field12 (T12D.PI.getD k 0) i < 3795) &&
      idxK (posTree Native.key3 TL) 3795 (Native.key3 (imgTrioB b t)) == field12 (T12D.PI.getD k 0) i)
      T12D.tB 0)
    (SliceGlue.slice TL (4 * 759) 759) (0 + 4 * 759) = true := by
  quickRfl

theorem close_ok : closeOK T12D.tB T12D.PI (posTree Native.key3 TL) TL = true := by
  unfold closeOK
  rw [Bool.and_eq_true]
  exact ⟨by quickRfl, allIdx_of_slices _ 759 5 TL 0 (Nat.eq_of_beq_eq_true (by quickRfl)) fun j hj => match j, hj with
    | 0, _ => close_ok_p0
    | 1, _ => close_ok_p1
    | 2, _ => close_ok_p2
    | 3, _ => close_ok_p3
    | 4, _ => close_ok_p4
    | _ + 5, h => absurd h (by omega)⟩

end CFSG.KC.M24G.T12C
