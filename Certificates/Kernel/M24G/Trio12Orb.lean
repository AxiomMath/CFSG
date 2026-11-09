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

theorem orb_ok_p0 : allIdx
    (fun p t => decide (1 < Native.zc Native.baseTrio t) || orbOK (piSteps T12D.PI) p)
    (SliceGlue.slice TL (0 * 759) 759) (0 + 0 * 759) = true := by
  quickRfl

theorem orb_ok_p1 : allIdx
    (fun p t => decide (1 < Native.zc Native.baseTrio t) || orbOK (piSteps T12D.PI) p)
    (SliceGlue.slice TL (1 * 759) 759) (0 + 1 * 759) = true := by
  quickRfl

theorem orb_ok_p2 : allIdx
    (fun p t => decide (1 < Native.zc Native.baseTrio t) || orbOK (piSteps T12D.PI) p)
    (SliceGlue.slice TL (2 * 759) 759) (0 + 2 * 759) = true := by
  quickRfl

theorem orb_ok_p3 : allIdx
    (fun p t => decide (1 < Native.zc Native.baseTrio t) || orbOK (piSteps T12D.PI) p)
    (SliceGlue.slice TL (3 * 759) 759) (0 + 3 * 759) = true := by
  quickRfl

theorem orb_ok_p4 : allIdx
    (fun p t => decide (1 < Native.zc Native.baseTrio t) || orbOK (piSteps T12D.PI) p)
    (SliceGlue.slice TL (4 * 759) 759) (0 + 4 * 759) = true := by
  quickRfl

theorem orb_ok : trioOrbF (piSteps T12D.PI) TL = true :=
  allIdx_of_slices _ 759 5 TL 0 (Nat.eq_of_beq_eq_true (by quickRfl)) fun j hj => match j, hj with
    | 0, _ => orb_ok_p0
    | 1, _ => orb_ok_p1
    | 2, _ => orb_ok_p2
    | 3, _ => orb_ok_p3
    | 4, _ => orb_ok_p4
    | _ + 5, h => absurd h (by omega)

end CFSG.KC.M24G.T12C
