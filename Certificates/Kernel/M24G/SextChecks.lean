module

public import Certificates.Data.Kernel.M24G.ListChecks
public import Certificates.Kernel.M24G.SextData
public import Certificates.Kernel.M24G.OctData
public import CFSG.Certificates.Kernel.Common.SliceGlue
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KC.M24G.SextC

open CFSG.KC.M24G CFSG.KC.ONanSmall CFSG.Quasithin.H13.AS91.M24G

theorem length : SL.length = 1771 := by decide +kernel

theorem items_p0 : (SliceGlue.slice SL (0 * 300) 300).all sextItem = true := by
  quickRfl

theorem items_p1 : (SliceGlue.slice SL (1 * 300) 300).all sextItem = true := by
  quickRfl

theorem items_p2 : (SliceGlue.slice SL (2 * 300) 300).all sextItem = true := by
  quickRfl

theorem items_p3 : (SliceGlue.slice SL (3 * 300) 300).all sextItem = true := by
  quickRfl

theorem items_p4 : (SliceGlue.slice SL (4 * 300) 300).all sextItem = true := by
  quickRfl

theorem items_p5 : (SliceGlue.slice SL (5 * 300) 300).all sextItem = true := by
  quickRfl

theorem items : SL.all sextItem = true :=
  SliceGlue.all_of_slices _ 300 6 _ (Nat.le_of_ble_eq_true (by quickRfl)) fun j hj => match j, hj with
    | 0, _ => items_p0
    | 1, _ => items_p1
    | 2, _ => items_p2
    | 3, _ => items_p3
    | 4, _ => items_p4
    | 5, _ => items_p5
    | _ + 6, h => absurd h (by omega)

theorem tets : tetsOK OctD.O (posTree Native.keyL SL) = true := by decide +kernel

end CFSG.KC.M24G.SextC
