module

public import Certificates.Data.Kernel.M24G.ListChecks
public import Certificates.Kernel.M24G.TrioData
public import Certificates.Kernel.M24G.OctData
public import CFSG.Certificates.Kernel.Common.SliceGlue
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KC.M24G.TrioC

open CFSG.KC.M24G CFSG.KC.ONanSmall CFSG.Quasithin.H13.AS91.M24G

theorem length : TL.length = 3795 := by decide +kernel

theorem items : TL.all trioItem = true := by decide +kernel

theorem count_p0 : ((SliceGlue.slice OctD.O (0 * 127) 127).all
    fun a => (OctD.O.filter fun b => a &&& b == 0 && a != b).length == 30) = true := by
  quickRfl

theorem count_p1 : ((SliceGlue.slice OctD.O (1 * 127) 127).all
    fun a => (OctD.O.filter fun b => a &&& b == 0 && a != b).length == 30) = true := by
  quickRfl

theorem count_p2 : ((SliceGlue.slice OctD.O (2 * 127) 127).all
    fun a => (OctD.O.filter fun b => a &&& b == 0 && a != b).length == 30) = true := by
  quickRfl

theorem count_p3 : ((SliceGlue.slice OctD.O (3 * 127) 127).all
    fun a => (OctD.O.filter fun b => a &&& b == 0 && a != b).length == 30) = true := by
  quickRfl

theorem count_p4 : ((SliceGlue.slice OctD.O (4 * 127) 127).all
    fun a => (OctD.O.filter fun b => a &&& b == 0 && a != b).length == 30) = true := by
  quickRfl

theorem count_p5 : ((SliceGlue.slice OctD.O (5 * 127) 127).all
    fun a => (OctD.O.filter fun b => a &&& b == 0 && a != b).length == 30) = true := by
  quickRfl

theorem count : disjCount OctD.O = 6 * 3795 := by
  have h : (OctD.O.all fun a => (OctD.O.filter fun b => a &&& b == 0 && a != b).length == 30) = true :=
    SliceGlue.all_of_slices _ 127 6 _ (Nat.le_of_ble_eq_true (by quickRfl)) fun j hj => match j, hj with
    | 0, _ => count_p0
    | 1, _ => count_p1
    | 2, _ => count_p2
    | 3, _ => count_p3
    | 4, _ => count_p4
    | 5, _ => count_p5
    | _ + 6, h => absurd h (by omega)
  have hl : OctD.O.length = 759 := Nat.eq_of_beq_eq_true (by quickRfl)
  unfold disjCount
  rw [SliceGlue.sum_map_of_all_eq _ 30 _ h, hl]

end CFSG.KC.M24G.TrioC
