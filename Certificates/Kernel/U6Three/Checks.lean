module

public import Certificates.Data.Kernel.U6Three.Defs
public import Certificates.Kernel.U6Three.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KC.U6Three

open CFSG.RankThree.PartOne.F106

set_option maxRecDepth 100000

theorem ch271061_paths : decide (u6ThreeCert.paths.length = 729) = true := by quickRfl

theorem ch271061_path0 : decide (u6ThreeCert.paths.getD 0 [] = []) = true := by quickRfl

theorem ch271061_letters :
    (u6ThreeCert.paths.all fun p => p.all fun k => decide (k < 6)) = true := by quickRfl

theorem ch271061_zl : decide (u6ThreeCert.zl.length < 243) = true := by quickRfl

theorem ch271061_lens : (u6ThreeRt.length == 4374 && u6ThreeInv.length == 729 &&
    u6ThreeWit.length == 729) = true := by quickRfl

theorem ch271061_tab : chkTab D.TP u6ThreePaths = true := by quickRfl

theorem ch271061_inj : chkInj D.TP D.JP = true := by quickRfl

theorem ch271061_inv : chkInv D.TP D.IP u6ThreeInv = true := by quickRfl

theorem ch271061_rt : chkRt D.TP u6ThreeRt = true := by quickRfl

theorem ch271061_wit : chkWit D.TP D.IP u6ThreeZl u6ThreeWit = true := by quickRfl

end CFSG.KC.U6Three
