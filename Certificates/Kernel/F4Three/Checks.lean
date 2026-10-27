module

public import Certificates.Data.Kernel.F4Three.Defs
public import Certificates.Kernel.F4Three.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KC.F4Three

open CFSG.RankThree.PartOne.F106

set_option maxRecDepth 100000

theorem ch271060_small : (decide (f4ThreeCert.paths.length = 729) &&
    decide (f4ThreeCert.paths.getD 0 [] = []) &&
    (f4ThreeCert.paths.all fun p => p.all fun k => decide (k < 6)) &&
    decide (f4ThreeCert.zl.length < 243)) = true := by quickRfl

theorem ch271060_lens : (f4ThreeCert.rt.length == 4374 && f4ThreeCert.inv.length == 729 &&
    f4ThreeCert.wit.length == 729) = true := by quickRfl

theorem ch271060_gb : (D.GB == f4ThreeCert.gbList) = true := by quickRfl

theorem ch271060_tab : chkTab f4ThreeCert D.GB D.TT = true := by quickRfl

theorem ch271060_nod : chkNod D.TT = true := by quickRfl

theorem ch271060_rt : chkRt D.GB D.TT f4ThreeCert.rt = true := by quickRfl

theorem ch271060_inv : chkInv D.TT f4ThreeCert.inv = true := by quickRfl

theorem ch271060_wit :
    chkWit D.TT f4ThreeCert.zl f4ThreeCert.inv f4ThreeCert.wit = true := by quickRfl

end CFSG.KC.F4Three
