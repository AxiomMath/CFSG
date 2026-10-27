module

public import Certificates.Data.Kernel.U6NA
public import Certificates.Data.U6NA
public import Certificates.Kernel.U6NA.Data
public import Certificates.Kernel.U6Three.Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.U6NA

open CFSG.KC.U6NA CFSG.KC.F4NA CFSG.KC.U6Three CFSG.KC.Loop CFSG.RankThree.PartOne.F106

theorem ch271034_rt : bindB 10 RT u6ThreeRt = true := by quickRfl
theorem ch271034_pw : pwB PW u6ThreePaths = true := by quickRfl
theorem ch271034_e3 : e3B RT PW E3 = true := by quickRfl
theorem ch271034_z : (Nat.beq (tabN D.TP 19) (enc U6Mon.zc) && bt E3 19) = true := by quickRfl

theorem ch271034_blk3 : allBelow 729 12 (fun i =>
    Bool.rec (motive := fun _ => Bool) true (bt E3 i) (blkN (tabN D.TP i))) = true := by quickRfl
theorem ch271034_cent : allBelow 729 12 (fun j => commI RT PW j 19) = true := by quickRfl

theorem ch271034_cE3 : Nat.beq (cnt fun i => bt E3 i) 297 = true := by quickRfl
theorem ch271034_cblk : Nat.beq (cnt fun i => blkN (tabN D.TP i)) 243 = true := by quickRfl
theorem ch271034_cq : Nat.beq (cnt fun i => blkN (tabN D.TP i) && (!trN (tabN D.TP i) &&
    !trN (tabN D.TP (mulI RT PW i 19)) &&
    !trN (tabN D.TP (mulI RT PW (mulI RT PW i 19) 19)))) 48 = true := by quickRfl
theorem ch271034_ctor : Nat.beq (cnt fun i => torN (tabN D.TP i)) 81 = true := by quickRfl
theorem ch271034_ctr : Nat.beq (cnt fun i => torN (tabN D.TP i) && !Nat.beq i 0 &&
    trN (tabN D.TP i)) 30 = true := by quickRfl

theorem ch271034_wits : witsB RT PW INV wits = true := by quickRfl
theorem ch271034_inv : bindB 10 INV u6ThreeInv = true := by quickRfl
theorem ch271034_cover : cov6B D.TP (recMask wits) = true := by quickRfl

end CFSG.KD.U6NA

end
