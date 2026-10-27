module

public import Certificates.Kernel.He31064.M
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

@[expose] public section

namespace CFSG.KD.He31064.CB

open CFSG.KC.DcTup CFSG.KD.He31064

theorem ab0 : invOK 8330 (nth ab 0) (nth ab 2) = true := by quickRfl
theorem ab1 : invOK 8330 (nth ab 1) (nth ab 3) = true := by quickRfl
theorem rg0 : tabOK ab (nthL rgw 0) 8330 (nth rg 0) = true := by quickRfl
theorem rg1 : tabOK ab (nthL rgw 1) 8330 (nth rg 1) = true := by quickRfl
theorem rgi0 : invOK 8330 (nth rg 0) (nth rgi 0) = true := by quickRfl
theorem rgi1 : invOK 8330 (nth rg 1) (nth rgi 1) = true := by quickRfl
theorem lab0 : allN 8330 (fun p => Nat.beq (im lb (im (nth rg 0) p)) (im lb p)) = true := by
  quickRfl
theorem lab1 : allN 8330 (fun p => Nat.beq (im lb (im (nth rg 1) p)) (im lb p)) = true := by
  quickRfl
theorem ord : Nat.beq (ordT 6174 C Q2 RW lv pts) 6174 = true := by quickRfl
theorem cl0 : Nat.beq (cntT (nth rg 0) 6174 C Q2 RW lv pts) 6174 = true := by quickRfl
theorem cl1 : Nat.beq (cntT (nth rg 1) 6174 C Q2 RW lv pts) 6174 = true := by quickRfl

end CFSG.KD.He31064.CB

end
