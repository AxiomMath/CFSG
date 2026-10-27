module

public import Certificates.Kernel.OmegaEight.T3KData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.T3K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PGrp CFSG.KC.Misc.ArrEnum
open CFSG.HardMathSupport.Curtis.Coordinator
open CertificateChecks.KernelO8 CertificateChecks.KernelO8.E9K

theorem perm : allN 10 (fun k => permB 360 9 (AP.S k)) = true := by quickRfl

theorem nums : (Nat.beq T3R.ng 4 && Nat.beq T3R.N 729 &&
    allN 3 (fun k => Nat.beq (T3R.G k) (E9Q.G k))) = true := by quickRfl

theorem keysR : keysSK 360 9 psR T3R.N T3R.T T3R.SK = true := by quickRfl

theorem lettersQ : (triData.qW.toList.all fun w => w.all fun l => decide (l < 8)) = true := by
  simp only [triData, Array.toList_map]
  decide +kernel

theorem lettersH : (triData.hW.toList.all fun w => w.all fun l => decide (l < 10)) = true := by
  simp only [triData, Array.toList_map]
  decide +kernel

theorem lettersY : (triData.yW.toList.all fun w => w.all fun l => decide (l < 3)) = true := by
  simp only [triData, Array.toList_map]
  decide +kernel

theorem lettersZ : (triData.zW.toList.all fun w => w.all fun l => decide (l < 3)) = true := by
  simp only [triData, Array.toList_map]
  decide +kernel

theorem lettersX : (triData.xW.all fun l => decide (l < 10)) = true := by
  simp only [triData]
  decide +kernel

theorem sizes : triData.qW.size = 3 ∧ triData.hW.size = 32 ∧ triData.yW.size = 32 ∧
    triData.zW.size = 32 := by
  simp only [triData, Array.size_map]
  decide +kernel

theorem wordsQ : triData.qW.toList.map (posWordK 360 9 AP.S) = (List.range 3).map E9Q.G := by
  simp only [triData, Array.toList_map]
  decide +kernel

theorem wordX : posWordK 360 9 AP.S triData.xW = T3R.G 3 := by
  simp only [triData]
  decide +kernel

theorem wordsH : triData.hW.toList.map (posWordK 360 9 AP.S) = (List.range 32).map T3H := by
  simp only [triData, Array.toList_map]
  decide +kernel

theorem wordsY : triData.yW.toList.map (posWordK 360 9 E9Q.G) = (List.range 32).map T3Y := by
  simp only [triData, Array.toList_map]
  decide +kernel

theorem wordsZ : triData.zW.toList.map (posWordK 360 9 E9Q.G) = (List.range 32).map T3Z := by
  simp only [triData, Array.toList_map]
  decide +kernel

theorem ncomm : allN 32 (fun e => !Nat.beq (pm (T3Y e) (T3Z e)) (pm (T3Z e) (T3Y e))) = true := by
  quickRfl

theorem pts : allN 729 triK = true := by quickRfl

end CertificateChecks.KernelO8.T3K

end
