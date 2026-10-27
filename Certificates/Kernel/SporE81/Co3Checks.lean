module

public import Certificates.Kernel.SporE81.Co3Data
public import Certificates.Kernel.Sporadic.Co3.C
public import Certificates.Data.Kernel.E81K
public import Certificates.Data.Kernel.Misc.ArrEnum
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelE81.Co3K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PGrp CFSG.KC.Misc.ArrEnum CFSG.KC.E81K
open CFSG.RankThree.PartTwo.Sec4.Item434SporE81
open CertificateChecks.KernelE81 CertificateChecks.KernelSpor

@[expose] noncomputable def pm (p q : Nat) : Nat := pcomp 276 9 (mask 9) p q

theorem perm : allN 2 (fun j => permB 276 9 (Co3C.S j)) = true := by quickRfl

theorem keysQ : keysSK 276 9 co3E81.qKeys C3Q.N C3Q.T C3Q.SK = true := by quickRfl

theorem keysR : keysSK 276 9 co3E81.rKeys C3R.N C3R.T C3R.SK = true := by quickRfl

theorem keysD : keysSK 276 9 co3E81.dKeys C3D.N C3D.T C3D.SK = true := by quickRfl

theorem lettersQ : (co3E81.qW.toList.all fun w => w.all fun l => decide (l < 2)) = true := by
  simp only [co3E81, Array.toList_map]
  decide +kernel

theorem lettersH : (co3E81.hW.toList.all fun w => w.all fun l => decide (l < 2)) = true := by
  simp only [co3E81, Array.toList_map]
  decide +kernel

theorem lettersZ : co3E81.zW.all (fun l => decide (l < 4)) = true := by
  simp only [co3E81]
  decide +kernel

theorem lettersR : (co3E81.rW.toList.all fun w => w.all fun l => decide (l < 4)) = true := by
  simp only [co3E81, Array.toList_map]
  decide +kernel

theorem lettersD : (co3E81.dW.toList.all fun ws => ws.toList.all fun w => w.all fun l =>
    decide (l < 4)) = true := by
  simp only [co3E81, List.toList_toArray, List.all_cons, List.all_nil, Array.toList_map]
  decide +kernel

theorem wordsQ : co3E81.qW.toList.map (posWordK 276 9 Co3C.S) = (List.range 4).map C3Q.G := by
  simp only [co3E81, Array.toList_map]
  decide +kernel

theorem wordsR : co3E81.rW.toList.map (posWordK 276 9 C3Q.G) = (List.range 3).map C3R.G := by
  simp only [co3E81, Array.toList_map]
  decide +kernel

theorem wordsD : co3E81.dW[0]!.toList.map (posWordK 276 9 C3Q.G) = (List.range 5).map C3D.G := by
  simp only [co3E81]
  rw [getElem!_pos _ 0 (by decide)]
  simp only [List.getElem_toArray, List.getElem_cons_zero, Array.toList_map]
  decide +kernel

theorem wordsH : co3E81.hW.toList.map (posWordK 276 9 Co3C.S) = (List.range 10).map C3H := by
  simp only [co3E81, Array.toList_map]
  decide +kernel

theorem wordZ : posWordK 276 9 C3Q.G co3E81.zW = C3Z 0 := by
  simp only [co3E81]
  decide +kernel

theorem zOK : (Nat.beq (pm (C3Z 0) (pm (C3Z 0) (C3Z 0))) (pidn 276 9) &&
    !Nat.beq (C3Z 0) (pidn 276 9) && Nat.beq (pm (C3Z 0) (C3Z 0)) (C3Z 1) &&
    allN 4 (fun k => Nat.beq (pm (C3Z 0) (C3Q.G k)) (pm (C3Q.G k) (C3Z 0)))) = true := by
  quickRfl

theorem elem : allN 5 (fun a => Nat.beq (pm (C3D.G a) (pm (C3D.G a) (C3D.G a))) (pidn 276 9) &&
    allN 5 fun b => Nat.beq (pm (C3D.G a) (C3D.G b)) (pm (C3D.G b) (C3D.G a))) = true := by
  quickRfl

theorem zw : allN 10 (zwK 276 9 10 C3H (fun _ => C3D.N) (fun _ => C3D.T) (C3Z 0) C3ZW) = true := by
  quickRfl

theorem cov : allN 729 (fun k => covK 276 9 10 1 C3H (fun _ => C3D.N) (fun _ => C3D.T) (C3Z 0)
    (C3Z 1) C3ZW (C3CW k) (C3R.T k)) = true := by
  quickRfl

end CertificateChecks.KernelE81.Co3K

end
