module

public import Certificates.Kernel.SporE81.Co2Data
public import Certificates.Kernel.Sporadic.Co2.ChainA
public import Certificates.Data.Kernel.E81K
public import Certificates.Data.Kernel.Misc.ArrEnum
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Spor.PackFld

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelE81.Co2K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PGrp CFSG.KC.Misc.ArrEnum CFSG.KC.E81K
open CFSG.RankThree.PartTwo.Sec4.Item434SporE81
open CertificateChecks.KernelE81 CertificateChecks.KernelSpor

@[expose] noncomputable def pm (p q : Nat) : Nat := pcomp 2300 12 (mask 12) p q

theorem perm : allN 2 (fun j => permB 2300 12 (Co2A.S j)) = true := by quickRfl

theorem keysQ : keysSK 2300 12 co2E81.qKeys C2Q.N C2Q.T C2Q.SK = true := by quickRfl

theorem keysD : keysSK 2300 12 co2E81.dKeys C2D.N C2D.T C2D.SK = true := by quickRfl

theorem lettersQ : (co2E81.qW.toList.all fun w => w.all fun l => decide (l < 2)) = true := by
  simp only [co2E81]
  decide +kernel

theorem lettersH : (co2E81.hW.toList.all fun w => w.all fun l => decide (l < 2)) = true := by
  simp only [co2E81]
  decide +kernel

theorem lettersZ : co2E81.zW.all (fun l => decide (l < 3)) = true := by
  simp only [co2E81]
  decide +kernel

theorem lettersR : (co2E81.rW.toList.all fun w => w.all fun l => decide (l < 3)) = true := by
  simp only [co2E81, Array.toList_map]
  decide +kernel

theorem lettersD : (co2E81.dW.toList.all fun ws => ws.toList.all fun w => w.all fun l =>
    decide (l < 3)) = true := by
  simp only [co2E81, List.toList_toArray, List.all_cons, List.all_nil, Array.toList_map]
  decide +kernel

theorem wordQ0 : posWordK 2300 12 Co2A.S (co2E81.qW.toList.getD 0 []) = C2Q.G 0 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem wordQ1 : posWordK 2300 12 Co2A.S (co2E81.qW.toList.getD 1 []) = C2Q.G 1 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem wordQ2 : posWordK 2300 12 Co2A.S (co2E81.qW.toList.getD 2 []) = C2Q.G 2 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem wordsQ : co2E81.qW.toList.map (posWordK 2300 12 Co2A.S) = (List.range 3).map C2Q.G := by
  have h3 : co2E81.qW.toList = [co2E81.qW.toList.getD 0 [], co2E81.qW.toList.getD 1 [],
      co2E81.qW.toList.getD 2 []] := by
    simp only [co2E81]
    rfl
  rw [h3, List.map_cons, List.map_cons, List.map_cons, List.map_nil, wordQ0, wordQ1, wordQ2]
  rfl

theorem wordsR : co2E81.rW.toList.map (posWordK 2300 12 C2Q.G) = (List.range 3).map C2Q.G := by
  simp only [co2E81, Array.toList_map]
  decide +kernel

theorem wordsD : co2E81.dW[0]!.toList.map (posWordK 2300 12 C2Q.G) = (List.range 4).map C2D.G := by
  simp only [co2E81]
  rw [getElem!_pos _ 0 (by decide)]
  simp only [List.getElem_toArray, List.getElem_cons_zero, Array.toList_map]
  decide +kernel

theorem hWlen : co2E81.hW.toList.length = 16 := by simp [co2E81]

theorem wordsH0 : allN 2 (fun i => Nat.beq (posWordK 2300 12 Co2A.S
    (co2E81.hW.toList.getD (0 + i) [])) (C2H (0 + i))) = true := by
  quickRfl

theorem wordsH1 : allN 2 (fun i => Nat.beq (posWordK 2300 12 Co2A.S
    (co2E81.hW.toList.getD (2 + i) [])) (C2H (2 + i))) = true := by
  quickRfl

theorem wordsH2 : allN 2 (fun i => Nat.beq (posWordK 2300 12 Co2A.S
    (co2E81.hW.toList.getD (4 + i) [])) (C2H (4 + i))) = true := by
  quickRfl

theorem wordsH3 : allN 2 (fun i => Nat.beq (posWordK 2300 12 Co2A.S
    (co2E81.hW.toList.getD (6 + i) [])) (C2H (6 + i))) = true := by
  quickRfl

theorem wordsH4 : allN 2 (fun i => Nat.beq (posWordK 2300 12 Co2A.S
    (co2E81.hW.toList.getD (8 + i) [])) (C2H (8 + i))) = true := by
  quickRfl

theorem wordsH5 : allN 2 (fun i => Nat.beq (posWordK 2300 12 Co2A.S
    (co2E81.hW.toList.getD (10 + i) [])) (C2H (10 + i))) = true := by
  quickRfl

theorem wordsH6 : allN 2 (fun i => Nat.beq (posWordK 2300 12 Co2A.S
    (co2E81.hW.toList.getD (12 + i) [])) (C2H (12 + i))) = true := by
  quickRfl

theorem wordsH7 : allN 2 (fun i => Nat.beq (posWordK 2300 12 Co2A.S
    (co2E81.hW.toList.getD (14 + i) [])) (C2H (14 + i))) = true := by
  quickRfl

theorem wordZ : posWordK 2300 12 C2Q.G co2E81.zW = C2Z 0 := by
  simp only [co2E81]
  decide +kernel

theorem zOK : (Nat.beq (pm (C2Z 0) (pm (C2Z 0) (C2Z 0))) (pidn 2300 12) &&
    !Nat.beq (C2Z 0) (pidn 2300 12) && Nat.beq (pm (C2Z 0) (C2Z 0)) (C2Z 1) &&
    allN 3 (fun k => Nat.beq (pm (C2Z 0) (C2Q.G k)) (pm (C2Q.G k) (C2Z 0)))) = true := by
  quickRfl

theorem elem : allN 4 (fun a => Nat.beq (pm (C2D.G a) (pm (C2D.G a) (C2D.G a))) (pidn 2300 12) &&
    allN 4 fun b => Nat.beq (pm (C2D.G a) (C2D.G b)) (pm (C2D.G b) (C2D.G a))) = true := by
  quickRfl

theorem zw : allN 16 (zwK 2300 12 16 C2H (fun _ => C2D.N) (fun _ => C2D.T) (C2Z 0) C2ZW) = true := by
  quickRfl

theorem covB0 : allN 81 (fun j => covK 2300 12 16 1 C2H (fun _ => C2D.N) (fun _ => C2D.T) (C2Z 0)
    (C2Z 1) C2ZW (C2CW (0 * 81 + j)) (C2Q.T (0 * 81 + j))) = true := by
  quickRfl

theorem covB1 : allN 81 (fun j => covK 2300 12 16 1 C2H (fun _ => C2D.N) (fun _ => C2D.T) (C2Z 0)
    (C2Z 1) C2ZW (C2CW (1 * 81 + j)) (C2Q.T (1 * 81 + j))) = true := by
  quickRfl

theorem covB2 : allN 81 (fun j => covK 2300 12 16 1 C2H (fun _ => C2D.N) (fun _ => C2D.T) (C2Z 0)
    (C2Z 1) C2ZW (C2CW (2 * 81 + j)) (C2Q.T (2 * 81 + j))) = true := by
  quickRfl

theorem covB3 : allN 81 (fun j => covK 2300 12 16 1 C2H (fun _ => C2D.N) (fun _ => C2D.T) (C2Z 0)
    (C2Z 1) C2ZW (C2CW (3 * 81 + j)) (C2Q.T (3 * 81 + j))) = true := by
  quickRfl

theorem covB4 : allN 81 (fun j => covK 2300 12 16 1 C2H (fun _ => C2D.N) (fun _ => C2D.T) (C2Z 0)
    (C2Z 1) C2ZW (C2CW (4 * 81 + j)) (C2Q.T (4 * 81 + j))) = true := by
  quickRfl

theorem covB5 : allN 81 (fun j => covK 2300 12 16 1 C2H (fun _ => C2D.N) (fun _ => C2D.T) (C2Z 0)
    (C2Z 1) C2ZW (C2CW (5 * 81 + j)) (C2Q.T (5 * 81 + j))) = true := by
  quickRfl

theorem covB6 : allN 81 (fun j => covK 2300 12 16 1 C2H (fun _ => C2D.N) (fun _ => C2D.T) (C2Z 0)
    (C2Z 1) C2ZW (C2CW (6 * 81 + j)) (C2Q.T (6 * 81 + j))) = true := by
  quickRfl

theorem covB7 : allN 81 (fun j => covK 2300 12 16 1 C2H (fun _ => C2D.N) (fun _ => C2D.T) (C2Z 0)
    (C2Z 1) C2ZW (C2CW (7 * 81 + j)) (C2Q.T (7 * 81 + j))) = true := by
  quickRfl

theorem covB8 : allN 81 (fun j => covK 2300 12 16 1 C2H (fun _ => C2D.N) (fun _ => C2D.T) (C2Z 0)
    (C2Z 1) C2ZW (C2CW (8 * 81 + j)) (C2Q.T (8 * 81 + j))) = true := by
  quickRfl

theorem cov : allN 729 (fun k => covK 2300 12 16 1 C2H (fun _ => C2D.N) (fun _ => C2D.T) (C2Z 0)
    (C2Z 1) C2ZW (C2CW k) (C2Q.T k)) = true := by
  refine CFSG.KS.PackFld.allN_of_forall fun k hk => ?_
  have hb : ∀ b < 9, ∀ j < 81, covK 2300 12 16 1 C2H (fun _ => C2D.N) (fun _ => C2D.T) (C2Z 0)
      (C2Z 1) C2ZW (C2CW (b * 81 + j)) (C2Q.T (b * 81 + j)) = true := by
    intro b hb j hj
    match b, hb with
    | 0, _ => exact CFSG.KS.allN_spec covB0 j hj
    | 1, _ => exact CFSG.KS.allN_spec covB1 j hj
    | 2, _ => exact CFSG.KS.allN_spec covB2 j hj
    | 3, _ => exact CFSG.KS.allN_spec covB3 j hj
    | 4, _ => exact CFSG.KS.allN_spec covB4 j hj
    | 5, _ => exact CFSG.KS.allN_spec covB5 j hj
    | 6, _ => exact CFSG.KS.allN_spec covB6 j hj
    | 7, _ => exact CFSG.KS.allN_spec covB7 j hj
    | 8, _ => exact CFSG.KS.allN_spec covB8 j hj
    | _ + 9, h => omega
  have h := hb (k / 81) (by omega) (k % 81) (Nat.mod_lt _ (by decide))
  rwa [Nat.div_add_mod'] at h

end CertificateChecks.KernelE81.Co2K

end
