module

public import Certificates.Kernel.Sporadic.Fi22.N2070Chk
public import Certificates.Kernel.Sporadic.Fi22.N2070Sift
public import Certificates.Kernel.Sporadic.Fi22.N3153Final
public import Certificates.Kernel.Sporadic.Fi22.E2065Eq
public import CFSG.Sporadic.FischerOddCore.Fi22RelBoundCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.N2070

open CFSG.KC.Enum CFSG.KC.N3153 CFSG.KD.N3153 CFSG.KS CFSG.KS.Text CFSG.KS.Raw CFSG.KS.Prim
open CFSG.KC.BfsPin CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
open CFSG.Sporadic.FischerOddCore CFSG.Sporadic.FischerOddCore.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fi22X

theorem up0 : UP 0 = GO := Nat.eq_of_beq_eq_true (by quickRfl)
theorem up1 : UP 1 = Fi22ExtT.L 22 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem up2 : UP 2 = Fi22ExtT.L 24 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem up3 : UP 3 = Fi22ExtT.L 25 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem up4 : UP 4 = Fi22ExtT.L 26 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem cent_eq {L : Nat} (hL : L < 306) : fi22CentArr L = unpack 3510 12 (Fi22CentT.L L) := by
  rw [fi22CentArr, fi22CentBytes, Fi22CentB.text_eq]
  exact Fi22E2065.cent_eq hL

theorem cell_of {c s : Nat} (hc : c < 4) (hs : s < (fi22CentRefPoints.getD c []).length) :
    cellK 3510 S (UP (c + 1)) (fi22CentRefPoints.getD c []) 4 s
      ((fi22CentRefBounds.getD c []).getD s 0) = true := by
  have hs10 : s < 10 := by
    interval_cases c <;> simp [fi22CentRefPoints] at hs <;> omega
  have key : ∀ j, cellB j = bIf(Nat.blt (j % 10) (fi22CentRefPoints.getD (j / 10) []).length,
      cellK 3510 S (UP (j / 10 + 1)) (fi22CentRefPoints.getD (j / 10) []) 4 (j % 10)
        ((fi22CentRefBounds.getD (j / 10) []).getD (j % 10) 0), true) := fun _ => rfl
  have hj : 10 * c + s < 40 := by omega
  have h := Cell.all (10 * c + s) hj
  have hb : Nat.blt s (fi22CentRefPoints.getD c []).length = true := Eq.mpr Nat.blt_eq hs
  rw [key, show (10 * c + s) % 10 = s by omega, show (10 * c + s) / 10 = c by omega, hb] at h
  exact h

theorem inj_of {c : Nat} (hc : c < 4) :
    injK 3510 S (UP (c + 1)) (fi22CentRefPoints.getD c []) 4 (CFSG.KD.N2070.O c) = true :=
  Inj.all c hc

theorem t_eq {c : Nat} (hc : c < 4) :
    fi22ExtArr (21 + fi22CentCases.getD (c + 1) 0) = unpack 3510 12 (UP (c + 1)) := by
  interval_cases c
  · rw [up1]
    exact Fi22E2067.ext_eq (L := 22) (by norm_num)
  · rw [up2]
    exact Fi22E2067.ext_eq (L := 24) (by norm_num)
  · rw [up3]
    exact Fi22E2067.ext_eq (L := 25) (by norm_num)
  · rw [up4]
    exact Fi22E2067.ext_eq (L := 26) (by norm_num)

theorem rel_ok {c : Nat}
    (hc : c < 4) : fi22RelBoundOK (c + 1) = true := by
  unfold fi22RelBoundOK
  rw [Nat.add_sub_cancel, t_eq hc]
  exact bounds_sound (d := 693) (R := R) (M := M) (S := S) (P := CFSG.KD.N2070.O c)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) N3153.nbr_eq N3153.rows N3153.symm rfl
    (by interval_cases c <;> rfl) (by interval_cases c <;> decide) (fun s hs => cell_of hc hs)
    (inj_of hc)

theorem not_true {b : Bool} (h : bIf(b, false, true) = true) : b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)

theorem facts2070 :
    ((allLt 3510 fun x =>
        fi22Nbr[fi22GraphOuterArr[x]!]! == imgSorted fi22GraphOuterArr fi22Nbr[x]!) = true ∧
      fi22InP (fi22CentArr 79) = false ∧
      fi22InP (compA 3510 fi22GraphOuterArr (fi22CentArr 79)) = true ∧
      eqA 3510 (compA 3510 (fi22CentArr 79) (fi22ExtArr 22))
        (compA 3510 (fi22ExtArr 22) (fi22CentArr 79)) = true ∧
      (∀ c < 4, ∀ x ∈ fi22CentRefPoints.getD c [], x < 3510)) ∧
    fi22RelBoundOK 1 = true ∧ fi22RelBoundOK 2 = true ∧ fi22RelBoundOK 3 = true ∧
      fi22RelBoundOK 4 = true := by
  have eC := cent_eq (L := 79) (by norm_num)
  have eT := Fi22E2067.ext_eq (L := 22) (by norm_num)
  refine ⟨⟨?_, ?_, ?_, ?_, by decide⟩, rel_ok (c := 0) (by norm_num), rel_ok (c := 1) (by norm_num),
    rel_ok (c := 2) (by norm_num), rel_ok (c := 3) (by norm_num)⟩
  · rw [N3153.nbr_eq]
    exact img_sound (P := UP 0) (by norm_num) N3153.rows (by rw [up0]; exact go_eq)
      (N3153.of_blocks ImgU.all)
  · rw [fi22InP, eC, siftK_eq bindsP permP Fi22PC.hl rfl (hi_of cnC) (range_of_canonK cnC)]
    exact not_true sC
  · rw [fi22InP, go_eq, eC, comp_eq cnG cnC, siftK_eq bindsP permP Fi22PC.hl rfl
      (hi_of (cn_c cnG cnC)) (range_of_canonK (cn_c cnG cnC))]
    exact sUC
  · rw [eC, eT, comp_eq cnC cnT1, comp_eq cnT1 cnC]
    exact eqA_of (cn_c cnC cnT1) (cn_c cnT1 cnC) comm

end CertificateChecks.KernelSpor.N2070

end
