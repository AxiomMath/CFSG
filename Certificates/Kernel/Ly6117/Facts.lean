module

public import CFSG.Certificates.Kernel.Ly6117.Sound
public import CFSG.Certificates.Kernel.LyE81.Sound
public import Certificates.Kernel.LyE81.Mats
public import Certificates.Kernel.SporSch.Ly.BS18009
public import Certificates.Kernel.Ly6117.Checks
public import Certificates.Kernel.Ly6117.Core
public import Certificates.Kernel.Ly6117.Rest
import Mathlib.Tactic.FinCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLy6117

open CFSG.KD.Ly6117 CFSG.KD.LyS0 CFSG.KS.SporSch.LyM CFSG.KS.Ly6117K CFSG.KS.LyS0K
open CFSG.Sporadic.Recognition.LyonsSims.LyFinal CFSG.Sporadic.He.Native
open CertificateChecks.KernelLyE81

local notation "U" X:max => unpackL 111 12 1332 X

theorem vC : vld C = true := CFSG.KS.allBlk_spec vM 0 (by norm_num)

theorem vD : vld D = true := CFSG.KS.allBlk_spec vM 1 (by norm_num)

theorem slpMax2_eq (X Y : Mat) :
    slpMax2 X Y = ((CFSG.RankThree.PartTwo.Sec4.Item434SporLy.slpM X Y).1,
      (CFSG.RankThree.PartTwo.Sec4.Item434SporLy.slpM X Y).2.1) := rfl

theorem cd_eq : cdMats = (U C, U D) := by
  have hs := CFSG.KS.LyE81K.slpM_eq CertificateChecks.KernelSporSch.LyBS.vA
    CertificateChecks.KernelSporSch.LyBS.vB slp1 slp2 slp3 slp4
  have e : cdMats = slpMax2 CFSG.Sporadic.Ly.Native.matA CFSG.Sporadic.Ly.Native.matB := rfl
  rw [e, CertificateChecks.KernelSporSch.LyBSF.matA_eq, CertificateChecks.KernelSporSch.LyBSF.matB_eq,
    slpMax2_eq, hs]

theorem c_eq : cdMats.1 = U C := by rw [cd_eq]

theorem d_eq : cdMats.2 = U D := by rw [cd_eq]

theorem dd_eq : mulM 5 111 cdMats.2 cdMats.2 = U (GD 4) := by
  rw [d_eq, mulE vD vD, Nat.eq_of_beq_eq_true dd]

theorem hcd (i : Fin 6) : cdLetters i = U (CDx i.val) ∧ vld (CDx i.val) = true := by
  fin_cases i
  · exact ⟨c_eq, vC⟩
  · exact ⟨d_eq, vD⟩
  all_goals exact ⟨idE, vOne⟩

theorem hcdi (i : Fin 6) : cdLettersInv i = U (CDIx i.val) ∧ vld (CDIx i.val) = true := by
  fin_cases i
  · exact ⟨c_eq, vC⟩
  · exact ⟨dd_eq, v4⟩
  all_goals exact ⟨idE, vOne⟩

theorem a_eq : wordM cdLetters cdLettersInv aWord = U (GD 0) := by
  rw [(wordK_eq hcd hcdi aWord).1, Nat.eq_of_beq_eq_true wa]

theorem b_eq : wordM cdLetters cdLettersInv bWord = U (GD 1) := by
  rw [(wordK_eq hcd hcdi bWord).1, Nat.eq_of_beq_eq_true wb]

theorem e_eq : wordM cdLetters cdLettersInv eWord = U (GD 2) := by
  rw [(wordK_eq hcd hcdi eWord).1, Nat.eq_of_beq_eq_true we]

theorem k_eq : kMat = U (GD 3) := by
  have e : kMat = rowsOf 5 111 kText := rfl
  rw [e, LyK.eq, payRunP_eq (w := 12) (S := 1332) _ (by norm_num) (by norm_num) (by norm_num),
    Nat.eq_of_beq_eq_true payK]

theorem arr_eq : genArr = #[U C, U D, U (GD 0), U (GD 1), U (GD 2), U (GD 3)] := by
  unfold genArr
  rw [c_eq, d_eq, a_eq, b_eq, e_eq, k_eq]

theorem invArr_eq :
    genInvArr = #[U C, U (GD 4), U (GD 0), U (GD 1), U (GD 2), U (GD 3)] := by
  have e : genInvArr = genArr.set! 1 (mulM 5 111 cdMats.2 cdMats.2) := rfl
  rw [e, arr_eq, dd_eq]
  rfl

theorem hg (i : Fin 6) : genM i = U (G i.val) ∧ vld (G i.val) = true := by
  have e : genM i = genArr[i.val]! := rfl
  rw [e, arr_eq]
  fin_cases i
  · exact ⟨rfl, vC⟩
  · exact ⟨rfl, vD⟩
  · exact ⟨rfl, v0⟩
  · exact ⟨rfl, v1⟩
  · exact ⟨rfl, v2⟩
  · exact ⟨rfl, v3⟩

theorem hgi (i : Fin 6) : genInvM i = U (GI i.val) ∧ vld (GI i.val) = true := by
  have e : genInvM i = genInvArr[i.val]! := rfl
  rw [e, invArr_eq]
  fin_cases i
  · exact ⟨rfl, vC⟩
  · exact ⟨rfl, v4⟩
  · exact ⟨rfl, v0⟩
  · exact ⟨rfl, v1⟩
  · exact ⟨rfl, v2⟩
  · exact ⟨rfl, v3⟩

theorem relAll : allK G GI (modularR Rcore107 modularD) = true := by
  unfold allK modularR
  rw [List.all_append, List.all_append]
  simp only [Bool.and_eq_true]
  exact ⟨⟨relCore, relLearned⟩, relD⟩

theorem lyRelCheck_true : lyRelCheck (modularR Rcore107 modularD) = true :=
  lyRelCheck_of hg hgi CertificateChecks.KernelSporSch.LyBSF.matA_eq
    CertificateChecks.KernelSporSch.LyBSF.matB_eq CertificateChecks.KernelSporSch.LyBS.vA
    CertificateChecks.KernelSporSch.LyBS.vB inv relAll wA wB

end CertificateChecks.KernelLy6117

end
