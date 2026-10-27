module

public import CFSG.Certificates.Kernel.Misc.SylowG2Sound
public import CFSG.Certificates.Kernel.Misc.OmegaSixOSound
public import Certificates.Kernel.Misc.SylowG2.Checks
public import Certificates.Data.Foote82SylowG2

public section

namespace CFSG.KD.SylowG2

open CFSG.CGT.Foote82.OmegaSix CFSG.CGT.Foote82.CaseIIG2Aux CFSG.ClassicalInvolution.Solomon73.Yamaki
  CFSG.KC.OmegaSix CFSG.KC.SylowG2 CFSG.KC.YamakiRep CFSG.KC.YamakiAut CFSG.KD.YamakiRep
  CFSG.KD.YamakiAut CFSG.KD.OmegaSix CFSG.KD.BfsK CFSG.KC.BfsEnum
open CFSG.KD.Sp62 (MULF ONE)

theorem sgMatP1 : pMat1 = matF (RPP 0) := by
  rw [pMat1.eq_1, matF]
  congr 1
  decide +kernel

theorem sgMatP2 : pMat2 = matF (RPP 1) := by
  rw [pMat2.eq_1, matF]
  congr 1
  decide +kernel

theorem sgMatP3 : pMat3 = matF (RPP 2) := by
  rw [pMat3.eq_1, matF]
  congr 1
  decide +kernel

theorem sgMatC1 : cMat1 = matF (HQ 0) := by
  rw [cMat1.eq_1, matF]
  congr 1
  decide +kernel

theorem sgMatD1 : dMat1 = matF (HQ 1) := by
  rw [dMat1.eq_1, matF]
  congr 1
  decide +kernel

theorem sgMatE1 : dInvMat1 = matF (HQ 2) := by
  rw [dInvMat1.eq_1, matF]
  congr 1
  decide +kernel

theorem sgMatC2 : cMat2 = matF (HQ 3) := by
  rw [cMat2.eq_1, matF]
  congr 1
  decide +kernel

theorem sgMatD2 : dMat2 = matF (HQ 4) := by
  rw [dMat2.eq_1, matF]
  congr 1
  decide +kernel

theorem sgMatE2 : dInvMat2 = matF (HQ 5) := by
  rw [dInvMat2.eq_1, matF]
  congr 1
  decide +kernel

theorem sgMatC3 : cMat3 = matF (HQ 6) := by
  rw [cMat3.eq_1, matF]
  congr 1
  decide +kernel

theorem sgMatD3 : dMat3 = matF (HQ 7) := by
  rw [dMat3.eq_1, matF]
  congr 1
  decide +kernel

theorem sgMatE3 : dInvMat3 = matF (HQ 8) := by
  rw [dInvMat3.eq_1, matF]
  congr 1
  decide +kernel

theorem sgGenP : ∀ j < 3, (genP ())[j]! = arrF (RPP (0 + j)) := by
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
  · rw [Nat.add_zero, arrF, ← sgMatP1]
    rfl
  · rw [Nat.zero_add, arrF, ← sgMatP2]
    rfl
  · rw [Nat.zero_add, arrF, ← sgMatP3]
    rfl

theorem sgCommArr (a b c : ℕ) :
    marr (matF a * matF b * matF a * matF c) = arrF (MULF (MULF (MULF a b) a) c) := by
  rw [arrF, matF_mul, matF_mul, matF_mul]

theorem sgGenQ : ∀ j < 3, (genQ ())[j]! = arrF (RQQ (0 + j)) := by
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
  · rw [Nat.add_zero, sg919101_comm0, ← sgCommArr, ← sgMatC1, ← sgMatD1, ← sgMatE1]
    rfl
  · rw [Nat.zero_add, sg919101_comm1, ← sgCommArr, ← sgMatC2, ← sgMatD2, ← sgMatE2]
    rfl
  · rw [Nat.zero_add, sg919101_comm2, ← sgCommArr, ← sgMatC3, ← sgMatD3, ← sgMatE3]
    rfl

theorem sgPermT1 : permArr tPerm1 = arrL 10 tl0 := by decide +kernel

theorem sgPermT2 : permArr tPerm2 = arrL 10 tl1 := by decide +kernel

theorem sgPermT3 : permArr tPerm3 = arrL 10 tl2 := by decide +kernel

theorem sgPermU1 : permArr uPerm1 = arrL 8 ul0 := by decide +kernel

theorem sgPermU2 : permArr uPerm2 = arrL 8 ul1 := by decide +kernel

theorem sgPermU3 : permArr uPerm3 = arrL 8 ul2 := by decide +kernel

theorem sgGenT : genT () = #[arrL 10 tl0, arrL 10 tl1, arrL 10 tl2] := by
  rw [genT, sgPermT1, sgPermT2, sgPermT3]

theorem sgGenU : genU () = #[arrL 8 ul0, arrL 8 ul1, arrL 8 ul2] := by
  rw [genU, sgPermU1, sgPermU2, sgPermU3]

theorem sgRowsP : ∀ t < 128, rowK RPP (rstG RPP 0) 3 128 3 t = true :=
  rows_of_chunks (L := 128) (m := 1) (fun q hq => by
    obtain rfl : q = 0 := by omega
    exact chunkK_of_chunkF3 sg919101_tabP) (by norm_num)

theorem sgRowsQ : ∀ t < 64, rowK RQQ (rstG RQQ 0) 3 64 3 t = true :=
  rows_of_chunks (L := 64) (m := 1) (fun q hq => by
    obtain rfl : q = 0 := by omega
    exact chunkK_of_chunkF3 sg919101_tabQ) (by norm_num)

theorem sgTabP : BInvE (fun t => arrF (recX RPP 3 t)) (recF RPP 3 0) (recF RPP 3 1) 128
      (bfsEnum (genP ()) 128) ∧ enumOK (bfsEnum (genP ()) 128) (genP ()) = true ∧
      ∀ t < 128, recX RPP 3 t < 2 ^ 36 :=
  table_invF (gs := genP ()) (R := RPP) (o := 3) (n := 128) (k := 3) (g := 0) rfl
    (by norm_num) (by norm_num) (by norm_num) sgGenP sg919101_headP sgRowsP

theorem sgTabQ : BInvE (fun t => arrF (recX RQQ 3 t)) (recF RQQ 3 0) (recF RQQ 3 1) 64
      (bfsEnum (genQ ()) 64) ∧ enumOK (bfsEnum (genQ ()) 64) (genQ ()) = true ∧
      ∀ t < 64, recX RQQ 3 t < 2 ^ 36 :=
  table_invF (gs := genQ ()) (R := RQQ) (o := 3) (n := 64) (k := 3) (g := 0) rfl
    (by norm_num) (by norm_num) (by norm_num) sgGenQ sg919101_headQ sgRowsQ

theorem pEnumCheck_ok : pEnumCheck () = true := by
  change (enumOK (bfsEnum (genP ()) 128) (genP ()) &&
    (bfsEnum (genP ()) 128).elems.size == 128) = true
  rw [sgTabP.2.1, Bool.true_and, beq_iff_eq]
  exact sgTabP.1.1

theorem qEnumCheck_ok : qEnumCheck () = true := by
  change (enumOK (bfsEnum (genQ ()) 64) (genQ ()) &&
    (bfsEnum (genQ ()) 64).elems.size == 64) = true
  rw [sgTabQ.2.1, Bool.true_and, beq_iff_eq]
  exact sgTabQ.1.1

theorem sgHead0 {R : ℕ → ℕ} {o n k : ℕ} (h : headK R o n k = true) : recX R o 0 = ONE := by
  unfold headK at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact h.1.1

theorem sgBuild {R : ℕ → ℕ} {n : ℕ} (h : ∀ t < n, rowK R (rstG R 0) 3 n 3 t = true) :
    ∀ i < n - 1, recF R 3 0 i ≤ i ∧ recF R 3 1 i < 3 ∧
      recX R 3 (i + 1) = MULF (recX R 3 (recF R 3 0 i)) (R (0 + recF R 3 1 i)) := by
  intro i hi
  obtain ⟨a, b, c⟩ := build_of_rows h i hi
  exact ⟨a, b, by rw [c, rstG, Nat.add_eq]⟩

theorem sgStep {R : ℕ → ℕ} {n : ℕ} (h : ∀ t < n, rowK R (rstG R 0) 3 n 3 t = true) :
    ∀ i < n * 3, recPOS R 3 3 i < n ∧
      recX R 3 (recPOS R 3 3 i) = MULF (recX R 3 (i / 3)) (R (0 + i % 3)) := by
  intro i hi
  obtain ⟨-, -, c, d, -⟩ := stepAt_facts (step_of_rows (by norm_num) (by norm_num) h i hi)
  exact ⟨c, by rw [d, rstG, Nat.add_eq]⟩

theorem pAutCheck_ok : pAutCheck () = true := by
  change autOK (bfsEnum (genP ()) 128) (genP ()) (genT ())
    (buildF (bfsEnum (genP ()) 128) (genT ())) = true
  rw [sgGenT]
  exact (autOK_of_codes3 (R := RPP) (RP := RT) (o := 3) (g := 0) (m := 10) (n := 128)
    (lr := List.range 10) (li0 := tl0) (li1 := tl1) (li2 := tl2) (ONEP := tOne)
    sgTabP.1 (by norm_num) (sgHead0 sg919101_headP) (sgBuild sgRowsP) sgTabP.2.2
    (sgStep sgRowsP) rfl sgGenP (by norm_num) rfl rfl rfl rfl (by decide) (by decide)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) sg919101_invP
    (autAt3_of_chunks (L := 128) (M := 1) (fun q hq => by
      obtain rfl : q = 0 := by omega
      exact sg919101_autP) (by norm_num))).1

theorem qAutCheck_ok : qAutCheck () = true := by
  change autOK (bfsEnum (genQ ()) 64) (genQ ()) (genU ())
    (buildF (bfsEnum (genQ ()) 64) (genU ())) = true
  rw [sgGenU]
  exact (autOK_of_codes3 (R := RQQ) (RP := RU) (o := 3) (g := 0) (m := 8) (n := 64)
    (lr := List.range 8) (li0 := ul0) (li1 := ul1) (li2 := ul2) (ONEP := uOne)
    sgTabQ.1 (by norm_num) (sgHead0 sg919101_headQ) (sgBuild sgRowsQ) sgTabQ.2.2
    (sgStep sgRowsQ) rfl sgGenQ (by norm_num) rfl rfl rfl rfl (by decide) (by decide)
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) sg919101_invQ
    (autAt3_of_chunks (L := 64) (M := 1) (fun q hq => by
      obtain rfl : q = 0 := by omega
      exact sg919101_autQ) (by norm_num))).1

end CFSG.KD.SylowG2

end
