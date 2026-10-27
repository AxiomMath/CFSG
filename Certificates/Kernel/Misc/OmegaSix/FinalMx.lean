module

public import CFSG.Certificates.Kernel.Misc.OmegaSixMxSound
public import Certificates.Kernel.Misc.OmegaSix.FinalO
public import Certificates.Kernel.Misc.OmegaSix.MaxHead
public import Certificates.Kernel.Misc.OmegaSix.MaxChecks1
public import Certificates.Kernel.Misc.OmegaSix.MaxChecks2
public import Certificates.Kernel.Misc.OmegaSix.MaxChecksW

public section

namespace CFSG.KD.OmegaSix

open CFSG.CGT.Foote82.OmegaSix CFSG.KC.OmegaSix CFSG.KC.Misc.Spec CFSG.KD.YamakiRepF
  CFSG.KD.YamakiRep

theorem maxMatCheck_ok : maxMatCheck () = true := by decide +kernel

theorem mMatC1 : cr1Mat = matF (RMC 0) := by
  rw [cr1Mat.eq_1, matF]
  congr 1
  decide +kernel

theorem mMatC2 : cr2Mat = matF (RMC 1) := by
  rw [cr2Mat.eq_1, matF]
  congr 1
  decide +kernel

theorem mMatD1 : dc1Mat = matF (RMH 0) := by
  rw [dc1Mat.eq_1, matF]
  congr 1
  decide +kernel

theorem mMatD2 : dc2Mat = matF (RMH 1) := by
  rw [dc2Mat.eq_1, matF]
  congr 1
  decide +kernel

theorem mcTab : ∀ q < 3, chunkF RMC (rstG RMC 0) 2 720 256 q = true := by
  intro q hq
  have h := ch919005CK.all q hq
  rwa [ch919005C] at h

theorem m1Tab : ∀ q < 102, chunkF3 RM1 (rstG RM1 0) 3 25920 256 q = true := by
  intro q hq
  have h := ch919005M1K.all q hq
  rwa [ch919005M1] at h

theorem m2Tab : ∀ q < 102, chunkF3 RM2 (rstG RM2 0) 3 25920 256 q = true := by
  intro q hq
  have h := ch919005M2K.all q hq
  rwa [ch919005M2] at h

theorem mCos : ∀ q < 102,
    cosetChunk RO 10 25920 RMC 2 720 RMW (RO 2) (RMH 2) (RMH 3) 256 q = true := by
  intro q hq
  have h := ch919005WK.all q hq
  simp only [ch919005W, CFSG.KC.YamakiRepF.strictY_eq] at h
  exact h

theorem maxMemCheck_ok : maxMemCheck () = true :=
  maxMemCheck_of oMatA oMatB oHead oTab mMatC1 mMatC2 mMatD1 mMatD2 mPos0 mPos1 mPos2 mPos3

theorem crEnumCheck_ok : crEnumCheck () = true := crEnumCheck_of mMatC1 mMatC2 mcHead mcTab

theorem maxGen1Check_ok : maxGen1Check () = true := by
  have hg : ∀ j < 3, (genCr1 ())[j]! = arrF (RM1 (0 + j)) := by
    intro j hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · rw [Nat.add_zero, m1Gen0, arrF, ← mMatC1]
      rfl
    · rw [Nat.zero_add, m1Gen1, arrF, ← mMatC2]
      rfl
    · rw [Nat.zero_add, m1Gen2, arrF, ← mMatD1]
      rfl
  exact maxGenCheck_of (L := 256) (m := 102) rfl hg (by norm_num) m1Head m1Tab

theorem maxGen2Check_ok : maxGen2Check () = true := by
  have hg : ∀ j < 3, (genCr2 ())[j]! = arrF (RM2 (0 + j)) := by
    intro j hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · rw [Nat.add_zero, m2Gen0, arrF, ← mMatC1]
      rfl
    · rw [Nat.zero_add, m2Gen1, arrF, ← mMatC2]
      rfl
    · rw [Nat.zero_add, m2Gen2, arrF, ← mMatD2]
      rfl
  exact maxGenCheck_of (L := 256) (m := 102) rfl hg (by norm_num) m2Head m2Tab

theorem maxCosetCheck_ok : maxCosetCheck () = true :=
  maxCosetCheck_of oMatA oMatB oMatR mMatC1 mMatC2 mMatD1 mMatD2 mS1 mS2 oHead oTab mcHead mcTab
    mCos

theorem maxReflCheck_ok : maxReflCheck () = true :=
  maxReflCheck_of (L := 256) (m := 203) (L' := 512) (m' := 102) oMatAO oMatBO oMatRO oLtR rRoot
    (by norm_num) oHeadO oTabO rHdr rHead rOrb (by norm_num) oRefl

end CFSG.KD.OmegaSix

end
