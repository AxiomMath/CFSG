module

public import CFSG.Certificates.Kernel.Misc.OmegaSixSound
public import Certificates.Kernel.Misc.OmegaSix.Head
public import Certificates.Kernel.Misc.OmegaSix.Checks
public import Certificates.Kernel.Misc.OmegaSix.ChecksC

public section

namespace CFSG.KD.OmegaSix

open CFSG.CGT.Foote82.OmegaSix CFSG.CGT.Foote82.CaseIIClassAux CFSG.KC.OmegaSix
  CFSG.KC.Misc.Spec

theorem oMatA : aMat = matF (RO 0) := by
  rw [aMat.eq_1, matF]
  congr 1
  decide +kernel

theorem oMatB : bMat = matF (RO 1) := by
  rw [bMat.eq_1, matF]
  congr 1
  decide +kernel

theorem oMatRA : rAMat = matF (RO 3) := by
  rw [rAMat.eq_1, matF]
  congr 1
  decide +kernel

theorem oMatE1 : e1Mat = matF (RO 8) := by
  rw [e1Mat.eq_1, matF]
  congr 1
  decide +kernel

theorem oMatE2 : e2Mat = matF (RO 9) := by
  rw [e2Mat.eq_1, matF]
  congr 1
  decide +kernel

theorem oTab : ∀ q < 51, CFSG.KD.YamakiRepF.chunkF RO (CFSG.KD.YamakiRep.rstG RO 0) 10 25920 512 q =
    true := by
  intro q hq
  have h := oTabK.all q hq
  rwa [oTabC] at h

theorem oClos : ∀ q < 51, closChunk RO 10 25920 (RO 3) (RO 8) (RO 9) 512 q = true := by
  intro q hq
  have h := oClosK.all q hq
  simp only [oClosC, CFSG.KC.YamakiRepF.strictY_eq] at h
  exact h

theorem closureCheck_ok : closureCheck () = true :=
  closureCheck_of oMatA oMatB oMatRA oMatE1 oMatE2 oHdrLt oHead oTab oClos oCent1 oCent2 oPos

end CFSG.KD.OmegaSix

end
