module

public import CFSG.Certificates.Kernel.Misc.OmegaSixClassSound
public import Certificates.Kernel.Misc.OmegaSix.Final
public import Certificates.Kernel.Misc.OmegaSix.ChecksK
public import Certificates.Kernel.Misc.OmegaSix.ChecksM
public import Certificates.Kernel.Misc.OmegaSix.ChecksN

public section

namespace CFSG.KD.OmegaSix

open CFSG.CGT.Foote82.OmegaSix CFSG.CGT.Foote82.CaseIIClassAux CFSG.KC.OmegaSix
  CFSG.KC.Misc.Spec CFSG.KD.YamakiRepF

theorem oMatR : rMat = matF (RO 2) := by
  rw [rMat.eq_1, matF]
  congr 1
  decide +kernel

theorem oMatRB : rBMat = matF (RO 4) := by
  rw [rBMat.eq_1, matF]
  congr 1
  decide +kernel

theorem cMatRA : rAMat = matF (RCA 4) := by
  rw [cRootA]
  exact oMatRA

theorem cMatRB : rBMat = matF (RCB 4) := by
  rw [cRootB]
  exact oMatRB

theorem cOrbA : ∀ q < 2, chunkF RCA (cjG RCA) 5 45 32 q = true := by
  intro q hq
  have h := ch919121AK.all q hq
  rwa [ch919121A] at h

theorem cOrbB : ∀ q < 9, chunkF RCB (cjG RCB) 5 270 32 q = true := by
  intro q hq
  have h := ch919121BK.all q hq
  rwa [ch919121B] at h

theorem cCls : ∀ q < 51, clsChunk RO 10 25920 RCA 45 RCB 270 512 q = true := by
  intro q hq
  have h := ch919121MK.all q hq
  rwa [ch919121M] at h

theorem omClassCheck_ok : omClassCheck () = true :=
  omClassCheck_of oMatA oMatB cMatRA cMatRB oHdrLt cRootA cRootB oHead oTab cHdrA cHeadA cOrbA
    cHdrB cHeadB cOrbB cCls

theorem centCountCheck_ok : centCountCheck () = true :=
  centCountCheck_of oMatA oMatB oMatR oMatRA oMatRB oHdrLt oHead oTab cntR cntRA cntRB

end CFSG.KD.OmegaSix

end
