module

public import CFSG.Certificates.Kernel.Misc.OmegaSixFSound
public import Certificates.Kernel.Misc.OmegaSix.HeadF
public import Certificates.Kernel.Misc.OmegaSix.ChecksF5
public import Certificates.Kernel.Misc.OmegaSix.ChecksFP
public import Certificates.Kernel.Misc.OmegaSix.FinalO

public section

namespace CFSG.KD.OmegaSix

open CFSG.CGT.Foote82.OmegaSix CFSG.KC.OmegaSix CFSG.KD.YamakiRepF

theorem fOrb : ∀ q < 11, chunkF3 RCF (cjO ROO RCF) 5 5184 512 q = true := by
  intro q hq
  have h := ch919150OK.all q hq
  simp only [ch919150O] at h
  exact h

theorem fFive : ∀ q < 51, fiveChunk RO 10 25920 RCF 5184 512 q = true := by
  intro q hq
  have h := ch919150FK.all q hq
  simp only [ch919150F] at h
  exact h

theorem fPair : ∀ q < 51, pairChunk RO 10 25920 relators (RO 1) PWF 10 512 q = true := by
  intro q hq
  have h := ch919150PK.all q hq
  simp only [ch919150P, CFSG.KC.YamakiRepF.strictY_eq] at h
  exact h

theorem fiveCheck_ok : fiveCheck () = true :=
  fiveCheck_of oMatA oMatB oHdrLt oHead oTab oMatAO oMatBO oMatRO fHdr fHead fOrb fFive

theorem pairCheck_ok : pairCheck () = true :=
  pairCheck_of oMatA oMatB oHead oTab oMatAO oMatBO oMatRO oHeadO oTabO fPW fPair

end CFSG.KD.OmegaSix

end
