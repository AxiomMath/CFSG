module

public import CFSG.Certificates.Kernel.Misc.OmegaSixASound
public import Certificates.Kernel.Misc.OmegaSix.FinalO
public import Certificates.Kernel.Misc.OmegaSix.HeadA
public import Certificates.Kernel.Misc.OmegaSix.ChecksCE
public import Certificates.Kernel.Misc.OmegaSix.ChecksCO

public section

namespace CFSG.KD.OmegaSix

open CFSG.CGT.Foote82.OmegaSix CFSG.KC.OmegaSix CFSG.KD.YamakiRepF

theorem aCentE : ∀ q < 51, centChunk RO 10 25920 (RO 3) (RO 4) RL 191 512 q = true := by
  intro q hq
  have h := ch919004EK.all q hq
  simp only [ch919004E, CFSG.KC.YamakiRepF.strictY_eq] at h
  exact h

theorem aCentO : ∀ q < 102, cLChunk ROO 3 51840 (RO 4) RL 191 512 q = true := by
  intro q hq
  have h := ch919004OK.all q hq
  simp only [ch919004O, CFSG.KC.YamakiRepF.strictY_eq] at h
  exact h

theorem oEnumCheck_ok : oEnumCheck () = true :=
  oEnumCheck_of (L := 256) (m := 203) oMatAO oMatBO oMatRO (by norm_num) oHeadO oTabO

theorem repCheck_ok : repCheck () = true :=
  repCheck_of oMatA oMatB oMatRA oMatRB oHead oTab aRepA aRepB

theorem classCheck_ok : classCheck () = true :=
  classCheck_of oMatA oMatB oMatRA oMatRB oHdrLt cRootA cRootB oHead oTab cHdrA cHeadA cOrbA
    cHdrB cHeadB cOrbB cCls oMatAO oMatBO oMatRO aHdrA aHeadA aOrbA aHdrB aHeadB aOrbB aSubA aSubB

theorem centCheck_ok : centCheck () = true :=
  centCheck_of oMatA oMatB oMatRA oMatRB oHead oTab oMatAO oMatBO oMatRO oHeadO oTabO aCentE aCentO

end CFSG.KD.OmegaSix

end
