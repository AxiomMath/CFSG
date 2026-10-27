module

public import CFSG.Certificates.Kernel.LocalQTBaseWSound
public import Certificates.Kernel.J2Cover.Tab4067
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.LQT.C4142

open CFSG.KC.LQT.BW CFSG.QuasithinUnique.K1.SporadicPerm

@[expose] def ta : List Nat :=
  CFSG.QuasithinUnique.Setup.X1.j2ta_0.toList ++ CFSG.QuasithinUnique.Setup.X1.j2ta_1.toList

@[expose] def tb : List Nat :=
  CFSG.QuasithinUnique.Setup.X1.j2tb_0.toList ++ CFSG.QuasithinUnique.Setup.X1.j2tb_1.toList

theorem ta_eq : j2ta = ta := by
  rw [← CertificateChecks.KernelJ2Cover.Tab.facts.1]
  simp [ta, CFSG.QuasithinUnique.Setup.X1.j2Data, CFSG.QuasithinUnique.Setup.X1.j2ta]

theorem tb_eq : j2tb = tb := by
  rw [← CertificateChecks.KernelJ2Cover.Tab.facts.2]
  simp [tb, CFSG.QuasithinUnique.Setup.X1.j2Data, CFSG.QuasithinUnique.Setup.X1.j2tb]

theorem valid : slpValidAux j2Prog 2 = true := by quickRfl

theorem bk : baseWK 315 9 (List.range 315) ta tb j2Prog j2Qp 143 181 185 183 187 7 100000 128 =
    true := by
  quickRfl

theorem cert : BaseCertS 315 (List.range 315) j2SLP j2Qp 143 181 185 183 187
    j2Enum.1 j2Enum.2.1 j2Enum.2.2 7 := by
  have h := baseW_sound (by norm_num) _ _ _ _ _ _ _ _ _ _ _ _ _ bk
  rw [← ta_eq, ← tb_eq] at h
  exact h

end CFSG.KD.LQT.C4142

end
