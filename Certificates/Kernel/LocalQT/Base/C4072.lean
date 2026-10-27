module

public import Certificates.Kernel.LocalQT.Base.C4072Check
public import Certificates.Kernel.LocalQT.Base.C4075
public import CFSG.Certificates.Kernel.LocalQTBaseSound
public import CFSG.Certificates.Kernel.LocalQTFusionSound

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.C4072

open CFSG.KC.LQT.BC CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Lin2

theorem fusion : FusionCert.FusionCertS 24 (List.range 24) m24ta.toArray m24tb.toArray m24Prog
    m24Qp m24Enum.1 m24Enum.2.1 m24Enum.2.2 10 m24ZI m24Wit m24GW := by
  obtain ⟨hqp, -, -, -, -, -, hinv, -, -, hE, hs, -⟩ :=
    base_sound (by norm_num) _ _ _ _ _ _ _ _ _ _ _ _ C4075.b24
  unfold FusionCert.FusionCertS FusionCert.FusionCertT m24Enum m24SLP
  refine ⟨hqp, fun p hp => hinv _ (List.mem_map_of_mem hp), ?_, hs,
    fusion_sound (by norm_num) _ _ _ _ _ _ _ _ _ fk⟩
  simpa only [List.map_map, Function.comp_def] using hE

end CFSG.KD.LQT.C4072

end
