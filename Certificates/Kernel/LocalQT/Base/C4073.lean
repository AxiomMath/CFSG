module

public import Certificates.Kernel.LocalQT.Base.C4073H
public import Certificates.Kernel.LocalQT.Base.C4073Q
public import Certificates.Kernel.LocalQT.Base.C4073W
public import Certificates.Kernel.LocalQT.Base.C4141
public import CFSG.Certificates.Kernel.LocalQTFusionBSound

public section

namespace CFSG.KD.LQT.C4073

open CFSG.KC.LQT.FB CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Lin2

theorem cert : FusionCert.FusionCertS 8330 heB heTa heTb heProg heQp heEnum.1 heEnum.2.1
    heEnum.2.2 10 heZI heWit heGW := by
  unfold heEnum heSLP
  rw [C4141.ta_eq, C4141.tb_eq]
  exact fusB_sound (hw := by norm_num) (s := 10) (R := 16) (CP := CP) (h := hd)
    (hnd := C4141.N.all) (hcp := Q.all) (hwit := W.all)

end CFSG.KD.LQT.C4073

end
