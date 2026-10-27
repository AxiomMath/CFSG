module

public import Certificates.Kernel.LocalQT.Base.C4143
public import Certificates.Kernel.LocalQT.Base.C4076B
public import Certificates.Kernel.LocalQT.Base.C4076H
public import Certificates.Kernel.LocalQT.Base.C4076C
public import Certificates.Kernel.LocalQT.Base.C4076Q
public import Certificates.Kernel.LocalQT.Base.C4076W
public import CFSG.Certificates.Kernel.LocalQTFusionSSound

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.C4076

open CFSG.KC.LQT.FS CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Lin2
open CFSG.Sporadic.Ru.Native (ruData)

theorem check : FusionCert.fusionCheck ruData.n ruB ruTa ruTb (ruQp.map fun p => ruSLP[p.1]!)
    ruEnum.1 ruEnum.2.1 ruEnum.2.2 ruZI ruWit ruGW = true := by
  unfold ruEnum ruSLP
  rw [C4143.n_eq, C4143.ta_eq, C4143.tb_eq]
  exact fusS_sound (hw := by norm_num) (h := C4143.hd) (hnd := C4143.N.all) (hs := C4143.S.all)
    (hb := B.all) (hcov := by norm_num) (hf := fh) (hc := C.all) (s := 20) (R := 10) (CP := CP)
    (hcp := Q.all) (hwit := W.all)

theorem cert : FusionCert.FusionCertS ruData.n ruB ruTa ruTb ruProg ruQp ruEnum.1 ruEnum.2.1
    ruEnum.2.2 14 ruZI ruWit ruGW := by
  have hb := C4143.cert
  unfold BaseCertS BaseCert at hb
  obtain ⟨hqp, -, -, -, -, -, hinv, -, -, henum, hsize, -⟩ := hb
  unfold FusionCert.FusionCertS FusionCert.FusionCertT
  refine ⟨hqp, fun p hp => hinv _ (List.mem_map_of_mem hp), ?_, hsize, check⟩
  rw [List.map_map, List.map_map] at henum
  exact henum

end CFSG.KD.LQT.C4076

end
