module

public import Certificates.Kernel.KDenseP.NortonSLP.Base
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Gen13EChk0
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Gen13EChk1
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Gen13Parse
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125000
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125001
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125002
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125003
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125004
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125005
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125006
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125007
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.C125008

public section

namespace CertificateChecks.KernelKDenseP.NortonSLP.Gen13

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.NortonSLP
  CertificateChecks.KernelKDenseP.Axis CertificateChecks.KernelKDenseP.NortonSLP
  CFSG.AGLEmbedding.Norton CFSG.AGLEmbedding.Norton.Gen13

set_option maxRecDepth 100000

theorem monoTab_ok : monoTabOK CFSG.KD.KDF.F CFSG.KD.SLP.Gen13M.MT = true := by
  kd_monoTabL CFSG.KD.SLP.Gen13ME t

theorem data_ok : dataOKP CFSG.KD.KDF.F CFSG.KD.SLP.Gen13M.MT CFSG.KD.KDF.KT CFSG.KD.KDF.TH
    CFSG.KD.KDF.OCT CFSG.KD.KDF.DU1 = true :=
  andB_true CFSG.KD.KDF.th_ok (andB_true CFSG.KD.KDF.oct_ok (andB_true CFSG.KD.KDF.du1_ok
    (andB_true CFSG.KD.KDF.keys_ok (andB_true CFSG.KD.KDF.keyPlanes_ok (andB_true CFSG.KD.KDF.fix_ok
      monoTab_ok)))))

theorem steps_eq : gen13Steps = CFSG.KD.SLP.Gen13.S := by
  unfold gen13Steps gen13Text
  exact steps_eq_of_parse CFSG.KD.SLP.Gen13.parse_ok

theorem c125000 : prodCheck gen13Gens gen13Steps 0 76 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125000.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125000 CFSG.KD.SLP.Gen13 CFSG.KD.SLP.c125000.E)

theorem c125001 : prodCheck gen13Gens gen13Steps 76 145 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125001.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125001 CFSG.KD.SLP.Gen13 CFSG.KD.SLP.c125001.E)

theorem c125002 : prodCheck gen13Gens gen13Steps 145 207 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125002.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125002 CFSG.KD.SLP.Gen13 CFSG.KD.SLP.c125002.E)

theorem c125003 : prodCheck gen13Gens gen13Steps 207 264 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125003.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125003 CFSG.KD.SLP.Gen13 CFSG.KD.SLP.c125003.E)

theorem c125004 : prodCheck gen13Gens gen13Steps 264 278 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125004.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125004 CFSG.KD.SLP.Gen13 CFSG.KD.SLP.c125004.E)

theorem c125005 : prodCheck gen13Gens gen13Steps 278 288 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125005.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125005 CFSG.KD.SLP.Gen13 CFSG.KD.SLP.c125005.E)

theorem c125006 : prodCheck gen13Gens gen13Steps 288 311 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125006.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125006 CFSG.KD.SLP.Gen13 12 CFSG.KD.SLP.c125006.E)

theorem c125007 : prodCheck gen13Gens gen13Steps 311 322 = true := by
  rw [steps_eq]
  exact prodCheck_of CFSG.KD.SLP.c125007.idx
    (kd_slpK% data_ok CFSG.KD.SLP.c125007 CFSG.KD.SLP.Gen13 12 CFSG.KD.SLP.c125007.E)

theorem c125008 : prodTargetsCheck gen13Gens gen13Steps 322 gen13Targets = true := by
  rw [steps_eq]
  exact prodTargetsCheck_of CFSG.KD.SLP.c125008.tgt
    (kd_slpK% data_ok CFSG.KD.SLP.c125008 CFSG.KD.SLP.Gen13 CFSG.KD.SLP.c125008.E)

end CertificateChecks.KernelKDenseP.NortonSLP.Gen13

end
