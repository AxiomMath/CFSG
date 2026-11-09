module

public import Certificates.Kernel.Sporadic.RawGenSchOJ
public import Certificates.Kernel.UnitarySix.Sec3.Arrs
meta import Certificates.Kernel.UnitarySix.Sec3.Arrs
public meta import Certificates.Kernel.Sporadic.RawGenSchOJ
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Fischer.T46Unitary
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
meta import CFSG.Certificates.NativeSchreierCard
meta import CFSG.Fischer.T46Unitary
meta import CFSG.LieType.BorelTits.CompleteFlag
meta import CFSG.LieType.Chevalley.C2E6StandardFixedData
meta import CFSG.LieType.Chevalley.C2E6UnitaryFourImages

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_data CertificateChecks.KernelU6.Sec3.CK1 693 10 64 64
  CertificateChecks.KernelU6.Sec3.sK1 CertificateChecks.KernelU6.Sec3.bK1 5
  CertificateChecks.KernelU6.Sec3.dK1

#ks_rawchain_sl2_lv CertificateChecks.KernelU6.Sec3.CK1 0 0 11
#ks_rawchain_sl2_lv CertificateChecks.KernelU6.Sec3.CK1 1 0 11
#ks_rawchain_sl2_lv CertificateChecks.KernelU6.Sec3.CK1 2 0 11

namespace CertificateChecks.KernelU6.Sec3.CK1

theorem sch1_0_0 : CFSG.KS.Raw.schK 693 10 (CFSG.KS.mask 10) (693 * 10)
    (CFSG.KC.Enum.pidn 693 10) S SI LR TR TRI 9 BP 3 1
    (CFSG.KS.Raw.stepsAt 693 10 S 9 BP 1) (0 * 64 + 0 * 6) 6 = true := by
  decide +kernel

theorem sch1_0_1 : CFSG.KS.Raw.schK 693 10 (CFSG.KS.mask 10) (693 * 10)
    (CFSG.KC.Enum.pidn 693 10) S SI LR TR TRI 9 BP 3 1
    (CFSG.KS.Raw.stepsAt 693 10 S 9 BP 1) (0 * 64 + 1 * 6) 6 = true := by
  decide +kernel

theorem sch1_0_2 : CFSG.KS.Raw.schK 693 10 (CFSG.KS.mask 10) (693 * 10)
    (CFSG.KC.Enum.pidn 693 10) S SI LR TR TRI 9 BP 3 1
    (CFSG.KS.Raw.stepsAt 693 10 S 9 BP 1) (0 * 64 + 2 * 6) 6 = true := by
  decide +kernel

theorem sch1_0_3 : CFSG.KS.Raw.schK 693 10 (CFSG.KS.mask 10) (693 * 10)
    (CFSG.KC.Enum.pidn 693 10) S SI LR TR TRI 9 BP 3 1
    (CFSG.KS.Raw.stepsAt 693 10 S 9 BP 1) (0 * 64 + 3 * 6) 6 = true := by
  decide +kernel

theorem sch1_0_4 : CFSG.KS.Raw.schK 693 10 (CFSG.KS.mask 10) (693 * 10)
    (CFSG.KC.Enum.pidn 693 10) S SI LR TR TRI 9 BP 3 1
    (CFSG.KS.Raw.stepsAt 693 10 S 9 BP 1) (0 * 64 + 4 * 6) 6 = true := by
  decide +kernel

theorem sch1_0_5 : CFSG.KS.Raw.schK 693 10 (CFSG.KS.mask 10) (693 * 10)
    (CFSG.KC.Enum.pidn 693 10) S SI LR TR TRI 9 BP 3 1
    (CFSG.KS.Raw.stepsAt 693 10 S 9 BP 1) (0 * 64 + 5 * 6) 6 = true := by
  decide +kernel

theorem sch1_0_6 : CFSG.KS.Raw.schK 693 10 (CFSG.KS.mask 10) (693 * 10)
    (CFSG.KC.Enum.pidn 693 10) S SI LR TR TRI 9 BP 3 1
    (CFSG.KS.Raw.stepsAt 693 10 S 9 BP 1) (0 * 64 + 6 * 6) 6 = true := by
  decide +kernel

theorem sch1_0_7 : CFSG.KS.Raw.schK 693 10 (CFSG.KS.mask 10) (693 * 10)
    (CFSG.KC.Enum.pidn 693 10) S SI LR TR TRI 9 BP 3 1
    (CFSG.KS.Raw.stepsAt 693 10 S 9 BP 1) (0 * 64 + 7 * 6) 6 = true := by
  decide +kernel

theorem sch1_0_8 : CFSG.KS.Raw.schK 693 10 (CFSG.KS.mask 10) (693 * 10)
    (CFSG.KC.Enum.pidn 693 10) S SI LR TR TRI 9 BP 3 1
    (CFSG.KS.Raw.stepsAt 693 10 S 9 BP 1) (0 * 64 + 8 * 6) 6 = true := by
  decide +kernel

theorem sch1_0_9 : CFSG.KS.Raw.schK 693 10 (CFSG.KS.mask 10) (693 * 10)
    (CFSG.KC.Enum.pidn 693 10) S SI LR TR TRI 9 BP 3 1
    (CFSG.KS.Raw.stepsAt 693 10 S 9 BP 1) (0 * 64 + 9 * 6) 6 = true := by
  decide +kernel

theorem sch1_0_10 : CFSG.KS.Raw.schK 693 10 (CFSG.KS.mask 10) (693 * 10)
    (CFSG.KC.Enum.pidn 693 10) S SI LR TR TRI 9 BP 3 1
    (CFSG.KS.Raw.stepsAt 693 10 S 9 BP 1) (0 * 64 + 10 * 6) 6 = true := by
  decide +kernel

theorem sch1_0 : CFSG.KS.Raw.schK 693 10 (CFSG.KS.mask 10) (693 * 10)
    (CFSG.KC.Enum.pidn 693 10) S SI LR TR TRI 9 BP 3 1
    (CFSG.KS.Raw.stepsAt 693 10 S 9 BP 1) (0 * 64) 64 = true :=
  CFSG.KS.Raw.schK_of_sub (K := 11) (SCH := 6) (by decide) fun k hk =>
    match k, hk with
    | 0, _ => sch1_0_0
    | 1, _ => sch1_0_1
    | 2, _ => sch1_0_2
    | 3, _ => sch1_0_3
    | 4, _ => sch1_0_4
    | 5, _ => sch1_0_5
    | 6, _ => sch1_0_6
    | 7, _ => sch1_0_7
    | 8, _ => sch1_0_8
    | 9, _ => sch1_0_9
    | 10, _ => sch1_0_10
    | _ + 11, h => absurd h (by omega)

theorem sch2_0_0 : CFSG.KS.Raw.schK 693 10 (CFSG.KS.mask 10) (693 * 10)
    (CFSG.KC.Enum.pidn 693 10) S SI LR TR TRI 9 BP 3 2
    (CFSG.KS.Raw.stepsAt 693 10 S 9 BP 2) (0 * 64 + 0 * 6) 6 = true := by
  decide +kernel

theorem sch2_0_1 : CFSG.KS.Raw.schK 693 10 (CFSG.KS.mask 10) (693 * 10)
    (CFSG.KC.Enum.pidn 693 10) S SI LR TR TRI 9 BP 3 2
    (CFSG.KS.Raw.stepsAt 693 10 S 9 BP 2) (0 * 64 + 1 * 6) 6 = true := by
  decide +kernel

theorem sch2_0_2 : CFSG.KS.Raw.schK 693 10 (CFSG.KS.mask 10) (693 * 10)
    (CFSG.KC.Enum.pidn 693 10) S SI LR TR TRI 9 BP 3 2
    (CFSG.KS.Raw.stepsAt 693 10 S 9 BP 2) (0 * 64 + 2 * 6) 6 = true := by
  decide +kernel

theorem sch2_0_3 : CFSG.KS.Raw.schK 693 10 (CFSG.KS.mask 10) (693 * 10)
    (CFSG.KC.Enum.pidn 693 10) S SI LR TR TRI 9 BP 3 2
    (CFSG.KS.Raw.stepsAt 693 10 S 9 BP 2) (0 * 64 + 3 * 6) 6 = true := by
  decide +kernel

theorem sch2_0_4 : CFSG.KS.Raw.schK 693 10 (CFSG.KS.mask 10) (693 * 10)
    (CFSG.KC.Enum.pidn 693 10) S SI LR TR TRI 9 BP 3 2
    (CFSG.KS.Raw.stepsAt 693 10 S 9 BP 2) (0 * 64 + 4 * 6) 6 = true := by
  decide +kernel

theorem sch2_0_5 : CFSG.KS.Raw.schK 693 10 (CFSG.KS.mask 10) (693 * 10)
    (CFSG.KC.Enum.pidn 693 10) S SI LR TR TRI 9 BP 3 2
    (CFSG.KS.Raw.stepsAt 693 10 S 9 BP 2) (0 * 64 + 5 * 6) 6 = true := by
  decide +kernel

theorem sch2_0_6 : CFSG.KS.Raw.schK 693 10 (CFSG.KS.mask 10) (693 * 10)
    (CFSG.KC.Enum.pidn 693 10) S SI LR TR TRI 9 BP 3 2
    (CFSG.KS.Raw.stepsAt 693 10 S 9 BP 2) (0 * 64 + 6 * 6) 6 = true := by
  decide +kernel

theorem sch2_0_7 : CFSG.KS.Raw.schK 693 10 (CFSG.KS.mask 10) (693 * 10)
    (CFSG.KC.Enum.pidn 693 10) S SI LR TR TRI 9 BP 3 2
    (CFSG.KS.Raw.stepsAt 693 10 S 9 BP 2) (0 * 64 + 7 * 6) 6 = true := by
  decide +kernel

theorem sch2_0_8 : CFSG.KS.Raw.schK 693 10 (CFSG.KS.mask 10) (693 * 10)
    (CFSG.KC.Enum.pidn 693 10) S SI LR TR TRI 9 BP 3 2
    (CFSG.KS.Raw.stepsAt 693 10 S 9 BP 2) (0 * 64 + 8 * 6) 6 = true := by
  decide +kernel

theorem sch2_0_9 : CFSG.KS.Raw.schK 693 10 (CFSG.KS.mask 10) (693 * 10)
    (CFSG.KC.Enum.pidn 693 10) S SI LR TR TRI 9 BP 3 2
    (CFSG.KS.Raw.stepsAt 693 10 S 9 BP 2) (0 * 64 + 9 * 6) 6 = true := by
  decide +kernel

theorem sch2_0_10 : CFSG.KS.Raw.schK 693 10 (CFSG.KS.mask 10) (693 * 10)
    (CFSG.KC.Enum.pidn 693 10) S SI LR TR TRI 9 BP 3 2
    (CFSG.KS.Raw.stepsAt 693 10 S 9 BP 2) (0 * 64 + 10 * 6) 6 = true := by
  decide +kernel

theorem sch2_0 : CFSG.KS.Raw.schK 693 10 (CFSG.KS.mask 10) (693 * 10)
    (CFSG.KC.Enum.pidn 693 10) S SI LR TR TRI 9 BP 3 2
    (CFSG.KS.Raw.stepsAt 693 10 S 9 BP 2) (0 * 64) 64 = true :=
  CFSG.KS.Raw.schK_of_sub (K := 11) (SCH := 6) (by decide) fun k hk =>
    match k, hk with
    | 0, _ => sch2_0_0
    | 1, _ => sch2_0_1
    | 2, _ => sch2_0_2
    | 3, _ => sch2_0_3
    | 4, _ => sch2_0_4
    | 5, _ => sch2_0_5
    | 6, _ => sch2_0_6
    | 7, _ => sch2_0_7
    | 8, _ => sch2_0_8
    | 9, _ => sch2_0_9
    | 10, _ => sch2_0_10
    | _ + 11, h => absurd h (by omega)

end CertificateChecks.KernelU6.Sec3.CK1

namespace CertificateChecks.KernelU6.Sec3

@[expose] def wK1o : List (List Nat) :=
  [[2, 1, 2, 0, 2, 1, 2, 0], [0], [2, 0, 2, 1, 0, 1, 2, 0, 2, 1, 0, 1], [1], [2]]

end CertificateChecks.KernelU6.Sec3

#ks_rawchain_sl2_osub CertificateChecks.KernelU6.Sec3.CK1 1 3 4
  CertificateChecks.KernelU6.Sec3.wK1o
#ks_rawchain_sl2_scho CertificateChecks.KernelU6.Sec3.CK1 0 2

#ks_rawchain_sl2_joino CertificateChecks.KernelU6.Sec3.CK1

end
