module

public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData
public meta import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData
public meta import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.OmegaEight.Bases
public meta import Certificates.Kernel.OmegaEight.Bases
public import Certificates.Kernel.OmegaEight.Bases3009
public meta import Certificates.Kernel.OmegaEight.Bases3009
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Sporadic.RawGenSchOJ
public meta import Certificates.Kernel.Sporadic.RawGenSchOJ

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

@[expose] def wSubAQ : List (List Nat) :=
  [[0], [1], [2], [3], [4, 0, 4, 4], [4, 1, 4, 4], [4, 4, 0, 4], [4, 4, 1, 4], [4], [5]]

@[expose] def wSubSY : List (List Nat) := [[0], [1], [3, 2, 3], [2], [3]]

end CertificateChecks.KernelO8

#ks_rawchain_sl2_data CertificateChecks.KernelO8.AQ 360 9 24 24 CFSG.EvenSmallLie.OmegaEight.autS
  CertificateChecks.KernelO8.omBaseP 10 CFSG.EvenSmallLie.OmegaEight.autWords

#ks_rawchain_sl2_lv CertificateChecks.KernelO8.AQ 0 0 15
#ks_rawchain_sl2_lv CertificateChecks.KernelO8.AQ 1 0 15
#ks_rawchain_sl2_lv CertificateChecks.KernelO8.AQ 2 0 15
#ks_rawchain_sl2_lv CertificateChecks.KernelO8.AQ 3 0 15
#ks_rawchain_sl2_lv CertificateChecks.KernelO8.AQ 4 0 15
#ks_rawchain_sl2_lv CertificateChecks.KernelO8.AQ 5 0 15
#ks_rawchain_sl2_lv CertificateChecks.KernelO8.AQ 6 0 15

#ks_rawchain_sl2_sch CertificateChecks.KernelO8.AQ 1 0 3
#ks_rawchain_sl2_sch CertificateChecks.KernelO8.AQ 2 0 2
#ks_rawchain_sl2_sch CertificateChecks.KernelO8.AQ 3 0 1
#ks_rawchain_sl2_sch CertificateChecks.KernelO8.AQ 4 0 1
#ks_rawchain_sl2_sch CertificateChecks.KernelO8.AQ 5 0 1
#ks_rawchain_sl2_sch CertificateChecks.KernelO8.AQ 6 0 1

#ks_rawchain_sl2_osub CertificateChecks.KernelO8.AQ 0 1 2 3 8 9 CertificateChecks.KernelO8.wSubAQ
#ks_rawchain_sl2_scho CertificateChecks.KernelO8.AQ 0 15

#ks_rawchain_sl2_joino CertificateChecks.KernelO8.AQ

#ks_rawchain_sl2_data CertificateChecks.KernelO8.SY 360 9 24 24 CFSG.EvenSmallLie.OmegaEight.sylowS
  CertificateChecks.KernelO8.syBaseP 5 CFSG.EvenSmallLie.OmegaEight.sylowWords

#ks_rawchain_sl2_lv CertificateChecks.KernelO8.SY 0 0 15
#ks_rawchain_sl2_lv CertificateChecks.KernelO8.SY 1 0 15
#ks_rawchain_sl2_lv CertificateChecks.KernelO8.SY 2 0 15
#ks_rawchain_sl2_lv CertificateChecks.KernelO8.SY 3 0 15
#ks_rawchain_sl2_lv CertificateChecks.KernelO8.SY 4 0 15

#ks_rawchain_sl2_sch CertificateChecks.KernelO8.SY 1 0 1
#ks_rawchain_sl2_sch CertificateChecks.KernelO8.SY 2 0 1
#ks_rawchain_sl2_sch CertificateChecks.KernelO8.SY 3 0 1
#ks_rawchain_sl2_sch CertificateChecks.KernelO8.SY 4 0 1

#ks_rawchain_sl2_osub CertificateChecks.KernelO8.SY 0 1 3 4 CertificateChecks.KernelO8.wSubSY
#ks_rawchain_sl2_scho CertificateChecks.KernelO8.SY 0 3

#ks_rawchain_sl2_joino CertificateChecks.KernelO8.SY

end
