module

public import Certificates.Kernel.SporSch.PairBT.McLSylEData
public import Certificates.Kernel.SporSch.PairBT.McLSyl5A1
public import Certificates.Kernel.SporSch.PairBT.McLSyl5A2
public import Certificates.Kernel.SporSch.PairBT.McLSyl5B
public meta import Certificates.Kernel.SporSch.PairBT.McLSyl5BtData
public import CFSG.Certificates.Kernel.SporSch.McLSylowCountSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.SporSch.McLSylowSound
public import CFSG.Certificates.Kernel.SporSch.SylowCover

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.McLSyl5Chk

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.MBT CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.McLBT

theorem c1 : canonK 275 9 (mask 9) (275 * 9) R1 = true := by quickRfl

theorem c2 : canonK 275 9 (mask 9) (275 * 9) R2 = true := by quickRfl

theorem s1 :
    siftK 275 9 (mask 9) (275 * 9) (pidn 275 9) PMcL.LR PMcL.TRI PMcL.BP 5 0 R1 = true := by
  quickRfl

theorem s2 :
    siftK 275 9 (mask 9) (275 * 9) (pidn 275 9) PMcL.LR PMcL.TRI PMcL.BP 5 0 R2 = true := by
  quickRfl

theorem o1 : ordIs 275 9 (mask 9) (pidn 275 9) R1 (5 - 1) = true := by quickRfl

theorem o2 : ordIs 275 9 (mask 9) (pidn 275 9) R2 (5 - 1) = true := by quickRfl

end CertificateChecks.KernelSporSch.McLSyl5Chk

#kss_btjoin
  CertificateChecks.KernelSporSch.McLSyl5Bt.J0 CertificateChecks.KernelSporSch.PMcL 275 9 4
  CertificateChecks.KernelSporSch.McLBT.R1 CertificateChecks.KernelSporSch.McLBT.syl5BtHint 0

#kss_btjoin
  CertificateChecks.KernelSporSch.McLSyl5Bt.J1 CertificateChecks.KernelSporSch.PMcL 275 9 4
  CertificateChecks.KernelSporSch.McLBT.R2 CertificateChecks.KernelSporSch.McLBT.syl5BtHint 1

namespace CertificateChecks.KernelSporSch.McLSyl5Chk

open CFSG.KS CFSG.KS.SporSch.MBT CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.McLBT

theorem b1 : btK 275 9 (mask 9) (275 * 9) PMcL.BP 5 PMcL.LR PMcL.TR PMcL.TRI R1 R1 = 750 :=
  McLSyl5Bt.J0.hb

theorem b2 : btK 275 9 (mask 9) (275 * 9) PMcL.BP 5 PMcL.LR PMcL.TR PMcL.TRI R2 R2 = 25 :=
  McLSyl5Bt.J1.hb

end CertificateChecks.KernelSporSch.McLSyl5Chk

end
