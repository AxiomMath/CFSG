module

public import Certificates.Kernel.Sp6Cover.Data
public import Certificates.Kernel.Sporadic.RawGen
meta import Certificates.Kernel.Sp6Cover.Data
meta import Certificates.Data.PhilipHallSp6Cover
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.Misc.ArrEnum
import CFSG.Certificates.Kernel.Misc.ArrBind

public section

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelSp6Cover.YC 240 8 60
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Sp6CoverData.yS
  CertificateChecks.KernelSp6Cover.yBaseA 3 CertificateChecks.KernelSp6Cover.yWD

namespace CertificateChecks.KernelSp6Cover

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Sp6CoverData

theorem ybindS : ∀ j < 12, CFSG.KC.Misc.ArrEnum.arrBind yS[j]! 240 8 (YC.S j) = true := by
  decide +kernel

theorem ybind : yS.size = 12 ∧ (∀ j < 12, yS[j]! = unpack 240 8 (YC.S j)) ∧ yBaseA.size = 4 ∧
    ∀ t < 4, yBaseA[t]! = pg 8 (mask 8) YC.BP t :=
  ⟨by decide +kernel, fun j hj => CFSG.KC.Misc.ArrEnum.arrBind_sound (ybindS j hj),
    by decide +kernel, by decide +kernel⟩

theorem yperm : allN 12 (fun j => permOK 240 8 (mask 8) (240 * 8) (YC.S j) (YC.SI j)) = true := by
  quickRfl

theorem ysizes : (List.range 4).map (fun i => rcnt (YC.LR i)) = [240, 126, 12, 8] := by
  decide +kernel

end CertificateChecks.KernelSp6Cover

end
