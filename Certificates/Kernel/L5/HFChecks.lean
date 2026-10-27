module

public import Certificates.Kernel.L5.HFPData
import CFSG.Certificates.Kernel.Common.Each

public section

namespace CFSG.Certificates.Kernel.L5H

set_option maxRecDepth 100000

theorem n24TabK : n24TabChk = true := by decide +kernel

theorem d8K : d8ChkAll = true := by decide +kernel

theorem G72AllK : (G72TabChk && G72Chk && G72LinChk && g72PinChk g72GN g72MP) = true := by
  decide +kernel

theorem band_left {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a <;> cases b <;> simp_all

theorem band_right {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a <;> cases b <;> simp_all

theorem G72TabK : G72TabChk = true := band_left (band_left (band_left G72AllK))

theorem G72K : G72Chk = true := band_right (band_left (band_left G72AllK))

theorem G72LinK : G72LinChk = true := band_right (band_left G72AllK)

theorem G72PinK : g72PinChk g72GN g72MP = true := band_right G72AllK

end CFSG.Certificates.Kernel.L5H

end
