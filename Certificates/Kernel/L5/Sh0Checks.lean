
module

public import Certificates.Data.Kernel.L5.Sh0T
public import CFSG.GH74.GLS.C3.Layer2.L5C5bInputs

public section

namespace CFSG.Certificates.Kernel.L5S

open CFSG.Certificates.Kernel.PkCV CFSG.GH74.GLS.C3.Layer2.L5

set_option maxRecDepth 100000

theorem sh0Chk_true : sh0Chk = true := by decide +kernel

theorem sh0C_codes : ((sh0C.map ev).map pcode).Nodup := by decide +kernel

theorem relK_mem : relK ∈ relsK := by decide +kernel

theorem gamGenK_true : ((List.range 4).all fun m => (List.range 3).all fun k =>
    decide (evFromT tF (xsK.getD m []) 0 (wdK.getD (gsK.getD k 0) []) =
      (xsK.getD m []).getD k 0)) = true := by
  decide +kernel

theorem invLK_lt : (invLT tF).all (fun x => decide (x < 128)) = true := by decide +kernel

end CFSG.Certificates.Kernel.L5S

end
