module

public import Certificates.Kernel.LocalComp.F3.Fi24Sec
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LC.F3

open CFSG.KC.LQT CFSG.KC.LocalComp.CubParts

theorem neg_sec_shift : Bool.not (secPartsOK Fi24Sec.lay Fi24Sec.V Fi24Sec.P Fi24Sec.N Fi24Sec.RO 5
    (fun k => Fi24Sec.J (k + 1))) = true := by quickRfl

theorem neg_sec_vtab : Bool.not (vtabK Fi24Sec.lay 2 (fun i => Fi24Sec.V (Fi24Sec.RO i)) 5
    (fun n => Fi24Sec.U (n + 1)) Fi24Sec.HI 0 10) = true := by
  quickRfl

theorem neg_kmod : Bool.not (kmodK Fi24Sec.lay (fun _ => Fi24Sec.lay.unit 0)
    (Fi24Sec.V (Fi24Sec.RO 5)) 0 5) = true := by quickRfl

end CFSG.KD.LC.F3
