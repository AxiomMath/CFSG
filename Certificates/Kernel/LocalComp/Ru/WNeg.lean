module

public import Certificates.Kernel.LocalComp.Ru.WData
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelLC.RuW.Neg

open CertificateChecks.KernelLC.RuW CFSG.KC.Enum CFSG.KS CFSG.KC.LocalComp.ThreeWP

theorem neg_q : (!Nat.beq (TQY 0)
    (ppow 4060 12 (mask 12) (pidn 4060 12) (wordP 4060 12 letP qW) 59)) = true := by quickRfl

theorem neg_head_q : (!headWP 4060 12 TE 30 (TQY 1) (TQY 1) 1) = true := by quickRfl

theorem neg_head_y : (!headWP 4060 12 TE 30 (TQY 0) (TQY 0) 1) = true := by quickRfl

theorem neg_head_nc : (!headWP 4060 12 TE 30 (TQY 0) (TQY 1) 30) = true := by quickRfl

theorem neg_row_inv : (!rowWP 4060 12 giP gP 2 TE TR 30 1) = true := by quickRfl

theorem neg_row_m : (!rowWP 4060 12 gP giP 2 TE TR 1 1) = true := by quickRfl

theorem neg_comm : (!commWP 4060 12 (fun i => if i = 0 then TQY 1 else TE i) 1) = true := by
  quickRfl

end CertificateChecks.KernelLC.RuW.Neg

end
