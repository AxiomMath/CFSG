module

public import Certificates.Kernel.FiveStd.S0
public import Certificates.Data.Kernel.FiveStdKDiag
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.FiveStd

open CFSG.KC.FiveStdK

set_option Elab.async false

theorem s0_valid : S0c.all validK = true := by decide +kernel

theorem s0_nodup : S0c.Nodup := by decide +kernel

theorem s0_one : S0c.contains oneK = true := by decide +kernel

theorem s0_z : S0c.contains zK = true := by decide +kernel

theorem s0_zcomm : S0c.all (fun y => Nat.beq (mulK zK y) (mulK y zK)) = true := by decide +kernel

theorem s0_mul : S0c.all (fun x => S0c.all fun y => S0c.contains (mulK x y)) = true := by
  decide +kernel

theorem s0_inv : S0c.all (fun x => S0c.contains (invK x)) = true := by decide +kernel

theorem s0_cent :
    (S0c.filter fun x => S0c.all fun y => Nat.beq (mulK x y) (mulK y x)).length = 2 := by
  decide +kernel

theorem s0_kk : (S0c.filter inKKK).length = 32 := by decide +kernel

end CertificateChecks.FiveStd

end
