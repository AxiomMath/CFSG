module

public import Certificates.Kernel.FiveStd.S0
public import Certificates.Data.Kernel.FiveStdKDiag
public import Certificates.Data.Kernel.RangeSplit
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.FiveStd

open CFSG.KC.FiveStdK CFSG.KC.RangeSplit

set_option Elab.async false

theorem s0_valid : S0c.all validK = true := by decide +kernel

theorem s0_nodup : S0c.Nodup := by decide +kernel

theorem s0_one : S0c.contains oneK = true := by decide +kernel

theorem s0_z : S0c.contains zK = true := by decide +kernel

theorem s0_zcomm : S0c.all (fun y => Nat.beq (mulK zK y) (mulK y zK)) = true := by decide +kernel

theorem s0_mul0 : (S0c.take 32).all (fun x => S0c.all fun y => S0c.contains (mulK x y)) = true := by
  quickRfl

theorem s0_mul1 : ((S0c.drop 32).take 32).all (fun x => S0c.all fun y => S0c.contains (mulK x y)) = true := by
  quickRfl

theorem s0_mul2 : (((S0c.drop 32).drop 32).take 32).all (fun x => S0c.all fun y => S0c.contains (mulK x y)) = true := by
  quickRfl

theorem s0_mul3 : (((S0c.drop 32).drop 32).drop 32).all (fun x => S0c.all fun y => S0c.contains (mulK x y)) = true := by
  quickRfl

theorem s0_mul : S0c.all (fun x => S0c.all fun y => S0c.contains (mulK x y)) = true :=
  all_cut S0c 32 s0_mul0 (all_cut (S0c.drop 32) 32 s0_mul1 (all_cut ((S0c.drop 32).drop 32) 32 s0_mul2 (s0_mul3)))

theorem s0_inv : S0c.all (fun x => S0c.contains (invK x)) = true := by decide +kernel

theorem s0_cent :
    (S0c.filter fun x => S0c.all fun y => Nat.beq (mulK x y) (mulK y x)).length = 2 := by
  decide +kernel

theorem s0_kk : (S0c.filter inKKK).length = 32 := by decide +kernel

end CertificateChecks.FiveStd

end
