module

public import Certificates.Data.H9Four
public import Certificates.Data.Kernel.H9Four.Pk
public import Certificates.Kernel.H9Four.Data
public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallTree

set_option maxRecDepth 100000

public section

namespace CFSG.KD.H9Four

open CFSG.KC.H9Four CFSG.Quasithin.H13.H9Four

theorem ch7104_inv : checkInvK invLCodes invSCodes = true := by quickRfl

theorem ch7104_pinInv : CFSG.KC.Misc.eqLN inv (invAllK invLCodes invSCodes) = true := by quickRfl

@[expose] noncomputable def ch7104walk (c : Nat) : Bool :=
  walkK invLCodes invSCodes (Nat.mul (nat_lit 4096) c) (nat_lit 4096)

#kc_each ch7104walk 0 16

#kc_forall_tree ch7104_walk (fun c => ch7104walk c = true) 16 CFSG.KD.H9Four.ch7104walk

theorem ch7104_pin : pinK repCodes repG repX = true := by quickRfl

@[expose] noncomputable def ch7104row (i : Nat) : Bool :=
  closRowK (nthK repG i) (nthK repX i) repX inv (nthK tab i)

#kc_each ch7104row 0 29

#kc_forall_tree ch7104_rows (fun i => ch7104row i = true) 29 CFSG.KD.H9Four.ch7104row

theorem ch7104_rank : rankK repG = true := by quickRfl

theorem ch7104_invar : invarK repG repX = true := by quickRfl

theorem ch7104_e16 : e16K (nthK repG 28) (nthK repX 28) (nthK repG 26) (nthK repX 26)
    (nthK repG 27) (nthK repX 27) = true := by quickRfl

end CFSG.KD.H9Four

end
