module

public import Certificates.Kernel.FiveStd.S0
public import Certificates.Kernel.FiveStd.ClsData
public import Certificates.Data.Kernel.FiveStdKDiag

public section

namespace CertificateChecks.FiveStd

open CFSG.KC.FiveStdK

set_option Elab.async false

@[expose] noncomputable def pwF (B M p : Nat) : Bool :=
  allN M fun j => letB (powK (f20 B j) p) fun y => orB (!Nat.beq (powK y p) oneK) (Nat.beq y oneK)

theorem ex_s0 : S0c.all (fun s => Nat.beq (powK s 8) oneK) = true := by decide +kernel

theorem ex_cb0 : pwF (CB.getD 0 0) (CM.getD 0 0) 5 = true := by decide +kernel

theorem ex_cb1 : pwF (CB.getD 1 0) (CM.getD 1 0) 5 = true := by decide +kernel

theorem ex_cb2 : pwF (CB.getD 2 0) (CM.getD 2 0) 5 = true := by decide +kernel

theorem ex_cb3 : pwF (CB.getD 3 0) (CM.getD 3 0) 3 = true := by decide +kernel

theorem ex_cb4 : pwF (CB.getD 4 0) (CM.getD 4 0) 3 = true := by decide +kernel

end CertificateChecks.FiveStd

end
