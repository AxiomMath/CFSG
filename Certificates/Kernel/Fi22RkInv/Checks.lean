module

public import Certificates.Data.Kernel.Fi22RkInv.Defs
public import Certificates.Kernel.Fi22RkInv.Data
public import Certificates.Kernel.Fi22Reps.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22RkInv

open CFSG.KS.Fi22RkInv CFSG.KD.Fi22RkInv

@[expose] noncomputable def xP (k y : Nat) : Nat :=
  CFSG.KC.Fi22S0.ent (CertificateChecks.KernelFi22Reps.xT k) y

@[expose] noncomputable def invRep (k : Nat) : Bool :=
  invK CFSG.KS.Fi22Gen.LT (xP k) (invAtW k).1 (invAtW k).2.1 (invAtW k).2.2.1 (invAtW k).2.2.2

set_option Elab.async false

theorem ch17373inv0 : invRep 0 = true := by quickRfl
theorem ch17373inv1 : invRep 1 = true := by quickRfl
theorem ch17373inv2 : invRep 2 = true := by quickRfl
theorem ch17373inv3 : invRep 3 = true := by quickRfl

end CertificateChecks.KernelFi22RkInv

end
