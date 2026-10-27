module

public import Certificates.Kernel.CU43Aut.Syl
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU43Rho

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CertificateChecks.KernelU43B CertificateChecks.KernelCU43Aut

@[expose] noncomputable def sqK (p : Nat) : Nat := pc p p

@[expose] noncomputable def e8K (p : Nat) : Nat := sqK (sqK (sqK p))

@[expose] noncomputable def slX (s : Nat) : Bool :=
  allN 128 (fun i => Nat.beq (e8K (TS.T (Nat.add (Nat.mul 128 s) i))) (pidn 820 10))

theorem tX0 : slX 0 = true := by quickRfl
theorem tX1 : slX 1 = true := by quickRfl
theorem tX2 : slX 2 = true := by quickRfl
theorem tX3 : slX 3 = true := by quickRfl
theorem tX4 : slX 4 = true := by quickRfl
theorem tX5 : slX 5 = true := by quickRfl
theorem tX6 : slX 6 = true := by quickRfl
theorem tX7 : slX 7 = true := by quickRfl

end CertificateChecks.KernelU43Rho

end
