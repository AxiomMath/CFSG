module

public import Certificates.Kernel.Sporadic.Fi22.E2065T0
public import Certificates.Kernel.Sporadic.Fi22.E2065T1
public import Certificates.Kernel.Sporadic.Fi22.E2065T2
public import Certificates.Kernel.Sporadic.Fi22.E2065T3
public import CFSG.Certificates.Kernel.Spor.TextJoin

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22CentT

open CFSG.Sporadic.FischerOddCore CFSG.KS.Text

@[expose] noncomputable def chars : List Char :=
  Fi22CP0.chars ++ (Fi22CP1.chars ++ (Fi22CP2.chars ++ Fi22CP3.chars))

theorem chars_eq :
    fi22CentP0 ++ fi22CentP1 ++ fi22CentP2 ++ fi22CentP3 = String.ofList chars := by
  rw [chars, String.ofList_append, String.ofList_append, String.ofList_append, ← Fi22CP0.eq,
    ← Fi22CP1.eq, ← Fi22CP2.eq, ← Fi22CP3.eq, String.append_assoc, String.append_assoc]

@[expose] noncomputable def L (j : Nat) : Nat :=
  nIf(Nat.blt j 77, Fi22CP0.L j, nIf(Nat.blt (Nat.sub j 77) 77, Fi22CP1.L (Nat.sub j 77),
    nIf(Nat.blt (Nat.sub (Nat.sub j 77) 77) 76, Fi22CP2.L (Nat.sub (Nat.sub j 77) 77),
      Fi22CP3.L (Nat.sub (Nat.sub (Nat.sub j 77) 77) 76))))

theorem all : hexBind chars 3 3510 12 306 0 306 L = true := by
  have h := hexBind_append Fi22CP0.all
    (hexBind_append Fi22CP1.all (hexBind_append Fi22CP2.all Fi22CP3.all))
  exact h

end CertificateChecks.KernelSpor.Fi22CentT

end
