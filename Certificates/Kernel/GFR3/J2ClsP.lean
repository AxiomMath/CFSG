module

public import Certificates.Kernel.GFR3.J2
public import CFSG.Certificates.Kernel.GFR3KSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGFR3.J2

open CFSG.KC.Enum CFSG.KC.GFR3K

@[expose] noncomputable def clsBlockP (b : Nat) : Bool :=
  allN 60 fun i => gfr3AtPK 315 9 1080 E.T 1080 3 1 (Nat.add (Nat.mul 60 b) i)

theorem clsBlock_eqP (b : Nat) : clsBlock b = clsBlockP b := by
  unfold clsBlock clsBlockP
  simp only [gfr3AtPK_eq (n := 315) (w := 9) (by decide) (by decide)]

end CertificateChecks.KernelGFR3.J2

end
