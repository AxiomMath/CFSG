module

public import Certificates.Kernel.LocalComp.L34NDefs
public import Certificates.Kernel.LocalComp.L34Bo.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34Ce

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K
open CertificateChecks.KernelLC.L34X
open CFSG.KLie.CT (andB orB notB anyN)

@[expose] noncomputable def cePt (β x : Nat) : Bool :=
  andB (commPt 42 6 x β)
    (orB (notB (andB (commPt 42 6 x (L34N.K 0)) (commPt 42 6 x (L34N.K 1))))
      (anyN 9 fun j => orB (Nat.beq x (L34N.AP j)) (Nat.beq x (pcomp 42 6 (mask 6) β (L34N.AP j)))))

@[expose] noncomputable def ceChk (β : Nat) : Bool :=
  allN 7755 fun q => strictB (L34N.J q) fun v =>
    bIf(Nat.beq (Nat.mod v 2) 1, cePt β (L34R.T (Nat.div v 32)), true)

theorem kCe : ceChk (RP 3) = true := by quickRfl

theorem kInS : andB (L34Bo.inS (L34N.K 0)) (L34Bo.inS (L34N.K 1)) = true := by quickRfl

end CertificateChecks.KernelLC.L34Ce

end
