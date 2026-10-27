module

public import Certificates.Kernel.ONKLat.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.ON5.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONKL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.ONSchreier
open CertificateChecks.KernelSpor

@[expose] noncomputable def gI (j : Nat) : Nat := CFSG.KS.pinvS 32 6 (mask 6) (T32E.G j)

@[expose] noncomputable def conjI (j t : Nat) : Nat := m6 (m6 (T32E.G j) t) (gI j)

@[expose] noncomputable def invI (D : List Nat) (i : Nat) : Bool :=
  strictB (T32E.T i) fun t => bIf(Nat.beq (m6 t t) i32, bIf(Nat.beq t i32, true,
    bIf(allN 6 (fun j => cm6 t (conjI j t)), inD D t, true)), true)

@[expose] noncomputable def wI (t : Nat) : Nat :=
  nIf(Nat.blt t 36, m6 (m6 (m6 (T32E.G (t / 6)) (T32E.G (t % 6))) (gI (t / 6))) (gI (t % 6)),
    m6 (T32E.G (t - 36)) (m6 (T32E.G (t - 36)) (m6 (T32E.G (t - 36)) (m6 (T32E.G (t - 36)) i32))))

@[expose] noncomputable def witI (z a b : Nat) : Bool :=
  bIf(cm6 a b, bIf(Nat.beq a z, true, bIf(Nat.beq b z, true, bIf(Nat.beq b a, true,
    bIf(Nat.beq b (m6 a z), true,
      bIf(allN 42 (fun t => bAnd(cm6 (wI t) a, cm6 (wI t) b)), false, true))))), true)

@[expose] noncomputable def tIOK : Bool :=
  bAnd(allN 512 (invI dP), allN 7 (fun a => allN 7 fun b =>
    witI zP (List.getD dP a 0) (List.getD dP b 0)))

theorem ch812105_tI : tIOK = true := by quickRfl

end CertificateChecks.KernelSpor.ONKL

end
