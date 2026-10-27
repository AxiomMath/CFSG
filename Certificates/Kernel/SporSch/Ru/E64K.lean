module

public import Certificates.Kernel.SporSch.Ru.E64Data
public import Certificates.Kernel.Misc.RuSq.Chain
public import Certificates.Kernel.SporSch.Ru.G2Ru7164K
public import Certificates.Data.Kernel.Misc.RuE64
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuE64

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.RuE64 CertificateChecks.KernelSporSch.RuE64D
open CertificateChecks.KernelSporSch.G2Ru7164 CFSG.Quasithin.H13.Ch4.G2Ru
open CFSG.KLie.CT (bit)

@[expose] noncomputable def eqB (a b : Bool) : Bool := bIf(a, b, bIf(b, false, true))

@[expose, reducible] noncomputable def LR : Nat → Nat := CertificateChecks.KernelMisc.RuSqS.LR
@[expose, reducible] noncomputable def TR : Nat → Nat := CertificateChecks.KernelMisc.RuSqS.TR

@[expose] noncomputable def cd (i : Nat) : Nat := pg 14 (mask 14) (CD 0) i

@[expose] noncomputable def deg (i : Nat) : Nat := pg 10 (mask 10) (D 0) i

@[expose] noncomputable def ub (r q : Nat) : Nat := pg 12 (mask 12) (UB r) q

@[expose] noncomputable def U (r e : Nat) : Nat :=
  conjK (wK CertificateChecks.KernelSporSch.RuG.SG (g2ConjWords.getD r [])) (WPk e)

@[expose] noncomputable def rowC (i : Nat) : Bool :=
  allN 687 fun j => eqB (bit (R i) j) (comK LR TR (cd i) (cd j))

@[expose] noncomputable def keepC (i : Nat) : Bool :=
  allN 687 fun j => eqB (bit (K i) j) (keepK 687 R i j)

@[expose] noncomputable def wC (r : Nat) : Bool :=
  allN 687 fun i => eqB (bit (W r) i) (inWK LR TR (ub r) (cd i))

@[expose] noncomputable def ubC (r : Nat) : Bool :=
  allN 64 fun e => bAnd(Nat.beq (ub r (2 * e)) (ap (U r e) 1), Nat.beq (ub r (2 * e + 1)) (ap (U r e) 0))

end CertificateChecks.KernelSporSch.RuE64

end
