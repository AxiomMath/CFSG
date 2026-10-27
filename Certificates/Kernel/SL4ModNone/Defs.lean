module

public import Certificates.Kernel.SL4ModNone.Data
public import Certificates.Kernel.SL4Mod.Defs

public section

namespace CertificateChecks.KernelSL4ModNone

open CFSG.LargeExtraspecial.SL4Mod.Native CertificateChecks.KernelSL4Mod

@[expose] noncomputable def ents : Nat → Nat → List (Nat × NoneRec × NoneRec)
  | 0, 0 => C00.map mkNoneEntry
  | 0, 1 => C01.map mkNoneEntry
  | 0, _ => C02.map mkNoneEntry
  | 1, 0 => C10.map mkNoneEntry
  | 1, 1 => C11.map mkNoneEntry
  | 1, _ => C12.map mkNoneEntry
  | _, 0 => C20.map mkNoneEntry
  | _, 1 => C21.map mkNoneEntry
  | _, _ => C22.map mkNoneEntry

@[expose] noncomputable def ch705102len (n : Nat) : Bool := (ents (n / 3) (n % 3)).length == 64

@[expose] noncomputable def ch705102ones (j : Nat) : Bool := onesFixedL (tabL (cd j).tau)

@[expose] noncomputable def ch705102blk (n : Nat) : Bool :=
  checkNoneFrom (tabL (cd (n / 12)).tau) (od (n / 12) (n / 4 % 3)) (16 * (n % 4))
    (((ents (n / 12) (n / 4 % 3)).drop (16 * (n % 4))).take 16)

end CertificateChecks.KernelSL4ModNone
