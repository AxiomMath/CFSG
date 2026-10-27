module

public import Certificates.Kernel.SL4ModClass.Data
public import Certificates.Kernel.SL4Mod.Defs
public import Certificates.Data.Kernel.SL4ModClassCerts
public import Certificates.Data.SL4ModClassData

public section

namespace CertificateChecks.KernelSL4ModClass

open CFSG.LargeExtraspecial.SL4Mod.Native CertificateChecks.KernelSL4Mod

@[expose] noncomputable def recs : Nat → Nat → List ClassRec
  | 0, 0 => C00.map mkRec
  | 0, 1 => C01.map mkRec
  | 0, _ => C02.map mkRec
  | 1, 0 => C10.map mkRec
  | 1, 1 => C11.map mkRec
  | 1, _ => C12.map mkRec
  | _, 0 => C20.map mkRec
  | _, 1 => C21.map mkRec
  | _, _ => C22.map mkRec

@[expose] def r14 : List (List (List Nat)) := refsL classRefRows14

@[expose] def r20 : List (List (List Nat)) := refsL classRefRows20

@[expose] noncomputable def lenK (n : Nat) : Bool := (recs (n / 3) (n % 3)).length == 127

@[expose] noncomputable def classK (n : Nat) : Bool :=
  checkClassFrom (tabL (cd (n / 12)).tau) r14 r20 (od (n / 12) (n / 4 % 3)) (32 * (n % 4) + 1)
    (((recs (n / 12) (n / 4 % 3)).drop (32 * (n % 4))).take 32)

end CertificateChecks.KernelSL4ModClass
