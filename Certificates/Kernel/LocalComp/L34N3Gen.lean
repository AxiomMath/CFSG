module

public import Certificates.Kernel.LocalComp.L34NGen
public import Certificates.Kernel.LocalComp.L34Gen2
public meta import Certificates.Kernel.LocalComp.L34NGen
public meta import Certificates.Kernel.LocalComp.L34Gen2

public section

namespace CertificateChecks.KernelLC.L34N3Gen

open CFSG.PSL3Four.Native
open CertificateChecks.KernelLC.L34Gen CertificateChecks.KernelLC.L34NGen
open CFSG.KS.RawGen (pack)

meta def rep (c : Nat) : Nat := (codes.findIdx? fun v => v / 8 == c + 1).getD 0

meta def lR : Array (Array Nat) := #[#[rep 0], #[rep 1], #[rep 2]]

meta def lay (c : Nat) := let o := oRun rRun.1[rep c]!; layout o.1 o.2 12 o.1.size

meta def o0T : Array (Array Nat) := (lay 0).1
meta def o0E : Array (Array Nat) := (lay 0).2.1
meta def o0S : Array (Array Nat) := (lay 0).2.2.1
meta def o0SI : Array (Array Nat) := (lay 0).2.2.2.1
meta def o1T : Array (Array Nat) := (lay 1).1
meta def o1E : Array (Array Nat) := (lay 1).2.1
meta def o1S : Array (Array Nat) := (lay 1).2.2.1
meta def o1SI : Array (Array Nat) := (lay 1).2.2.2.1
meta def o2T : Array (Array Nat) := (lay 2).1
meta def o2E : Array (Array Nat) := (lay 2).2.1
meta def o2S : Array (Array Nat) := (lay 2).2.2.1
meta def o2SI : Array (Array Nat) := (lay 2).2.2.2.1

meta def cI (c : Nat) : Array Nat :=
  let r := rRun.1[rep c]!
  (Array.range sPts.size).filter fun j => comp 42 sPts[j]! r == comp 42 r sPts[j]!

meta def c0X : Array (Array Nat) := (cI 0).map fun j => #[j]
meta def c0P : Array (Array Nat) := (cI 0).map fun j => #[pack 6 sPts[j]!]
meta def c1X : Array (Array Nat) := (cI 1).map fun j => #[j]
meta def c1P : Array (Array Nat) := (cI 1).map fun j => #[pack 6 sPts[j]!]
meta def c2X : Array (Array Nat) := (cI 2).map fun j => #[j]
meta def c2P : Array (Array Nat) := (cI 2).map fun j => #[pack 6 sPts[j]!]

end CertificateChecks.KernelLC.L34N3Gen

end
