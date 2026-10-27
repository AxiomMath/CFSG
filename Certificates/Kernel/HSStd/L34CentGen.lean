module

public import Certificates.Kernel.LocalComp.L34Gen
public meta import Certificates.Kernel.LocalComp.L34Gen

public section

namespace CertificateChecks.KernelHSStd.L34CentGen

open CFSG.PSL3Four.Native CertificateChecks.KernelLC.L34Gen
open CFSG.KS.RawGen (pack)

meta def c3Idx : Array Nat :=
  let pts := rRun.1
  (Array.range pts.size).filter fun j => comp 42 pts[j]! r₃T == comp 42 r₃T pts[j]!

meta def c3X : Array (Array Nat) := c3Idx.map fun j => #[j]

meta def c3P : Array (Array Nat) := c3Idx.map fun j => #[pack 6 rRun.1[j]!]

meta def c3Cnt : Array (Array Nat) :=
  (Array.range 181).map fun s => #[(c3Idx.filter (· < 1344 * s)).size]

end CertificateChecks.KernelHSStd.L34CentGen

end
