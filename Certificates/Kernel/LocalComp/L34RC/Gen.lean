module

public import Certificates.Kernel.LocalComp.L34Gen2
public meta import Certificates.Kernel.LocalComp.L34Gen2
public import Certificates.Data.CFSGNative.PSL3Four.Basic

public section

namespace CertificateChecks.KernelLC.L34RCGen

open CFSG.PSL3Four.Native CertificateChecks.KernelLC.L34Gen

meta def uM : Array (Array Nat) :=
  let r := (rTabs ())[3]!
  rRun.1.filter fun t => comp 42 t r == comp 42 r t && comp 42 t t == idTab 42 && !(t == idTab 42)

meta def pow2 (x : Array Nat) : Nat → Array Nat
  | 0 => x
  | k + 1 => let y := pow2 x k; comp 42 y y

meta def qM : Array (Array Nat) :=
  let iS := posIn sPts
  chunks 16 (rRun.1.map fun x =>
    if pow2 x 5 == idTab 42 then iS.getD (comp 42 x x) 0 + 1 else 0)

end CertificateChecks.KernelLC.L34RCGen

end
