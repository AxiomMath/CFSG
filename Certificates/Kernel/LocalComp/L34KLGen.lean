module

public import Certificates.Kernel.LocalComp.L34NGen
public import Certificates.Kernel.LocalComp.L34Gen2
public meta import Certificates.Kernel.LocalComp.L34NGen
public meta import Certificates.Kernel.LocalComp.L34Gen2

public section

namespace CertificateChecks.KernelLC.L34KLGen

open CFSG.PSL3Four.Native
open CertificateChecks.KernelLC.L34Gen CertificateChecks.KernelLC.L34NGen

meta def hits : Array Nat :=
  (Array.range listing.size).filter fun q => listing[q]! % 2 == 1 && listing[q]! % 32 / 8 == 3

meta def nS : Array Nat :=
  let e9 := e9T ()
  let inA := fun (y g : Array Nat) => e9.any fun e => comp 42 y g == comp 42 e y
  (Array.range sPts.size).filter fun j => inA sPts[j]! a₀T && inA sPts[j]! b₀T

meta def qW (x : Array Nat) : Nat :=
  (nS.find? fun j => let y := sPts[j]!; let y2 := comp 42 y y
    comp 42 y2 y2 == idTab 42 && y2 != idTab 42 && comp 42 x y2 == comp 42 y2 x).getD 0

meta def tW (x : Array Nat) : Nat :=
  (nS.find? fun j => let t := sPts[j]!
    comp 42 t t == idTab 42 && t != idTab 42 &&
      comp 42 t a₀T == comp 42 (comp 42 a₀T a₀T) t &&
      comp 42 t b₀T == comp 42 (comp 42 b₀T b₀T) t && comp 42 x t == comp 42 t x).getD 0

meta def lW : Array (Array Nat) :=
  hits.map fun q => let x := rRun.1[listing[q]! / 32]!; #[q, qW x, tW x]

meta def lA : Array (Array Nat) :=
  #[#[(sPts.findIdx? (· == a₀T)).getD 0], #[(sPts.findIdx? (· == b₀T)).getD 0]]

end CertificateChecks.KernelLC.L34KLGen

end
