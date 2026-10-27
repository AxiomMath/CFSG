module

public import Certificates.Kernel.LocalComp.L34Gen
public meta import Certificates.Kernel.LocalComp.L34Gen
public meta import Certificates.Data.CFSGNative.PSL3Four.L34Cent
public meta import Certificates.Data.L34OuterGen

public section

namespace CertificateChecks.KernelLC.L34NGen

open CFSG.PSL3Four.Native
open CertificateChecks.KernelLC.L34Gen Certificates.L34OuterGen
open CFSG.KS.RawGen (pack)

meta def nfix (x : Array Nat) : Nat := ((List.range 42).filter fun p => x[p]! == p).length

meta def code (e9 : Array (Array Nat)) (x : Array Nat) : Nat :=
  let inA := fun (g : Array Nat) => e9.any fun e => comp 42 x g == comp 42 e x
  let nA := if inA a₀T && inA b₀T then 1 else 0
  let cZ := if comp 42 x t3aT == comp 42 t3aT x then 2 else 0
  let pr := fun (p : Nat) => p == 1 || p == 27
  let sT := if pr x[1]! && pr x[27]! then 4 else 0
  let o3 := x != idTab 42 && comp 42 x (comp 42 x x) == idTab 42
  let c := if !o3 then 0 else
    let f := nfix x
    if f == 0 then 1 else if f == 6 then 2 else if f == 12 then 3 else 4
  nA + cZ + sT + 8 * c

meta def codes : Array Nat := let e9 := e9T (); rRun.1.map (code e9)

meta def listing : Array Nat :=
  (Array.range codes.size).filterMap fun k =>
    if codes[k]! == 0 then none else some (32 * k + codes[k]!)

meta def lJ : Array (Array Nat) := chunks 16 listing

meta def lC : Array (Array Nat) :=
  (Array.range 181).map fun s => #[(listing.filter fun v => v / 32 < 1344 * s).size]

meta def lK : Array (Array Nat) :=
  (#[a₀T, b₀T, t3aT] ++ (e9T ())).map fun x => #[pack 6 x]

end CertificateChecks.KernelLC.L34NGen

end
