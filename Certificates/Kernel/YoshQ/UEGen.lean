module

public meta import Certificates.Kernel.YoshQ.Gen
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Lean
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.YoshQ.Gen

open Lean CFSG.KC.Tab CFSG.KS.RawGen

namespace CertificateChecks.KernelYoshQ

open CFSG.Sporadic.Th.Native CFSG.EvenSporadicStandard.M12Std.Yosh CFSG.EvenSporadicStandard.Fin76b

public meta def ueData (α k : Nat) :
    Nat × Nat × Array Nat × List Nat × List Nat × List Nat × List Nat := Id.run do
  let LE := (mulClosureS 16 16 (wgens α k eWords) 4000).1.toList
  let LS := (mulClosureS 16 16 (wgens α k sWords) 4000).1.toList
  let cT := nwT α k cWord
  let pk := packT 16 5
  let RE := LE.map pk
  let mut P := 128
  while (RE.map (· % P)).eraseDups.length < RE.length do
    P := P + 1
  let tbl := (List.range P).map fun h => (RE.find? (fun e => e % P == h)).getD 0
  let M := RE.foldl (fun m e => m ||| (1 <<< (e % P))) 0
  let Y := LS.filter fun y => !memTab 16 LE y && sqIn 16 cT y
  let bits := fun (l : List Bool) => l.foldr (fun b acc => 2 * acc + (if b then 1 else 0)) 0
  let MK := Y.map fun y => bits (LE.map fun x => commIn 16 cT x y)
  return (P, M, tbl.toArray, LE.map fun x => pk (invT 16 x), Y.map pk,
    Y.map fun y => pk (invT 16 y), MK)

open CFSG.KC.Eval in
public meta def ueStep : Step := fun args => do
  let (α, k) ← match args with
    | #[.nat a, .nat b] => pure (a, b)
    | _ => throw "ueStep: expected α k"
  let (P, M, _, LI, YL, YI, MK) := ueData α k
  let natsV := fun (l : List Nat) => Val.list (l.toArray.map .nat)
  return #[(`P, .nat P), (`M, .nat M), (`LI, natsV LI), (`YL, natsV YL), (`YI, natsV YI),
    (`MK, natsV MK)]

public meta def ueTab (α k : Nat) : Array Nat := (ueData α k).2.2.1

public meta def ueTab00 : Array Nat := ueTab 0 0
public meta def ueTab01 : Array Nat := ueTab 0 1
public meta def ueTab10 : Array Nat := ueTab 1 0
public meta def ueTab11 : Array Nat := ueTab 1 1

end CertificateChecks.KernelYoshQ
