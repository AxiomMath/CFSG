module

public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.Quasithin.Vol2.KGFactG2RuInputs
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CertificateChecks.KernelSporSch.RuE64D

open CFSG.Sporadic.RuSchreier CFSG.Quasithin.H13.Ch4.G2Ru

meta def ev (c x : Nat) : Nat :=
  ((ruLevS[0]!.tr[c / 8]!)[((ruLevS[1]!.tr[c % 8]!)[x]!)]!)

meta def codes : Array Nat :=
  (List.range 16384).toArray.filter fun c =>
    ev c (ev c 1) == 1 && ev c (ev c 0) == 0 && !(ev c 1 == 1 && ev c 0 == 0)

meta def com (c d : Nat) : Bool :=
  ev c (ev d 1) == ev d (ev c 1) && ev c (ev d 0) == ev d (ev c 0)

meta def rowsM : Array (Array Nat) :=
  codes.map fun c => codes.map fun d => if com c d then 1 else 0

meta def pop (a b : Array Nat) : Nat :=
  (List.range a.size).foldl (fun s k => s + a[k]! * b[k]!) 0

meta def keepM : Array (Array Nat) :=
  let R := rowsM
  (List.range codes.size).toArray.map fun i => (List.range codes.size).toArray.map fun j =>
    if i != j && (R[i]!)[j]! == 1 && 63 ≤ pop R[i]! R[j]! then 1 else 0

meta def degM : Array (Array Nat) := #[keepM.map fun r => r.foldl (· + ·) 0]

meta def ubM : Array (Array Nat) :=
  (List.range 4).toArray.map fun r => (g2WrArr[r]!).foldl (fun a u => (a.push u[1]!).push u[0]!) #[]

meta def wM : Array (Array Nat) :=
  let U := ubM
  (List.range 4).toArray.map fun r => codes.map fun c =>
    if (List.range 64).any (fun e => ev c 1 == (U[r]!)[2 * e]! && ev c 0 == (U[r]!)[2 * e + 1]!) then 1
    else 0

meta def cdM : Array (Array Nat) := #[codes]

end CertificateChecks.KernelSporSch.RuE64D

#kmisc_packarrs CertificateChecks.KernelSporSch.RuE64D.CD CertificateChecks.KernelSporSch.RuE64D.cdM 14
#kmisc_packarrs CertificateChecks.KernelSporSch.RuE64D.R CertificateChecks.KernelSporSch.RuE64D.rowsM 1
#kmisc_packarrs CertificateChecks.KernelSporSch.RuE64D.K CertificateChecks.KernelSporSch.RuE64D.keepM 1
#kmisc_packarrs CertificateChecks.KernelSporSch.RuE64D.D CertificateChecks.KernelSporSch.RuE64D.degM 10
#kmisc_packarrs CertificateChecks.KernelSporSch.RuE64D.W CertificateChecks.KernelSporSch.RuE64D.wM 1
#kmisc_packarrs CertificateChecks.KernelSporSch.RuE64D.UB CertificateChecks.KernelSporSch.RuE64D.ubM 12

end
