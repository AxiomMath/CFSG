module

public import Certificates.Data.GrSLitL34Sec4FWCommCheck

public section

namespace CertificateChecks.KernelLC.L34FW

open CFSG.PSL3Four.Native CFSG.PSL3Four.Native.FWComm

@[expose] def parArr : Array (Array Nat) := (commTree invTabs).1.map fun p => #[p]

@[expose] def depArr : Array (Array Nat) := (commTree invTabs).2.map fun d => #[d]

@[expose] def idxOf (t : Tab) : Nat := ((List.range 315).find? fun j => (invTabs)[j]! == t).getD 315

@[expose] def g₁Pair : Nat × Nat :=
  ((List.range 315).findSome? fun a =>
    ((List.range 315).find? fun b => comp 42 (invTabs)[a]! (invTabs)[b]! == g₁T).map
      fun b => (a, b)).getD (315, 315)

@[expose] def genArr : Array (Array Nat) :=
  #[#[g₁Pair.1], #[g₁Pair.2], #[idxOf g₂T], #[idxOf g₃T]]

end CertificateChecks.KernelLC.L34FW

end
