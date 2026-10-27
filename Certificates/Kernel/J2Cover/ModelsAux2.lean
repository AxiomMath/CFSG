module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsNative

public section

namespace CertificateChecks.KernelJ2Cover

open CFSG.ComponentClassification.J2Cover.Models

@[expose] def decompP : Array (Array Nat) := decompCols.1

@[expose] def decompI : Array (Array Nat) := decompCols.2

@[expose] def ydP : Array (Array Nat) :=
  Array.ofFn (n := 3) fun k => Array.ofFn (n := 4725) fun i => (yDecomp k.val i.val).1

@[expose] def ydI : Array (Array Nat) :=
  Array.ofFn (n := 3) fun k => Array.ofFn (n := 4725) fun i => (yDecomp k.val i.val).2

end CertificateChecks.KernelJ2Cover

end
