module

public import CFSG.GH74.GLS.C3.Layer2.L5C9Inputs

public section

namespace CertificateChecks.KernelL5

open Equiv CFSG.GH74.GLS.C3.Layer2.L5.HF

@[expose] def g72Src : Array (Array Nat) :=
  #[(G72L.map fun σ =>
    (List.finRange 16).foldl (fun acc i => acc ||| (σ i).val <<< (5 * i.val)) 0).toArray]

@[expose] def g72MulSrc : Array (Array Nat) :=
  #[((List.range 72).flatMap fun a => (List.range 72).map fun b =>
    G72L.idxOf (G72L.getD a 1 * G72L.getD b 1)).toArray]

end CertificateChecks.KernelL5

end
