module

public import Certificates.Kernel.HN1408.Words

public section

namespace CFSG.KD.HN1408

@[expose] noncomputable def powK (X e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) idK (fun _ acc => pc X acc) e

@[expose] noncomputable def specK (G : List Nat) (spec : List (Nat × Nat)) : Nat :=
  spec.foldl (fun acc p => pc acc (powK (G.getD (p.1 - 1) idK) p.2)) idK

end CFSG.KD.HN1408

end
