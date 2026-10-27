module

public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.F2Word
public import CFSG.LargeExtraspecial.S63CD4Inputs
meta import CFSG.LargeExtraspecial.S63CD4Inputs

public section

namespace CertificateChecks.KernelS63.CD

open CFSG.LargeExtraspecial.S63

meta def sing (a : Array Nat) : Array (Array Nat) := a.map fun x => #[x]

meta def key (r : Array Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [0:r.size] do
    acc := acc ||| (r[i]! <<< (24 * i))
  return acc

meta def allM : Array (Array Nat) := Id.run do
  let e := mkEnum cGens
  let mut ws : Array Nat := #[]
  for h in [0:e.El.size] do
    for l in [0:cGens.size] do
      ws := ws.push (e.idx (mulR cGens[l]! e.El[h]!))
  let srt := (((Array.range e.El.size).map fun i => (key e.El[i]!, i)).qsort
    fun a b => a.1 < b.1).map Prod.snd
  return cGens ++ #[t0R] ++ e.El ++ sing e.P ++ sing e.K ++ sing ws ++ sing srt ++ sing e.inv ++
    #[#[findOrder3 e]]

end CertificateChecks.KernelS63.CD

#kmisc_packarrs CertificateChecks.KernelS63.CD.T CertificateChecks.KernelS63.CD.allM 24

namespace CertificateChecks.KernelS63.CD

@[expose] noncomputable def CG (l : Nat) : Nat := T l
@[expose] noncomputable def T0 (_ : Nat) : Nat := T 4
@[expose] noncomputable def EP (i : Nat) : Nat := T (5 + i)
@[expose] noncomputable def EPar (i : Nat) : Nat := T (3077 + i)
@[expose] noncomputable def ELab (i : Nat) : Nat := T (6149 + i)
@[expose] noncomputable def EW (i : Nat) : Nat := T (9221 + i)
@[expose] noncomputable def ES (i : Nat) : Nat := T (21509 + i)
@[expose] noncomputable def EInv (i : Nat) : Nat := T (24581 + i)
@[expose] noncomputable def C3 (_ : Nat) : Nat := T 27653

end CertificateChecks.KernelS63.CD

end
