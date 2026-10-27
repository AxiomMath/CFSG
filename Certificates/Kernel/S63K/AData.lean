module

public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.F2Word
public import CFSG.LargeExtraspecial.S63CD4InputsA
meta import CFSG.LargeExtraspecial.S63CD4InputsA

public section

namespace CertificateChecks.KernelS63.AD

open CFSG.LargeExtraspecial.S63

meta def sing (a : Array Nat) : Array (Array Nat) := a.map fun x => #[x]

meta def key (r : Array Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [0:r.size] do
    acc := acc ||| (r[i]! <<< (24 * i))
  return acc

meta def enumM (gs : Array (Array Nat)) : Array (Array Nat) := Id.run do
  let e := mkEnum gs
  let mut ws : Array Nat := #[]
  for h in [0:e.El.size] do
    for l in [0:gs.size] do
      ws := ws.push (e.idx (mulR gs[l]! e.El[h]!))
  let keys := e.El.map key
  let srt := (List.range keys.size).toArray.qsort fun a b => keys[a]! < keys[b]!
  return e.El ++ sing e.P ++ sing e.K ++ sing ws ++ sing srt ++ sing e.inv

meta def rpM (q l : EnumData) (j : Nat) : Array Nat :=
  if q.El[j]! == oneR || q.El[j]! == z0R then #[] else
    ((subProds (irrList l (irrChoice q l j) q.El[j]!)).map q.idx).toArray

meta def allM : Array (Array Nat) :=
  let q := mkEnum qGens
  let l := mkEnum lGens
  qGens ++ lGens ++ #[z0R] ++ enumM qGens ++ enumM lGens ++
    (Array.ofFn (n := 512) fun j => rpM q l j.val) ++
    #[((subProds (commList q l (commChoice q l))).map q.idx).toArray]

end CertificateChecks.KernelS63.AD

#kmisc_packarrs CertificateChecks.KernelS63.AD.T CertificateChecks.KernelS63.AD.allM 24

namespace CertificateChecks.KernelS63.AD

@[expose] noncomputable def QG (l : Nat) : Nat := T l
@[expose] noncomputable def LG (l : Nat) : Nat := T (8 + l)
@[expose] noncomputable def Zp : Nat := T 14
@[expose] noncomputable def QP (i : Nat) : Nat := T (15 + i)
@[expose] noncomputable def QPar (i : Nat) : Nat := T (527 + i)
@[expose] noncomputable def QLab (i : Nat) : Nat := T (1039 + i)
@[expose] noncomputable def QW (i : Nat) : Nat := T (1551 + i)
@[expose] noncomputable def QS (i : Nat) : Nat := T (5647 + i)
@[expose] noncomputable def QInv (i : Nat) : Nat := T (6159 + i)
@[expose] noncomputable def LP (i : Nat) : Nat := T (6671 + i)
@[expose] noncomputable def LPar (i : Nat) : Nat := T (7175 + i)
@[expose] noncomputable def LLab (i : Nat) : Nat := T (7679 + i)
@[expose] noncomputable def LW (i : Nat) : Nat := T (8183 + i)
@[expose] noncomputable def LS (i : Nat) : Nat := T (11207 + i)
@[expose] noncomputable def LInv (i : Nat) : Nat := T (11711 + i)
@[expose] noncomputable def RP (j : Nat) : Nat := T (12215 + j)
@[expose] noncomputable def RC : Nat := T 12727

end CertificateChecks.KernelS63.AD

end
