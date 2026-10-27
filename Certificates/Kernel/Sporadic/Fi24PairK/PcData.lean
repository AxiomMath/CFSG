module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.Sporadic.Fi24PairK.Data
public import Certificates.Data.Kernel.Spor.Fi24PairPc

#kc_repo #kc_json_gz CFSG.KD.Fi24PairPc.J "Certificates/Kernel/Sporadic/Fi24PairK/data/pc.json.gz"
  15914 11897457272046361289
  (xsT : List (List Nat)) (psT : List Nat) (pwT : List (List Nat)) (cjT : List (List (List Nat)))
  (gwT : List (List Nat))
  (xsA : List (List Nat)) (psA : List Nat) (pwA : List (List Nat)) (cjA : List (List (List Nat)))
  (gwA : List (List Nat))
  (xsB : List (List Nat)) (psB : List Nat) (pwB : List (List Nat)) (cjB : List (List (List Nat)))
  (gwB : List (List Nat))

public section

namespace CFSG.KD.Fi24PairPc

open CFSG.KC CFSG.KC.Loop CFSG.KC.Fi24PairK CFSG.KC.Fi24PairPc
open CFSG.KD.Fi24PairK (NV net)

@[expose] def lvT : List Nat := [15, 16, 17, 18, 19, 22, 23, 24, 25, 26]

@[expose] def lvA : List Nat := [15, 16, 17, 18, 19, 20, 22, 23, 24, 25, 26, 27]

@[expose] def lvB : List Nat := [15, 16, 17, 18, 19, 21, 22, 23, 24, 25, 26, 28]

@[expose] noncomputable def cT (g : Nat) : Bool := pcCk NV net J.xsT J.psT J.pwT J.cjT 21 g

@[expose] noncomputable def cA (g : Nat) : Bool := pcCk NV net J.xsA J.psA J.pwA J.cjA 24 g

@[expose] noncomputable def cB (g : Nat) : Bool := pcCk NV net J.xsB J.psB J.pwB J.cjB 23 g

@[expose] noncomputable def gT (g : Nat) : Bool := genOK NV net J.xsT 21 (nthN lvT g) (nthLL J.gwT g)

@[expose] noncomputable def gA (g : Nat) : Bool := genOK NV net J.xsA 24 (nthN lvA g) (nthLL J.gwA g)

@[expose] noncomputable def gB (g : Nat) : Bool := genOK NV net J.xsB 23 (nthN lvB g) (nthLL J.gwB g)

@[expose] noncomputable def gck (g : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) (gB (Nat.sub g 22)) (gA (Nat.sub g 10)) (Nat.blt g 22))
    (gT g) (Nat.blt g 10)

end CFSG.KD.Fi24PairPc

end
