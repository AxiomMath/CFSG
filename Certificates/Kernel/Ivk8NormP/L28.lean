module

public import Certificates.Data.Kernel.Ivk8NormPC
public import CFSG.GH74.KGroups.L28Inputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KS.Ivk8NormP.L28

open CFSG.Certificates.Kernel.PkEnum CFSG.KS.Ivk8Norm CFSG.KS.Ivk8NormP CFSG.GH74.KGroups.L28

@[expose] noncomputable def gens : List (VP 9) :=
  [mkV 9 (1126655256, 1126655256) (by decide +kernel),
  mkV 9 (22666416936, 1686577461) (by decide +kernel),
  mkV 9 (321222276, 5138048376) (by decide +kernel)]

@[expose] def wX : List (List ℤ) :=
  [[2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2], [-2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2]]

@[expose] def wCB : List ℤ := [2, -3, -3]

@[expose] def wCAB : List ℤ := [3, 2, 1, -2]

@[expose] def qaWords : List (List ℤ) := [[-1, 2], [4, 4, -1, -3], [4, -5, 4], [6, 5, 6]]

@[expose] noncomputable def a : VP 9 := gens.getD 0 (oneV 9)

@[expose] noncomputable def xs : List (VP 9) := a :: wX.map (evV gens)

@[expose] noncomputable def b' : VP 9 := evV gens (wX.getD 0 [])

@[expose] noncomputable def c1 : VP 9 := evV gens wCB

@[expose] noncomputable def c2 : VP 9 := evV gens wCAB

@[expose] noncomputable def strong : List (VP 9) := buildV gens qaWords

@[expose] noncomputable def enum : List Nat := (enumV strong #v[0, 1, 2, 3]).map fun y => y.1.1

@[expose] noncomputable def wits (c : VP 9) (S : List (VP 9)) : List (Nat × Nat) :=
  (subprodsV (S.map (conjV (invV c)))).tail.map Subtype.val

@[expose] noncomputable def wAll (r : VP 9) (S : List (VP 9)) (L : List Nat) : Bool :=
  chkPC 9 4 r.1.1 [3, 7] [wits (oneV 9) S, wits c1 S, wits c2 S] L

theorem ch5253_l28_gens :
    (gens.map Subtype.val == [(codeV pa).1, (codeV pb).1, (codeV sg).1]) = true := by
  quickRfl

theorem ch5253_l28_xs : (xs.all invoV && xs.all fun x => xs.all (commV x)) = true := by quickRfl

theorem ch5253_l28_klein : kleinOK a b' = true := by quickRfl

theorem ch5253_l28_conj : (!difV (conjV c1 a) b' && !difV (conjV c2 a) (mulV a b')) = true := by
  quickRfl

theorem ch5253_l28_w : wAll a xs enum = true := by quickRfl

end CFSG.KS.Ivk8NormP.L28

end
