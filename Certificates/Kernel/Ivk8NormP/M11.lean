module

public import Certificates.Data.Kernel.Ivk8NormPC
public import CFSG.Sporadic.Schreier.M11Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KS.Ivk8NormP.M11

open CFSG.Certificates.Kernel.PkEnum CFSG.KS.Ivk8Norm CFSG.KS.Ivk8NormP CFSG.Sporadic.Schreier
  CFSG.Sporadic.Mathieu

@[expose] noncomputable def gens : List (VP 11) :=
  [mkV 11 (3399539401360, 3399539401360) (by decide +kernel),
  mkV 11 (11617995925315, 11635708199815) (by decide +kernel)]

@[expose] def wY : List ℤ := [2, 2, 1, 2, 2, 1]

@[expose] def wZ : List ℤ := [-2, 1, -2, 1, -2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1]

@[expose] def wU : List (List ℤ) :=
  [[-2, 1, 2, 2, 1, 2], [-2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2], [-2, 1, 2, 1, -2, 1, 2],
    [-2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2]]

@[expose] noncomputable def eGens : List (VP 11) := [evV gens wY, evV gens wZ]

@[expose] noncomputable def us : List (VP 11) := wU.map (evV gens)

@[expose] noncomputable def eEnum : List (VP 11) := enumV (buildV eGens []) #v[1]

@[expose] def wB : List ℤ := [2, 2, 1, 2, 2, 1, 2, 2]

@[expose] def wCB : List ℤ := [-2, 1, -2, 1, 2, 1, 2]

@[expose] def wCAB : List ℤ := [2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2]

@[expose] noncomputable def a : VP 11 := gens.getD 0 (oneV 11)

@[expose] noncomputable def b' : VP 11 := evV gens wB

@[expose] noncomputable def xs : List (VP 11) := [a, b']

@[expose] noncomputable def c1 : VP 11 := evV gens wCB

@[expose] noncomputable def c2 : VP 11 := evV gens wCAB

@[expose] noncomputable def enum : List Nat :=
  (enumV (buildV gens m11Words) #v[0, 1, 2, 3]).map fun y => y.1.1

@[expose] noncomputable def wits (c : VP 11) (S : List (VP 11)) : List (Nat × Nat) :=
  (subprodsV (S.map (conjV (invV c)))).tail.map Subtype.val

@[expose] noncomputable def wAll (r : VP 11) (S : List (VP 11)) (L : List Nat) : Bool :=
  chkPC 11 4 r.1.1 [5, 11] [wits (oneV 11) S, wits c1 S, wits c2 S] L

theorem ch5253_m11_gens : (gens.map Subtype.val == [(codeV m11gA).1, (codeV m11gB).1]) = true := by
  quickRfl

theorem ch5253_m11_eSch : schV (buildV eGens []) #v[1] = true := by quickRfl

theorem ch5253_m11_eOrd : (ordV (buildV eGens []) #v[1] == 9) = true := by quickRfl

theorem ch5253_m11_hh : hhAll us eEnum = true := by quickRfl

theorem ch5253_m11_xs : (xs.all invoV && xs.all fun x => xs.all (commV x)) = true := by quickRfl

theorem ch5253_m11_klein : kleinOK a b' = true := by quickRfl

theorem ch5253_m11_conj : (!difV (conjV c1 a) b' && !difV (conjV c2 a) (mulV a b')) = true := by
  quickRfl

theorem ch5253_m11_w : wAll a xs enum = true := by quickRfl

end CFSG.KS.Ivk8NormP.M11

end
