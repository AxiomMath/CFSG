module

public import Certificates.Data.Kernel.Ivk8NormPC
public import CFSG.GH74.Uniqueness.SU.KI1r4F61L216Inputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KS.Ivk8NormP.L216

open CFSG.Certificates.Kernel.PkEnum CFSG.KS.Ivk8Norm CFSG.KS.Ivk8NormP
  CFSG.GH74.Uniqueness.SU.K.R4.L216M

@[expose] noncomputable def gens : List (VP 17) :=
  [mkV 17 (305932526675304725816368, 305932526675304725816368) (by decide +kernel),
  mkV 17 (11311545963260131346061456, 198863370911954521665769) (by decide +kernel),
  mkV 17 (19734123076685340054032416, 19811849773714136564372512) (by decide +kernel)]

@[expose] def wX : List (List ℤ) :=
  [[2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2],
    [2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2],
    [-2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2]]

@[expose] def wCB : List ℤ := [-2, 3, -2, 1, -2]

@[expose] def wCAB : List ℤ := [3, 2, 3, 2, -3, 2]

@[expose] def qaWords : List (List ℤ) :=
  [[-1, 2], [-3, -4, 3, 4], [5, 5, 5, 5, 5, 5, 5, 3, 5, 3], [-5, -6, -5, 4, 6, 3]]

@[expose] noncomputable def a : VP 17 := gens.getD 0 (oneV 17)

@[expose] noncomputable def xs : List (VP 17) := a :: wX.map (evV gens)

@[expose] noncomputable def b' : VP 17 := evV gens (wX.getD 0 [])

@[expose] noncomputable def c1 : VP 17 := evV gens wCB

@[expose] noncomputable def c2 : VP 17 := evV gens wCAB

@[expose] noncomputable def strong : List (VP 17) := buildV gens qaWords

@[expose] noncomputable def enum : List Nat := (enumV strong #v[0, 2, 1, 3]).map fun y => y.1.1

@[expose] noncomputable def wits (c : VP 17) (S : List (VP 17)) : List (Nat × Nat) :=
  (subprodsV (S.map (conjV (invV c)))).tail.map Subtype.val

@[expose] noncomputable def wAll (r : VP 17) (S : List (VP 17)) (L : List Nat) : Bool :=
  chkPC 17 5 r.1.1 [3, 5, 17] [wits (oneV 17) S, wits c1 S, wits c2 S] L

theorem ch5253_l216_gens :
    (gens.map Subtype.val == [(codeV pa).1, (codeV pb).1, (codeV sg).1]) = true := by
  quickRfl

theorem ch5253_l216_xs : (xs.all invoV && xs.all fun x => xs.all (commV x)) = true := by
  quickRfl

theorem ch5253_l216_klein : kleinOK a b' = true := by quickRfl

theorem ch5253_l216_conj :
    (!difV (conjV c1 a) b' && !difV (conjV c2 a) (mulV a b')) = true := by
  quickRfl

theorem ch5253_l216_w : wAll a xs enum = true := by quickRfl

end CFSG.KS.Ivk8NormP.L216

end
