module

public import Certificates.Data.Kernel.Ivk8NormP
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23Data
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Mathieu.Simple
public import CFSG.Sporadic.Schreier.M23Base
public import CFSG.Sporadic.Schreier.M23CheckBase
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Schreier.Outer

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 100

namespace CFSG.KS.Ivk8NormP.M23

open CFSG.Certificates.Kernel.PkEnum CFSG.KS.Ivk8Norm CFSG.KS.Ivk8NormP CFSG.Sporadic.Schreier
  CFSG.Sporadic.Mathieu

@[expose] noncomputable def gens : List (VP 23) :=
  [mkV 23 (29396287020561317414859794500619265, 29396287020561317414859794500619265)
    (by decide +kernel),
  mkV 23 (4436007312844787929641103698034959, 9299982975027872919014373496400226) (by decide +kernel)]

@[expose] def wH : List (List ℤ) :=
  [[2, 1, 1, 2, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, -2, -1, 2, -1, -2, -1, -2, -1, -2, -1, 2, -1, 2, -1,
    -2, -1, -1, -2, -2, -1, -2, -2, -1, -2, -1, -2, -2, -1, -2, -2, -1, -2, -2, 1, 2, 2, 1, 2, 1, -2,
    1, 2, 1, 2, 1, 2, 1, 2],
  [-1, -2, -1, -2, 1, 2, 1, -2, 1, 2, 1, -2, -1, 2, -1, -2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -2, -1,
    -1, -2, -2, -1, -2, -2, -1, -2, -1, -2, -2, -1, -2, -2, -1, -2, -2, 1, 2, 2, 1, 2, 1, -2, 1, 2, 1,
    2, 1, 2, 1, 2],
  [-1, -1, 2, -1, -2, -1, 2, -1, -2, -1, 2, -1, 2, -1, -2, -1, 2, -1, -2, -1, -2, -1, -2, -1, -2, -1,
    -2, -1, 2, -1, 2, -1, 2, -1, 2, 1, 2, 2, 1, 2, -1, -2, -2, -1, -2, -2, -1, -2, -1, -2, -2, -1, -2,
    -2, -1, -2, -2, 1, 2, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2]]

@[expose] def wC1 : List ℤ :=
  [-1, 2, -1, -2, -1, 2, -1, -2, -1, -2, -1, -2, -2, -1, 2, -1, 2, -1, -2, -1, 2, -1, -2, -1, -1, 2,
    -1, -2, -1, -2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2, -2, -1, -2, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1,
    2, 1, 2, 1, -2, 1, 2, 1, 2, 2, -1, -2, -1, 2, -1, -2, -1, -2, -1, -2, -1, 2, -1, -2, -2]

@[expose] def wC2 : List ℤ :=
  [-2, 1, 2, 1, -2, 1, 2, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, -1, 2, -1, -2, -2, -1, 2, -1, -2,
    -1, 2, -1, 2, -1, -2, -1, -2, -1, -2, -1, -2, -2, -1, 2, -1, -2, -1, -2, -1, -2, -1, 2, -1, -2, 1,
    2, 1, -2, -1, -2, -1, -2, -2, -1, 2, -1, -2, -1, 2, -1, 2, -1, -2, -1, 2]

@[expose] noncomputable def a : VP 23 := gens.getD 0 (oneV 23)

@[expose] noncomputable def xs : List (VP 23) := a :: wH.map (evV gens)

@[expose] noncomputable def b' : VP 23 := evV gens (wH.getD 2 [])

@[expose] noncomputable def c1 : VP 23 := evV gens wC1

@[expose] noncomputable def c2 : VP 23 := evV gens wC2

@[expose] noncomputable def strong : List (VP 23) :=
  buildV (m23CentWords1.map (evV gens)) m23CentChainWords1

@[expose] noncomputable def enum : List Nat := (enumV strong #v[2, 0, 5, 4]).map fun y => y.1.1

@[expose] noncomputable def wits (c : VP 23) (S : List (VP 23)) : List (Nat × Nat) :=
  (subprodsV (S.map (conjV (invV c)))).tail.map Subtype.val

@[expose] noncomputable def wAll (S : List (VP 23)) (L : List Nat) : Bool :=
  chkP 23 5 3 (wits (oneV 23) S) L && chkP 23 5 7 (wits (oneV 23) S) L &&
    chkP 23 5 3 (wits c1 S) L && chkP 23 5 7 (wits c1 S) L &&
    chkP 23 5 3 (wits c2 S) L && chkP 23 5 7 (wits c2 S) L

theorem ch5253_m23_gens :
    (gens.map Subtype.val == [(codeV m23PermA).1, (codeV m23PermB).1]) = true := by
  quickRfl

theorem ch5253_m23_xs : (xs.all invoV && xs.all fun x => xs.all (commV x)) = true := by quickRfl

theorem ch5253_m23_conj : (!difV (conjV c1 a) b' && !difV (conjV c2 a) (mulV a b')) = true := by
  quickRfl

theorem ch5253_m23_w : wAll xs enum = true := by quickRfl

end CFSG.KS.Ivk8NormP.M23

end
