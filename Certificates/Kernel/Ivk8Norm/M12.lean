module

public import Certificates.Data.Kernel.Ivk8Norm
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12Data
public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Schreier.M12
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

namespace CFSG.KS.Ivk8Norm.M12

open CFSG.Certificates.Kernel.PkEnum CFSG.KS.Ivk8Norm CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu

@[expose] noncomputable def gens : List (VP 12) :=
  [mkV 12 (92532767328531, 92532767328531) (by decide +kernel),
  mkV 12 (180734465348391, 82837192188216) (by decide +kernel)]

@[expose] noncomputable def strong : List (VP 12) :=
  [mkV 12 (92532767328531, 92532767328531) (by decide +kernel),
  mkV 12 (73835162417541, 58418099104116) (by decide +kernel),
  mkV 12 (5807168789106, 72808665796731) (by decide +kernel),
  mkV 12 (5052613415451, 5052613415451) (by decide +kernel),
  mkV 12 (178499231497056, 47589874809456) (by decide +kernel),
  mkV 12 (83108013879936, 182043938599536) (by decide +kernel),
  mkV 12 (39953809160976, 39953809160976) (by decide +kernel),
  mkV 12 (73355502368016, 164130148006416) (by decide +kernel)]

@[expose] def wA : List ℤ := [1, -2, 1, 1, -2, -1, 2, -1, -2, -1, -2, -2, 1, -2, 1, 2, 2, 1]

@[expose] def wB : List ℤ :=
  [2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -1, 2, -1, -2, -1, 2, 1, 2, -1, -2, 1, 2, -1, 2, -1, -2]

@[expose] def wcs : List (List ℤ) :=
  [[-2, -2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -2, -1, 2, -1, 2, -1, -2, -1, 2, -1, 2, -1, -2, -1, 2,
    -1, 2, 2, 1, 2, -1, -2, -1, -2, -1, 2, -1, -2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2, -1, -2, -1,
    2],
  [-2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2],
  [-1, -2, -1, 2, -1, -2, -1, 2, -1, -2, -1, -2, -1, -2, -1, 2, -1, 2, -1, 2, -1, 2, -1, -2, -1, 2,
    -1, -2, -1, -2, -2, 1, 2, 1, -2, 1, 2, 1, 2, -1, -2, -1, -2, -1, 2, -1, -2, -1, 2, -1, 2, -1, 2,
    -1, -2, -1, -2, -1, -2, -1, 2]]

@[expose] noncomputable def A : VP 12 := mkV 12 (22645037478066, 22645037478066) (by decide +kernel)

@[expose] noncomputable def B : VP 12 := mkV 12 (28825763484336, 28825763484336) (by decide +kernel)

@[expose] noncomputable def cs : List (VP 12) :=
  [mkV 12 (47732236592436, 179801979624261) (by decide +kernel),
  mkV 12 (204002894767941, 203036576270166) (by decide +kernel),
  mkV 12 (45567002781876, 21589045300101) (by decide +kernel)]

@[expose] noncomputable def pairs : List (VP 12 × VP 12) := cs.zip [A, B, mulV A B]

set_option maxRecDepth 100000

theorem ch5244_gens : (gens.map Subtype.val == [(codeV m12gA).1, (codeV m12gB).1]) = true := by
  quickRfl

theorem ch5244_strong :
    ((buildV (m12CentWords1.map (evV gens)) m12CentChainWords1).map Subtype.val ==
      strong.map Subtype.val) = true := by
  quickRfl

theorem ch5244_words :
    ((A :: B :: cs).map Subtype.val == (wA :: wB :: wcs).map fun w => (evV gens w).1) = true := by
  quickRfl

theorem ch5244_klein : kleinOK A B = true := by quickRfl

theorem ch5244_conj : conjOK (gens.getD 0 (oneV 12)) pairs = true := by quickRfl

theorem ch5244_chk : chk A B cs (enumV strong #v[0, 1, 2]) = true := by quickRfl

end CFSG.KS.Ivk8Norm.M12

end
