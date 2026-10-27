module

public import Certificates.Data.Kernel.Ivk8Norm
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22Data
public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Schreier.M22
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

namespace CFSG.KS.Ivk8Norm.M22

open CFSG.Certificates.Kernel.PkEnum CFSG.KS.Ivk8Norm CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu

@[expose] noncomputable def gens : List (VP 22) :=
  [mkV 22 (228952723507329932679484465855724, 228952723507329932679484465855724) (by decide +kernel),
  mkV 22 (81506110577382089737470578414133, 3070152317748115085723440829844) (by decide +kernel)]

@[expose] noncomputable def strong : List (VP 22) :=
  [mkV 22 (139621859501485755211986955675146, 549069195563130098935253750683939) (by decide +kernel),
  mkV 22 (261870867209400485234522215124448, 370851637956546617032411847925088) (by decide +kernel),
  mkV 22 (370970325831954112643234993245222, 268192838110604514212509277826089) (by decide +kernel),
  mkV 22 (261870867209400485234522215124448, 370851637956546617032411847925088) (by decide +kernel),
  mkV 22 (671317716958168823305330478887968, 330168073594559581352610925808672) (by decide +kernel),
  mkV 22 (383604909577116587447111735360608, 383604909577116587447111735360608) (by decide +kernel)]

@[expose] def wA : List ℤ := [1, 2, 1, -2, 1, -2, 1, 2, 1, 2, -1, -2, -1]

@[expose] def wB : List ℤ := [-1, -2, -1, 2, 1, 2, 1, -2, 1, -2, -1, 2, 1]

@[expose] def wcs : List (List ℤ) :=
  [[-2, 1, 2, 1, -2, -2, -1, -2, -1, -2, -1, 2, -1, -2, -2, -1, -2, -2, 1, -2, 1, 2, 2, 1, 2, 1, 2, 1,
    2, -1, -2, -2, -1, -2, -1, -2, -2, -2, 1],
  [-1, -2, -2, -1, 2, 2, 2, 1, 2, 1, -2, -2, -1, -2, -1, 2, -1, -2, -1, -2, -1, 2, -1, 2, -1, 2, -1,
    -2, -1, -2],
  [2, 2, 1, 2, -1, -2, -1, -2, -1, -2, -1, 2, -1, -2, -2, -1, -2, -1, -2, -2, -2, -1, 2, -1, -2, -2,
    -1, 2, -1, -2, -1, -2, -1, 2, -1, -2, -1, -2, -1, -2, 1, 2, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1]]

@[expose] noncomputable def A : VP 22 :=
  mkV 22 (553453832861254764372055591816586, 553453832861254764372055591816586) (by decide +kernel)

@[expose] noncomputable def B : VP 22 :=
  mkV 22 (66676011893587446957424746007207, 66676011893587446957424746007207) (by decide +kernel)

@[expose] noncomputable def cs : List (VP 22) :=
  [mkV 22 (228438751152251680996466005412365, 512860106983049677739517085714726) (by decide +kernel),
  mkV 22 (872233488833208432521703157436909, 870300460524700509858722348158118) (by decide +kernel),
  mkV 22 (430472029571146965629613937887501, 388717552705959758757852990638470) (by decide +kernel)]

@[expose] noncomputable def pairs : List (VP 22 × VP 22) := cs.zip [A, B, mulV A B]

set_option maxRecDepth 100000

theorem ch5245_gens : (gens.map Subtype.val == [(codeV m22gA).1, (codeV m22gB).1]) = true := by
  quickRfl

theorem ch5245_strong :
    ((buildV (m22CentWords1.map (evV gens)) m22CentChainWords1).map Subtype.val ==
      strong.map Subtype.val) = true := by
  quickRfl

theorem ch5245_words :
    ((A :: B :: cs).map Subtype.val == (wA :: wB :: wcs).map fun w => (evV gens w).1) = true := by
  quickRfl

theorem ch5245_klein : kleinOK A B = true := by quickRfl

theorem ch5245_conj : conjOK (gens.getD 0 (oneV 22)) pairs = true := by quickRfl

theorem ch5245_chk : chk A B cs (enumV strong #v[0, 1, 2]) = true := by quickRfl

end CFSG.KS.Ivk8Norm.M22

end
