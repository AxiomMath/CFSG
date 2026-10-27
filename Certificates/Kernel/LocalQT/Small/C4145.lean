module

public import CFSG.Certificates.Kernel.LocalQTR9Sound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachUnfold
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementBlock
public import CFSG.ClassicalGroups
public import CFSG.GH74.Exceptional.LinearFourTwo
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.LocalAnalysis.ComponentInitial.LinearTwoOuterOrder
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Glue
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X35Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.D8
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_12Aux
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15Aux
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15FactsGen
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6
public import CFSG.Permutation.AlternatingAutomorphism.Conjugation
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.C4145

open CFSG.KC.LQT.R CFSG.QuasithinUnique.Unc25K1

@[expose] def wu : List Nat :=
  [142020186640, 142087296592, 142154406544, 77864116768, 77931227744, 77998335648,
    36592287812, 40887275588, 45182263364, 176379941396, 172152194132, 180809214356,
    112223887908, 103701153892, 108063184292, 18405785736, 22700789896, 26995744904,
    159200088600, 163562218840, 155039434904, 95044002344, 90816223592, 86588392616,
    35434660353, 44024599041, 39729635841, 35568878145, 44158816833, 39863853633,
    35501769345, 44091708033, 39796744833, 69005869585, 69140089425, 69072979601,
    137993781793, 138128000609, 138060892833, 35451437573, 44041409029, 39746429445,
    103365607957, 107794688341, 112022623381, 172353520165, 181077579109, 176715557029,
    19345310217, 27935265289, 23640318473, 86185738777, 94909847641, 90547725721,
    155173650985, 159602812009, 163830585769, 39007044610, 43570464770, 17263886594,
    25853837570, 21558886658, 17532323074, 17800759554, 8875213314, 26055098882, 43234984450,
    77594694146, 94774579714, 111954465282, 146314174978, 163494060546, 180673946114,
    8942323202, 4915792386, 176446002242, 112289949762, 18337628482, 22632632642,
    26927587650, 154971276610, 86520236354, 146381284930, 73635273282, 107726529666,
    181009422466, 19411370370, 28001325442, 23706378626, 86251799938, 155239713154,
    77661804162, 142354754178, 8876261906, 8943371794, 9010481682, 4849730082, 4983948834,
    4916840994, 34511913222, 38806896902, 43101880582, 39008093206, 34780350742, 43236033046,
    43571513382, 35048785190, 39209484838, 17264935178, 25854886154, 21559935242,
    21895350298, 17533371674, 26056147482, 26458735658, 17801808170, 22029632042]

theorem hu : codeR (rr u0S) = 131585 := by decide +kernel
theorem ha : codeR (rr aS) = 164865 := by decide +kernel
theorem hb : codeR (rr bS) = 149505 := by decide +kernel
theorem ht : (TlS.map rr).map codeR = [65793, 164865, 149505, 82177, 98561, 66817, 67841, 34305, 18945] := by decide +kernel
theorem hk : c4145 131585 164865 149505 [65793, 164865, 149505, 82177, 98561, 66817, 67841, 34305, 18945] WsS wu = true := by quickRfl
@[expose] noncomputable def sF (c : Nat) : Bool :=
  allSLc c (sl4145 131585 [65793, 164865, 149505, 82177, 98561, 66817, 67841, 34305, 18945] wu)

#kc_each_unfold sF 0 20 as CFSG.KD.LQT.C4145.s
theorem hs : ∀ c < 20, allSLc c (sl4145 131585 [65793, 164865, 149505, 82177, 98561, 66817, 67841, 34305, 18945] wu) = true :=
  forall_lt_20 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19

end CFSG.KD.LQT.C4145

end
