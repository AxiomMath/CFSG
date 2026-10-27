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

namespace CFSG.KD.LQT.C4048

open CFSG.KC.LQT.R CFSG.QuasithinUnique.Unc25K1 CFSG.QuasithinUnique.Unc25L33

theorem ha : codeR sa = 25872 := by decide +kernel
theorem hb : codeR sb = 34818 := by decide +kernel
theorem hp : P0R.map codeR = [65793, 34818, 25872, 137736, 18054, 132705, 83076, 164448, 108948, 104808, 73818, 37017, 156690, 152073, 4518, 10341] := by decide +kernel
theorem hw : W3.map codeR = [67921, 157076] := by decide +kernel
theorem hk : c4048 25872 34818 [65793, 34818, 25872, 137736, 18054, 132705, 83076, 164448, 108948, 104808, 73818, 37017, 156690, 152073, 4518, 10341]
    [34818, 132705, 108948, 104808, 152073] [67921, 157076] [16, 24, 17, 33, 2, 10, 26, 34, 3, 19, 12, 20] = true := by quickRfl

@[expose] noncomputable def sF (c : Nat) : Bool :=
  allSLc c (sl4048 25872 34818 [65793, 34818, 25872, 137736, 18054, 132705, 83076, 164448, 108948,
    104808, 73818, 37017, 156690, 152073, 4518, 10341] [34818, 132705, 108948, 104808, 152073]
    [16, 24, 17, 33, 2, 10, 26, 34, 3, 19, 12, 20])

#kc_each_unfold sF 0 20 as CFSG.KD.LQT.C4048.s

theorem hs : ∀ c < 20, allSLc c (sl4048 25872 34818 [65793, 34818, 25872, 137736, 18054, 132705, 83076, 164448, 108948, 104808, 73818, 37017, 156690, 152073, 4518, 10341] [34818, 132705, 108948, 104808, 152073] [16, 24, 17, 33, 2, 10, 26, 34, 3, 19, 12, 20]) = true :=
  forall_lt_20 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19

end CFSG.KD.LQT.C4048

end
