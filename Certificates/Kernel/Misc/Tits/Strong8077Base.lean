
module

public import CFSG.Quasithin.Recognition.CertTitsBase
public import CFSG.Quasithin.Recognition.CertPermSimple
public import CFSG.Quasithin.Recognition.CertDataTitsSimple
public import Certificates.Data.CFSGNative.YGroups.ExactCheck
public import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Quasithin.Recognition.CertTitsSimpleInputs
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Quasithin.Recognition.CertTitsSimpleMainBase
public import CFSG.Blueprint.Catalog
public import Certificates.Kernel.Misc.Tits.Prim8077
public import Certificates.Kernel.TitsW.Alg
public import Certificates.Kernel.Sporadic.Tits.GroupT2264
public import CFSG.Certificates.Kernel.Spor.StrongOfSound
public import CFSG.Certificates.Kernel.Spor.Co2ChainSound
public import CFSG.Certificates.Kernel.Spor.DecLinesRead
public import CFSG.Certificates.Kernel.YModel.Sound
public import Certificates.Kernel.YModel.Basic
public import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic

@[expose] public section

set_option maxRecDepth 400000

open CFSG CFSG.Quasithin CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CertificateChecks.KernelMisc CertificateChecks.KernelTitsW CertificateChecks.KernelSpor.Tits2264
open CertificateChecks.KernelMisc.TitsPrim8077

namespace CertificateChecks.TitsStrong8077

theorem textLines_nl (cs : List Char) :
    CFSG.YGroups.ModelNative.textLines (String.ofList ('\n' :: cs)) =
      CFSG.YGroups.ModelNative.textLines (String.ofList cs) := by
  rw [CFSG.KS.DecLines.textLines_ofList, CFSG.KS.DecLines.textLines_ofList,
    List.splitOnP_cons_eq_ite_modifyHead]
  simp

theorem textLines_zero (cs : List Char) :
    CFSG.YGroups.ModelNative.textLines (String.ofList ('0' :: '\n' :: cs)) =
      "0" :: CFSG.YGroups.ModelNative.textLines (String.ofList cs) := by
  rw [CFSG.KS.DecLines.textLines_ofList, CFSG.KS.DecLines.textLines_ofList,
    List.splitOnP_cons_eq_ite_modifyHead, List.splitOnP_cons_eq_ite_modifyHead]
  simp

theorem ab_chars : TitsAbC.chars = '\n' :: TitsAbC.chars.tail := by decide +kernel

theorem words_eq : titsAbWords = abW := by
  have h := (CFSG.KC.YModel.decBind_chain (by decide) TitsAbT.ok).2
  rw [← CFSG.KC.YModel.charsOf_eq, TitsOut.abChars, ab_chars] at h
  unfold CFSG.YGroups.ModelNative.chainWords at h
  rw [textLines_zero] at h
  have e : titsAbWords = (CFSG.KC.YModel.linesW (CFSG.KC.YModel.lget TitsAbT.El) 32
      (fun L => CFSG.KC.YModel.joinW 32 (CFSG.KC.YModel.lgetL TitsAbT.Cl L)) TitsAbT.lines).toList := by
    rw [titsAbWords, TitsAbC.eq, ab_chars, textLines_nl, ← h]
    simp
  rw [e]
  rfl

theorem perm2 : allN 2 (fun j => permOK 1755 11 (mask 11) (1755 * 11) (DS j) (DSI j)) =
    true :=
  CFSG.KS.Raw.Orb.allN_iff.2 fun j hj => CFSG.KS.Raw.Orb.allN_iff.1 dPerm j (by omega)

theorem split {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem letters₀ : lettersOK 2 (titsAbWords.getD 0 []) = true := by
  rw [words_eq, ← CFSG.KS.Co2SShape.lettersK_eq]
  exact (@split (lettersK 2 (abW.getD 0 [])) (lettersK 2 (abW.getD 1 [])) letters).1

theorem letters₁ : lettersOK 2 (titsAbWords.getD 1 []) = true := by
  rw [words_eq, ← CFSG.KS.Co2SShape.lettersK_eq]
  exact (@split (lettersK 2 (abW.getD 0 [])) (lettersK 2 (abW.getD 1 [])) letters).2

theorem gdA : Gd A := Gd_WD _

theorem gdB : Gd B := Gd_WD _

theorem s_eq : TitsPCh.S 0 = A ∧ TitsPCh.S 1 = B := by
  obtain ⟨h1, h2⟩ := @split (Nat.beq (TitsPCh.S 0) A) (Nat.beq (TitsPCh.S 1) B) sOK
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2⟩

theorem pwords_eq : titsPairWords = TitsPCT.words.toArray := by
  have h := (CFSG.KC.YModel.decBind_chain (by decide) TitsPCT.ok).2
  rw [← CFSG.KC.YModel.charsOf_eq] at h
  have e : CFSG.YGroups.ModelNative.chainWords titsPairChainText =
      CFSG.YGroups.ModelNative.chainWords (String.ofList (CFSG.KC.YModel.charsOf TitsPCT.CH)) := by
    rw [TitsPCT.eq]
    unfold CFSG.YGroups.ModelNative.chainWords
    simp only [List.replicate_one, List.append_eq, List.singleton_append, textLines_nl]
  rw [titsPairWords, e, h]
  rfl

theorem baseOK : allN 7 (fun t => Nat.beq ((titsPairBase.map Fin.val).toArray)[t]!
    (pg 11 (mask 11) TitsPCh.BP t)) = true := by quickRfl

end CertificateChecks.TitsStrong8077

end
