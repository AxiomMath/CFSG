module

public import Certificates.Data.Kernel.EvenSporSuz.Cover
public import Certificates.Kernel.EvenSporSuz.Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.CoverCheck
public import Certificates.Kernel.Bounds.Suz.Route
public import Certificates.Kernel.LocalComp.SurjGen
public import Certificates.Data.Kernel.CosetJ.WordsT
meta import Certificates.Data.CFSGNative.Bridge.SuzGPL
import all Certificates.Kernel.EvenSporSuz.Data
import all CFSG.Sporadic.Recognition.SuzMultiplierInputs
import all CFSG.Sporadic.Presentation.SuzInputs
import all CFSG.LieType.Multipliers.CoverWords
import all CFSG.Certificates.CentralizerRelations
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Suzuki

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSuz.CoverST CFSG.Sporadic.Bridge.SuzGPL.Native.surjText
#lc_words CertificateChecks.KernelSuz.CoverST CFSG.Sporadic.Bridge.SuzGPL.Native.surjText

namespace CertificateChecks.KernelSuz

open CFSG.KC.EvenSporSuz CFSG.EvenSporadicStandard.TwoSuz
  CFSG.Sporadic.Recognition.SuzMultiplier

@[expose] noncomputable def YM : List (List ℕ) := (List.range 7).map fun k => rowsL (cgL k)

@[expose] noncomputable def YI : List (List ℕ) := YM.map invR24

@[expose] def relCodes : List (List ℕ) :=
  CFSG.KBRoute.Suz.rels.map (List.map fun l => 2 * l.1 + if l.2 then 0 else 1)

@[expose] noncomputable def cover25001K : Bool :=
  (nonEmptyLines CG.chars).length / 12 == 9 &&
    (List.range 9).all (fun k => (cgL k).length == 144 && (cgL k).all (· < 3)) &&
    validR YM YI &&
    relCodes.all (fun r => pmR (evalR YM YI r)) &&
    (List.finRange gcS).all (fun i => evalR YM YI (wordCodes ((i, false) :: suzCommWord i)) == oneR) &&
    evalR YM YI (wordCodes suzR3) == oneR &&
    evalR YM YI [6, 6] == negR &&
    mulR negR AR == evalR YM YI ((CoverST.W.getD 0 []).map zCode) &&
    mulR negR BR == evalR YM YI ((CoverST.W.getD 1 []).map zCode)

set_option maxHeartbeats 0 in
theorem cover25001K_true : cover25001K = true := by decide +kernel

theorem coverST_ok : CFSG.KC.WordsT.wordsT CoverST.chars CoverST.W = true := by decide +kernel

theorem neg_d_sq : (evalR YM YI [6, 6] == oneR) = false := by decide +kernel

theorem neg_pm : pmR (evalR YM YI [0]) = false := by decide +kernel

theorem neg_rel3 : (evalR YM YI (relCodes.getD 3 []) == oneR) = false := by decide +kernel

end CertificateChecks.KernelSuz
