module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi23IdentInputs
public import CFSG.YGroups.Model432FInputs
public import Certificates.Data.CFSGNative.YGroups.ExactCheck
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Kernel.YModel.Y432F
public import CFSG.Certificates.Kernel.Bounds.Fi23Alt.Binding
import CFSG.Certificates.Kernel.Common.Harness
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Sporadic.Presentation.Common
public import Mathlib

public section

namespace CertificateChecks.KernelYModel

open CFSG.KC.YModel CFSG.YGroups
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

set_option maxRecDepth 100000

theorem t23Words_eq :
    t23Words = CFSG.KBRoute.Fi23Alt.rels.map (List.map fun l => t23Letter l.1) := by
  have e : TauCeti.SporadicName.Fi23.presentation = TauCeti.Sporadic.fi23Presentation := rfl
  rw [← CFSG.KBRoute.Fi23Alt.rels_eq, TauCeti.GroupPresentation.relatorLetters_def, List.map_map,
    t23Words, CFSG.Sporadic.Presentation.Fi23.R0, e]
  apply List.map_congr_left
  intro w _
  rw [Function.comp_apply, List.map_map]
  rfl

theorem c291373_rels :
    relsOK 15 10 CFSG.KD.YMY432F.Nf
      (CFSG.KBRoute.Fi23Alt.rels.map (List.map fun l => t23Letter l.1)) = true := by
  quickRfl

theorem c291373_count : TauCeti.SporadicName.Fi23.presentation.generatorCount = 10 :=
  CFSG.KBRoute.Fi23Alt.gens_eq

theorem c291373_relators :
    ModelNative.relatorsOK 31671 y432FArrays t23Words = true := by
  rw [y432F_arrays_eq, t23Words_eq]
  exact relatorsOK_of_relsOK y432F_let c291373_rels

open CFSG.YGroups CFSG.Monster.B.Co2.Native
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three in
theorem c291373 :
    TauCeti.SporadicName.Fi23.presentation.generatorCount = 10 ∧
    ModelNative.relatorsOK 31671 y432FArrays t23Words = true := ⟨c291373_count, c291373_relators⟩

end CertificateChecks.KernelYModel

end
