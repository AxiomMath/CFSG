module

public import Certificates.Kernel.EvenSporSuz.Outer25030
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.OuterCheck
import Certificates.Kernel.EvenSporSuz.Data
import Init.Data.List.SplitOn.Basic
public import Certificates.Kernel.EvenSporSuz.Outer25030F
import Certificates.Kernel.EvenSporSuz.Bridge
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSuz

open CFSG.KC.EvenSporSuz CFSG.EvenSporadicStandard.TwoSuz

theorem coverGS_getD {k : ℕ} (hk : k < 7) : coverGS.mats.getD k oneM = (cgL k).toArray := by
  have hn : (nonEmptyLines CG.chars).length / 12 = 9 := inputs.2.2.2.2.2.2.2.1
  have hCM : coverMats = ((List.range 9).map fun k => (cgL k).toArray).toArray := by
    unfold coverMats
    rw [CG.eq, parseMats_ofList]
    unfold matsK
    rw [hn]
    rfl
  have hE : coverGS.mats = ((List.range 7).map fun k => (cgL k).toArray).toArray := by
    change coverMats.extract 0 7 = _
    rw [hCM]
    apply Array.toList_inj.1
    simp only [Array.toList_extract, List.toList_toArray, List.extract_eq_drop_take,
      List.drop_zero, Nat.sub_zero]
    apply List.ext_getElem
    · simp
    · intro n h1 h2
      simp
  rw [hE, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_range hk, Option.map_some, Option.getD_some]

end CertificateChecks.KernelSuz

end
