module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TableTDefs
public import CFSG.Blueprint.ChevalleyRootsInputs
public import CFSG.Blueprint.ChevalleyStringsInputs
import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TableTTransport
import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TableTStatic
import CFSG.Certificates.Kernel.E6TT.CoverSound
import CFSG.Certificates.Kernel.E6TT.PmSound
import CFSG.Certificates.Kernel.E6TT.TableTA2Sound
import Certificates.Kernel.E6TT.Glue
import Certificates.Kernel.E6TT.CoverCheck
import Certificates.Kernel.E6TT.WeylChecks
import Certificates.Kernel.E6TT.RowChecks
import Certificates.Kernel.E6TT.PmCheck

namespace CertificateChecks.KernelE6TT

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
open CFSG.KC.E6TT
open Certificates.Data.E6TableT (Vec roots reps classes)
open CFSG.StandardType.TablePThreeKG (E6TableTAt E6TableTStmt repZ e6TableTStmt_iff
  e6TableTAt_genActZ e6TableTAt_repA4A1 e6TableTAt_repD4 e6TableTAt_repA5 e6TableTAt_repD5)

public theorem e6TableT_kernel :
    E6TableTStmt := by
  obtain ⟨-, -, hc⟩ := wOKK_spec weylA2
  have h0 : E6TableTAt (repZ 0) := e6TableTAt_repA2_of_two e6TableTTwo_kernel weylA2 hsA2
    fun l hl σ hadd hmaps hip => by
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
      have hcj := hc j hj
      have hpj := pmAll_spec pmA2 j hj
      rw [List.getD_eq_getElem _ _ hj] at hcj hpj
      exact pmK_sound (class_roots 0 hl) hcj hpj hadd hmaps hip
  have hrep : ∀ k : Fin 5, E6TableTAt (repZ k) := by
    intro k
    fin_cases k
    exacts [h0, e6TableTAt_repA4A1, e6TableTAt_repD4, e6TableTAt_repA5, e6TableTAt_repD5]
  refine e6TableTStmt_iff.2 fun v => ?_
  by_cases hv : v = 0
  · intro ρ r _ _ _ hv0
    exact absurd hv hv0
  · obtain ⟨k, hk⟩ := e6_cover_of_coverK coverOK v hv
    clear hv
    induction hk with
    | refl => exact hrep k
    | tail _ hbc ih =>
      obtain ⟨j, rfl⟩ := hbc
      exact e6TableTAt_genActZ j _ ih

end CertificateChecks.KernelE6TT
