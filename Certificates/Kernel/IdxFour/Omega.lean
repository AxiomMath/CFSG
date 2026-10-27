
module

public import Certificates.Kernel.IdxFour.OmegaOK
public import CFSG.Certificates.Kernel.IdxFourReachSound
public import CFSG.GF2Type.Smith1979.IdxFourModelLemma5Base

public section

namespace CFSG.KD.IF4W

open CFSG.KC.IF4C CFSG.KC.IF4W CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.Viol
open CFSG.GF2Type.Smith1979.IdxFour

theorem rows_gens : pGens = [rowsP (look G 0), rowsP (look G 1)] := by decide +kernel

theorem exists_pGens_gen : ∀ g < 2, ∃ U ∈ genGrp pGens, IsP U (look G g) := by
  have key : ∀ g : Nat, rowsP (look G g) ∈ pGens → ∃ U ∈ genGrp pGens, IsP U (look G g) :=
    fun g hr => ⟨_, gen_mem gensOK_pGens hr, fun v => by rw [eqvOf_apply, linP_eq_of_rowsP rfl]⟩
  intro g hg
  interval_cases g
  · exact key 0 (by rw [rows_gens]; simp)
  · exact key 1 (by rw [rows_gens]; simp)

theorem exists_pGens_of_inOmegab (v : V12) (hv : Orb.inOmegab (codeOf v) = true) :
    ∃ U ∈ genGrp pGens, U (vecOf 12) = v :=
  exists_of_reachOK cf17606tree exists_pGens_gen v (by rw [inOmK_eq]; exact hv)

end CFSG.KD.IF4W

end
