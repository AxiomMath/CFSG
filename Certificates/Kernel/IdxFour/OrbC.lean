module

public import Certificates.Kernel.IdxFour.OrbCOK
public import CFSG.Certificates.Kernel.IdxFourOrbCSound
public import CFSG.GF2Type.Smith1979.IdxFourModelLemma5Base

public section

namespace CFSG.KD.IF4V

open CFSG.KC.IF4C CFSG.KC.IF4V CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.Viol
open CFSG.GF2Type.Smith1979.IdxFour

theorem rows_gens : pGens = [rowsP (look G 0), rowsP (look G 1)] := by decide +kernel

theorem exists_pGens_gen : ∀ g < 2, ∃ U ∈ genGrp pGens, IsP U (look G g) := by
  have key : ∀ g : Nat, rowsP (look G g) ∈ pGens → ∃ U ∈ genGrp pGens, IsP U (look G g) :=
    fun g hr => ⟨_, gen_mem gensOK_pGens hr, fun v => by rw [eqvOf_apply, linP_eq_of_rowsP rfl]⟩
  intro g hg
  interval_cases g
  · exact key 0 (by rw [rows_gens]; simp)
  · exact key 1 (by rw [rows_gens]; simp)

theorem ncard_orbit_pGens (v : V12) (hv : Orb.inO1701b (codeOf v) = true)
    (hf : f0 v (vecOf 3) = 0) : 64 ≤ Set.ncard {u : V12 | ∃ U ∈ genGrp pGens, U v = u} := by
  have h3 : f0b (codeOf v) 3 = false := (f0_codes_eq_zero v 3 (by norm_num)).1 hf
  exact ncard_orbit_of_orbCOK cf17640ok exists_pGens_gen v (by rw [inCK_eq, hv, h3]; rfl)

end CFSG.KD.IF4V

end
