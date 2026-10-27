module

public import Certificates.Kernel.OmegaEight.C3006G
public import Certificates.Kernel.OmegaEight.Coset3006

public section

namespace CertificateChecks.KernelO8.C3006

open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Cover CFSG.LieType.Multipliers
    CFSG.CosetTable in
open Certificates in
theorem c3006 : (((List.finRange 8).all fun j => (List.finRange 360).all fun x =>
      (genArrs[(j : ℕ)]!)[(x : ℕ)]! == ((cycPerm 360 (genCycles j) x : Fin 360) : ℕ)) = true)
    ∧ (((rels.all fun r => decide (word r = 1)) && ((List.finRange 4).all fun i =>
        decide (word (commWords (pairs i)) = gens i)) && ((List.finRange 8).all fun j =>
        decide (word (genWords j) = cycPerm 360 (genCycles j))) && decide (word uWord * word uWord
        = 1) && decide (word tuWord = rhoT * word uWord * rhoT⁻¹)) = true)
    ∧ ((genSub {r | r ∈ rels.map FreeGroup.mk} (subsetOf 4 [0, 1, 2])).FiniteIndex ∧
        (genSub {r | r ∈ rels.map FreeGroup.mk} (subsetOf 4 [0, 1, 2])).index ≤ 120)
    ∧ ((genSub {r | r ∈ coverWs.map FreeGroup.mk} (subsetOf 4 [0, 1, 2])).FiniteIndex ∧
        (genSub {r | r ∈ coverWs.map FreeGroup.mk} (subsetOf 4 [0, 1, 2])).index ≤ 240)
    ∧ (((coverWs.all fun r => decide (rhoWord r = 1)) && decide (rhoWord uWord * rhoWord uWord =
        1) && !decide (rhoWord tuWord * rhoWord tuWord = 1)) = true) :=
  ⟨gen3006, model3006, pres3006, cover3006, rho3006⟩

end CertificateChecks.KernelO8.C3006

end
