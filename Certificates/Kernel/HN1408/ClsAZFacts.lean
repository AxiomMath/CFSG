
module

public import Certificates.Kernel.HN1408.CzTScan
public import Certificates.Kernel.HN1408.ClsBFacts

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.ClsR

open Subgroup CFSG.EvenSporadicStandard.HNRecog CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.KD.HN1408.Tr2 (genC gen_mem)

theorem caz_le_cent :
    genC classaz.centGens ≤ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) :=
  gens_le_cent rfl (fun l hl => by interval_cases l <;> decide) (by decide) CzInv.cazComm_ok

theorem cz_le_caz : CzT.czC ≤ genC classaz.centGens := by
  have h := wordsIn_mem (gs := classaz.centGens) (hs := classz.centGens) (by decide)
    (fun l hl => by interval_cases l <;> decide) (fun l hl => CzT.gen_letters hl)
    CzInv.azWords_ok
  refine (closure_le _).2 ?_
  rintro _ ⟨w, hw, rfl⟩
  have hw' : w ∈ classz.centGens := hw
  obtain ⟨l, hl, e⟩ := List.getElem_of_mem hw'
  have e' : classz.centGens.getD l [] = w := by rw [List.getD_eq_getElem _ _ hl, e]
  rw [← e']
  exact h l hl

theorem az_facts (hP : Nat.card ↥P1408 = 177408000) :
    (conjClass P1408 (elemA * elemZ)).ncard = 5775 ∧
      Nat.card ↥(P1408 ⊓ centralizer ({elemA * elemZ} : Set (Equiv.Perm (Fin 1408)))) = 30720 ∧
      genC classaz.centGens =
        P1408 ⊓ centralizer ({elemA * elemZ} : Set (Equiv.Perm (Fin 1408))) := by
  have ha := basic_ab.2.2.1
  refine ⟨CzT.class_az_card hP ha, CzT.card_cent_az hP ha, ?_⟩
  rw [CzT.cent_az ha]
  refine le_antisymm caz_le_cent ?_
  rw [← (CzT.czT_eq hP).1]
  exact cz_le_caz

end CFSG.KD.HN1408.ClsR

end
