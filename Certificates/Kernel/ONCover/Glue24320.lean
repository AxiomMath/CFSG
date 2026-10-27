module

public import Certificates.Kernel.CosPres.F24320A
public import Certificates.Kernel.ONCover.Glue

public section

namespace CertificateChecks.KernelONCover

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.LieType.Multipliers
open CFSG.Sporadic.Recognition.CoverRecipe CFSG.Sporadic.Recognition.ONMultiplier

@[expose] def onCover1U : List (List (Fin (subsetOf 4 [0, 1, 2]).length × Bool)) :=
  restrictWords (subsetOf 4 [0, 1, 2]) (coverWords onRels onCommWord ++ squareWords onRels)

theorem onCover1_perm : onCover1.Perm onCover1U := by
  unfold onCover1 onCover onCover1U cover₂Words restrictWords
  exact (List.mergeSort_perm _ _).filterMap _

@[expose] def wsB24 : List (List (Fin (subsetOf 4 [0, 1, 2]).length × Bool)) :=
  CFSG.KBRoute.F24320b.rels.map (decW _)

theorem wsB24_enc : wsB24.map encW = CFSG.KBRoute.F24320b.rels := by decide +kernel

theorem wsB24_restrict :
    (restrictWords (subsetOf (subsetOf 4 [0, 1, 2]).length [0, 1]) wsB24).map encW =
      CFSG.KBRoute.F24320c.rels := by
  decide +kernel

theorem wsB24_perm : wsB24.Perm onCover1U := by decide +kernel

theorem card_onCover1_le : Finite (PG _ onCover1) ∧ Nat.card (PG _ onCover1) ≤ 1876896 := by
  have hb := CFSG.KBFact.F24320b
  rw [← wsB24_enc] at hb
  have hc := CFSG.KBFact.F24320c
  rw [← wsB24_restrict] at hc
  obtain ⟨f, c⟩ := TableFact.card_restrict wsB24 (by decide)
    (subsetOf (subsetOf 4 [0, 1, 2]).length [0, 1]) (by decide) hb hc
  exact card_of_perm (wsB24_perm.trans onCover1_perm.symm) ⟨f, c.trans (by norm_num)⟩

end CertificateChecks.KernelONCover

end
