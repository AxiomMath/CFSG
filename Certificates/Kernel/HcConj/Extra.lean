module

public import Certificates.Kernel.HcConj.Classes
import all Certificates.Data.G23RecogGlueInputs

public section

namespace CFSG.KC.HcPack

open CFSG.GH74.QTGen4.Recog.G23 CFSG.GH74.QTGen4.Recog.G23.HFactsData
  CFSG.GH74.QTGen4.Recog.G23.HCharData

@[expose] def wP (p : Fin 5 × Bool) : ℕ := cond p.2 (hcG.getD p.1 0) (hcG.getD (p.1 + 5) 0)

@[expose] noncomputable def evalP (w : List (Fin 5 × Bool)) : ℕ := w.foldr (fun p acc => mulP (wP p) acc) idP

theorem ch320017_letters :
    ∀ p : Fin 5 × Bool, pk (Lx (cond p.2 (gA p.1) (gA p.1)⁻¹)) = wP p := by
  decide +kernel

theorem ch320017_words : ∀ j : Fin 20, evalP (hcWords j) = hcRP.getD j 0 := by
  decide +kernel

theorem ch320017_gp : ∀ k : Fin 5,
    cjGP.getD (2 * k) (0, 0) = (pk (Lx (gA k)), pk (Lx (gA k)⁻¹)) ∧
      cjGP.getD (2 * k + 1) (0, 0) = (pk (Lx (gA k)⁻¹), pk (Lx (gA k))) := by
  decide +kernel

theorem ch320017_head : ∀ j : Fin 20, (hcRP.getD j 0, idP) ∈ (hcF j).zip (hcS j) := by
  decide +kernel

theorem ch320017_conj : ∀ j : Fin 20, ∀ q ∈ (hcF j).zip (hcS j),
    mulP q.2 (hcRP.getD j 0) = mulP q.1 q.2 := by
  decide +kernel

end CFSG.KC.HcPack

end
