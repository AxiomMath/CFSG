module

public import Certificates.Kernel.SporSch.PairBT.McLSylFacts
public import Certificates.Kernel.SporSch.PairBT.McLZOrb
public import CFSG.Certificates.Kernel.SporSch.CntZKProof

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.McLClass

open CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch.MOC CFSG.KS.SporSch.MBT CFSG.Sporadic.Schreier
open CertificateChecks.KernelSporSch

theorem mclGen_img {j : Nat} (hj : j < 2) :
    CFSG.Monster.B.Mathieu.imageList (mclGen j) = (unpack 275 9 (PMcL.S j)).toList := by
  have h := rep_mclStrongPerm (j := j) (by omega)
  rw [PMcLCheck.arr_eq j (by omega)] at h
  have h' : CFSG.Monster.B.Co2.Rep 275 (unpack 275 9 (PMcL.S j)) (mclGen j) := h
  apply List.ext_getElem
  · rw [CFSG.Monster.B.Mathieu.imageList, List.length_ofFn, Array.length_toList, unpack,
      Array.size_ofFn]
  · intro i h1 h2
    have hi : i < 275 := by
      rw [CFSG.Monster.B.Mathieu.imageList, List.length_ofFn] at h1
      exact h1
    have key : ∀ (t : Array ℕ) (h : i < t.size), t[i]! = t[i] := fun t h => getElem!_pos t i h
    simp only [CFSG.Monster.B.Mathieu.imageList, List.getElem_ofFn, Array.getElem_toList]
    rw [← h'.apply hi]
    exact key _ _

theorem card_class :
    Nat.card {x : mclP // IsConj (⟨mclGen 0, Subgroup.subset_closure (by simp)⟩ : mclP) x} =
      22275 := by
  classical
  have h := clsCard_sem (n := 275) (w := 9) (gA := mclGen 0) (gB := mclGen 1) (by norm_num)
    ⟨mclGen 0, Subgroup.subset_closure (by simp)⟩
    (McLZOrb.sem (mclGen_img (j := 0) (by omega)) (mclGen_img (j := 1) (by omega)))
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
    Nat.eq_of_beq_eq_true McLSylFacts.dc0] at h
  exact h

end CertificateChecks.KernelSporSch.McLClass

end
