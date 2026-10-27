module

public import Certificates.Kernel.GL33T.Nodes
public import Certificates.Kernel.GL33T.Shape
public import CFSG.Certificates.Kernel.GL33TSound
public import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.RankThree.PartTwo.Sec21.FF79GL33Basis
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.KD.GL33T

open CFSG.KC.GL33T

#kc_forall_chunks nodeAll (fun i => nodeC i = true) 48 CFSG.KD.GL33T.ch799501n_ 1

#kc_forall_chunks qAll (fun k => qC k = true) 4 CFSG.KD.GL33T.ch799501q_ 1

open CFSG.RankThree.PartTwo.Sec21.FF79.GL33 (GL33At e0 e1 e2) in
theorem gl33_tree : ∀ X : Subgroup (GL (Fin 3) (ZMod 3)), GL33At X e0 e1 e2 := by
  have hr := ch799501root
  unfold rootC at hr
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, Nat.beq_eq, Nat.beq_eq,
    Nat.beq_eq] at hr
  obtain ⟨⟨⟨h0, hl⟩, -⟩, hq⟩ := hr
  have hsh := (uptoK_iff _ _).1 ch799501shape
  refine tree_sound (G' := gens) hl h0 fun i hi => ⟨mask, List.getD recs i [],
    List.getD mask i 0, List.getD kind i 9, List.getD qmask (List.getD q i 0) 0,
    List.getD qreps (List.getD q i 0) [], List.getD s1reps i [], List.getD s1cov i [],
    List.getD orr i [], List.getD org i [], List.getD ori i [], List.getD ucov i [],
    List.getD phiw i [], List.getD ch i [], nodeAll i hi, hsh i hi, ?_⟩
  by_cases hk : List.getD q i 0 < 4
  · exact Or.inr ⟨_, qAll _ hk⟩
  · left
    rw [List.getD_eq_default]
    rw [lenK_eq] at hq
    change qmask.length = 4 at hq
    omega

open CFSG.RankThree.PartTwo.Sec21.FF79 CFSG.RankThree.PartTwo.Sec21.FF79.GL33 in
theorem ff79 : FF79KGL33 := by
  intro X v w₁ w₂ hli
  have hU := isUnit_basisMat v w₁ w₂ hli
  let P : GL (Fin 3) (ZMod 3) := hU.unit
  have hP : (P : Mat) = basisMat v w₁ w₂ := rfl
  have e0' : ∀ (M : Mat) (j : Fin 3), Matrix.vecMul e0 M j = M 0 j := by
    intro M j
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, e0]
  have h0 : psi P e0 = v := by
    funext j; exact (e0' (P : Mat) j).trans (by rw [hP]; rfl)
  have h1 : psi P e1 = w₁ := by
    funext j; exact (vecMul_e1 (P : Mat) j).trans (by rw [hP]; rfl)
  have h2 : psi P e2 = w₂ := by
    funext j; exact (vecMul_e2 (P : Mat) j).trans (by rw [hP]; rfl)
  have := GL33At_transport P X (gl33_tree (conjSub P X))
  rw [h0, h1, h2] at this
  exact this

end CFSG.KD.GL33T

end
