module

public import Certificates.Data.S5RowsG23
public import Certificates.Kernel.G2Three.RowsChecks
public import Certificates.Kernel.G2Three.Final

public section

namespace CFSG.KD.G2Three

open CFSG.KC.G2Three CFSG.KC.Ord CFSG.RankThree.PartTwo.Census.Carrier.G2Three
  Certificates.S5RowsG23

theorem q8RelC_pk {i j : List ℕ} {I J : ℕ} (hi : canon14 i = true ∧ pk i = I)
    (hj : canon14 j = true ∧ pk j = J) : q8RelC i j = q8K I J := by
  have s := mulE consts_ok hi hi
  have s2 := mulE consts_ok s s
  have sj := mulE consts_ok hj hj
  have ij := mulE consts_ok hi hj
  have iji := mulE consts_ok ij hi
  simp only [q8RelC, q8K, sq14, bne, beq_pk s2.1 canon14_one14, beq_pk s.1 canon14_one14,
    beq_pk s.1 sj.1, beq_pk iji.1 hj.1, s2.2, s.2, sj.2, iji.2, hj.2, bone]

theorem threeCycC_pk {y i j : List ℕ} {Y I J : ℕ} (hy : canon14 y = true ∧ pk y = Y)
    (hi : canon14 i = true ∧ pk i = I) (hj : canon14 j = true ∧ pk j = J) :
    threeCycC y i j = threeK Y I J := by
  have iy := mulE consts_ok hi hy
  have yj := mulE consts_ok hy hj
  have jy := mulE consts_ok hj hy
  have yij := mulE consts_ok hy (mulE consts_ok hi hj)
  have yji := mulE consts_ok hy (mulE consts_ok hj hi)
  simp only [threeCycC, threeK, beq_pk iy.1 yj.1, beq_pk jy.1 yij.1, beq_pk jy.1 yji.1, iy.2,
    yj.2, jy.2, yij.2, yji.2]

theorem getElem_getD {α : Type} {E : Array α} {t : ℕ} (ht : t < E.size) (d : α) :
    E[t] = E.getD t d := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ht]
  rfl

theorem ok516003 : g23RowsF4 () = true := by
  obtain ⟨hSz, -, -, -, hS⟩ := tabS
  obtain ⟨hXz, -, -, -, hX⟩ := tabX
  have h := rows516003_ok
  unfold rowsK at h
  have hA := allBelow_g2 h (by decide)
  unfold g23RowsF4
  simp only [Array.all_eq_true]
  intro a ha b hb
  rw [hSz] at ha hb
  have hab := allBelow_g2 (hA a ha) (by decide) b hb
  rw [getElem_getD _ [], getElem_getD _ [], q8RelC_pk (hS a ha) (hS b hb)]
  cases hq : q8K (XS a) (XS b)
  · rfl
  · rw [hq, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hab
    obtain ⟨hw, h3⟩ := hab
    have hw' : RowW (Nat.add (Nat.mul 64 a) b) < 576 := Nat.blt_eq.mp hw
    rw [Bool.not_true, Bool.false_or, Array.any_eq_true]
    refine ⟨_, hXz ▸ hw', ?_⟩
    rw [getElem_getD _ [], threeCycC_pk (hX _ hw') (hS a ha) (hS b hb)]
    exact h3

end CFSG.KD.G2Three

end
