module

public import CFSG.Quasithin.H13.L32NS7Inputs
public import CFSG.Quasithin.H13.L32NMat8

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.H13.S7Cert

@[expose] def bpOK (blks : List (List ℕ)) (x : List ℕ) : Bool :=
  blks.all fun b => decide (blkIdx blks (mv8 x (b.getD 0 0)) < blks.length) &&
    b.all fun v => blkIdx blks (mv8 x v) == blkIdx blks (mv8 x (b.getD 0 0))

theorem mv8_mul8 {x y : List ℕ} (hx : Valid8 x) (hy : Valid8 y) (w : ℕ) :
    mv8 (mul8 x y) w = mv8 x (mv8 y w) := by
  apply vec8_inj (mv8_lt (valid8_mul8 hx hy) w) (mv8_lt hx _)
  rw [← dec8_mulVec, dec8_mul8 _ _ hy.1, ← Matrix.mulVec_mulVec, dec8_mulVec, dec8_mulVec]

theorem blkPerm_mul8 {blks : List (List ℕ)} {x y : List ℕ} (hx : Valid8 x) (hy : Valid8 y)
    (hbx : bpOK blks x = true) (hby : bpOK blks y = true) :
    blkPerm blks (mul8 x y) = compL (blkPerm blks x) (blkPerm blks y) := by
  simp only [blkPerm, compL, List.map_map]
  apply List.map_congr_left
  intro b hb
  simp only [Function.comp_apply, mv8_mul8 hx hy]
  simp only [bpOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hbx hby
  have hj := (hby b hb).1
  rw [List.getD_eq_getElem (List.map (fun b => blkIdx blks (mv8 x (b.getD 0 0))) blks) 0
    (by rw [List.length_map]; exact hj), List.getElem_map]
  have hc : (blks[blkIdx blks (mv8 y (b.getD 0 0))]'hj).contains (mv8 y (b.getD 0 0)) = true :=
    List.findIdx_getElem (w := hj)
  exact (hbx _ (List.getElem_mem hj)).2 _ (List.contains_iff_mem.mp hc)

theorem pairs_of_bpOK (E : List (List ℕ)) (bA bB : List (List ℕ)) (hv : ∀ x ∈ E, Valid8 x)
    (hok : E.all (fun x => bpOK bA x && bpOK bB x) = true) :
    (E.all fun x => E.all fun y =>
      blkPerm bA (mul8 x y) == compL (blkPerm bA x) (blkPerm bA y) &&
        blkPerm bB (mul8 x y) == compL (blkPerm bB x) (blkPerm bB y)) = true := by
  simp only [List.all_eq_true, Bool.and_eq_true] at hok ⊢
  intro x hx y hy
  rw [blkPerm_mul8 (hv x hx) (hv y hy) (hok x hx).1 (hok y hy).1,
    blkPerm_mul8 (hv x hx) (hv y hy) (hok x hx).2 (hok y hy).2]
  simp

theorem valid8_elemsOf (gens : List (List ℕ)) (hg : ∀ g ∈ gens, Valid8 g) (cap : ℕ) :
    ∀ x ∈ elemsOf gens cap, Valid8 x := by
  intro x hx
  rw [elemsOf, List.mem_map] at hx
  obtain ⟨w, -, rfl⟩ := hx
  exact valid8_evalW gens hg w

end CertificateChecks.KernelH13

end
