module

public import Certificates.Kernel.HeIdx.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Quasithin.EmptyFaithful.S151S9THeInputs
public import Certificates.Data.Kernel.S151IdxF
public import Certificates.Kernel.SporSch.Ru.RowsGen

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public noncomputable section

namespace CFSG.KD.HeIdx

open CFSG.KC.IdxF CFSG.KC.E64F CFSG.Quasithin.S151S9T

@[expose] def h3Blk (n : Nat) (g : Nat → Bool) (b : Nat) : Bool :=
  (List.range 64).all fun j => !decide (64 * b + j < n) || g (64 * b + j)

theorem all_of_h3Blk {n k : Nat} {g : Nat → Bool} (hk : n ≤ 64 * k)
    (h : ∀ b < k, h3Blk n g b = true) : (List.range n).all g = true := by
  rw [List.all_eq_true]
  intro p hp
  have hp := List.mem_range.1 hp
  have hb := h (p / 64) (by omega)
  unfold h3Blk at hb
  have hj := List.all_eq_true.1 hb (p % 64) (List.mem_range.2 (Nat.mod_lt _ (by decide)))
  rw [Nat.div_add_mod p 64] at hj
  simpa [hp] using hj

theorem h3_or {a b c : Prop} [Decidable a] [Decidable b] [Decidable c] {x : Bool}
    (h : (decide a || decide b || decide c || x) = true) (hn : ¬(a ∨ b ∨ c)) : x = true := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;> simp_all

theorem h3_and4 {a b d e : Bool} (h : (a && b && d && e) = true) {c : Bool} (hc : c = true) :
    (a && b && c && d && e) = true := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> simp_all

@[expose] def h3zj (t : Nat) : Nat := [7, 8, 10].getD t 0

@[expose] def h3zm (t : Nat) : Bool := mlen (h3zj t) == 1

@[expose] def h3zb (m : Nat) : Bool :=
  h3Blk 8330 (fun p => Z (CFSG.KD.HeDc.Lm (h3zj (m / 131)) (4 + 0) p) ==
    CFSG.KD.HeDc.Lm (h3zj (m / 131)) (4 + 0) (Z p)) (m % 131)

@[expose] def h3cf (j : Nat) : Bool :=
  decide (j = 7) || decide (j = 8) || decide (j = 10) ||
    (heWit1.czv.getD j false == (List.range (mlen j)).all fun k =>
      eqOn 8330 (fun p => Z (CFSG.KD.HeDc.Lm j (4 + k) p))
        (fun p => CFSG.KD.HeDc.Lm j (4 + k) (Z p)))

@[expose] def h3xb : Nat → Bool :=
  h3Blk 8330 fun p => xF heWit1 CFSG.KD.HeDc.Lm (xF heWit1 CFSG.KD.HeDc.Lm
    (xF heWit1 CFSG.KD.HeDc.Lm p)) == p

@[expose] def h3rb (m : Nat) : Bool :=
  h3Blk 8330 (fun p => wordF Sl (heWit1.rw.getD (m / 131) [])
    (wordF Sl (heWit1.ri.getD (m / 131) []) p) == p) (m % 131)

@[expose] def h3w (i : Nat) : Bool :=
  (heWit1.rw.getD i []).all (fun l => decide (l < 4)) &&
    (heWit1.ri.getD i []).all (fun l => decide (l < 4)) &&
    fixLab CFSG.KD.HeDc.Δ (wordF (three (xF heWit1 CFSG.KD.HeDc.Lm)
      (wordF Sl (heWit1.rw.getD i [])) id) [0, 0, 1, 0]) &&
    fixLab CFSG.KD.HeDc.Δ (wordF (three (xF heWit1 CFSG.KD.HeDc.Lm)
      (wordF Sl (heWit1.rw.getD i [])) id) [0, 1, 0, 0])

end CFSG.KD.HeIdx

#kss_each CFSG.KD.HeIdx.H3M CFSG.KD.HeIdx.h3zm 3
#kss_each CFSG.KD.HeIdx.H3Z CFSG.KD.HeIdx.h3zb 393
#kss_each CFSG.KD.HeIdx.H3F CFSG.KD.HeIdx.h3cf 11
#kss_each CFSG.KD.HeIdx.H3X CFSG.KD.HeIdx.h3xb 131
#kss_each CFSG.KD.HeIdx.H3R CFSG.KD.HeIdx.h3rb 655
#kss_each CFSG.KD.HeIdx.H3W CFSG.KD.HeIdx.h3w 5

namespace CFSG.KD.HeIdx

open CFSG.KC.IdxF CFSG.KC.E64F CFSG.Quasithin.S151S9T

theorem h3_ztrue {t : Nat} (ht : t < 3) : (List.range (mlen (h3zj t))).all (fun k =>
    eqOn 8330 (fun p => Z (CFSG.KD.HeDc.Lm (h3zj t) (4 + k) p))
      (fun p => CFSG.KD.HeDc.Lm (h3zj t) (4 + k) (Z p))) = true := by
  have hm := H3M.all t ht
  unfold h3zm at hm
  rw [beq_iff_eq.1 hm]
  refine List.all_eq_true.2 fun k hk => ?_
  have hk : k = 0 := by
    have := List.mem_range.1 hk
    omega
  subst hk
  refine all_of_h3Blk (k := 131) (by decide) fun b hb => ?_
  have hm : 131 * t + b < 393 := by omega
  have h := H3Z.all (131 * t + b) hm
  have e1 : (131 * t + b) / 131 = t := by omega
  have e2 : (131 * t + b) % 131 = b := by omega
  unfold h3zb at h
  rw [e1, e2] at h
  exact h

theorem h3_czv {t : Nat} (ht : t < 3) : heWit1.czv.getD (h3zj t) false = true := by
  have : t = 0 ∨ t = 1 ∨ t = 2 := by omega
  rcases this with rfl | rfl | rfl <;> rfl

theorem h3_cz : (List.range 11).all (fun j => heWit1.czv.getD j false ==
    (List.range (mlen j)).all fun k => eqOn 8330 (fun p => Z (CFSG.KD.HeDc.Lm j (4 + k) p))
      (fun p => CFSG.KD.HeDc.Lm j (4 + k) (Z p))) = true := by
  refine List.all_eq_true.2 fun j hj => ?_
  have hj := List.mem_range.1 hj
  by_cases h7 : j = 7 ∨ j = 8 ∨ j = 10
  · obtain ⟨t, ht, rfl⟩ : ∃ t < 3, h3zj t = j := by
      rcases h7 with rfl | rfl | rfl
      exacts [⟨0, by decide, rfl⟩, ⟨1, by decide, rfl⟩, ⟨2, by decide, rfl⟩]
    rw [h3_ztrue ht, h3_czv ht]
    rfl
  · have hf := H3F.all j hj
    unfold h3cf at hf
    exact h3_or hf h7

theorem h3_xord : idOn 8330 (fun p => xF heWit1 CFSG.KD.HeDc.Lm (xF heWit1 CFSG.KD.HeDc.Lm
    (xF heWit1 CFSG.KD.HeDc.Lm p))) = true :=
  all_of_h3Blk (k := 131) (by decide) H3X.all

theorem h3_rid {i : Nat} (hi : i < 5) : idOn 8330 (fun p => wordF Sl (heWit1.rw.getD i [])
    (wordF Sl (heWit1.ri.getD i []) p)) = true := by
  refine all_of_h3Blk (k := 131) (by decide) fun b hb => ?_
  have hm : 131 * i + b < 655 := by omega
  have h := H3R.all (131 * i + b) hm
  have e1 : (131 * i + b) / 131 = i := by omega
  have e2 : (131 * i + b) % 131 = b := by omega
  unfold h3rb at h
  rw [e1, e2] at h
  exact h

theorem h3_rows : (List.range 5).all (fun i =>
    (heWit1.rw.getD i []).all (fun l => decide (l < 4)) &&
      (heWit1.ri.getD i []).all (fun l => decide (l < 4)) &&
      idOn 8330 (fun p => wordF Sl (heWit1.rw.getD i []) (wordF Sl (heWit1.ri.getD i []) p)) &&
      fixLab CFSG.KD.HeDc.Δ (wordF (three (xF heWit1 CFSG.KD.HeDc.Lm)
        (wordF Sl (heWit1.rw.getD i [])) id) [0, 0, 1, 0]) &&
      fixLab CFSG.KD.HeDc.Δ (wordF (three (xF heWit1 CFSG.KD.HeDc.Lm)
        (wordF Sl (heWit1.rw.getD i [])) id) [0, 1, 0, 0])) = true := by
  refine List.all_eq_true.2 fun i hi => ?_
  have hi := List.mem_range.1 hi
  have h := H3W.all i hi
  unfold h3w at h
  exact h3_and4 h (h3_rid hi)

theorem idx3_ok : idx3OkF heWit1 8330 CFSG.KD.HeDc.Δ 11 4 mlen CFSG.KD.HeDc.Lm Sl Z = true := by
  have A {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true :=
    Bool.and_eq_true_iff.2 ⟨ha, hb⟩
  unfold idx3OkF
  refine A (A (A (A (A (A (A (A (A (A (A ?_ ?_) ?_) ?_) ?_) h3_cz) h3_xord) ?_) ?_) ?_)
    h3_rows) ?_ <;> quickRfl

end CFSG.KD.HeIdx

end
