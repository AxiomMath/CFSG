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

@[expose] def heBlk64 (n : Nat) (g : Nat → Bool) (b : Nat) : Bool :=
  (List.range 64).all fun j => !decide (64 * b + j < n) || g (64 * b + j)

theorem all_of_heBlk64 {n k : Nat} {g : Nat → Bool} (hk : n ≤ 64 * k)
    (h : ∀ b < k, heBlk64 n g b = true) : (List.range n).all g = true := by
  rw [List.all_eq_true]
  intro p hp
  have hp := List.mem_range.1 hp
  have hb := h (p / 64) (by omega)
  unfold heBlk64 at hb
  have hj := List.all_eq_true.1 hb (p % 64) (List.mem_range.2 (Nat.mod_lt _ (by decide)))
  rw [Nat.div_add_mod p 64] at hj
  simpa [hp] using hj

@[expose] def x1b : Nat → Bool :=
  heBlk64 8330 fun p => x1F heWit9 CFSG.KD.HeDc.Lm (x1F heWit9 CFSG.KD.HeDc.Lm
    (x1F heWit9 CFSG.KD.HeDc.Lm p)) == p

@[expose] def x6b : Nat → Bool :=
  heBlk64 8330 fun p => x6F heWit9 CFSG.KD.HeDc.Lm (x6F heWit9 CFSG.KD.HeDc.Lm
    (x6F heWit9 CFSG.KD.HeDc.Lm p)) == p

@[expose] def cmb : Nat → Bool :=
  heBlk64 8330 fun p => x1F heWit9 CFSG.KD.HeDc.Lm (x6F heWit9 CFSG.KD.HeDc.Lm p) ==
    x6F heWit9 CFSG.KD.HeDc.Lm (x1F heWit9 CFSG.KD.HeDc.Lm p)

@[expose] def d9ib (m : Nat) : Bool :=
  heBlk64 8330 (fun p => wordF Sl (heWit9.rw.getD (m / 131) [])
    (wordF Sl (heWit9.ri.getD (m / 131) []) p) == p) (m % 131)

@[expose] def ea9b (m : Nat) : Bool :=
  heBlk64 8330 (fun p => fF heWit9 CFSG.KD.HeDc.Lm (m / 131) (fF heWit9 CFSG.KD.HeDc.Lm (m / 131)
    (fF heWit9 CFSG.KD.HeDc.Lm (m / 131) p)) == p) (m % 131)

@[expose] def d9 (i : Nat) : Bool :=
  (heWit9.rw.getD i []).all (fun l => decide (l < 4)) &&
    (heWit9.ri.getD i []).all (fun l => decide (l < 4)) &&
    (List.range 3).all fun a => (List.range 3).all fun b =>
      fixLab CFSG.KD.HeDc.Δ (wordF (three (x1F heWit9 CFSG.KD.HeDc.Lm)
        (x6F heWit9 CFSG.KD.HeDc.Lm) (wordF Sl (heWit9.rw.getD i []))) (conj9Word a b))

@[expose] def eb9 (k : Nat) : Bool :=
  distinct5 8330 (fun i => wordF (three (wordF Sl (heWit9.rw.getD i []))
    (fF heWit9 CFSG.KD.HeDc.Lm k) (wordF Sl (heWit9.ri.getD i []))) dcWord)

end CFSG.KD.HeIdx

#kss_each CFSG.KD.HeIdx.X1 CFSG.KD.HeIdx.x1b 131
#kss_each CFSG.KD.HeIdx.X6 CFSG.KD.HeIdx.x6b 131
#kss_each CFSG.KD.HeIdx.CM CFSG.KD.HeIdx.cmb 131
#kss_each CFSG.KD.HeIdx.D9I CFSG.KD.HeIdx.d9ib 655
#kss_each CFSG.KD.HeIdx.A9 CFSG.KD.HeIdx.ea9b 524
#kss_each CFSG.KD.HeIdx.D9 CFSG.KD.HeIdx.d9 5
#kss_each CFSG.KD.HeIdx.B9 CFSG.KD.HeIdx.eb9 4

namespace CFSG.KD.HeIdx

open CFSG.KC.IdxF CFSG.KC.E64F CFSG.Quasithin.S151S9T

theorem x1_ord : idOn 8330 (fun p => x1F heWit9 CFSG.KD.HeDc.Lm (x1F heWit9 CFSG.KD.HeDc.Lm
    (x1F heWit9 CFSG.KD.HeDc.Lm p))) = true :=
  all_of_heBlk64 (k := 131) (by decide) X1.all

theorem x6_ord : idOn 8330 (fun p => x6F heWit9 CFSG.KD.HeDc.Lm (x6F heWit9 CFSG.KD.HeDc.Lm
    (x6F heWit9 CFSG.KD.HeDc.Lm p))) = true :=
  all_of_heBlk64 (k := 131) (by decide) X6.all

theorem comm : eqOn 8330 (fun p => x1F heWit9 CFSG.KD.HeDc.Lm (x6F heWit9 CFSG.KD.HeDc.Lm p))
    (fun p => x6F heWit9 CFSG.KD.HeDc.Lm (x1F heWit9 CFSG.KD.HeDc.Lm p)) = true :=
  all_of_heBlk64 (k := 131) (by decide) CM.all

theorem r_id {i : Nat} (hi : i < 5) : idOn 8330 (fun p => wordF Sl (heWit9.rw.getD i [])
    (wordF Sl (heWit9.ri.getD i []) p)) = true := by
  refine all_of_heBlk64 (k := 131) (by decide) fun b hb => ?_
  have hm : 131 * i + b < 655 := by omega
  have h := D9I.all (131 * i + b) hm
  have e1 : (131 * i + b) / 131 = i := by omega
  have e2 : (131 * i + b) % 131 = b := by omega
  unfold d9ib at h
  rw [e1, e2] at h
  exact h

theorem f_ord {k : Nat} (hk : k < 4) : idOn 8330 (fun p => fF heWit9 CFSG.KD.HeDc.Lm k
    (fF heWit9 CFSG.KD.HeDc.Lm k (fF heWit9 CFSG.KD.HeDc.Lm k p))) = true := by
  refine all_of_heBlk64 (k := 131) (by decide) fun b hb => ?_
  have hm : 131 * k + b < 524 := by omega
  have h := A9.all (131 * k + b) hm
  have e1 : (131 * k + b) / 131 = k := by omega
  have e2 : (131 * k + b) % 131 = b := by omega
  unfold ea9b at h
  rw [e1, e2] at h
  exact h

theorem idx9_ok : idx9OkF heWit9 8330 CFSG.KD.HeDc.Δ 11 4 mlen CFSG.KD.HeDc.Lm Sl = true := by
  have A {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true :=
    Bool.and_eq_true_iff.2 ⟨ha, hb⟩
  unfold idx9OkF
  refine A (A ?_ ?_) ?_
  · refine A (A (A (A (A (A (A (A (A (A (A (A (A ?_ ?_) ?_) ?_) ?_) ?_) ?_) x1_ord) ?_)
      x6_ord) ?_) comm) ?_) ?_ <;> quickRfl
  · refine List.all_eq_true.2 fun i hi => ?_
    have hi := List.mem_range.1 hi
    have h := D9.all i hi
    unfold d9 at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := Bool.and_eq_true_iff.1 h |>.imp_left Bool.and_eq_true_iff.1
    exact A (A (A h1 h2) (r_id hi)) h3
  · exact List.all_eq_true.2 fun k hk => Bool.and_eq_true_iff.2
      ⟨f_ord (List.mem_range.1 hk), B9.all k (List.mem_range.1 hk)⟩

end CFSG.KD.HeIdx

end
