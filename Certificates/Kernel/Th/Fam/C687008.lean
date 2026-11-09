module

public import Certificates.Kernel.Th.Fam.K
public import Certificates.Data.Th687.MFactsD
public import Certificates.Kernel.Th.Fam.C687011L
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ListSlices
public import CFSG.Certificates.Kernel.Common.ForallTree
meta import CFSG.Certificates.Kernel.Common.ForallTree

public section

set_option maxRecDepth 100000
set_option Elab.async false

namespace CertificateChecks.KernelTh.Fam

open CFSG.KC.Th.Expr CFSG.Sporadic.Th.Recog

@[expose] def wjT (i : Fin 8) : TE := .mul (.word (wJ i)) (.pow .a (εJ i))

@[expose] def w1T : TE := .mul (wjT 3) (wjT 4)

@[expose] def w12T : TE := .mul w1T (.mul (.mul (wjT 7) w1T) (.pow (wjT 7) 3))

@[expose] noncomputable def commL (G : Nat) : List (Fin 512) :=
  (List.finRange 512).filter fun k =>
    Nat.beq (thK.mul G ((TE.nf k).pk thK)) (thK.mul ((TE.nf k).pk thK) G)

@[expose] noncomputable def invL (L : List (Fin 512)) : Bool :=
  L.all fun k => decide (k.val ≤ 1) ||
    !Nat.beq ((TE.mul (.nf k) (.nf k)).pk thK) (TE.one.pk thK)

@[expose] noncomputable def c8cm (G : Nat) (k : Fin 512) : Bool :=
  Nat.beq (thK.mul G ((TE.nf k).pk thK)) (thK.mul ((TE.nf k).pk thK) G)

@[expose] noncomputable def c8inv (G : Nat) (k : Fin 512) : Bool :=
  decide (k.val ≤ 1) || !c8cm G k || !Nat.beq ((TE.mul (.nf k) (.nf k)).pk thK) (TE.one.pk thK)

theorem c8commL (G : Nat) : commL G = (List.finRange 512).filter (c8cm G) := rfl

theorem c8invL (G : Nat) : invL (commL G) = (List.finRange 512).all (c8inv G) := by
  unfold invL commL c8inv c8cm
  rw [List.all_filter]
  congr 1
  funext k
  cases decide (k.val ≤ 1) <;> simp

theorem c8countP_chunks {α : Type} (p : α → Bool) (m : Nat) : ∀ (c : List Nat) (l : List α),
    l.length ≤ m * c.length →
      (∀ s < c.length, ((l.drop (m * s)).take m).countP p = c.getD s 0) → l.countP p = c.sum
  | [], l, hl, _ => by
    rw [List.length_nil, Nat.mul_zero] at hl
    rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)]
    rfl
  | a :: c, l, hl, h => by
    rw [← List.take_append_drop m l, List.countP_append, List.sum_cons]
    congr 1
    · simpa using h 0 (by simp)
    · refine c8countP_chunks p m c (l.drop m) ?_ fun s hs => ?_
      · rw [List.length_drop]
        rw [List.length_cons, Nat.mul_add, Nat.mul_one] at hl
        omega
      · have := h (s + 1) (by simp; omega)
        have e : m * (s + 1) = m + m * s := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
        rw [e, ← List.drop_drop] at this
        simpa using this

theorem c8lv3 : Nat.beq CFSG.KD.Th687L.lv3 ((wjT 3).pk thK) = true := by quickRfl
theorem c8lv4 : Nat.beq CFSG.KD.Th687L.lv4 ((wjT 4).pk thK) = true := by quickRfl
theorem c8lv5 : Nat.beq CFSG.KD.Th687L.lv5 ((wjT 5).pk thK) = true := by quickRfl
theorem c8lv7 : Nat.beq CFSG.KD.Th687L.lv7 ((wjT 7).pk thK) = true := by quickRfl

@[expose] noncomputable def c8g1 : Nat := thK.mul CFSG.KD.Th687L.lv3 CFSG.KD.Th687L.lv4

@[expose] noncomputable def c8g12 : Nat :=
  thK.mul c8g1 (thK.mul (thK.mul CFSG.KD.Th687L.lv7 c8g1) (thK.pow CFSG.KD.Th687L.lv7 3))

theorem c8g1_eq : c8g1 = w1T.pk thK := by
  unfold c8g1
  rw [Nat.eq_of_beq_eq_true c8lv3, Nat.eq_of_beq_eq_true c8lv4]
  rfl

theorem c8g12_eq : c8g12 = w12T.pk thK := by
  unfold c8g12
  rw [c8g1_eq, Nat.eq_of_beq_eq_true c8lv7]
  rfl

@[expose] noncomputable def c8inA (s : Nat) : Bool :=
  (((List.finRange 512).drop (32 * s)).take 32).all (c8inv c8g12)

@[expose] noncomputable def c8inB (s : Nat) : Bool :=
  (((List.finRange 512).drop (32 * s)).take 32).all (c8inv c8g1)

@[expose] def c8cntL : List Nat := [2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 2]

@[expose] noncomputable def c8cnt (s : Nat) : Bool :=
  Nat.beq ((((List.finRange 512).drop (32 * s)).take 32).countP (c8cm CFSG.KD.Th687L.lv5))
    (c8cntL.getD s 0)

#kc_each c8inA 0 16

#kc_each c8inB 0 16

#kc_each c8cnt 0 16

#kc_forall_tree c8inA_all (fun s => CertificateChecks.KernelTh.Fam.c8inA s = true) 16
  CertificateChecks.KernelTh.Fam.c8inA
#kc_forall_tree c8inB_all (fun s => CertificateChecks.KernelTh.Fam.c8inB s = true) 16
  CertificateChecks.KernelTh.Fam.c8inB
#kc_forall_tree c8cnt_all (fun s => CertificateChecks.KernelTh.Fam.c8cnt s = true) 16
  CertificateChecks.KernelTh.Fam.c8cnt

theorem ok687008a : invL (commL (w12T.pk thK)) = true := by
  rw [← c8g12_eq, c8invL]
  exact CFSG.KS.ListSlices.all_chunks _ 32 16 (List.finRange 512) (by simp) c8inA_all

theorem ok687008b : invL (commL (w1T.pk thK)) = true := by
  rw [← c8g1_eq, c8invL]
  exact CFSG.KS.ListSlices.all_chunks _ 32 16 (List.finRange 512) (by simp) c8inB_all

theorem ok687008c : Nat.beq (commL ((wjT 5).pk thK)).length 8 = true := by
  rw [← Nat.eq_of_beq_eq_true c8lv5, c8commL, ← List.countP_eq_length_filter,
    c8countP_chunks (c8cm CFSG.KD.Th687L.lv5) 32 c8cntL (List.finRange 512) (by simp [c8cntL])
      fun s hs => Nat.eq_of_beq_eq_true (c8cnt_all s (by simpa [c8cntL] using hs))]
  rfl

end CertificateChecks.KernelTh.Fam

end
