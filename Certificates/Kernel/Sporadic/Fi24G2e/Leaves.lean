module

public import Certificates.Kernel.Sporadic.Fi24G2e.LData
public import CFSG.Certificates.Kernel.Spor.Fi24G2eSound
import Certificates.Kernel.Sporadic.Fi24G2e.LT0
import Certificates.Kernel.Sporadic.Fi24G2e.LT1

public section

namespace CertificateChecks.KernelFi24G2e

open CFSG.KC.Fi24FixK CFSG.KC.Fi24G2e CFSG.KC.Fi24G2eS CFSG.KD.Fi24G2e

theorem l0_all : ∀ j < 6, permLOK FLC0 (brayWalk CFSG.KD.Fi24Fix.TG LWC0 (LWL0 j) (LEN0 j)
    (Nat.beq (LON0 j) 1)) (TB0 j) 504 = true := LT0.L.all

theorem o0_all : ∀ t < 24, Nat.beq (brayWalk CFSG.KD.Fi24Fix.TG LWC0 (LWL0 (t / 4))
    (LEN0 (t / 4)) (Nat.beq (LON0 (t / 4)) 1) (OWN0.getD (t % 4) 0)) (OWV0.getD t 0) = true :=
  LT0.O.all

theorem i0_all : ∀ k < 21, invLOK (TB0 k) (TI0 k) 504 = true := LT0.I.all

theorem n0_all : ∀ t < 15, cmLOK (TB0 (NODE.getD (2 * t) 0)) (TI0 (NODE.getD (2 * t) 0))
    (TB0 (NODE.getD (2 * t + 1) 0)) (TI0 (NODE.getD (2 * t + 1) 0)) (TB0 (t + 6)) 504 = true :=
  LT0.N.all

theorem l1_all : ∀ j < 6, permLOK FLC1 (brayWalk CFSG.KD.Fi24Fix.TG LWC1 (LWL1 j) (LEN1 j)
    (Nat.beq (LON1 j) 1)) (TB1 j) 696 = true := LT1.L.all

theorem o1_all : ∀ t < 18, Nat.beq (brayWalk CFSG.KD.Fi24Fix.TG LWC1 (LWL1 (t / 3))
    (LEN1 (t / 3)) (Nat.beq (LON1 (t / 3)) 1) (OWN1.getD (t % 3) 0)) (OWV1.getD t 0) = true :=
  LT1.O.all

theorem i1_all : ∀ k < 21, invLOK (TB1 k) (TI1 k) 696 = true := LT1.I.all

theorem n1_all : ∀ t < 15, cmLOK (TB1 (NODE.getD (2 * t) 0)) (TI1 (NODE.getD (2 * t) 0))
    (TB1 (NODE.getD (2 * t + 1) 0)) (TI1 (NODE.getD (2 * t + 1) 0)) (TB1 (t + 6)) 696 = true :=
  LT1.N.all

theorem own_vals : OWN0 = [37886, 22978, 22975, 22973] ∧ OWN1 = [37886, 22978, 22975] ∧
    (∀ t < 24, OWV0.getD t 0 ∈ OWN0) ∧ (∀ t < 18, OWV1.getD t 0 ∈ OWN1) := by decide +kernel

theorem leaves_W2B :
    (∀ j < 6, ∀ i < 504, TB0 j i < 504 ∧ walk CFSG.KD.Fi24Fix.TG
      (brayWord CFSG.KD.Fi24G2d.W2B (LWL0 j) (LEN0 j) (Nat.beq (LON0 j) 1)) (CFSG.KD.Fi24G2d.F2B i) =
        CFSG.KD.Fi24G2d.F2B (TB0 j i)) ∧
    (∀ t < 24, walk CFSG.KD.Fi24Fix.TG (brayWord CFSG.KD.Fi24G2d.W2B (LWL0 (t / 4)) (LEN0 (t / 4))
      (Nat.beq (LON0 (t / 4)) 1)) (OWN0.getD (t % 4) 0) = OWV0.getD t 0) ∧
    (∀ k < 21, ∀ i < 504, TI0 k i < 504 ∧ TB0 k (TI0 k i) = i) ∧
    (∀ t < 15, ∀ i < 504, TB0 (t + 6) i = TI0 (NODE.getD (2 * t + 1) 0) (TI0 (NODE.getD (2 * t) 0)
      (TB0 (NODE.getD (2 * t + 1) 0) (TB0 (NODE.getD (2 * t) 0) i)))) ∧
    ((Finset.range 504).filter fun i => TB0 20 i = i).card = 4 := by
  refine ⟨fun j hj i hi => ?_, fun t ht => ?_, fun k hk => invLOK_spec (i0_all k hk) (by omega),
    fun t ht => cmLOK_spec (n0_all t ht) (by omega), ?_⟩
  · have h := permLOK_spec (l0_all j hj) (by omega) i hi
    rw [brayWalk_eq] at h
    exact h
  · have h := Nat.eq_of_beq_eq_true (o0_all t ht)
    rw [brayWalk_eq] at h
    exact h
  · rw [← cntId_eq _ (by omega)]
    exact Nat.eq_of_beq_eq_true CFSG.KD.Fi24G2e.LT0.cnt

theorem leaves_W2D :
    (∀ j < 6, ∀ i < 696, TB1 j i < 696 ∧ walk CFSG.KD.Fi24Fix.TG
      (brayWord CFSG.KD.Fi24G2d.W2D (LWL1 j) (LEN1 j) (Nat.beq (LON1 j) 1)) (CFSG.KD.Fi24G2d.F2D i) =
        CFSG.KD.Fi24G2d.F2D (TB1 j i)) ∧
    (∀ t < 18, walk CFSG.KD.Fi24Fix.TG (brayWord CFSG.KD.Fi24G2d.W2D (LWL1 (t / 3)) (LEN1 (t / 3))
      (Nat.beq (LON1 (t / 3)) 1)) (OWN1.getD (t % 3) 0) = OWV1.getD t 0) ∧
    (∀ k < 21, ∀ i < 696, TI1 k i < 696 ∧ TB1 k (TI1 k i) = i) ∧
    (∀ t < 15, ∀ i < 696, TB1 (t + 6) i = TI1 (NODE.getD (2 * t + 1) 0) (TI1 (NODE.getD (2 * t) 0)
      (TB1 (NODE.getD (2 * t + 1) 0) (TB1 (NODE.getD (2 * t) 0) i)))) ∧
    ((Finset.range 696).filter fun i => TB1 20 i = i).card = 8 := by
  refine ⟨fun j hj i hi => ?_, fun t ht => ?_, fun k hk => invLOK_spec (i1_all k hk) (by omega),
    fun t ht => cmLOK_spec (n1_all t ht) (by omega), ?_⟩
  · have h := permLOK_spec (l1_all j hj) (by omega) i hi
    rw [brayWalk_eq] at h
    exact h
  · have h := Nat.eq_of_beq_eq_true (o1_all t ht)
    rw [brayWalk_eq] at h
    exact h
  · rw [← cntId_eq _ (by omega)]
    exact Nat.eq_of_beq_eq_true CFSG.KD.Fi24G2e.LT1.cnt

end CertificateChecks.KernelFi24G2e

end
