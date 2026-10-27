module

public import Certificates.Kernel.OmegaEight.Roots127K
public import Certificates.Kernel.OmegaEight.Bridge3009
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native


private theorem rep_AP {j : ℕ} (hj : j < 10) : Rep 360 (unpack 360 9 (AP.S j)) (gen j) := by
  rw [← gen_get hj]
  exact rep_gen hj

private theorem rep_pc {p q : ℕ} {g h : Equiv.Perm (Fin 360)} (hp : cn p = true)
    (hq : cn q = true) (rp : Rep 360 (unpack 360 9 p) g) (rq : Rep 360 (unpack 360 9 q) h) :
    Rep 360 (unpack 360 9 (pc p q)) (g * h) := by
  rw [← compA_pc hp hq]
  exact rep_compA rp rq

theorem rels127 : gen 8 * (gen 8 * gen 8) = 1 ∧ gen 9 * gen 9 = 1 ∧
    gen 9 * gen 8 * gen 9 = gen 8 * gen 8 := by
  have hC := kStrC
  simp only [bAnd_iff] at hC
  have hc : ∀ j < 10, cn (AP.S j) = true := allN_spec hC.1
  have c8 : cn (AP.S 8) = true := hc 8 (by norm_num)
  have c9 : cn (AP.S 9) = true := hc 9 (by norm_num)
  have r8 := rep_AP (j := 8) (by norm_num)
  have r9 := rep_AP (j := 9) (by norm_num)
  have rid : Rep 360 (unpack 360 9 pid) 1 := by
    rw [← idA_eq]
    exact rep_idA
  have hR := kRel127
  simp only [bAnd_iff] at hR
  obtain ⟨e1, e2, e3⟩ := hR
  have q1 := rep_pc c8 (cn_pc c8 c8) r8 (rep_pc c8 c8 r8 r8)
  have q2 := rep_pc c9 c9 r9 r9
  have q3 := rep_pc (cn_pc c9 c8) c9 (rep_pc c9 c8 r9 r8) r9
  rw [Nat.eq_of_beq_eq_true e1] at q1
  rw [Nat.eq_of_beq_eq_true e2] at q2
  rw [Nat.eq_of_beq_eq_true e3] at q3
  exact ⟨q1.unique rid, q2.unique rid, q3.unique (rep_pc c8 c8 r8 r8)⟩

theorem rho_not_mem127 : gen 8 ∉ omegaT ∧ gen 8 * gen 8 ∉ omegaT := by
  have h0 : ((gen 8 (0 : Fin 360) : Fin 360) : ℕ) = 120 := by rw [gen8_val]; rfl
  have hz : ((0 : Fin 360) : ℕ) < 120 := by simp
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := (omegaT_le_stab0 h (0 : Fin 360)).1 hz
    rw [h0] at this
    omega
  · have h1 : (((gen 8 * gen 8) (0 : Fin 360) : Fin 360) : ℕ) = 240 := by
      rw [Equiv.Perm.mul_apply, gen8_val, h0]
    have := (omegaT_le_stab0 h (0 : Fin 360)).1 hz
    rw [h1] at this
    omega

end CertificateChecks.KernelO8

end
