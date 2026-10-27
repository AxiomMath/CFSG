module

public import Certificates.Kernel.Multipliers.Sz8Base

set_option exponentiation.threshold 2048
set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelSz8

open CFSG.Certificates.LabZ CertificateChecks.KernelMult

@[expose] def ρ0 : List ℤ :=
  [0, 0, -1, 0, 0, 0, 0, 0, 5]

theorem r0 : zprod gg 9 (fun d => ρ0.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.Sz8C.sY0 (by decide)

@[expose] def ρ1 : List ℤ :=
  [1, 2, 0, -1, 0, 0, 0, -1, 5]

theorem r1 : zprod gg 9 (fun d => ρ1.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.Sz8C.sY1 (by decide)

@[expose] def ρ2 : List ℤ :=
  [1, -1, -1, 1, 0, 0, -1, 0, -5]

theorem r2 : zprod gg 9 (fun d => ρ2.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.Sz8C.sY2 (by decide)

@[expose] def ρ3 : List ℤ :=
  [7, 7, 0, -2, 0, 0, 0, 0, 0]

theorem r3 : zprod gg 9 (fun d => ρ3.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.Sz8C.sY3 (by decide)

@[expose] def ρ4 : List ℤ :=
  [21, 7, 0, 0, 0, -2, 0, 0, 0]

theorem r4 : zprod gg 9 (fun d => ρ4.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.Sz8C.sY4 (by decide)

@[expose] def ρ5 : List ℤ :=
  [20, 10, 0, 0, -2, 0, 0, 0, 0]

theorem r5 : zprod gg 9 (fun d => ρ5.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.Sz8C.sY5 (by decide)

@[expose] def ρ6 : List ℤ :=
  [14, 0, 7, 2, -2, -2, 0, 0, 5]

theorem r6 : zprod gg 9 (fun d => ρ6.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.Sz8C.sY6 (by decide)

@[expose] def ρ7 : List ℤ :=
  [70, 35, -57, 0, 8, 0, 0, 0, -15]

theorem r7 : zprod gg 9 (fun d => ρ7.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.Sz8C.sY7 (by decide)

@[expose] def rhos : List (List ℤ) :=
  [ρ0, ρ1, ρ2, ρ3, ρ4, ρ5, ρ6, ρ7]

theorem rhos_one : ∀ ρ ∈ rhos, zprod gg 9 (fun d => ρ.getD d 0) = 1 := by
  intro ρ hρ
  simp only [rhos, List.mem_cons, List.not_mem_nil, or_false] at hρ
  rcases hρ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact r0
  · exact r1
  · exact r2
  · exact r3
  · exact r4
  · exact r5
  · exact r6
  · exact r7

@[expose] def c0 : List ℤ :=
  [-6, 0, -2, 6, -7, -3, 7, 1]

@[expose] def τ0 : List ℤ :=
  [1, 0, 0, 0, 0, 0, 2, 0, 0]

theorem t0 : zprod gg 9 (fun d => τ0.getD d 0) = 1 :=
  zprod_target gg_comm 9 c0 rhos rhos_one _ (by decide)

@[expose] def c1 : List ℤ :=
  [8, -4, 0, -5, 7, 3, -7, -1]

@[expose] def τ1 : List ℤ :=
  [0, 1, 0, 0, 0, 0, 0, 4, 0]

theorem t1 : zprod gg 9 (fun d => τ1.getD d 0) = 1 :=
  zprod_target gg_comm 9 c1 rhos rhos_one _ (by decide)

@[expose] def c2 : List ℤ :=
  [-4, -5, -5, 7, -7, -3, 7, 1]

@[expose] def τ2 : List ℤ :=
  [0, 0, 1, 0, 0, 0, 5, 5, 0]

theorem t2 : zprod gg 9 (fun d => τ2.getD d 0) = 1 :=
  zprod_target gg_comm 9 c2 rhos rhos_one _ (by decide)

@[expose] def c3 : List ℤ :=
  [7, -14, -7, 3, 0, 0, 0, 0]

@[expose] def τ3 : List ℤ :=
  [0, 0, 0, 1, 0, 0, 7, 14, 0]

theorem t3 : zprod gg 9 (fun d => τ3.getD d 0) = 1 :=
  zprod_target gg_comm 9 c3 rhos rhos_one _ (by decide)

@[expose] def c4 : List ℤ :=
  [-40, -40, -40, 70, -70, -31, 70, 10]

@[expose] def τ4 : List ℤ :=
  [0, 0, 0, 0, 2, 0, 40, 40, 0]

theorem t4 : zprod gg 9 (fun d => τ4.getD d 0) = 1 :=
  zprod_target gg_comm 9 c4 rhos rhos_one _ (by decide)

@[expose] def c5 : List ℤ :=
  [-61, -28, -42, 76, -84, -35, 83, 12]

@[expose] def τ5 : List ℤ :=
  [0, 0, 0, 0, 0, 2, 42, 28, 0]

theorem t5 : zprod gg 9 (fun d => τ5.getD d 0) = 1 :=
  zprod_target gg_comm 9 c5 rhos rhos_one _ (by decide)

@[expose] def taus : List (List ℤ) :=
  [τ0, τ1, τ2, τ3, τ4, τ5]

theorem tau_shape : ∀ k < 6, ∀ d < 9, (taus.getD k []).getD d 0 =
    (if d = k then (if 4 ≤ k then 2 else 1) else 0) ∨ (6 ≤ d ∧ d < 8) := by
  decide

theorem tau_eq : ∀ k < 6, zprod gg 9 (fun d => (taus.getD k []).getD d 0) = 1 := by
  intro k hk
  interval_cases k
  exacts [t0, t1, t2, t3, t4, t5]

theorem tau_pow {k : ℕ} (hk : k < 6) :
    zprod gg 9 (fun d => (taus.getD k []).getD d 0) = gg k ^ ((taus.getD k []).getD k 0) := by
  refine zprod_eq_pow (by omega) fun d hd hdk => ?_
  rcases tau_shape k hk d hd with h | h
  · simp only [h, hdk, ↓reduceIte, zpow_zero]
  · rw [show d = 6 + (d - 6) by omega, gg_cover (by omega), one_zpow]

theorem z_eq_one {k : ℕ} (hk : k < 4) : z k = 1 := by
  have h := (tau_pow (k := k) (by omega)).symm.trans (tau_eq k (by omega))
  rcases tau_shape k (by omega) k (by omega) with e | e
  · rw [e] at h
    simp only [↓reduceIte, show ¬ 4 ≤ k by omega, zpow_one] at h
    rw [← gg_rel (by omega)]
    exact h
  · omega

theorem z_sq {k : ℕ} (hk4 : 4 ≤ k) (hk : k < 6) : z k ^ 2 = 1 := by
  have h := (tau_pow (k := k) hk).symm.trans (tau_eq k hk)
  rcases tau_shape k hk k (by omega) with e | e
  · rw [e] at h
    simp only [↓reduceIte, hk4] at h
    rw [← gg_rel hk]
    exact_mod_cast h
  · omega

end CertificateChecks.KernelSz8

end
