module

public import Certificates.Kernel.Multipliers.U42Base

set_option exponentiation.threshold 2048
set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelU42

open CFSG.Certificates.LabZ CertificateChecks.KernelMult

@[expose] def ρ0 : List ℤ :=
  [0, 0, -1, 0, 0, 0, 0, 9]

theorem r0 : zprod gg 8 (fun d => ρ0.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U42C.sY0 (by decide)

@[expose] def ρ1 : List ℤ :=
  [0, 0, 0, -2, 0, 0, 0, 0]

theorem r1 : zprod gg 8 (fun d => ρ1.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U42C.sY1 (by decide)

@[expose] def ρ2 : List ℤ :=
  [0, 0, 0, 0, -2, 0, 0, 0]

theorem r2 : zprod gg 8 (fun d => ρ2.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U42C.sY2 (by decide)

@[expose] def ρ3 : List ℤ :=
  [0, 0, -1, -3, 0, 0, 0, 9]

theorem r3 : zprod gg 8 (fun d => ρ3.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U42C.sY3 (by decide)

@[expose] def ρ4 : List ℤ :=
  [18, 7, -3, 0, -4, 0, -1, -9]

theorem r4 : zprod gg 8 (fun d => ρ4.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U42C.sY4 (by decide)

@[expose] def ρ5 : List ℤ :=
  [-23, -9, 4, 6, 6, -1, 0, 9]

theorem r5 : zprod gg 8 (fun d => ρ5.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U42C.sY5 (by decide)

@[expose] def ρ6 : List ℤ :=
  [22, 9, -4, 8, 8, -1, 0, -9]

theorem r6 : zprod gg 8 (fun d => ρ6.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.U42C.sY6 (by decide)

@[expose] def rhos : List (List ℤ) :=
  [ρ0, ρ1, ρ2, ρ3, ρ4, ρ5, ρ6]

theorem rhos_one : ∀ ρ ∈ rhos, zprod gg 8 (fun d => ρ.getD d 0) = 1 := by
  intro ρ hρ
  simp only [rhos, List.mem_cons, List.not_mem_nil, or_false] at hρ
  rcases hρ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact r0
  · exact r1
  · exact r2
  · exact r3
  · exact r4
  · exact r5
  · exact r6

@[expose] def c0 : List ℤ :=
  [14, 14, -7, -14, 0, -1, -1]

@[expose] def τ0 : List ℤ :=
  [1, 0, 0, 0, 0, 2, 0, 0]

theorem t0 : zprod gg 8 (fun d => τ0.getD d 0) = 1 :=
  zprod_target gg_comm 8 c0 rhos rhos_one _ (by decide)

@[expose] def c1 : List ℤ :=
  [-7, -7, 12, 6, -5, -2, 2]

@[expose] def τ1 : List ℤ :=
  [0, 1, 0, 0, 0, 0, 5, 0]

theorem t1 : zprod gg 8 (fun d => τ1.getD d 0) = 1 :=
  zprod_target gg_comm 8 c1 rhos rhos_one _ (by decide)

@[expose] def c2 : List ℤ :=
  [50, 50, -10, -52, -9, -8, -1]

@[expose] def τ2 : List ℤ :=
  [0, 0, 1, 0, 0, 9, 9, 0]

theorem t2 : zprod gg 8 (fun d => τ2.getD d 0) = 1 :=
  zprod_target gg_comm 8 c2 rhos rhos_one _ (by decide)

@[expose] def c3 : List ℤ :=
  [1, 1, 0, -1, 0, 0, 0]

@[expose] def τ3 : List ℤ :=
  [0, 0, 0, 1, 0, 0, 0, 0]

theorem t3 : zprod gg 8 (fun d => τ3.getD d 0) = 1 :=
  zprod_target gg_comm 8 c3 rhos rhos_one _ (by decide)

@[expose] def c4 : List ℤ :=
  [0, 0, -1, 0, 0, 0, 0]

@[expose] def τ4 : List ℤ :=
  [0, 0, 0, 0, 2, 0, 0, 0]

theorem t4 : zprod gg 8 (fun d => τ4.getD d 0) = 1 :=
  zprod_target gg_comm 8 c4 rhos rhos_one _ (by decide)

@[expose] def taus : List (List ℤ) :=
  [τ0, τ1, τ2, τ3, τ4]

theorem tau_shape : ∀ k < 5, ∀ d < 8, (taus.getD k []).getD d 0 =
    (if d = k then (if k = 4 then 2 else 1) else 0) ∨ (5 ≤ d ∧ d < 7) := by
  decide

theorem tau_eq : ∀ k < 5, zprod gg 8 (fun d => (taus.getD k []).getD d 0) = 1 := by
  intro k hk
  interval_cases k
  exacts [t0, t1, t2, t3, t4]

theorem tau_pow {k : ℕ} (hk : k < 5) :
    zprod gg 8 (fun d => (taus.getD k []).getD d 0) = gg k ^ ((taus.getD k []).getD k 0) := by
  refine zprod_eq_pow (by omega) fun d hd hdk => ?_
  rcases tau_shape k hk d hd with h | h
  · simp only [h, hdk, ↓reduceIte, zpow_zero]
  · rw [show d = 5 + (d - 5) by omega, gg_cover (by omega), one_zpow]

theorem z_eq_one {k : ℕ} (hk : k < 4) : z k = 1 := by
  have h := (tau_pow (k := k) (by omega)).symm.trans (tau_eq k (by omega))
  rcases tau_shape k (by omega) k (by omega) with e | e
  · rw [e] at h
    simp only [↓reduceIte, show k ≠ 4 by omega, zpow_one] at h
    rw [← gg_rel (by omega)]
    exact h
  · omega

theorem z4_sq : z 4 ^ 2 = 1 := by
  have h := (tau_pow (k := 4) (by omega)).symm.trans (tau_eq 4 (by omega))
  rcases tau_shape 4 (by omega) 4 (by omega) with e | e
  · rw [e] at h
    simp only [↓reduceIte] at h
    rw [← gg_rel (by omega)]
    exact_mod_cast h
  · omega

end CertificateChecks.KernelU42

end
