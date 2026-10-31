
module

public import Certificates.Kernel.Ly3085.SqueezeBase

@[expose] public section

noncomputable section

namespace CertificateChecks.KernelLy.Omega

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier CFSG.Sporadic.LySchreier.Native
open CFSG.Sporadic.Ly.Omega
open MulAction

def subSizes : Fin 5 → ℕ := ![1, 19530, 968750, 2034375, 5812500]

set_option maxRecDepth 10000 in
theorem subSizes_blocks : ∀ S : Finset (Fin 5), (0 : Fin 5) ∈ S →
    (∑ i ∈ S, subSizes i) ∣ 8835156 → S = {0} ∨ S = Finset.univ := by
  decide

section

variable [LySeed]

def omE : orbit J opE := ⟨opE, mem_orbit_self _⟩

theorem mem_subO_iff (i : Fin 5) (y : LyOperator) : y ∈ subO i ↔ y ∈ orbit lyH (repOp i.val) := by
  unfold subO
  rw [Set.Finite.mem_toFinset]

theorem smul_mem_subO {h : J} (hh : h ∈ lyH) {i : Fin 5} {y : LyOperator} (hy : y ∈ subO i) :
    h • y ∈ subO i := by
  rw [mem_subO_iff] at hy ⊢
  obtain ⟨⟨g, hg⟩, rfl⟩ := hy
  refine ⟨⟨h * g, lyH.mul_mem hh hg⟩, ?_⟩
  change (h * g) • repOp i.val = h • (g • repOp i.val)
  exact mul_smul h g _

end

end CertificateChecks.KernelLy.Omega

end
