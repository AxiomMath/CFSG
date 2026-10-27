module

public import Certificates.Kernel.Fi22F.PairWalks
public import Certificates.Kernel.Fi22F.Words
public import Certificates.Kernel.Fi22.Bray

public section

namespace CertificateChecks.KernelFi22F

open CFSG.KC CFSG.KC.LceS CFSG.Certificates CFSG.Certificates.LCE CFSG.KC.Fi22F.Walks
  CFSG.Sporadic.Presentation.Fi22Exact CertificateChecks.KernelFi22

theorem pwOK_spec {blk : ℕ → ℕ} {nf : ℕ} {ps : List (Conj × Conj)} {Rs : List ℕ} {k₀ : ℕ}
    (h : pwOK blk nf ps Rs k₀ = true) : ∀ k (hk : k < ps.length),
      lt6 (pairWord ps[k]) = true ∧ (pairWord ps[k]).length < 1024 ∧
        CFSG.KC.HOrb.walkTo blk nf (entW (pairWord ps[k])) 0 (Rs.getD (k₀ + k) 0) 0 = true := by
  induction ps generalizing k₀ with
  | nil => intro k hk; cases hk
  | cons p ps ih =>
    have h' : andB (andB (andB (lt6 (pairWord p)) (Nat.blt (pairWord p).length 1024))
        (CFSG.KC.HOrb.walkTo blk nf (entW (pairWord p)) 0 (Rs.getD k₀ 0) 0))
        (pwOK blk nf ps Rs (Nat.succ k₀)) = true := h
    obtain ⟨h1, h2⟩ := (andB_eq' _ _).1 h'
    obtain ⟨h3, h4⟩ := (andB_eq' _ _).1 h1
    obtain ⟨h5, h6⟩ := (andB_eq' _ _).1 h3
    intro k hk
    cases k with
    | zero => exact ⟨h5, Nat.le_of_ble_eq_true h6, by simpa using h4⟩
    | succ k =>
      have := ih h2 k (by simpa using hk)
      rw [show k₀ + (k + 1) = Nat.succ k₀ + k by omega]
      exact this

theorem pairs_cent : ∀ pp ∈ allPairs,
    ((pairWord pp).map (letV tg)).prod ∈ Subgroup.centralizer {tg 0} := by
  obtain ⟨rep, h0, hw⟩ := bray_walk
  intro pp hpp
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hpp
  obtain ⟨h6, hlen, hwk⟩ := pwOK_spec pw_ok k hk
  have := hw _ 0 _ 0 (by norm_num) hwk
  rw [h0, one_mul, inv_one, mul_one, bval_entW tg _ hlen (fun c hc => by
    have := lt6_spec h6 c hc
    omega)] at this
  exact a_cent this

end CertificateChecks.KernelFi22F

end
