
module

public import Certificates.Kernel.SchreierFam.C22241K
public import CFSG.Certificates.Kernel.BfsPairsSound
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1UBridgeBase
public import Certificates.Data.CatFactsL4U4P1U43Data

public section

namespace CertificateChecks.KernelSchreierFam.C22241

open CFSG.KC.BfsPairs CFSG.LieType.Multipliers.U43 CFSG.ComponentClassification.HarrisLit.P1
  CFSG.ComponentClassification.HarrisLit.P1.U43 CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Matrix
  CFSG.Assembly.LowTwoRank

theorem ap_tu {k j : ℕ} (hj : j < 820) :
    ap (tu k false) j = ptIndex (mv4 (matN9 k) (decode j)) := by
  rw [tu, ap_ofFn _ hj, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (ptIndex_lt_two_pow _)]
  rfl

theorem good_tu {b c₁ c₂ : ℕ} (hb : b < 820)
    (u₁ : ((matN9 c₁).map (· ^ 3))ᵀ * matN9 c₁ = 1) (d₁ : (matN9 c₁).det = 1)
    (u₂ : ((matN9 c₂).map (· ^ 3))ᵀ * matN9 c₂ = 1) (d₂ : (matN9 c₂).det = 1)
    (f₁ : ptIndex (mv4 (matN9 c₁) (decode b)) = b) (f₂ : ptIndex (mv4 (matN9 c₂) (decode b)) = b)
    (ho : onlyFix b c₁ c₂ = true) :
    Good 820 psi.range b (tu c₁ false, tu c₂ false) := by
  let A₁ : StatedSU 4 3 F9 := ⟨GeneralLinearGroup.mk'' (matN9 c₁) (by rw [d₁]; exact isUnit_one),
    Subgroup.subset_closure ⟨d₁, u₁⟩⟩
  let A₂ : StatedSU 4 3 F9 := ⟨GeneralLinearGroup.mk'' (matN9 c₂) (by rw [d₂]; exact isUnit_one),
    Subgroup.subset_closure ⟨d₂, u₂⟩⟩
  have r₁ : Rep 820 (tu c₁ false) (psi (QuotientGroup.mk A₁)) := by
    rw [psi_mk]
    exact rep_tu_false rfl
  have r₂ : Rep 820 (tu c₂ false) (psi (QuotientGroup.mk A₂)) := by
    rw [psi_mk]
    exact rep_tu_false rfl
  have e₁ : ∀ j < 820, idx 820 (psi (QuotientGroup.mk A₁)) j =
      ptIndex (mv4 (matN9 c₁) (decode j)) := fun j hj => (r₁ j hj).symm.trans (ap_tu hj)
  have e₂ : ∀ j < 820, idx 820 (psi (QuotientGroup.mk A₂)) j =
      ptIndex (mv4 (matN9 c₂) (decode j)) := fun j hj => (r₂ j hj).symm.trans (ap_tu hj)
  have m₁ : psi (QuotientGroup.mk A₁) ∈ psi.range := MonoidHom.mem_range.2 ⟨_, rfl⟩
  have m₂ : psi (QuotientGroup.mk A₂) ∈ psi.range := MonoidHom.mem_range.2 ⟨_, rfl⟩
  have i₁ : idx 820 (psi (QuotientGroup.mk A₁)) b = b := by rw [e₁ b hb, f₁]
  have i₂ : idx 820 (psi (QuotientGroup.mk A₂)) b = b := by rw [e₂ b hb, f₂]
  unfold Good
  dsimp only
  refine ⟨hb, _, m₁, _, m₂, r₁, r₂, i₁, i₂, ?_⟩
  intro j hj h₁ h₂
  rw [e₁ j hj] at h₁
  rw [e₂ j hj] at h₂
  have h := List.all_eq_true.1 ho j (List.mem_range.2 hj)
  simpa [h₁, h₂] using h

theorem stepU_eq : ∀ l < uPg.size, ∀ p < 820, stepU l p = ap uPg[l]! p := by
  intro l hl p hp
  have hl2 : l < 2 := hl
  interval_cases l
  · rw [uPg_zero, toTable, ap_ofFn _ hp, stepU, if_pos rfl]
  · rw [uPg_one, toTable, ap_ofFn _ hp, stepU, if_neg (by norm_num)]

theorem bases_good : ∀ b ∈ u43Bases, Good 820 psi.range b.1 b.2 := by
  intro b hb
  simp only [u43Bases, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact good_tu (by norm_num) unitary1 det1 unitary2 det2 fixes.1 fixes.2.1 only0
  · exact good_tu (by norm_num) unitary3 det3 unitary4 det4 fixes.2.2.1 fixes.2.2.2 only4

theorem centTriv : centTrivOK 820 uSift u43CentTriv = true := by
  rw [u43CentTriv_def]
  exact centTrivOK_bfsPairs u43_groupData stepU_eq bases_good reach

end CertificateChecks.KernelSchreierFam.C22241
