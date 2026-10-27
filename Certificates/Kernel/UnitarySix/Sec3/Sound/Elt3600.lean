module

public import Certificates.Kernel.UnitarySix.Sec3.C3600S
public import Certificates.Kernel.UnitarySix.Sec3.C3600N
public import Certificates.Kernel.UnitarySix.Sec3.C3600A
public import Certificates.Kernel.UnitarySix.Sec3.Sound.Glue3600

public section

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS.Raw CFSG.Monster.B.Co2
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3

theorem sInt_k' : ∀ x ∈ chS.grp, ∃ a, Rep 693 a x ∧ sIntAt a = true := by
  intro x hx
  obtain ⟨L, hL, hR, hf⟩ :=
    chS_K.forall_lazy' tabs_k (by unfold ChainData.GensOK; decide) (by decide) kSInt x hx
  exact ⟨_, hR, sInt_L' hL hf⟩

theorem t2Int_k' : ∀ x ∈ chT2.grp, ∃ a, Rep 693 a x ∧ t2IntAt a = true := by
  intro x hx
  obtain ⟨L, hL, hR, hf⟩ :=
    chT2_K.forall_lazy' tabs_k (by unfold ChainData.GensOK; decide) (by decide) kT2 x hx
  unfold t2L at hf
  rw [strictB_eq] at hf
  exact ⟨_, hR, (t2Int_of' (prodL_canon hL)).trans hf⟩

theorem t1Int_k' : ∀ x ∈ chT1.grp, ∃ a, Rep 693 a x ∧ t1IntAt a = true := by
  intro x hx
  obtain ⟨L, hL, hR, hf⟩ :=
    chT1_K.forall_lazy' tabs_k (by unfold ChainData.GensOK; decide) (by decide) kT1 x hx
  unfold t1L at hf
  rw [strictB_eq] at hf
  exact ⟨_, hR, (t1Int_of' (prodL_canon hL)).trans hf⟩

theorem ka1_k' : ∀ x ∈ chA1.grp, ∃ a, Rep 693 a x ∧ ka1At a = true := by
  intro x hx
  obtain ⟨L, hL, hR, hf⟩ :=
    chA1_K.forall_lazy' tabs_k (by unfold ChainData.GensOK; decide) (by decide) kKa1 x hx
  unfold ka1L at hf
  rw [strictB_eq] at hf
  exact ⟨_, hR, (ka1_of' (prodL_canon hL)).trans hf⟩

theorem ka2_k' : ∀ x ∈ chA2.grp, ∃ a, Rep 693 a x ∧ ka2At a = true := by
  intro x hx
  obtain ⟨L, hL, hR, hf⟩ :=
    chA2_K.forall_lazy' tabs_k (by unfold ChainData.GensOK; decide) (by decide) kKa2 x hx
  unfold ka2L at hf
  rw [strictB_eq] at hf
  exact ⟨_, hR, (ka2_of' (prodL_canon hL)).trans hf⟩

theorem norm_k' : ∀ x ∈ chK1.grp, ∃ a, Rep 693 a x ∧ normAt a = true := by
  intro x hx
  obtain ⟨L, hL, hR, hf⟩ :=
    chK1_K.forall_lazy' tabs_k (by unfold ChainData.GensOK; decide) (by decide) kNorm x hx
  exact ⟨_, hR, norm_L' hL hf⟩

end CertificateChecks.KernelU6.Sec3
