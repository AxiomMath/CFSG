module

public import Certificates.Kernel.UnitarySix.Sec3.Elt3601
public import Certificates.Kernel.UnitarySix.Sec3.Sound.F3601
public import Certificates.Kernel.UnitarySix.Sec3.C3601P

public section

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3

theorem zS_k' : ∀ x ∈ chA2.grp, ∃ a, Rep 693 a x ∧ zSAt a = true := by
  intro x hx
  obtain ⟨L, hL, hR, hf⟩ :=
    chA2_K.forall_lazy' tabs_k (by unfold ChainData.GensOK; decide) (by decide) kZS x hx
  unfold zSL at hf
  rw [strictB_eq] at hf
  exact ⟨_, hR, (zS_of' (prodL_canon hL)).trans hf⟩

theorem a2_k' : ∀ x ∈ chA2.grp, ∃ a, Rep 693 a x ∧ a2At a = true := by
  intro x hx
  obtain ⟨L, hL, hR, hf⟩ :=
    chA2_K.forall_lazy' tabs_k (by unfold ChainData.GensOK; decide) (by decide) kA2 x hx
  unfold a2L at hf
  rw [strictB_eq] at hf
  exact ⟨_, hR, (a2_of' (prodL_canon hL)).trans hf⟩

theorem zA3_k' : ∀ x ∈ chA3.grp, ∃ a, Rep 693 a x ∧ zA3At a = true := by
  intro x hx
  obtain ⟨L, hL, hR, hf⟩ :=
    chA3_K.forall_lazy' tabs_k (by unfold ChainData.GensOK; decide) (by decide) kZA3 x hx
  exact ⟨_, hR, (zA3_L' hL).trans hf⟩

theorem a1_k' : ∀ x ∈ chA1.grp, ∃ a, Rep 693 a x ∧ a1At a = true := by
  intro x hx
  obtain ⟨L, hL, hR, hf⟩ :=
    chA1_K.forall_lazy' tabs_k (by unfold ChainData.GensOK; decide) (by decide) kA1 x hx
  unfold a1L at hf
  rw [strictB_eq] at hf
  exact ⟨_, hR, (a1_of' (prodL_canon hL)).trans hf⟩

theorem a4_k' : ∀ x ∈ chA4.grp, ∃ a, Rep 693 a x ∧ a4At a = true := by
  intro x hx
  obtain ⟨L, -, hR, hf⟩ :=
    chA4_K.forall_lazy' tabs_k (by unfold ChainData.GensOK; decide) (by decide) kA4_parts.1 x hx
  unfold a4L at hf
  rw [strictB_eq] at hf
  exact ⟨_, hR, a4_of' rfl rfl hf⟩

theorem a4Pair_k' : ∀ x ∈ chA4.grp, ∀ y ∈ chX1.grp, ∃ b a, Rep 693 b y ∧ Rep 693 a x ∧
    a4PairAt b a = true := by
  intro x hx y hy
  obtain ⟨L, -, hR, hf⟩ :=
    chA4_K.forall_lazy' tabs_k (by unfold ChainData.GensOK; decide) (by decide) kA4_parts.2 x hx
  unfold a4PairL at hf
  obtain ⟨L', -, hR', hf'⟩ :=
    chX1_K.forall_lazy' tabs_k (by unfold ChainData.GensOK; decide) (by decide) hf y hy
  rw [strictB_eq, strictB_eq] at hf'
  exact ⟨_, _, hR', hR, a4Pair_of' hf'⟩

theorem z2s_k' : ∀ x ∈ chZ2S.grp, ∃ a, Rep 693 a x ∧ z2sAt a = true := by
  intro x hx
  obtain ⟨L, hL, hR, hf⟩ :=
    chZ2S_K.forall_lazy' tabs_k (by unfold ChainData.GensOK; decide) (by decide) kZ2S_parts.1 x hx
  unfold z2sL at hf
  rw [strictB_eq] at hf
  exact ⟨_, hR, (z2s_of' (prodL_canon hL)).trans hf⟩

theorem z2sPair_k' : ∀ x ∈ chZ2S.grp, ∀ y ∈ chX1.grp, ∃ b a, Rep 693 b y ∧ Rep 693 a x ∧
    z2sPairAt b a = true := by
  intro x hx y hy
  obtain ⟨L, -, hR, hf⟩ :=
    chZ2S_K.forall_lazy' tabs_k (by unfold ChainData.GensOK; decide) (by decide) kZ2S_parts.2 x hx
  unfold z2sPairL at hf
  obtain ⟨L', -, hR', hf'⟩ :=
    chX1_K.forall_lazy' tabs_k (by unfold ChainData.GensOK; decide) (by decide) hf y hy
  rw [strictB_eq, strictB_eq] at hf'
  exact ⟨_, _, hR', hR, z2sPair_of' hf'⟩

theorem p2_k' : ∀ x ∈ chK1.grp, ∃ a, Rep 693 a x ∧ p2At a = true := by
  intro x hx
  obtain ⟨L, hL, hR, hf⟩ :=
    chK1_K.forall_lazy' tabs_k (by unfold ChainData.GensOK; decide) (by decide) kP2 x hx
  exact ⟨_, hR, p2_L' hL hf⟩

end CertificateChecks.KernelU6.Sec3
