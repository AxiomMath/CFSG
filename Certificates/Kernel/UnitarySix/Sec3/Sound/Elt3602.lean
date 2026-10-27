module

public import Certificates.Kernel.UnitarySix.Sec3.Elt3602
public import CFSG.Certificates.Kernel.U6Sec3ChainSound
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.UnitarySix.Sec3.E3602

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native

theorem chA2s0_k' : chA2s0.ok = true ∧ chA2s0.order = 512 :=
  ⟨chA2s0_K.facts'.1, chA2s0_K.facts'.2.1.trans (by decide +kernel)⟩
theorem chA2s1_k' : chA2s1.ok = true ∧ chA2s1.order = 512 :=
  ⟨chA2s1_K.facts'.1, chA2s1_K.facts'.2.1.trans (by decide +kernel)⟩
theorem chA2s2_k' : chA2s2.ok = true ∧ chA2s2.order = 512 :=
  ⟨chA2s2_K.facts'.1, chA2s2_K.facts'.2.1.trans (by decide +kernel)⟩
theorem chA1s0_k' : chA1s0.ok = true ∧ chA1s0.order = 512 :=
  ⟨chA1s0_K.facts'.1, chA1s0_K.facts'.2.1.trans (by decide +kernel)⟩
theorem chA1s1_k' : chA1s1.ok = true ∧ chA1s1.order = 512 :=
  ⟨chA1s1_K.facts'.1, chA1s1_K.facts'.2.1.trans (by decide +kernel)⟩
theorem chA3s0_k' : chA3s0.ok = true ∧ chA3s0.order = 4096 :=
  ⟨chA3s0_K.facts'.1, chA3s0_K.facts'.2.1.trans (by decide +kernel)⟩
theorem chA3s1_k' : chA3s1.ok = true ∧ chA3s1.order = 4096 :=
  ⟨chA3s1_K.facts'.1, chA3s1_K.facts'.2.1.trans (by decide +kernel)⟩
theorem chA3s2_k' : chA3s2.ok = true ∧ chA3s2.order = 4096 :=
  ⟨chA3s2_K.facts'.1, chA3s2_K.facts'.2.1.trans (by decide +kernel)⟩
theorem chA3s3_k' : chA3s3.ok = true ∧ chA3s3.order = 4096 :=
  ⟨chA3s3_K.facts'.1, chA3s3_K.facts'.2.1.trans (by decide +kernel)⟩
theorem chA3s4_k' : chA3s4.ok = true ∧ chA3s4.order = 4096 :=
  ⟨chA3s4_K.facts'.1, chA3s4_K.facts'.2.1.trans (by decide +kernel)⟩

theorem a3Orb_L' {L : List ℕ} (hL : ∀ t ∈ L, canonK 693 10 (mask 10) (693 * 10) t = true) :
    a3OrbAt (unpack 693 10 (prodL 693 10 (mask 10) L)) = a3OrbL L := by
  unfold a3OrbAt a3OrbL keyA3 lvA4
  rw [prodL_get hL (i := 205) (by norm_num), prodL_get hL (i := 251) (by norm_num), memL_eq,
    strictB_eq, chA4_K.sift' (prodL_canon hL)]
  rfl

open CFSG.Monster.B.Co2 in
theorem a2Orb_k' : ∀ x ∈ chA2.grp, ∃ a, Rep 693 a x ∧ a2OrbAt a = true := by
  intro x hx
  obtain ⟨L, hL, hR, hf⟩ :=
    chA2_K.forall_lazy' tabs_k (by unfold ChainData.GensOK; decide) (by decide) kA2Orb x hx
  exact ⟨_, hR, (a2Orb_L hL).trans hf⟩

open CFSG.Monster.B.Co2 in
theorem a1Orb_k' : ∀ x ∈ chA1.grp, ∃ a, Rep 693 a x ∧ a1OrbAt a = true := by
  intro x hx
  obtain ⟨L, hL, hR, hf⟩ :=
    chA1_K.forall_lazy' tabs_k (by unfold ChainData.GensOK; decide) (by decide) kA1Orb_parts.1 x
      hx
  exact ⟨_, hR, (a1Orb_L hL).trans hf⟩

open CFSG.Monster.B.Co2 in
theorem sing_k' : ∀ x ∈ chA1.grp, ∃ a, Rep 693 a x ∧ singAt a = true := by
  intro x hx
  obtain ⟨L, hL, hR, hf⟩ :=
    chA1_K.forall_lazy' tabs_k (by unfold ChainData.GensOK; decide) (by decide) kA1Orb_parts.2 x
      hx
  exact ⟨_, hR, (sing_L hL).trans hf⟩

open CFSG.Monster.B.Co2 in
theorem a3Orb_k' : ∀ x ∈ chA3.grp, ∃ a, Rep 693 a x ∧ a3OrbAt a = true := by
  intro x hx
  obtain ⟨L, hL, hR, hf⟩ :=
    chA3_K.forall_lazy' tabs_k (by unfold ChainData.GensOK; decide) (by decide) kA3Orb x hx
  exact ⟨_, hR, (a3Orb_L' hL).trans hf⟩

end CertificateChecks.KernelU6.Sec3
