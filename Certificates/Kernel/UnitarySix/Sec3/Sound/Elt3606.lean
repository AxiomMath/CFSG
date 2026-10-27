module

public import Certificates.Kernel.UnitarySix.Sec3.Elt3606
public import CFSG.Certificates.Kernel.U6Sec3ChainSound
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.UnitarySix.Sec3.K3606

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaHAut (dTab sTab d2Tab dsTab d2sTab)
open CFSG.Monster.B.Co2 (allLt_iff)

section

variable {L : List ℕ} (hL : ∀ t ∈ L, canonK 693 10 (mask 10) (693 * 10) t = true)
include hL

theorem c11b_L' : c11bAt (unpack 693 10 (prodL 693 10 (mask 10) L)) =
    (c11RK L || strictB (prodL 693 10 (mask 10) L) sfP2) := by
  unfold c11bAt c11RejW c11RK lvP2
  rw [chP2_K.sift' (prodL_canon hL), strictB_eq, chZ2S_K.O_any]
  have hl : chZ2S.gens.length = 3 := rfl
  rw [hl]
  congr 1
  refine range_any_congr fun j hj => ?_
  have hj' := PermK.canon (chZ2S_P j (hl ▸ hj))
  congr 1
  refine allLt_congrN fun p hp => ?_
  have h2 := canon_lt hj' hp
  rw [strictB_eq, unpack_get hp, prodL_get hL h2, prodL_get hL hp,
    anyWL_eq z2sW_lt _ (ptL_lt hL hp)]

theorem k3606_L' (h : k3606L L = true) :
    c10At (unpack 693 10 (prodL 693 10 (mask 10) L)) = true ∧
      c8At (unpack 693 10 (prodL 693 10 (mask 10) L)) = true ∧
      c11bAt (unpack 693 10 (prodL 693 10 (mask 10) L)) = true := by
  unfold k3606L at h
  simp only [Bool.and_eq_true] at h
  rw [c10_L hL, c8_L hL, c11b_L' hL]
  exact ⟨h.1.1, h.1.2, h.2⟩

end

open CFSG.Monster.B.Co2 in
theorem k3606_mem' : ∀ x ∈ chK1.grp, ∃ a, Rep 693 a x ∧
    (c10At a = true ∧ c8At a = true ∧ c11bAt a = true) := by
  intro x hx
  obtain ⟨L, hL, hR, hf⟩ :=
    chK1_K.forall_lazy' tabs_k (by unfold ChainData.GensOK; decide) (by decide) k3606_loop x hx
  exact ⟨_, hR, k3606_L' hL hf⟩

open CFSG.Monster.B.Co2 in
theorem c10_k' : ∀ x ∈ chK1.grp, ∃ a, Rep 693 a x ∧ c10At a = true := fun x hx =>
  (k3606_mem' x hx).imp fun _ h => ⟨h.1, h.2.1⟩

open CFSG.Monster.B.Co2 in
theorem c8_k' : ∀ x ∈ chK1.grp, ∃ a, Rep 693 a x ∧ c8At a = true := fun x hx =>
  (k3606_mem' x hx).imp fun _ h => ⟨h.1, h.2.2.1⟩

open CFSG.Monster.B.Co2 in
theorem c11b_k' : ∀ x ∈ chK1.grp, ∃ a, Rep 693 a x ∧ c11bAt a = true := fun x hx =>
  (k3606_mem' x hx).imp fun _ h => ⟨h.1, h.2.2.2⟩

open CFSG.Monster.B.Co2 in
theorem z2sKey_k' : ∀ x ∈ chZ2S.grp, ∃ a, Rep 693 a x ∧ z2sKeyAt a = true := by
  intro x hx
  obtain ⟨L, hL, hR, hf⟩ :=
    chZ2S_K.forall_lazy' tabs_k (by unfold ChainData.GensOK; decide) (by decide) kZ2SK x hx
  exact ⟨_, hR, (z2sKey_L hL).trans hf⟩

end CertificateChecks.KernelU6.Sec3
