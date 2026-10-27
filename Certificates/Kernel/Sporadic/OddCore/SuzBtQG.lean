
module

public import Certificates.Kernel.Sporadic.OddCore.SuzBtTG
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EV
public import CFSG.Sporadic.SuzRecog.C1ModelCent
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.HeFixKFix

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzBtQG

open CFSG.KC.Enum CFSG.KS CFSG.KS.BTup CertificateChecks.KernelSpor
open CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.C1Model
open CFSG.Sporadic.SuzRecog.SuzL34Cert CertificateChecks.KernelSpor.SuzBtTG

theorem kC0 : allN 16 (fun k => allN 16 (fun l => allN 3 (fun t =>
    Nat.beq (pg 11 (mask 11) (SuzC1EV.T (SuzC1EC.getD k 0))
      (pg 11 (mask 11) (SuzC1EV.T (SuzC1EC.getD l 0)) (pg 11 (mask 11) SuzBtT0.B t)))
      (pg 11 (mask 11) (SuzC1EV.T (SuzC1EC.getD l 0))
        (pg 11 (mask 11) (SuzC1EV.T (SuzC1EC.getD k 0)) (pg 11 (mask 11) SuzBtT0.B t)))))) =
    true := by quickRfl

theorem kC0I : allN 16 (fun k => allN 3 (fun t =>
    Nat.beq (pg 11 (mask 11) (SuzC1EV.T (SuzC1EC.getD k 0))
      (pg 11 (mask 11) (SuzC1EV.T (SuzC1EC.getD k 0)) (pg 11 (mask 11) SuzBtT0.B t)))
      (pg 11 (mask 11) SuzBtT0.B t))) = true := by quickRfl

theorem C0_le_invE : C0 ≤ invE 1 := fun _ hg => (mem_V0_iff.1 (C0_le_V0 hg)).2

theorem pk_C0 {x : Equiv.Perm (Fin 1782)} (hx : x ∈ C0) : ∃ k < 16, ∀ p : Fin 1782,
    pg 11 (mask 11) (SuzC1EV.T (SuzC1EC.getD k 0)) p = x p := by
  obtain ⟨k, hk, hrep⟩ := enumerates_C0.exists_pos hx
  rw [cent_c0Tabs] at hk
  refine ⟨k, hk, fun p => ?_⟩
  rw [← CFSG.KC.HeFixK.unpack_getElem! p.2, ← SuzC1EV.c0Tabs_get hk]
  exact hrep.2 p

theorem C0_comm {x y : Equiv.Perm (Fin 1782)} (hx : x ∈ C0) (hy : y ∈ C0) : x * y = y * x := by
  obtain ⟨k, hk, hxk⟩ := pk_C0 hx
  obtain ⟨l, hl, hyl⟩ := pk_C0 hy
  refine invE1_ext (Subgroup.mul_mem _ (C0_le_invE hx) (C0_le_invE hy))
    (Subgroup.mul_mem _ (C0_le_invE hy) (C0_le_invE hx)) fun t => Fin.ext ?_
  have h := Nat.beq_eq.mp (CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1
    (CFSG.KS.Raw.Orb.allN_iff.1 kC0 k hk) l hl) t t.2)
  rw [hbT t, hyl, hxk, hxk, hyl] at h
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  exact h

theorem C0_sq {x : Equiv.Perm (Fin 1782)} (hx : x ∈ C0) : x * x = 1 := by
  obtain ⟨k, hk, hxk⟩ := pk_C0 hx
  refine invE1_eq_one (Subgroup.mul_mem _ (C0_le_invE hx) (C0_le_invE hx)) fun t => Fin.ext ?_
  have h := Nat.beq_eq.mp (CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 kC0I k hk) t t.2)
  rw [hbT t, hxk, hxk] at h
  rw [Equiv.Perm.mul_apply]
  exact h

theorem Z_le_C0 : Subgroup.centralizer (T0 : Set (Equiv.Perm (Fin 1782))) ⊓ T0 ≤ C0 := by
  intro x hx
  obtain ⟨hc, hT⟩ := Subgroup.mem_inf.1 hx
  unfold C0 CT0
  exact Subgroup.mem_inf.2 ⟨T0_le_centralizer_w0 hT, Subgroup.mem_inf.2 ⟨hc, T0_le_invE hT⟩⟩

theorem f7Prop : F7Prop := by
  unfold F7Prop
  dsimp only
  rw [tabSubgroup_t0Tabs, tabSubgroup_c0Tabs, tabSubgroup_ct0Tabs]
  exact ⟨card_C0, fun x hx y hy => C0_comm hx hy, fun x hx => C0_sq hx, Z_le_C0, card_CT0⟩

end CertificateChecks.KernelSpor.SuzBtQG

end
