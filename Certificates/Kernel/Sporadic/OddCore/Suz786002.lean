module

public import Certificates.Data.GrSLitL34SuzStdOddLeafRootPerm
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzOuter
public import Certificates.Kernel.Sporadic.OddCore.Suz786002KS
public import Certificates.Kernel.Sporadic.OddCore.Suz26681
import CFSG.Certificates.Kernel.CentSubSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Suz786002

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.L34K CFSG.KC.L34Scan
open CFSG.KC.CentScan CFSG.KC.CentSub CertificateChecks.KernelSpor
open CFSG.KLie.CT (andB notB)
open CFSG Subgroup CFSG.Sporadic.SuzOddCore CFSG.EvenSporadicStandard.Solomon78
  CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.ComponentClassification.GrSLit.L34Sec5S

def Pt (p : Nat) (g : Equiv.Perm (Fin 42)) : Prop :=
  canonK 42 6 (mask 6) (42 * 6) p = true ∧ TabRep (unpack 42 6 p) g

theorem pt_mul {p q : Nat} {g h : Equiv.Perm (Fin 42)} (hp : Pt p g) (hq : Pt q h) :
    Pt (Suz786002.mul p q) (g * h) := by
  refine ⟨CFSG.KC.BfsPin.canonK_pcomp hp.1 hq.1, ?_⟩
  change TabRep (unpack 42 6 (pcomp 42 6 (mask 6) p q)) (g * h)
  rw [← CFSG.KC.L34KSnd.comp_unpack' hp.1 hq.1]
  exact hp.2.comp hq.2

theorem pt_one : Pt (pidn 42 6) 1 := by
  refine ⟨CFSG.KC.L34KSnd.canon_pidn hsz42, ?_⟩
  rw [← CFSG.KC.L34KSnd.idTab_unpack' hsz42]
  exact TabRep.idTab

theorem scan {i : Nat} (hi : i < SK0.cnt) :
    ptOK (pidn 42 6) RA RB (SuzSV 0) (SK0.T i) = true := by
  have hN : SK0.cnt = 1260 * 32 := by rw [SuzK0.hd_parts.1]
  refine scanSl_spec (f := ptOK (pidn 42 6) RA RB (SuzSV 0)) hN (by decide) (fun s hs => ?_) i hi
  have h1 := scAll s hs
  unfold scSl at h1
  simpa only [CFSG.KC.L34Scan.strictB_app] using h1

section Perms


theorem pt_dp {j : Nat} (hj : j < 5) : Pt (SuzDP j) (dperm j) := by
  refine ⟨(SuzOut.dp_get hj).2, ?_⟩
  rw [← (SuzOut.dp_get hj).1]
  exact tabRep_dperm hj

theorem dperm_mem {j : Nat} (hj : j < 5) : dperm j ∈ suzD :=
  Subgroup.subset_closure ⟨j, hj, rfl⟩

theorem x0_eq : suzRootPerm 0 = dperm 4 := by
  simp [suzRootPerm, suzRootWords]

theorem x1_eq : suzRootPerm 1 = dperm 3 * (dperm 4 * dperm 3) := by
  simp [suzRootPerm, suzRootWords]

theorem d6_eq : repPerm 6 = dperm 4 * dperm 4 := by
  simp [repPerm, classWords]

theorem pt_RA : Pt RA (suzRootPerm 0) := by
  rw [x0_eq]
  exact pt_dp (by decide)

theorem pt_RB : Pt RB (suzRootPerm 1) := by
  rw [x1_eq]
  exact pt_mul (pt_dp (by decide)) (pt_mul (pt_dp (by decide)) (pt_dp (by decide)))

theorem pt_DL : Pt DL (repPerm 6) := by
  rw [d6_eq]
  exact pt_mul (pt_dp (by decide)) (pt_dp (by decide))

theorem pt_RP {j : Nat} (hj : j < 2) : Pt (RP j) (suzRootPerm j) := by
  interval_cases j
  · exact pt_RA
  · exact pt_RB

theorem root_mem (j : Nat) (hj : j < 2) : suzRootPerm j ∈ suzD := by
  interval_cases j
  · rw [x0_eq]
    exact dperm_mem (by decide)
  · rw [x1_eq]
    exact suzD.mul_mem (dperm_mem (by decide))
      (suzD.mul_mem (dperm_mem (by decide)) (dperm_mem (by decide)))

theorem pt_ZP {k : Nat} (hk : k < 4) : ∃ z ∈ suzD, Pt (ZP k) z := by
  have ha := root_mem 0 (by decide)
  have hb := root_mem 1 (by decide)
  interval_cases k
  · exact ⟨1, suzD.one_mem, pt_one⟩
  · exact ⟨_, suzD.mul_mem ha ha, pt_mul pt_RA pt_RA⟩
  · exact ⟨_, suzD.mul_mem hb hb, pt_mul pt_RB pt_RB⟩
  · exact ⟨_, suzD.mul_mem (suzD.mul_mem ha ha) (suzD.mul_mem hb hb),
      pt_mul (pt_mul pt_RA pt_RA) (pt_mul pt_RB pt_RB)⟩

theorem roots_ok {j : Nat} (hj : j < 2) :
    suzRootPerm j * repPerm 6 = repPerm 6 * suzRootPerm j ∧ suzRootPerm j ^ 4 = 1 := by
  have hr := pt_RP hj
  have hd := pt_DL
  have hk : rootOK DL (pidn 42 6) (RP j) = true := by
    obtain ⟨h0, h1⟩ := CFSG.KC.L34KSnd.andB_iff.1 kRoot
    interval_cases j
    · exact h0
    · exact h1
  unfold rootOK at hk
  obtain ⟨hc, h4⟩ := CFSG.KC.L34KSnd.andB_iff.1 hk
  refine ⟨((hr.2.comp hd.2).eq_iff (hd.2.comp hr.2)).1
    ((CFSG.KC.L34KSnd.commPt_iff hr.1 hd.1).1 hc), ?_⟩
  have hp := pt_mul (pt_mul hr hr) (pt_mul hr hr)
  rw [Nat.eq_of_beq_eq_true h4] at hp
  rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, pow_succ, pow_succ, pow_one, mul_assoc]
  exact hp.2.perm_eq pt_one.2

theorem exists_pt {y : Equiv.Perm (Fin 42)} (hy : y ∈ rho0.range) :
    ∃ i < SK0.cnt, Pt (SK0.T i) y := by
  obtain ⟨t, ht, hrep⟩ := CFSG.Sporadic.SuzOddCore.rho0_enumerates.complete y hy
  have ht' : t ∈ (pts 42 6 SK0.cnt SK0.T).toList := by
    rw [← SuzK0.tabs_eq]
    exact ht
  obtain ⟨i, hi, rfl⟩ := exists_getElem!_of_mem ht'
  rw [size_pts] at hi
  rw [pts_get' hi] at hrep
  exact ⟨i, hi, SuzK0.pt_canon hi, hrep⟩

theorem mem_suzD_of_mem_range {y : Equiv.Perm (Fin 42)} (hy : y ∈ rho0.range)
    (hc : ∀ j < 2, y * suzRootPerm j = suzRootPerm j * y) : y ∈ suzD := by
  obtain ⟨i, hi, hx⟩ := exists_pt hy
  have hpt := scan hi
  unfold ptOK at hpt
  obtain ⟨hcs, -⟩ := CFSG.KC.L34KSnd.andB_iff.1 hpt
  obtain ⟨k, hk, hxk⟩ := centSubK_sound hx.1 (fun c hc' => (pt_RP hc').1) hcs fun c hc' =>
    ((hx.2.comp (pt_RP hc').2).eq_iff ((pt_RP hc').2.comp hx.2)).2 (hc c hc')
  obtain ⟨z, hz, hpz⟩ := pt_ZP hk
  have hx2 := hx.2
  rw [hxk] at hx2
  rwa [hx2.perm_eq hpz.2]

theorem not_comm_of_mem_coset {σ : Equiv.Perm (Fin 42)} (hσ : TabRep suzTabV0 σ)
    {g : Equiv.Perm (Fin 42)} (hg : g ∈ rho0.range) :
    ¬ ∀ j < 2, (σ * g) * suzRootPerm j = suzRootPerm j * (σ * g) := by
  intro hcomm
  obtain ⟨i, hi, hx⟩ := exists_pt hg
  rw [SuzOut.sv_eq] at hσ
  have hsx := pt_mul ⟨SuzOut.sv_parts.2.1, hσ⟩ hx
  have hpt := scan hi
  unfold ptOK at hpt
  obtain ⟨-, hoff⟩ := CFSG.KC.L34KSnd.andB_iff.1 hpt
  unfold offK at hoff
  have hall : (allN 2 fun c => commPt 42 6 (pcomp 42 6 (mask 6) (SuzSV 0) (SK0.T i))
      (roots RA RB c)) = true :=
    CFSG.KS.Raw.Orb.allN_iff.2 fun c hc => (CFSG.KC.L34KSnd.commPt_iff hsx.1 (pt_RP hc).1).2
      (((hsx.2.comp (pt_RP hc).2).eq_iff ((pt_RP hc).2.comp hsx.2)).2 (hcomm c hc))
  rw [hall] at hoff
  exact absurd hoff (by decide)

end Perms

theorem check786002 :
    (∀ j < 2, suzRootPerm j * repPerm 6 = repPerm 6 * suzRootPerm j ∧ suzRootPerm j ^ 4 = 1) ∧
      ∀ (τ : Equiv.Perm (Fin 1782))
        (hτ : τ ∈ suzT ⊓ centralizer ({suzInv 0} : Set (Equiv.Perm (Fin 1782)))),
        (∀ j < 2, rhoHat ⟨τ, hτ⟩ * suzRootPerm j = suzRootPerm j * rhoHat ⟨τ, hτ⟩) →
          ∃ hτE : τ ∈ invE 0, rho0 ⟨τ, hτE⟩ ∈ suzD := by
  refine ⟨fun j hj => roots_ok hj, fun τ hτ hc => ?_⟩
  by_cases hτM : τ ∈ suzM
  · have hτE : τ ∈ invE 0 :=
      mem_invE_zero.2 ⟨hτM, Subgroup.mem_centralizer_singleton_iff.1 hτ.2⟩
    refine ⟨hτE, mem_suzD_of_mem_range ?_ ?_⟩
    · exact rho0.mem_range.2 ⟨⟨τ, hτE⟩, rfl⟩
    · intro j hj
      have hρ : rhoHat ⟨τ, hτ⟩ = rho0 ⟨τ, hτE⟩ := rfl
      rw [← hρ]
      exact hc j hj
  · exfalso
    set Ê : Subgroup (Equiv.Perm (Fin 1782)) :=
      suzT ⊓ centralizer ({suzInv 0} : Set (Equiv.Perm (Fin 1782))) with hÊdef
    have hτT : τ ∈ suzT := hτ.1
    have hτc : τ * suzInv 0 = suzInv 0 * τ :=
      Subgroup.mem_centralizer_singleton_iff.1 hτ.2
    have hv0Ê : suzV0 ∈ Ê :=
      ⟨suzV0_mem, Subgroup.mem_centralizer_singleton_iff.2 suzV0_comm⟩
    have ha : (⟨suzV0⁻¹, suzT.inv_mem suzV0_mem⟩ : suzT) ∉ suzM.subgroupOf suzT := by
      rw [Subgroup.mem_subgroupOf]
      intro h
      exact suzV0_not_mem (by simpa using suzM.inv_mem h)
    have hb : (⟨τ, hτT⟩ : suzT) ∉ suzM.subgroupOf suzT := by
      rw [Subgroup.mem_subgroupOf]
      exact hτM
    have he : suzV0⁻¹ * τ ∈ suzM := by
      have h3 := (Subgroup.mul_mem_iff_of_index_two suzM_index_T).2 (iff_of_false ha hb)
      rw [Subgroup.mem_subgroupOf] at h3
      exact h3
    have h1 : suzV0⁻¹ * suzInv 0 = suzInv 0 * suzV0⁻¹ := by
      calc suzV0⁻¹ * suzInv 0 = suzV0⁻¹ * (suzInv 0 * suzV0) * suzV0⁻¹ := by group
        _ = suzV0⁻¹ * (suzV0 * suzInv 0) * suzV0⁻¹ := by rw [suzV0_comm]
        _ = suzInv 0 * suzV0⁻¹ := by group
    have heC : suzV0⁻¹ * τ * suzInv 0 = suzInv 0 * (suzV0⁻¹ * τ) := by
      calc suzV0⁻¹ * τ * suzInv 0 = suzV0⁻¹ * (τ * suzInv 0) := by group
        _ = suzV0⁻¹ * (suzInv 0 * τ) := by rw [hτc]
        _ = (suzV0⁻¹ * suzInv 0) * τ := by group
        _ = (suzInv 0 * suzV0⁻¹) * τ := by rw [h1]
        _ = suzInv 0 * (suzV0⁻¹ * τ) := by group
    have heE : suzV0⁻¹ * τ ∈ invE 0 := mem_invE_zero.2 ⟨he, heC⟩
    have heÊ : suzV0⁻¹ * τ ∈ Ê :=
      ⟨suzM_le_suzT he, Subgroup.mem_centralizer_singleton_iff.2 heC⟩
    have hprod : (⟨τ, hτ⟩ : Ê) = ⟨suzV0, hv0Ê⟩ * ⟨suzV0⁻¹ * τ, heÊ⟩ :=
      Subtype.ext (by simp)
    have hσ : TabRep suzTabV0 (rhoHat ⟨suzV0, hv0Ê⟩) := by
      unfold suzTabV0
      exact (fixList_points hm0).tabRep_restrHom _ suzHat_preserves
        ⟨suzV0, hv0Ê⟩ rep_suzArrV0
    have hy : rhoHat ⟨τ, hτ⟩ =
        rhoHat ⟨suzV0, hv0Ê⟩ * rho0 ⟨suzV0⁻¹ * τ, heE⟩ := by
      rw [hprod, map_mul]
      rfl
    have hcomm : ∀ j < 2,
        (rhoHat ⟨suzV0, hv0Ê⟩ * rho0 ⟨suzV0⁻¹ * τ, heE⟩) * suzRootPerm j =
          suzRootPerm j * (rhoHat ⟨suzV0, hv0Ê⟩ * rho0 ⟨suzV0⁻¹ * τ, heE⟩) := by
      intro j hj
      rw [← hy]
      exact hc j hj
    exact not_comm_of_mem_coset hσ
      (rho0.mem_range.2 ⟨⟨suzV0⁻¹ * τ, heE⟩, rfl⟩) hcomm

end CertificateChecks.KernelSpor.Suz786002

end
