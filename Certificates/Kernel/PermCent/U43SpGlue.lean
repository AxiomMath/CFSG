module

public import Certificates.Kernel.PermCent.U43QuatFinal
public import Certificates.Kernel.PermCent.U43SpC0
public import Certificates.Kernel.PermCent.U43SpC1
public import Certificates.Kernel.PermCent.U43SpC2
public import Certificates.Kernel.PermCent.U43SpC3
public import Certificates.Kernel.PermCent.U43SpC4
public import Certificates.Kernel.PermCent.U43SpC5
public import Certificates.Kernel.PermCent.U43SpC6
public import Certificates.Kernel.PermCent.U43SpC7
public import CFSG.Certificates.Kernel.QuatSpKSound
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1UC
public import Certificates.Data.U43SProp
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1UA
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Arr
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43CountBase
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Model

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelPermCent.U43Sp

open CFSG.ClassicalInvolution.Q3.TL4.E3S3O.U4M

@[expose] def SpCoreK (y : Equiv.Perm (Fin 820)) : Prop :=
  y * u0P = u0P * y ∧ y * v0P = v0P * y ∧ y * y = 1 ∧
    (∃ x ∈ L1P, y * u1P = x * y) ∧ (∃ x ∈ L1P, y * v1P = x * y) ∧
      ∀ x ∈ L1P, y * x = x * y → x = 1 ∨ x = r0P

section Frame

open CFSG.ComponentClassification.HarrisLit.P1.U43.Cover CFSG.ComponentClassification.HarrisLit.P1.U43
  CFSG.ComponentClassification.HarrisLit.P1.U43.Quat CFSG.LieType.Multipliers.U43 CFSG.KC.Enum CFSG.KS
  CFSG.KS.Prim CFSG.KC.QuatK CFSG.ClassicalInvolution.Q3.TL4.E4C CertificateChecks.KernelPermCent.U43P1
  CertificateChecks.KernelPermCent.U43Quat Subgroup
open CFSG.EvenSporadicStandard.M24Std.CU43 (P P_eq_range tP)

theorem sp_coset_all : ∀ k < 8, spCoset k = true := by
  intro k hk
  interval_cases k
  · exact sp_coset0
  · exact sp_coset1
  · exact sp_coset2
  · exact sp_coset3
  · exact sp_coset4
  · exact sp_coset5
  · exact sp_coset6
  · exact sp_coset7

theorem sp_none_qE {g : Equiv.Perm (Fin 820)} (hg : g ∈ P)
    {k : ℕ} (hk : k < 8) : ¬ SpCoreK (g * tP k) := by
  rintro ⟨h1, h2, h3, ⟨x4, hx4, h4⟩, ⟨x5, hx5, h5⟩, h6⟩
  rw [u0_eq] at h1
  rw [v0_eq] at h2
  rw [L1_eq] at hx4 hx5 h6
  rw [u1_eq] at h4
  rw [v1_eq] at h5
  rw [r0_eq] at h6
  have c1 : Commute (g * tP k) (qE 1) := h1
  have cy : Commute (g * tP k) (qE 0) := by
    have h := c1.mul_right c1
    rwa [u0_sq] at h
  have cg : Commute g (qE 0) := by
    have e : g = g * tP k * (tP k)⁻¹ := by group
    rw [e]
    exact cy.mul_left (commute_tP_r0 k).inv_left
  have hgP : phi g ∈ psi.range ⊓ centralizer ({tRep 0} : Set (Equiv.Perm (Fin 820))) := by
    refine mem_inf.2 ⟨P_eq_range ▸ phi_mem hg, mem_centralizer_singleton_iff.2 ?_⟩
    rw [← conj_r0, ← map_mul, ← map_mul, cg.eq]
  obtain ⟨i, hi, hpi⟩ := cen0_facts.1 _ hgP
  have hS := (crep_fr (prep_tPK k)).1
  have hL1 : q8Elems (tRep 0) (phi (qE 3)) (phi (qE 4)) = L1E.map phi := by
    rw [← conj_r0, q8Elems_map, L1E]
  have hL := forall₂_q8F (a := 3) (b := 4) (by norm_num) (by norm_num)
  refine spRefK_spec (by norm_num) hpi hS crep_eP crep_rF
    (crep_fr (prep_qE (j := 1) (by norm_num))).1 (crep_fr (prep_qE (j := 2) (by norm_num))).1
    (crep_fr (prep_qE (j := 3) (by norm_num))).1 (crep_fr (prep_qE (j := 4) (by norm_num))).1
    hL (spScanK_spec (sp_coset_all k hk) hi) ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e := congrArg phi h1
    simpa only [map_mul] using e
  · have e := congrArg phi h2
    simpa only [map_mul] using e
  · have e := congrArg phi h3
    simpa only [map_mul, map_one] using e
  · refine ⟨phi x4, by rw [hL1]; exact List.mem_map_of_mem hx4, ?_⟩
    have e := congrArg phi h4
    simpa only [map_mul] using e
  · refine ⟨phi x5, by rw [hL1]; exact List.mem_map_of_mem hx5, ?_⟩
    have e := congrArg phi h5
    simpa only [map_mul] using e
  · intro X hX hXc
    rw [hL1, List.mem_map] at hX
    obtain ⟨x, hx, rfl⟩ := hX
    have e : phi (g * tP k * x) = phi (x * (g * tP k)) := by
      simpa only [map_mul] using hXc
    rcases h6 x hx (phi.injective e) with rfl | rfl
    · exact Or.inl (map_one phi)
    · exact Or.inr conj_r0

end Frame

section Count

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.LieType.Multipliers.U43
open CFSG.EvenSporadicStandard.M24Std.CU43 CFSG.ComponentClassification.HarrisLit.P1.U43
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.TL4.E4A CFSG.ClassicalInvolution.Q3.TL4.E4C
open CFSG.Sporadic.SmallOddCore

theorem spW_iffK {w : List (Array ℕ)} {g : Equiv.Perm (Fin 820)} (hw : RepW 820 w g)
    {t : Array ℕ} {T : Equiv.Perm (Fin 820)} (ht : Rep 820 t T) :
    spW t (u0A ()) (v0A ()) (u1A ()) (v1A ()) (r0A ()) (q8A 820 (r0A ()) (u1A ()) (v1A ())) w =
        true ↔ SpCoreK (g * T) := by
  have hy : RepW 820 (t :: w) (g * T) := RepW.cons ht hw
  have hL : List.Forall₂ (Rep 820) (q8A 820 (r0A ()) (u1A ()) (v1A ())) L1P :=
    forall₂_q8A rep_r0 rep_u1 rep_v1
  have hany : ∀ (a : Array ℕ) (A : Equiv.Perm (Fin 820)), Rep 820 a A →
      (((q8A 820 (r0A ()) (u1A ()) (v1A ())).any fun x => twW a x (t :: w)) = true ↔
        ∃ x ∈ L1P, g * T * A = x * (g * T)) := by
    intro a A ha
    rw [any_eq_of_forall₂ hL (g := fun x => decide (g * T * A = x * (g * T))) fun b B hbB => by
      rw [Bool.eq_iff_iff, decide_eq_true_iff]
      exact twW_iff hy ha hbB]
    simp
  have hall : (((q8A 820 (r0A ()) (u1A ()) (v1A ())).all fun x =>
      !twW x x (t :: w) || eqA 820 x (idA 820) || eqA 820 x (r0A ())) = true ↔
        ∀ x ∈ L1P, g * T * x = x * (g * T) → x = 1 ∨ x = r0P) := by
    rw [all_eq_of_forall₂ hL (g := fun x => decide (g * T * x = x * (g * T) → x = 1 ∨ x = r0P))
      fun b B hbB => by
        have e1 : twW b b (t :: w) = decide (g * T * B = B * (g * T)) := by
          rw [Bool.eq_iff_iff, decide_eq_true_iff]
          exact twW_iff hy hbB hbB
        rw [e1, eqA_eq hbB rep_idA, eqA_eq hbB rep_r0]
        by_cases h1 : g * T * B = B * (g * T) <;> by_cases h2 : B = 1 <;>
          by_cases h3 : B = r0P <;> simp [h1, h2, h3]]
    simp only [List.all_eq_true, decide_eq_true_eq]
  rw [spW, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true, twW_iff hy rep_u0 rep_u0, twW_iff hy rep_v0 rep_v0, allLt_sq_iff hy,
    hany _ _ rep_u1, hany _ _ rep_v1, hall, SpCoreK]
  simp only [and_assoc]

theorem spCountCheck_true :
    spCountCheck () = true := by
  classical
  simp only [spCountCheck, spCounts, List.all_map, List.all_eq_true, List.mem_range,
    Function.comp_apply, beq_iff_eq]
  intro k hk
  rw [← card_eq_countW_P (Pr := fun g => SpCoreK (g * tP k))
    (fun w g hw _ => spW_iffK hw (rep_tArr k))]
  have : IsEmpty {x : P // SpCoreK ((x : Equiv.Perm (Fin 820)) * tP k)} :=
    ⟨fun x => sp_none_qE x.1.2 hk x.2⟩
  exact Nat.card_of_isEmpty

end Count

end CertificateChecks.KernelPermCent.U43Sp

end
