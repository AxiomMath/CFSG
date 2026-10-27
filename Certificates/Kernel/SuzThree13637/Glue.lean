
module

public import Certificates.Kernel.SuzThree13637.QFacts
public import Certificates.Kernel.SuzThree13637.YChk
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.SuzThree13637

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.PSearch CFSG.KS.HypK CFSG.KS.QMdlK
  CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K CertificateChecks.KernelSpor
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
  CFSG.RankThree.Native
open CFSG.Sporadic.SuzOddCore (suzM)
open CFSG.Monster.B.Co2 (permOfArr Rep rep_compA)
open CFSG.Monster.B.Mathieu (rep_powArr)

theorem dGen_valid {i : ℕ} (hi : i < 5) : validA 1782 (dGens ())[i]! = true := by
  rw [(d_gen hi).1]
  exact validA_of (d_gen hi).2

theorem e_eq {k : ℕ} (hk : k < 243) : permOfArr 1782 (dElts ())[k]! = EK k := by
  have hr : ∀ i (hi : i < 5), Rep 1782 (dGens ())[i]! (dPerm ⟨i, hi⟩) :=
    fun i hi => rep_of_validA (dGen_valid hi)
  have he : (dElts ())[k]! = dProd (dGens ()) k := by
    rw [dElts, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  rw [he, dProd]
  apply CFSG.Monster.B.Mathieu.permOfArr_eq_of_rep
  unfold EK
  rw [φK_vec]
  exact rep_compA (rep_powArr (hr 0 (by norm_num)) _) (rep_compA (rep_powArr (hr 1 (by norm_num)) _)
    (rep_compA (rep_powArr (hr 2 (by norm_num)) _) (rep_compA (rep_powArr (hr 3 (by norm_num)) _)
      (rep_powArr (hr 4 (by norm_num)) _))))

theorem yArr_eq : unpack 1782 11 (CE.G 0) = yArr (levels ()) := (c_get (by norm_num)).symm.trans rfl

theorem y_valid : validA 1782 (yArr (levels ())) = true := by
  rw [← yArr_eq]
  exact validA_of (ce_reb' (by norm_num)).2.2

theorem y_cube : yP ^ 3 = 1 := by
  have h := y_ok
  rw [Bool.and_eq_true] at h
  have h1 := prep_pcomp n32_13637 prep_Y prep_Y2
  rw [Nat.eq_of_beq_eq_true h.1] at h1
  rw [pow_three]
  exact prep_eq13637 h1 prep_I

theorem y_ne : yP ≠ 1 := by
  intro h1
  have h := y_ok
  rw [Bool.and_eq_true] at h
  have e := Nat.eq_of_beq_eq_true h.2
  rw [prep_Y ⟨0, by norm_num⟩, h1] at e
  exact absurd e (by decide)

theorem y_mem : yP ∈ suzM := by
  have h := gen_mem (k := 0) (by norm_num)
  rw [yArr_eq] at h
  exact (Subgroup.mem_inf.1 h).2

theorem body13637 :
    Qg ≤ suzM ∧ Nat.card Qg = 2187 ∧
    (∀ i < 5, validA 1782 (dGens ())[i]! = true ∧ permOfArr 1782 (dGens ())[i]! ∈ suzM ∧
      permOfArr 1782 (dGens ())[i]! ^ 3 = 1) ∧
    (∀ i < 5, ∀ j < 5, Commute (permOfArr 1782 (dGens ())[i]!) (permOfArr 1782 (dGens ())[j]!)) ∧
    (∀ k < 243, ∀ k' < 243, permOfArr 1782 (dElts ())[k]! = permOfArr 1782 (dElts ())[k']! →
      k = k') ∧
    (∀ B : Subgroup (Equiv.Perm (Fin 1782)), (∀ b ∈ B, ∃ k < 243, b = permOfArr 1782 (dElts ())[k]!) →
      Nat.card B * 3 = 243 → ∀ c ∈ Subgroup.centralizer (B : Set (Equiv.Perm (Fin 1782))) ⊓ suzM,
        ∃ k < 243, c = permOfArr 1782 (dElts ())[k]!) ∧
    validA 1782 (yArr (levels ())) = true ∧ yPerm ∈ suzM ∧ yPerm ^ 3 = 1 ∧ yPerm ≠ 1 ∧
    Subgroup.closure (permsA 1782 (cGens (levels ()))) =
      Subgroup.centralizer ({yPerm} : Set (Equiv.Perm (Fin 1782))) ⊓ suzM ∧
    Nat.card (Subgroup.closure (permsA 1782 (cGens (levels ())))) = 3240 ∧
    enumOK 1782 (cGens (levels ())) cKeys (cCert (levels ())) = true ∧
    (∀ w ∈ Subgroup.closure (permsA 1782 (cGens (levels ()))), w ≠ 1 → (w ^ 2 = 1 ∨ w ^ 5 = 1) →
      Nat.card ↥(Subgroup.centralizer ({w} : Set (Equiv.Perm (Fin 1782))) ⊓
        Subgroup.closure (permsA 1782 (cGens (levels ())))) < 81) ∧
    (∀ x ∈ suzM, orderOf x = 3 → ∃ h ∈ suzM, (∃ k < 243, h * x * h⁻¹ = permOfArr 1782 (dElts ())[k]!) ∨
      h * x * h⁻¹ = yPerm ∨ h * x * h⁻¹ = yPerm ^ 2) := by
  refine ⟨QgK_le, card_QgK, fun i hi => ⟨dGen_valid hi, dK_mem ⟨i, hi⟩, dK_pow ⟨i, hi⟩⟩,
    fun i hi j hj => dK_comm ⟨i, hi⟩ ⟨j, hj⟩, fun k hk k' hk' h => ?_, fun B hB hcard c hc => ?_,
    y_valid, y_mem, y_cube, y_ne, c_cent, c_card, c_enum.1, fun w hw h1 h25 => c_class hw h1 h25,
    fun x hx hxo => ?_⟩
  · rw [e_eq hk, e_eq hk'] at h
    exact EK_inj hk hk' h
  · have hBD : B ≤ DK := fun b hb => by
      obtain ⟨k, hk, rfl⟩ := hB b hb
      rw [e_eq hk]
      exact EK_mem k
    rw [centralizer_hyp hBD hcard] at hc
    obtain ⟨k, hk, rfl⟩ := DK_eq hc
    exact ⟨k, hk, (e_eq hk).symm⟩
  · obtain ⟨h, hh, hcase⟩ := fusion_suzK hx hxo
    refine ⟨h, hh, ?_⟩
    rcases hcase with hD | hy | hy2
    · obtain ⟨k, hk, e⟩ := DK_eq hD
      exact Or.inl ⟨k, hk, e.trans (e_eq hk).symm⟩
    · exact Or.inr (Or.inl hy)
    · exact Or.inr (Or.inr hy2)

end CFSG.KD.SuzThree13637

end
