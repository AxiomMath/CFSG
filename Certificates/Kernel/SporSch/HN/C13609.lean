module

public import Certificates.Kernel.SporSch.HN.C13609K
public import Certificates.Kernel.SporSch.HN.Pt2085
public import CFSG.Certificates.Kernel.ConjKeySound
public import CFSG.Certificates.Kernel.LocalQTSecLemmas
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Sporadic.HNSchreier.ThreeCent
public import CFSG.Sporadic.HNSchreier.InvolSpec

public section

namespace CertificateChecks.KernelSporSch.HN13609

open CFSG.KC.ConjKey CFSG.KS.ConjKey CFSG.KS.Ord CFSG.KS.SporSch CFSG.KC.LQT.SecS
open CFSG.Sporadic.HNSchreier CertificateChecks.KernelSporSch Matrix

local notation "OM" => ordMat 5 133 13 1729
local notation "mm" => CFSG.KC.LL.HN.mm
local notation "G3" => CFSG.KD.HNPt2109.G3F

theorem mul2_of {A B D : ℕ} (hA : Canon 5 133 13 A) (hB : Canon 5 133 13 B) (e : mm A B = D) :
    Canon 5 133 13 D ∧ OM D = OM A * OM B := by
  subst e
  exact HNXP.mm_sound hA hB

theorem mul3_of {A B C D : ℕ} (hA : Canon 5 133 13 A) (hB : Canon 5 133 13 B)
    (hC : Canon 5 133 13 C) (e : mm (mm A B) C = D) :
    Canon 5 133 13 D ∧ OM D = OM A * OM B * OM C := by
  subst e
  obtain ⟨h1, h2⟩ := HNXP.mm_sound hA hB
  obtain ⟨h3, h4⟩ := HNXP.mm_sound h1 hC
  exact ⟨h3, by rw [h4, h2]⟩

theorem pow5_of {A D : ℕ} (hA : Canon 5 133 13 A) (e : mm (mm (mm (mm A A) A) A) A = D) :
    OM A ^ 5 = OM D := by
  subst e
  obtain ⟨h1, h2⟩ := HNXP.mm_sound hA hA
  obtain ⟨h3, h4⟩ := HNXP.mm_sound h1 hA
  obtain ⟨h5, h6⟩ := HNXP.mm_sound h3 hA
  obtain ⟨-, h8⟩ := HNXP.mm_sound h5 hA
  rw [h8, h6, h4, h2]
  simp only [pow_succ, pow_zero, one_mul]

theorem c3J_eq {j : ℕ} (hj : j < 7) : HNPt2109.C3J j = c3J j := by
  unfold HNPt2109.C3J c3J
  split_ifs with h
  · exact HNPt2085.wJ_sL _ (HNPt2109.letters_ok.2.2.1 j h)
  · simp only [HNPt2109.G3J, g3J, HNPt2085.seedWordJ_eq,
      HNPt2085.wJ_sL _ HNPt2109.letters_ok.2.2.2.1]

theorem G3_eq {l : ℕ} (hl : l < 7) : G3 l = HNPt2109.C3W l := by
  interval_cases l <;> rfl

theorem G_mat {l : ℕ} (hl : l < 7) :
    Canon 5 133 13 (G3 l) ∧ OM (G3 l) = matJ (c3J l) := by
  rw [G3_eq hl, ← c3J_eq hl]
  exact HNPt2109.C3_mat hl

theorem GI_mat {l : ℕ} (hl : l < 7) :
    Canon 5 133 13 (CFSG.KD.HN13609.CIF l) ∧ OM (CFSG.KD.HN13609.CIF l) = matJ (c3J l)⁻¹ := by
  have hc : Canon 5 133 13 (CFSG.KD.HN13609.CIF l) :=
    HNXP.canon_of_validHN (CFSG.KS.allN_spec valid_CI l hl)
  obtain ⟨hg, hgm⟩ := G_mat hl
  have e : mm (G3 l) (CFSG.KD.HN13609.CIF l) = CFSG.KD.OrdHN.ONE :=
    eqK_spec (CFSG.KS.allN_spec inv_CI l hl)
  obtain ⟨-, hm⟩ := mul2_of hg hc e
  rw [HNXP.one_ord, hgm] at hm
  exact ⟨hc, CFSG.KS.HNArr.mat_inv_of_mul hm.symm⟩

noncomputable abbrev yE : JH := c3J 6 * c3J 0 * c3J 0

theorem Y_mat :
    Canon 5 133 13 CFSG.KD.HN13609.Y ∧ OM CFSG.KD.HN13609.Y = matJ yE := by
  obtain ⟨h6, m6⟩ := G_mat (l := 6) (by norm_num)
  obtain ⟨h0, m0⟩ := G_mat (l := 0) (by norm_num)
  obtain ⟨hY, mY⟩ := mul3_of h6 h0 h0 (eqK_spec y_eq)
  refine ⟨hY, ?_⟩
  rw [mY, m6, m0, CFSG.KS.HNArr.matJ_mul, CFSG.KS.HNArr.matJ_mul]

theorem vm_sound {v M : ℕ} (hv : VCanon 5 133 13 v) (hM : Canon 5 133 13 M) :
    VCanon 5 133 13 (vmHN v M) ∧ toVec 5 133 13 (vmHN v M) = toVec 5 133 13 v ᵥ* OM M :=
  vecR_sound CFSG.KD.OrdHN.consts hv hM

theorem one_lt_pow_mul (w d : ℕ) (h : 0 < w * d) : 1 < 2 ^ (w * d) := Nat.one_lt_two_pow (by omega)

theorem e_canon : VCanon 5 133 13 1 := by
  unfold VCanon
  refine ⟨one_lt_pow_mul 13 133 (by norm_num), fun j _ => ?_⟩
  unfold lane
  have : 1 / 2 ^ (13 * j) % 2 ^ 13 ≤ 1 := (Nat.mod_le _ _).trans (Nat.div_le_self _ _)
  omega

theorem key_spec (c : ℕ) :
    VCanon 5 133 13 (keyOf vmHN G3 CFSG.KD.HN13609.CIF 8 CFSG.KD.HN13609.Y 1 c) ∧
      toVec 5 133 13 (keyOf vmHN G3 CFSG.KD.HN13609.CIF 8 CFSG.KD.HN13609.Y 1 c) =
        toVec 5 133 13 1 ᵥ* matJHom (elF c3J 8 c * yE * (elF c3J 8 c)⁻¹) := by
  refine keyOf_sound (ρ := matJHom) (g := c3J) (Ok := VCanon 5 133 13) (toV := toVec 5 133 13)
    (fun v l hl hv => ?_) (fun v l hl hv => ?_) (fun v hv => ?_) 8 e_canon c
  · obtain ⟨hc, hm⟩ := G_mat hl
    have h := vm_sound hv hc
    rw [hm] at h
    exact h
  · obtain ⟨hc, hm⟩ := GI_mat hl
    have h := vm_sound hv hc
    rw [hm] at h
    exact h
  · have h := vm_sound hv Y_mat.1
    rw [Y_mat.2] at h
    exact h

theorem conj_nodup :
    CFSG.KD.HN13609.W.length = 972 ∧
      (CFSG.KD.HN13609.W.map fun c => elF c3J 8 c * yE * (elF c3J 8 c)⁻¹).Nodup := by
  obtain ⟨hl, hn⟩ := conjKeysOK_spec keys
  refine ⟨hl, List.Nodup.map_on (fun a ha b hb hab => ?_) (List.Nodup.of_map _ hn)⟩
  refine List.inj_on_of_nodup_map hn ha hb ?_
  refine vec_inj (by norm_num) (key_spec a).1 (key_spec b).1 ?_
  rw [(key_spec a).2, (key_spec b).2, hab]

theorem elF_mem :
    ∀ fuel c, elF c3J fuel c ∈ CJ (sJ 2)
  | 0, c => by
    rw [elF_zero]
    exact one_mem _
  | fuel + 1, c => by
    by_cases hc : c = 0
    · subst hc
      rw [elF_succ_zero]
      exact one_mem _
    · rw [elF_succ c3J fuel hc]
      exact mul_mem (mem_CJ.2 (c3J_comm (letter_lt c)).symm) (elF_mem fuel _)

theorem facts :
    Nat.card (CJ (sJ 2) ⊓ Subgroup.centralizer ({yE} : Set JH) : Subgroup JH) ≤ 30 ∧
      orderOf yE = 5 := by
  obtain ⟨hl, hn⟩ := conj_nodup
  have hC := card_CJ_s3
  have h := length_mul_card_le (CJ (sJ 2)) yE (CFSG.KD.HN13609.W.map (elF c3J 8))
    (fun x hx => by
      obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
      exact elF_mem 8 c)
    (by rw [List.map_map]; exact hn) (by rw [hC]; norm_num)
  rw [List.length_map, hl, hC] at h
  refine ⟨by omega, ?_⟩
  have hp : matJHom (yE ^ 5) = matJHom 1 := by
    have hY : matJHom yE = OM CFSG.KD.HN13609.Y := Y_mat.2.symm
    rw [map_pow, map_one, hY, pow5_of Y_mat.1 (eqK_spec y_pow), HNXP.one_ord]
  have h5 : yE ^ 5 = 1 := matJ_injective hp
  have h1 : yE ≠ 1 := by
    intro hy
    have e : ∀ c, elF c3J 8 c * yE * (elF c3J 8 c)⁻¹ = 1 := fun c => by
      rw [hy, mul_one, mul_inv_cancel]
    have h01 := (hn.getElem_inj_iff (i := 0) (j := 1) (hi := by simp [hl])
      (hj := by simp [hl])).1 (by simp only [List.getElem_map, e])
    omega
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime h5 h1

end CertificateChecks.KernelSporSch.HN13609

end
