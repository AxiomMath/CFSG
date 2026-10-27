module

public import Certificates.Kernel.J4ZC9686.RhoChecks
public import Certificates.Kernel.J4M2.C4202Glue
public import CFSG.Quasithin.EmptyFaithful.ONanJ4ZCentB0Defs

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelJ4ZC9686

open Equiv CFSG.KC.Enum CFSG.KC.LQT.L CFSG.KS.PK CFSG.KC.J4M2K CFSG.Quasithin.J4M2
  CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat
open CFSG.KC.J4ZC9686 CFSG.Quasithin.J4ZCent
open CFSG.Sporadic.J4.ZCent (g0W rW tW)
open CertificateChecks.KernelJ4M2 (hexLt4202 code7_sig4202 ofNat_val77 h77)

theorem code7_mul (σ τ : Perm (Fin 77)) : code7 (σ * τ) = mul7 77 (code7 σ) (code7 τ) := by
  rw [← rnc7_enc, RN.enc_mul, rnc7_mul h77, rnc7_enc, rnc7_enc]

theorem code7_one : code7 (1 : Perm (Fin 77)) = one7 77 := by
  rw [← rnc7_enc, RN.enc_one, rnc7_one h77]

theorem code7_inj {σ τ : Perm (Fin 77)} (h : code7 σ = code7 τ) : σ = τ :=
  RN.enc_inj (rnc7_inj h77 (by rw [rnc7_enc, rnc7_enc, h]))

theorem sigW_cons (l : ℤ) (w : List ℤ) : sigW (l :: w) = mul7 77 (sigC (l.toNat - 1)) (sigW w) :=
  rfl

theorem wordC_cons (l : ℤ) (w : List ℤ) : wordC (l :: w) = mul7 77 (letC l) (wordC w) := rfl

theorem g0W_lt : ∀ i < 16, ∀ l ∈ g0W.getD i [], l.toNat - 1 < 32 := by
  decide

theorem code7_sigProd : ∀ w : List ℤ, (∀ l ∈ w, l.toNat - 1 < 32) →
    code7 ((w.map fun l => sigPerm (l.toNat - 1)).prod) = sigW w
  | [], _ => code7_one
  | l :: w, hw => by
    rw [List.map_cons, List.prod_cons, code7_mul, code7_sig4202 (hw l List.mem_cons_self),
      code7_sigProd w (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')), sigW_cons]

theorem code7_b0Perm (i : ℕ) : code7 (b0Perm i) = b0C i := by
  unfold b0Perm b0C
  by_cases hi : i < 16
  · exact code7_sigProd _ (g0W_lt i hi)
  · have e : g0W.getD i [] = [] := List.getD_eq_default _ _ (by simp [g0W]; omega)
    rw [e]
    exact code7_one

theorem rho_parts :
    closedK7 77 [codeL (PL.getD 0 []), codeL (PL.getD 1 [])]
        (bfsK7 77 [codeL (PL.getD 0 []), codeL (PL.getD 1 [])] 64) = true ∧
      (bfsK7 77 [codeL (PL.getD 0 []), codeL (PL.getD 1 [])] 64).size = 960 ∧
      (∀ i < 16, memT (bfsK7 77 [codeL (PL.getD 0 []), codeL (PL.getD 1 [])] 64).t (b0C i) = true) ∧
      codeL (PL.getD 0 []) = ev7 ((List.range 16).map b0C) [4, 4, 13] ∧
      codeL (PL.getD 1 []) = ev7 ((List.range 16).map b0C) [15, 4, 4, 12] ∧
      mul7 77 (b0C 3) i3C = one7 77 ∧ mul7 77 (b0C 4) i4C = one7 77 ∧
      closedK7 77 (rW.map wordC) (bfsK7 77 (rW.map wordC) 64) = true ∧
      ∀ i < 60, i ≠ 0 → memT (bfsK7 77 (rW.map wordC) 64).t (wordC (tW.getD i [])) = false := by
  have h := ch9686rho
  rw [rhoChk, strictB_eq', strictB_eq', rhoCore] at h
  simp only [brec_and, Bool.and_eq_true, nbeq_iff, allR_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, fun i hi hi0 => ?_⟩
  have h9i := h9 i hi
  have hb : Nat.beq i 0 = false := by
    cases hc : Nat.beq i 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hc) hi0
  rw [hb] at h9i
  cases hm : memT (bfsK7 77 (rW.map wordC) 64).t (wordC (tW.getD i []))
  · rfl
  · rw [hm] at h9i
    exact Bool.noConfusion h9i

theorem inv3 : code7 (b0Perm 3)⁻¹ = i3C := by
  have hb := code7_b0Perm 3
  have h1 : code7 (b0Perm 3 * (b0Perm 3 * (b0Perm 3 * b0Perm 3))) =
      code7 (1 : Perm (Fin 77)) := by
    rw [code7_mul, code7_mul, code7_mul, hb, code7_one]
    exact rho_parts.2.2.2.2.2.1
  have e : (b0Perm 3)⁻¹ = b0Perm 3 * (b0Perm 3 * b0Perm 3) :=
    inv_eq_of_mul_eq_one_right (code7_inj h1)
  rw [e, code7_mul, code7_mul, hb]
  rfl

theorem inv4 : code7 (b0Perm 4)⁻¹ = i4C := by
  have hb := code7_b0Perm 4
  have h1 : code7 (b0Perm 4 * (b0Perm 4 * b0Perm 4)) = code7 (1 : Perm (Fin 77)) := by
    rw [code7_mul, code7_mul, hb, code7_one]
    exact rho_parts.2.2.2.2.2.2.1
  have e : (b0Perm 4)⁻¹ = b0Perm 4 * b0Perm 4 := inv_eq_of_mul_eq_one_right (code7_inj h1)
  rw [e, code7_mul, hb]
  rfl

theorem code7_letter (l : ℤ) (hl : (decide (0 < l) || l == -4 || l == -5) = true) :
    code7 (if 0 < l then b0Perm (l.toNat - 1) else (b0Perm ((-l).toNat - 1))⁻¹) = letC l := by
  rcases l with n | n
  · by_cases hn : 0 < (Int.ofNat n : ℤ)
    · rw [if_pos hn, code7_b0Perm]
      rfl
    · have : n = 0 := by
        simp only [Int.ofNat_eq_coe] at hn
        omega
      subst this
      exact absurd hl (by decide)
  · rw [if_neg (by omega)]
    have h34 : n = 3 ∨ n = 4 := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hl
      omega
    rcases h34 with rfl | rfl
    · exact inv3
    · exact inv4

theorem code7_wordPerm : ∀ w : List ℤ, negOK w = true → code7 (wordPerm w) = wordC w
  | [], _ => code7_one
  | l :: w, hw => by
    unfold negOK at hw
    rw [List.all_cons, Bool.and_eq_true] at hw
    have ih := code7_wordPerm w hw.2
    unfold wordPerm at ih ⊢
    rw [List.map_cons, List.prod_cons, code7_mul, ih, code7_letter l hw.1, wordC_cons]

theorem PL_len {j : ℕ} (hj : j < 2) : (PL.getD j []).length = 77 := by
  interval_cases j <;> decide

theorem phiL_spec {j : ℕ} (hj : j < 2) :
    ∀ i < 77, phiK hexP (fd 5 (gimg (p5Gens.getD j 1))) i = (PL.getD j []).getD i 0 := by
  have h : ch9686phiL j = true := by
    interval_cases j
    exacts [ch9686phiL0, ch9686phiL1]
  rw [ch9686phiL, strictB_eq', strictB_eq', allR_eq, List.all_eq_true] at h
  intro i hi
  exact nbeq_iff.1 (h i (List.mem_range.2 hi))

theorem perm_spec {j : ℕ} (hj : j < 2) :
    ∀ i : Fin 77, ((permImg (PL.getD j [])) i : ℕ) = (PL.getD j []).getD i 0 := by
  have h : ch9686perm j = true := by
    interval_cases j
    exacts [ch9686perm0, ch9686perm1]
  rw [ch9686perm, List.all_eq_true] at h
  intro i
  have := beq_iff_eq.1 (h i.val (List.mem_range.2 i.isLt))
  rwa [ofNat_val77] at this

theorem phiRN_list {j : ℕ} (hj : j < 2) :
    (phiRN (p5Gens.getD j 1)).val.toList.map Fin.val = PL.getD j [] := by
  refine List.ext_getElem (by rw [List.length_map, Vector.length_toList, PL_len hj]) ?_
  intro i hi _
  rw [List.getElem_map, Vector.getElem_toList]
  have hi' : i < 77 := by simpa using hi
  have hv := phiRN_val hexLt4202 (p5Gens.getD j 1) ⟨i, hi'⟩
  rw [Fin.getElem_fin] at hv
  rw [hv, phiL_spec hj i hi', List.getD_eq_getElem _ _ (by
    rw [PL_len hj]; exact hi')]

theorem codeL_eq {l : List ℕ} (hl : ∀ i < 77, l.getD i 0 < 2 ^ 7) :
    codeL l = enc 7 (fun i => l.getD i 0) 77 :=
  pmk_eq (by norm_num) hl

theorem code7_phiPerm {j : ℕ} (hj : j < 2) :
    code7 (phiPerm (p5Gens.getD j 1)) = codeL (PL.getD j []) := by
  unfold phiPerm
  rw [phiRN_list hj, code7_of_getD _ (perm_spec hj), codeL_eq]
  intro i hi
  rw [← perm_spec hj ⟨i, hi⟩]
  exact lt_of_lt_of_le (Fin.isLt _) (by norm_num)

theorem codeL_phiC {j : ℕ} (hj : j < 2) :
    codeL (PL.getD j []) = phiC hexP (gimg (p5Gens.getD j 1)) := by
  have hb : ∀ i < 77, (PL.getD j []).getD i 0 < 2 ^ 7 := fun i hi => by
    rw [← phiL_spec hj i hi]
    exact lt_of_lt_of_le (phiK_lt hexLt4202 _ hi) (by norm_num)
  rw [codeL_eq hb, phiC, pmk_eq (by norm_num) fun i hi => by
    rw [phiL_spec hj i hi]; exact hb i hi]
  exact enc_congr fun i hi => (phiL_spec hj i hi).symm

theorem p5Gens_length : p5Gens.length = 2 := rfl

theorem p5Phi_codes : p5Phi.map code7 = [codeL (PL.getD 0 []), codeL (PL.getD 1 [])] := by
  rw [← code7_phiPerm (j := 0) (by norm_num), ← code7_phiPerm (j := 1) (by norm_num)]
  rfl

theorem b0Perms_codes : b0Perms.map code7 = (List.range 16).map b0C := by
  unfold b0Perms
  rw [List.map_map]
  exact List.map_congr_left fun i _ => code7_b0Perm i

theorem negOK_rW : ∀ w ∈ rW, negOK w = true := by
  have h := ch9686neg
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  exact h.1

theorem negOK_tW (i : ℕ) : negOK (tW.getD i []) = true := by
  have h := ch9686neg
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  by_cases hi : i < tW.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h.2 _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    rfl

theorem rPerms_codes : rPerms.map code7 = rW.map wordC := by
  unfold rPerms
  rw [List.map_map]
  exact List.map_congr_left fun w hw => code7_wordPerm w (negOK_rW w hw)

theorem mem_p5Gens {g : Perm (Fin 22)} (hg : g ∈ p5Gens) : ∃ j < 2, g = p5Gens.getD j 1 := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  rw [p5Gens_length] at hj
  exact ⟨j, hj, (List.getD_eq_getElem _ _ (by rw [p5Gens_length]; exact hj)).symm⟩

theorem p5_closed : closedH (p5Phi.map RN.enc) (bfsSet (p5Phi.map RN.enc) 64) = true := by
  rw [← closedK7_eq h77, p5Phi_codes]
  exact rho_parts.1

theorem r_closed : closedH (rPerms.map RN.enc) (bfsSet (rPerms.map RN.enc) 64) = true := by
  rw [← closedK7_eq h77, rPerms_codes]
  exact rho_parts.2.2.2.2.2.2.2.1

theorem phi_eq' : ∀ g ∈ p5Gens, RN.enc (phiPerm g) = phiRN g := by
  intro g hg
  obtain ⟨j, hj, rfl⟩ := mem_p5Gens hg
  apply rnc7_inj h77
  rw [rnc7_enc, code7_phiPerm hj, rnc7_phiRN hexLt4202, codeL_phiC hj]

theorem card_LamP' : Nat.card LamP = 960 := by
  rw [LamP, card_closure_of_closedH (rawIsEnc 77) p5Phi 64 p5_closed, ← size_bfsK7 h77,
    p5Phi_codes]
  exact rho_parts.2.1

theorem tPerm_not_mem_P2' {i : ℕ} (hi : i < 60) (hi0 : i ≠ 0) : tPerm i ∉ P2 := by
  intro hmem
  rw [P2, mem_closure_iff_H (rawIsEnc 77) rPerms 64 r_closed] at hmem
  have hc := Std.HashSet.contains_iff_mem.2 hmem
  rw [contains_bfsK7 h77, rnc7_enc, rPerms_codes, tPerm, code7_wordPerm _ (negOK_tW i),
    rho_parts.2.2.2.2.2.2.2.2 i hi hi0] at hc
  exact Bool.noConfusion hc

theorem phi_word {j : ℕ} (hj : j < 2) : phiPerm (p5Gens.getD j 1) =
    CFSG.QuasithinUnique.Vol2Native.A312L.PermLat.evalW b0Perms (p5Words.getD j []) := by
  apply code7_inj
  rw [code7_phiPerm hj, ← rnc7_enc, enc_evalW (rawIsEnc 77), rnc7_evalW, map_rnc7_enc,
    b0Perms_codes]
  interval_cases j
  · exact rho_parts.2.2.2.1
  · exact rho_parts.2.2.2.2.1

theorem closure_b0Perms_eq' : Subgroup.closure {p | p ∈ b0Perms} = LamP := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
    rw [SetLike.mem_coe, LamP, mem_closure_iff_H (rawIsEnc 77) p5Phi 64 p5_closed,
      ← Std.HashSet.contains_iff_mem, contains_bfsK7 h77, rnc7_enc, code7_b0Perm, p5Phi_codes]
    exact rho_parts.2.2.1 i (List.mem_range.1 hi)
  · rw [LamP, Subgroup.closure_le]
    intro g hg
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hg
    obtain ⟨j, hj, rfl⟩ := mem_p5Gens hp
    rw [SetLike.mem_coe, phi_word hj]
    exact evalW_mem_closure b0Perms _

end CertificateChecks.KernelJ4ZC9686
