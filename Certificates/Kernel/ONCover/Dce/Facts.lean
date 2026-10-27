module

public import Certificates.Kernel.ONCover.Dce.Walk

public section

namespace CFSG.KD.ONCoverDce3

open CFSG.KC.TwDce2 CFSG.KC.TwDce3 CFSG.CosetTable CFSG.Certificates.TwDce
  CFSG.Certificates.CosetEnumeration CFSG.Sporadic.Recognition.ONMultiplier
  CFSG.LieType.Multipliers CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONCover
open scoped commutatorElement

theorem hgen_lt : ∀ c < 6, onHGen c = 0 ∨ onHGen c = 1 ∨ onHGen c = 2 := by decide

theorem inv_eq : ∀ c < 12, ivL INVM c = if c < 6 then (if c % 2 = 0 then c + 1 else c - 1) else c := by
  decide +kernel

theorem onHGen_congr {d e : ℕ} (h : d / 2 = e / 2) : onHGen d = onHGen e := by
  simp only [onHGen, h]

theorem hinv : ∀ c < 12, ivL INVM c < 12 ∧ onX (ivL INVM c) = (onX c)⁻¹ := by
  intro c hc
  refine ⟨by rw [inv_eq c hc]; split_ifs <;> omega, ?_⟩
  rw [inv_eq c hc]
  by_cases h6 : c < 6
  · rw [if_pos h6]
    by_cases h : c % 2 = 0
    · rw [if_pos h]
      simp only [onX, if_pos h6, if_pos (show c + 1 < 6 by omega), if_pos h,
        if_neg (show ¬ (c + 1) % 2 = 0 by omega), onHGen_congr (show (c + 1) / 2 = c / 2 by omega)]
    · rw [if_neg h]
      simp only [onX, if_pos h6, if_pos (show c - 1 < 6 by omega), if_neg h,
        if_pos (show (c - 1) % 2 = 0 by omega), inv_inv,
        onHGen_congr (show (c - 1) / 2 = c / 2 by omega)]
  · rw [if_neg h6]
    simp [onX, h6]

theorem nt_eq : NT = 4 := by decide +kernel

theorem psf_eq : PSF = idMap := by decide +kernel

theorem psb_eq : PSB = idMap := by decide +kernel

@[expose] noncomputable def lenB (n : ℕ) : ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun _ ih a => (Nat.blt (CFSG.KC.TwDce.wLen (RW a)) 65536 &&
      Nat.blt (CFSG.KC.TwDce.wLen (RA a)) 65536) && ih (a + 1)) n

theorem lenB_sound : ∀ n a, lenB n a = true → ∀ r < n,
    CFSG.KC.TwDce.wLen (RW (a + r)) < 2 ^ 16 ∧ CFSG.KC.TwDce.wLen (RA (a + r)) < 2 ^ 16
  | 0, _, _, r, hr => absurd hr (Nat.not_lt_zero r)
  | n + 1, a, h, r, hr => by
    have h' : ((Nat.blt (CFSG.KC.TwDce.wLen (RW a)) 65536 &&
        Nat.blt (CFSG.KC.TwDce.wLen (RA a)) 65536) && lenB n (a + 1)) = true := h
    simp only [Bool.and_eq_true, Nat.blt_eq] at h'
    rcases r with _ | r
    · exact ⟨h'.1.1, h'.1.2⟩
    · have e := lenB_sound n (a + 1) h'.2 r (by omega)
      rwa [Nat.add_right_comm, Nat.add_assoc] at e

theorem len_ok : lenB 18934 0 = true := by decide +kernel

theorem hlenR : ∀ r < 18934, CFSG.KC.TwDce.wLen (RW r) < 2 ^ 16 ∧
    CFSG.KC.TwDce.wLen (RA r) < 2 ^ 16 := by
  intro r hr
  have e := lenB_sound 18934 0 len_ok r hr
  rwa [Nat.zero_add] at e

noncomputable abbrev relEl (r : List (Fin 4 × Bool)) : onPC :=
  PresentedGroup.mk {r : FreeGroup (Fin 4) | r ∈ mainWs.map FreeGroup.mk} (FreeGroup.mk r)

theorem relEl_one {w : List (Fin 4 × Bool)} (hw : w ∈ cov ++ rsWs) : relEl w = 1 :=
  PresentedGroup.one_of_mem (List.mem_map_of_mem (mem_mainWs_of hw))

theorem relEl_comm {r : List (Fin 4 × Bool)} (hr : r ∈ onRels) (i : Fin 4) :
    Commute (PresentedGroup.of i : onPC) (relEl r) := by
  have h : relEl (commWord [(i, true)] r) = 1 := relEl_one (List.mem_append_left _
    (List.mem_append_left _ (List.mem_flatMap.2 ⟨i, List.mem_finRange _,
      List.mem_map_of_mem (f := fun r => commWord [(i, true)] r) hr⟩)))
  rw [relEl, mk_commWord, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h
  exact h

noncomputable abbrev onU : onPC := PresentedGroup.of 0

noncomputable abbrev onY : onPC := PresentedGroup.of 2

theorem onX_zero : onX 0 = onU := rfl
theorem onX_two : onX 2 = onY := rfl

@[expose] def relU : List (Fin 4 × Bool) := ofCodes [1, 1, 1]

@[expose] def relY : List (Fin 4 × Bool) := ofCodes [5, 5]

@[expose] def relA : List (Fin 4 × Bool) := ofCodes [7, 1, 6, 0]

@[expose] def relB : List (Fin 4 × Bool) := ofCodes [7, 5, 6, 5]

theorem relU_mem : relU ∈ cov ++ rsWs := by decide
theorem relY_mem : relY ∈ cov ++ rsWs := by decide
theorem relA_mem : relA ∈ onRels := by decide
theorem relB_mem : relB ∈ onRels := by decide

theorem relU_eq : relEl relU = onU⁻¹ * (onU⁻¹ * onU⁻¹) := by
  rw [relEl, CFSG.Sporadic.Recognition.CoverTransfer.mk_eq_lift_of, FreeGroup.lift_mk]
  simp only [relU, ofCodes, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rfl

theorem relY_eq : relEl relY = onY⁻¹ * onY⁻¹ := by
  rw [relEl, CFSG.Sporadic.Recognition.CoverTransfer.mk_eq_lift_of, FreeGroup.lift_mk]
  simp only [relY, ofCodes, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rfl

theorem relA_eq : relEl relA = onT⁻¹ * onU⁻¹ * onT * onU := by
  rw [relEl, CFSG.Sporadic.Recognition.CoverTransfer.mk_eq_lift_of, FreeGroup.lift_mk]
  simp only [relA, ofCodes, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    mul_assoc]
  rfl

theorem relB_eq : relEl relB = onT⁻¹ * onY⁻¹ * onT * onY⁻¹ := by
  rw [relEl, CFSG.Sporadic.Recognition.CoverTransfer.mk_eq_lift_of, FreeGroup.lift_mk]
  simp only [relB, ofCodes, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    mul_assoc]
  rfl

theorem u_pow : onU ^ 3 = 1 := by
  have h := relEl_one relU_mem
  rw [relU_eq] at h
  have e : onU ^ 3 = (onU⁻¹ * (onU⁻¹ * onU⁻¹))⁻¹ := by group
  rw [e, h, inv_one]

theorem y_pow : onY ^ 2 = 1 := by
  have h := relEl_one relY_mem
  rw [relY_eq] at h
  have e : onY ^ 2 = (onY⁻¹ * onY⁻¹)⁻¹ := by group
  rw [e, h, inv_one]

theorem eq_one_of_pows {G : Type*} [Group G] {a b : G} (hab : Commute a b) (h3 : a ^ 3 = 1)
    (h2 : b ^ 2 = 1) (h7 : (a * b) ^ 7 = 1) : a = 1 ∧ b = 1 := by
  have ha : a ^ 7 = a := by
    have e : (7 : ℕ) = 3 * 2 + 1 := by norm_num
    rw [e, pow_succ, pow_mul, h3, one_pow, one_mul]
  have hb : b ^ 7 = b := by
    have e : (7 : ℕ) = 2 * 3 + 1 := by norm_num
    rw [e, pow_succ, pow_mul, h2, one_pow, one_mul]
  have hab1 : a * b = 1 := by rw [← h7, hab.mul_pow, ha, hb]
  have hb' : b = a⁻¹ := eq_inv_of_mul_eq_one_right hab1
  have ha2 : a ^ 2 = 1 := by
    rw [hb', inv_pow, inv_eq_one] at h2
    exact h2
  have ha1 : a = 1 := by
    have e : a ^ 3 = a ^ 2 * a := pow_succ a 2
    rw [h3, ha2, one_mul] at e
    exact e.symm
  exact ⟨ha1, by rw [hb', ha1, inv_one]⟩

theorem tconj_pow (g : onPC) : ∀ n : ℕ, (onT⁻¹ * g * onT) ^ n = onT⁻¹ * g ^ n * onT
  | 0 => by simp
  | n + 1 => by rw [pow_succ, tconj_pow g n, pow_succ]; group

theorem comm_relB {r : List (Fin 4 × Bool)} (hr : r ∈ onRels) : Commute (relEl r) (relEl relB) := by
  have ht := (relEl_comm hr 3).symm
  have hy := (relEl_comm hr 2).symm
  rw [relB_eq]
  exact ((ht.inv_right.mul_right hy.inv_right).mul_right ht).mul_right hy.inv_right

theorem hT_of (huy : (onU * onY) ^ 7 = 1) : ∀ c < 4, onX c * onT = onT * onX c := by
  have hyi : onY⁻¹ = onY := inv_eq_of_mul_eq_one_right (by rw [← pow_two, y_pow])
  have hsu : onT⁻¹ * onU * onT = onU * (relEl relA)⁻¹ := by rw [relA_eq]; group
  have hsy : onT⁻¹ * onY * onT = onY * (relEl relB)⁻¹ := by
    have e : onT⁻¹ * onY * onT = onY⁻¹ * (relEl relB)⁻¹ := by rw [relB_eq]; group
    rw [e, hyi]
  have hau : Commute onU (relEl relA)⁻¹ := (relEl_comm relA_mem 0).inv_right
  have hay : Commute onY (relEl relA)⁻¹ := (relEl_comm relA_mem 2).inv_right
  have hbu : Commute onU (relEl relB)⁻¹ := (relEl_comm relB_mem 0).inv_right
  have hby : Commute onY (relEl relB)⁻¹ := (relEl_comm relB_mem 2).inv_right
  have hab : Commute (relEl relA)⁻¹ (relEl relB)⁻¹ := (comm_relB relA_mem).inv_inv
  have h3 : ((relEl relA)⁻¹) ^ 3 = 1 := by
    have e := tconj_pow onU 3
    rw [hsu, hau.mul_pow, u_pow, one_mul] at e
    rw [e]
    group
  have h2 : ((relEl relB)⁻¹) ^ 2 = 1 := by
    have e := tconj_pow onY 2
    rw [hsy, hby.mul_pow, y_pow, one_mul] at e
    rw [e]
    group
  have hc : onT⁻¹ * (onU * onY) * onT = (onU * onY) * ((relEl relA)⁻¹ * (relEl relB)⁻¹) := by
    calc onT⁻¹ * (onU * onY) * onT = (onT⁻¹ * onU * onT) * (onT⁻¹ * onY * onT) := by group
      _ = onU * (relEl relA)⁻¹ * (onY * (relEl relB)⁻¹) := by rw [hsu, hsy]
      _ = onU * (onY * (relEl relA)⁻¹) * (relEl relB)⁻¹ := by rw [hay.eq]; group
      _ = (onU * onY) * ((relEl relA)⁻¹ * (relEl relB)⁻¹) := by group
  have h7 : ((relEl relA)⁻¹ * (relEl relB)⁻¹) ^ 7 = 1 := by
    have e := tconj_pow (onU * onY) 7
    rw [hc, ((hau.mul_left hay).mul_right (hbu.mul_left hby)).mul_pow, huy, one_mul] at e
    rw [e]
    group
  obtain ⟨ha1, hb1⟩ := eq_one_of_pows hab h3 h2 h7
  have cu : onU * onT = onT * onU := by
    calc onU * onT = onT * (onT⁻¹ * onU * onT) := by group
      _ = onT * onU := by rw [hsu, ha1, mul_one]
  have cy : onY * onT = onT * onY := by
    calc onY * onT = onT * (onT⁻¹ * onY * onT) := by group
      _ = onT * onY := by rw [hsy, hb1, mul_one]
  intro c hc4
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega) with rfl | rfl | rfl | rfl
  · exact cu
  · exact (Commute.inv_left cu)
  · exact cy
  · exact (Commute.inv_left cy)

theorem uy7_fix : ∀ i < NB, [0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2].foldl
    (fun p c => CFSG.KC.YModel.fieldAt PB (F c) p) (CFSG.KC.TwDce.fld BS (16 * i) 65535) =
      CFSG.KC.TwDce.fld BS (16 * i) 65535 := by
  decide +kernel

end CFSG.KD.ONCoverDce3

end
