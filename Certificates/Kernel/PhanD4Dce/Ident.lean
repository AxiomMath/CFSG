module

public import Certificates.Kernel.PhanD4Dce.Residue
public import Certificates.Kernel.PhanD4Dce.FoldQ0
public import Certificates.Kernel.PhanD4Dce.FoldQ1
public import Certificates.Kernel.PhanD4Dce.FoldQ2
public import Certificates.Kernel.PhanD4Dce.FoldQ3
public import Certificates.Kernel.PhanD4Dce.FoldQ4
public import Certificates.Kernel.PhanD4Dce.FoldQ5
public import Certificates.Kernel.PhanD4Dce.FoldQ6
public import Certificates.Kernel.PhanD4Dce.FoldQ7
public import Certificates.Kernel.PhanD4Dce.FoldQ8
public import Certificates.Kernel.PhanD4Dce.FoldQ9
public import Certificates.Kernel.PhanD4Dce.FoldQ10
public import Certificates.Kernel.PhanD4Dce.FoldQ11
public import Certificates.Kernel.PhanD4Dce.FoldQ12
public import Certificates.Kernel.PhanD4Dce.FoldQ13
public import Certificates.Kernel.PhanD4Dce.FoldQ14
public import Certificates.Kernel.PhanD4Dce.FoldQ15
public import Certificates.Kernel.PhanD4Dce.FoldQ16
public import Certificates.Kernel.PhanD4Dce.FoldQ17
public import Certificates.Kernel.PhanD4Dce.TabRels
public import Certificates.Kernel.PhanD4Dce.Stab0
public import CFSG.Certificates.Kernel.TwistDce3.Fold
public import CFSG.Certificates.Kernel.TwistDce3.FoldQ
public import CFSG.Certificates.Kernel.TwistDce3.Sound
public import CFSG.Certificates.Kernel.TwistDce3.ChainPSound

public section

namespace CFSG.KD.PhanD4Dce

open CFSG.KC.TwDce2 CFSG.KC.TwDce3 CFSG.CosetTable CFSG.Certificates.CosetEnumeration
  CFSG.KC.YModel CFSG.Certificates.TwDce CFSG.ClassicalInvolution.Phan.Q3G
open CFSG.Certificates.TwDce2 (wdVal)
open CFSG.Certificates.TwDce2.ChainB (chainLens)

theorem foldRange_add (m : ℕ) : ∀ n a S,
    foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ a (n + m) S =
    foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ (a + n) m
      (foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ a n S)
  | 0, a, S => by simp only [Nat.zero_add, Nat.add_zero]; rfl
  | n + 1, a, S => by
    have e1 : n + 1 + m = (n + m) + 1 := by omega
    have e2 : a + 1 + n = a + (n + 1) := by omega
    rw [e1, CFSG.Certificates.TwDce3.Fold.foldRange_succ, foldRange_add m n (a + 1),
      CFSG.Certificates.TwDce3.Fold.foldRange_succ, e2]

theorem fold_step {n m k S S' : ℕ}
    (h : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 0 n 1 = S)
    (hp : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ n m S = S') (hk : n + m = k) :
    foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 0 k 1 = S' := by
  rw [← hk, foldRange_add m n 0 1, h, Nat.zero_add, hp]

theorem nb_eq : NB = 3 := by decide +kernel

theorem fq (a n S S' : ℕ) (h : CFSG.KC.TwDce3Q.foldIs (CFSG.KC.TwDce3Q.isOneQ PB F BS)
    INVM NT PSF PSB RD RW RA WD RJ a n S S' = true) :
    foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ a n S = S' :=
  CFSG.Certificates.TwDce3.FoldQ.fold_of PB F INVM BS NB NT PSF PSB RD RW RA WD RJ nb_eq h

theorem fold0 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 0 925 1 = 21 :=
  fq 0 925 1 21 foldq0
theorem fold1 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 925 925 21 = 33 :=
  fq 925 925 21 33 foldq1
theorem fold2 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 1850 925 33 = 42 :=
  fq 1850 925 33 42 foldq2
theorem fold3 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 2775 925 42 = 49 :=
  fq 2775 925 42 49 foldq3
theorem fold4 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 3700 925 49 = 56 :=
  fq 3700 925 49 56 foldq4
theorem fold5 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 4625 925 56 = 61 :=
  fq 4625 925 56 61 foldq5
theorem fold6 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 5550 925 61 = 66 :=
  fq 5550 925 61 66 foldq6
theorem fold7 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 6475 925 66 = 71 :=
  fq 6475 925 66 71 foldq7
theorem fold8 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 7400 925 71 = 75 :=
  fq 7400 925 71 75 foldq8
theorem fold9 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 8325 925 75 = 79 :=
  fq 8325 925 75 79 foldq9
theorem fold10 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 9250 925 79 = 82 :=
  fq 9250 925 79 82 foldq10
theorem fold11 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 10175 925 82 = 86 :=
  fq 10175 925 82 86 foldq11
theorem fold12 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 11100 925 86 = 89 :=
  fq 11100 925 86 89 foldq12
theorem fold13 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 12025 925 89 = 95 :=
  fq 12025 925 89 95 foldq13
theorem fold14 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 12950 925 95 = 106 :=
  fq 12950 925 95 106 foldq14
theorem fold15 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 13875 925 106 = 117 :=
  fq 13875 925 106 117 foldq15
theorem fold16 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 14800 925 117 = 127 :=
  fq 14800 925 117 127 foldq16
theorem fold17 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 15725 900 127 = 138 :=
  fq 15725 900 127 138 foldq17

theorem fold_ok : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 0 16625 1 = 138 := by
  have h1 := fold_step (k := 1850) fold0 fold1 (by norm_num)
  have h2 := fold_step (k := 2775) h1 fold2 (by norm_num)
  have h3 := fold_step (k := 3700) h2 fold3 (by norm_num)
  have h4 := fold_step (k := 4625) h3 fold4 (by norm_num)
  have h5 := fold_step (k := 5550) h4 fold5 (by norm_num)
  have h6 := fold_step (k := 6475) h5 fold6 (by norm_num)
  have h7 := fold_step (k := 7400) h6 fold7 (by norm_num)
  have h8 := fold_step (k := 8325) h7 fold8 (by norm_num)
  have h9 := fold_step (k := 9250) h8 fold9 (by norm_num)
  have h10 := fold_step (k := 10175) h9 fold10 (by norm_num)
  have h11 := fold_step (k := 11100) h10 fold11 (by norm_num)
  have h12 := fold_step (k := 12025) h11 fold12 (by norm_num)
  have h13 := fold_step (k := 12950) h12 fold13 (by norm_num)
  have h14 := fold_step (k := 13875) h13 fold14 (by norm_num)
  have h15 := fold_step (k := 14800) h14 fold15 (by norm_num)
  have h16 := fold_step (k := 15725) h15 fold16 (by norm_num)
  exact fold_step h16 fold17 (by norm_num)

theorem nt_eq : NT = 8 := by decide +kernel

theorem pb_eq : PB = 12 := by decide +kernel

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

theorem len_ok : lenB 16625 0 = true := by decide +kernel

theorem hlenR : ∀ r < 16625, CFSG.KC.TwDce.wLen (RW r) < 2 ^ 16 ∧
    CFSG.KC.TwDce.wLen (RA r) < 2 ^ 16 := by
  intro r hr
  have e := lenB_sound 16625 0 len_ok r hr
  rwa [Nat.zero_add] at e

@[expose] noncomputable def belowB (n : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih a => wBelow 12 (RW a) && ih (a + 1)) n

theorem belowB_sound : ∀ n a, belowB n a = true → ∀ r < n, wBelow 12 (RW (a + r)) = true
  | 0, _, _, r, hr => absurd hr (Nat.not_lt_zero r)
  | n + 1, a, h, r, hr => by
    have h' : (wBelow 12 (RW a) && belowB n (a + 1)) = true := h
    rw [Bool.and_eq_true] at h'
    rcases r with _ | r
    · exact h'.1
    · have e := belowB_sound n (a + 1) h'.2 r (by omega)
      rwa [Nat.add_right_comm, Nat.add_assoc] at e

theorem below_ok : belowB 16625 0 = true := by decide +kernel

theorem rw_below : ∀ r < 16625, wBelow 12 (RW r) = true := by
  intro r hr
  have e := belowB_sound 16625 0 below_ok r hr
  rwa [Nat.zero_add] at e

abbrev PC : Type := PhanD4Group

@[expose] def lGen (c : ℕ) : Fin 6 := ⟨[0, 1, 4, 5, 2, 3].getD (c / 2) 0 % 6, Nat.mod_lt _ (by norm_num)⟩

@[expose] noncomputable def onX (c : ℕ) : PC :=
  if c < 12 then (if c % 2 = 0 then a3Gens (lGen c) else (a3Gens (lGen c))⁻¹) else 1

noncomputable abbrev onT : PC := PresentedGroup.of 7

theorem inv_eq : ∀ c < 12, ivL INVM c = if c % 2 = 0 then c + 1 else c - 1 := by
  decide +kernel

theorem lGen_congr {d e : ℕ} (h : d / 2 = e / 2) : lGen d = lGen e := by
  simp only [lGen, h]

theorem ivl_lt {c : ℕ} (hc : c < 12) : ivL INVM c < 12 := by
  rw [inv_eq c hc]
  split_ifs <;> omega

theorem hinv : ∀ c < 12, ivL INVM c < 12 ∧ onX (ivL INVM c) = (onX c)⁻¹ := by
  intro c hc
  refine ⟨ivl_lt hc, ?_⟩
  rw [inv_eq c hc]
  by_cases h : c % 2 = 0
  · rw [if_pos h]
    simp only [onX, if_pos hc, if_pos (by omega : c + 1 < 12), if_pos h,
      if_neg (by omega : ¬ (c + 1) % 2 = 0), lGen_congr (by omega : (c + 1) / 2 = c / 2)]
  · rw [if_neg h]
    simp only [onX, if_pos hc, if_pos (by omega : c - 1 < 12), if_neg h,
      if_pos (by omega : (c - 1) % 2 = 0), inv_inv, lGen_congr (by omega : (c - 1) / 2 = c / 2)]

theorem a3Gens_mem (i : Fin 6) : a3Gens i ∈ phanR := Subgroup.subset_closure ⟨i, rfl⟩

theorem hxH : ∀ c < 12, onX c ∈ phanR := by
  intro c hc
  rw [onX, if_pos hc]
  split_ifs
  · exact a3Gens_mem _
  · exact phanR.inv_mem (a3Gens_mem _)

theorem rel_of {w : List ℕ} {l : List (Fin 8 × Bool)} (hw : w ∈ d4RankTwoCodes)
    (hl : decodeWord 8 w = l) : (l.map (letterVal fun i => (PresentedGroup.of i : PC))).prod = 1 := by
  rw [← hl]
  exact wordVal_rel (List.mem_append_left _ (List.mem_map_of_mem hw))

theorem a3_eq : (PresentedGroup.of 6 : PC) =
    PresentedGroup.of 2 * onT * (PresentedGroup.of 2)⁻¹ * onT := by
  have h := rel_of (w := [4, 14, 5, 14, 13])
    (l := [(2, true), (7, true), (2, false), (7, true), (6, false)]) (by decide) (by decide)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, letterVal, cond_true,
    cond_false, mul_one] at h
  calc (PresentedGroup.of 6 : PC) =
        ((PresentedGroup.of 2 : PC) * (PresentedGroup.of 7 * ((PresentedGroup.of 2)⁻¹ *
          (PresentedGroup.of 7 * (PresentedGroup.of 6)⁻¹))))⁻¹ *
        (PresentedGroup.of 2 * onT * (PresentedGroup.of 2)⁻¹ * onT) := by group
    _ = _ := by rw [h, inv_one, one_mul]

theorem comm_t {i : Fin 8} (h : (PresentedGroup.of i : PC) * (PresentedGroup.of 7 *
    ((PresentedGroup.of i)⁻¹ * ((PresentedGroup.of 7)⁻¹ * 1))) = 1) :
    (PresentedGroup.of i : PC) * onT = onT * PresentedGroup.of i :=
  calc (PresentedGroup.of i : PC) * onT = (PresentedGroup.of i * (PresentedGroup.of 7 *
        ((PresentedGroup.of i)⁻¹ * ((PresentedGroup.of 7)⁻¹ * 1)))) * onT * PresentedGroup.of i := by
        group
    _ = onT * PresentedGroup.of i := by rw [h, one_mul]

theorem comm_a0 : (PresentedGroup.of 0 : PC) * onT = onT * PresentedGroup.of 0 := by
  have h := rel_of (w := [0, 14, 1, 15]) (l := [(0, true), (7, true), (0, false), (7, false)])
    (by decide) (by decide)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, letterVal, cond_true,
    cond_false] at h
  exact comm_t h

theorem comm_b0 : (PresentedGroup.of 1 : PC) * onT = onT * PresentedGroup.of 1 := by
  have h := rel_of (w := [2, 14, 3, 15]) (l := [(1, true), (7, true), (1, false), (7, false)])
    (by decide) (by decide)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, letterVal, cond_true,
    cond_false] at h
  exact comm_t h

theorem comm_a2 : (PresentedGroup.of 4 : PC) * onT = onT * PresentedGroup.of 4 := by
  have h := rel_of (w := [8, 14, 9, 15]) (l := [(4, true), (7, true), (4, false), (7, false)])
    (by decide) (by decide)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, letterVal, cond_true,
    cond_false] at h
  exact comm_t h

theorem comm_b2 : (PresentedGroup.of 5 : PC) * onT = onT * PresentedGroup.of 5 := by
  have h := rel_of (w := [10, 14, 11, 15]) (l := [(5, true), (7, true), (5, false), (7, false)])
    (by decide) (by decide)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, letterVal, cond_true,
    cond_false] at h
  exact comm_t h

theorem onX_0 : onX 0 = (PresentedGroup.of 0 : PC) := rfl
theorem onX_1 : onX 1 = (PresentedGroup.of 0 : PC)⁻¹ := rfl
theorem onX_2 : onX 2 = (PresentedGroup.of 1 : PC) := rfl
theorem onX_3 : onX 3 = (PresentedGroup.of 1 : PC)⁻¹ := rfl
theorem onX_4 : onX 4 = (PresentedGroup.of 4 : PC) := rfl
theorem onX_5 : onX 5 = (PresentedGroup.of 4 : PC)⁻¹ := rfl
theorem onX_6 : onX 6 = (PresentedGroup.of 5 : PC) := rfl
theorem onX_7 : onX 7 = (PresentedGroup.of 5 : PC)⁻¹ := rfl
theorem onX_8 : onX 8 = (PresentedGroup.of 2 : PC) := rfl
theorem onX_9 : onX 9 = (PresentedGroup.of 2 : PC)⁻¹ := rfl
theorem onX_10 : onX 10 = (PresentedGroup.of 3 : PC) := rfl
theorem onX_11 : onX 11 = (PresentedGroup.of 3 : PC)⁻¹ := rfl

theorem hT : ∀ c < 8, onX c * onT = onT * onX c := by
  intro c hc
  have hc' : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 := by omega
  rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact comm_a0
  · exact Commute.inv_left comm_a0
  · exact comm_b0
  · exact Commute.inv_left comm_b0
  · exact comm_a2
  · exact Commute.inv_left comm_a2
  · exact comm_b2
  · exact Commute.inv_left comm_b2

theorem hgen : Subgroup.closure ((phanR : Set PC) ∪ {onT}) = ⊤ := by
  rw [eq_top_iff, ← PresentedGroup.closure_range_of, Subgroup.closure_le]
  have hsub : (phanR : Set PC) ⊆ Subgroup.closure ((phanR : Set PC) ∪ {onT}) :=
    fun x hx => Subgroup.subset_closure (Or.inl hx)
  have ht : onT ∈ Subgroup.closure ((phanR : Set PC) ∪ {onT}) :=
    Subgroup.subset_closure (Or.inr rfl)
  rintro _ ⟨⟨j, hj⟩, rfl⟩
  by_cases h6 : j < 6
  · exact hsub (a3Gens_mem ⟨j, h6⟩)
  by_cases h7 : j = 6
  · subst h7
    have h2 := hsub (a3Gens_mem 2)
    change (PresentedGroup.of 6 : PC) ∈ _
    rw [a3_eq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h2 ht)
      (Subgroup.inv_mem _ h2)) ht
  · have e : j = 7 := by omega
    subst e
    exact ht

@[expose] def topCodes : List (List ℕ) :=
  [[12, 12, 12], [10, 12, 11, 12, 10, 13], [8, 8, 12, 9, 12, 9, 13, 8, 13, 9],
   [8, 13, 8, 13, 9, 11, 8, 12, 9, 12, 11]]

theorem wdVal_lt {c : ℕ} (hc : c < 12) : wdVal onX onT c = onX c := by
  simp [wdVal, hc]

theorem wdVal_12 : wdVal onX onT 12 = onT := by simp [wdVal]

theorem wdVal_13 : wdVal onX onT 13 = onT⁻¹ := by simp [wdVal]

theorem top_one : ∀ r ∈ topCodes, evalWord (wdVal onX onT) r = 1 := by
  intro r hr
  simp only [topCodes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · have h := rel_of (w := [14, 14, 14]) (l := [(7, true), (7, true), (7, true)]) (by decide)
      (by decide)
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, letterVal, cond_true,
      mul_one] at h
    simp only [evalWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      wdVal_12]
    exact h
  · have h := rel_of (w := [6, 14, 7, 14, 6, 15])
      (l := [(3, true), (7, true), (3, false), (7, true), (3, true), (7, false)]) (by decide)
      (by decide)
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, letterVal, cond_true,
      cond_false, mul_one] at h
    simp only [evalWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      wdVal_12, wdVal_13, wdVal_lt (by norm_num : 10 < 12), wdVal_lt (by norm_num : 11 < 12),
      onX_10, onX_11]
    exact h
  · have h := rel_of (w := [4, 12, 5, 13])
      (l := [(2, true), (6, true), (2, false), (6, false)]) (by decide) (by decide)
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, letterVal, cond_true,
      cond_false, mul_one] at h
    rw [a3_eq] at h
    simp only [evalWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      wdVal_12, wdVal_13, wdVal_lt (by norm_num : 8 < 12), wdVal_lt (by norm_num : 9 < 12),
      onX_8, onX_9]
    rw [← h]
    group
  · have h := rel_of (w := [4, 13, 7, 12, 7])
      (l := [(2, true), (6, false), (3, false), (6, true), (3, false)]) (by decide) (by decide)
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, letterVal, cond_true,
      cond_false, mul_one] at h
    rw [a3_eq] at h
    simp only [evalWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      wdVal_12, wdVal_13, wdVal_lt (by norm_num : 8 < 12), wdVal_lt (by norm_num : 9 < 12),
      wdVal_lt (by norm_num : 11 < 12), onX_8, onX_9, onX_11]
    rw [← h]
    group

@[expose] def wdShape (w : ℕ) : Prop :=
  CFSG.KC.TwDce.wLen w < 2 ^ 12 ∧ (∀ c ∈ wList w, c < 15) ∧
    ((wList w).filter (· != 14) = [] ∨ (wList w).filter (· != 14) = [12, 13] ∨
      (wList w).filter (· != 14) = [13, 12] ∨
      ∃ r ∈ topCodes, r.length = ((wList w).filter (· != 14)).length ∧
        (wList w).filter (· != 14) ∈ rotations r)

@[expose] noncomputable def modB (n : ℕ) : ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun _ ih a => Nat.beq (WD a) (WD (a % 32)) && ih (a + 1)) n

theorem modB_sound : ∀ n a, modB n a = true → ∀ r < n, WD (a + r) = WD ((a + r) % 32)
  | 0, _, _, r, hr => absurd hr (Nat.not_lt_zero r)
  | n + 1, a, h, r, hr => by
    have h' : (Nat.beq (WD a) (WD (a % 32)) && modB n (a + 1)) = true := h
    simp only [Bool.and_eq_true] at h'
    rcases r with _ | r
    · exact Nat.eq_of_beq_eq_true h'.1
    · have e := modB_sound n (a + 1) h'.2 r (by omega)
      rwa [Nat.add_right_comm, Nat.add_assoc] at e

theorem mod_ok : modB 4064 32 = true := by decide +kernel

theorem wd_mod : ∀ i < 4096, WD i = WD (i % 32) := by
  intro i hi
  by_cases h : i < 32
  · rw [Nat.mod_eq_of_lt h]
  · have e := modB_sound 4064 32 mod_ok (i - 32) (by omega)
    rwa [Nat.add_sub_cancel' (by omega)] at e

theorem wd_ok32 : ∀ i < 32, wdShape (WD i) := by
  unfold wdShape
  decide +kernel

theorem wdVal_filter : ∀ l : List ℕ,
    evalWord (wdVal onX onT) l = evalWord (wdVal onX onT) (l.filter (· != 14))
  | [] => rfl
  | c :: l => by
    by_cases h : c = 14
    · subst h
      rw [List.filter_cons_of_neg (by decide), evalWord_cons, ← wdVal_filter l]
      simp [wdVal]
    · rw [List.filter_cons_of_pos (by simpa using h), evalWord_cons, evalWord_cons,
        wdVal_filter l]

theorem hWD : ∀ i < 4096, CFSG.KC.TwDce.wLen (WD i) < 2 ^ 12 ∧ (∀ c ∈ wList (WD i), c < 15) ∧
    evalWord (wdVal onX onT) (wList (WD i)) = 1 := by
  intro i hi
  rw [wd_mod i hi]
  obtain ⟨h1, h2, h3⟩ := wd_ok32 _ (Nat.mod_lt i (by norm_num))
  refine ⟨h1, h2, ?_⟩
  rw [wdVal_filter]
  rcases h3 with h | h | h | ⟨r, hr, -, hv⟩
  · rw [h]; rfl
  · rw [h]; simp [evalWord, wdVal]
  · rw [h]; simp [evalWord, wdVal]
  · exact CFSG.CosetTable.evalWord_rotation hv (top_one r hr)

@[expose] def hcode (i : Fin 6) : ℕ := [0, 2, 8, 10, 4, 6].getD i.val 0

@[expose] def a3Letter (l : Fin 6 × Bool) : ℕ := hcode l.1 + cond l.2 0 1

theorem hcode_lt : ∀ i : Fin 6, hcode i < 12 := by decide

theorem hcode_inv : ∀ i : Fin 6, ivL INVM (hcode i) = hcode i + 1 := by decide +kernel

theorem hcode_lGen : ∀ c < 12, hcode (lGen c) + c % 2 = c := by decide

theorem codes_eq : (phanA3Rels ++ [phanA3U1, phanA3U2]).map (List.map a3Letter) = a3CodesL := by
  decide +kernel

theorem codes_len : ∀ w ∈ a3CodesL, w.length < 2 ^ 32 := by decide

theorem codes_mem {w : List (Fin 6 × Bool)} (hw : w ∈ phanA3Rels ++ [phanA3U1, phanA3U2]) :
    w.map a3Letter ∈ a3CodesL := by
  rw [← codes_eq]
  exact List.mem_map_of_mem hw

abbrev QB : Type := PhanA3Group ⧸ phanP.ker

section Act

variable {PB' NP : ℕ} {Tb : ℕ → ℕ} (hL : lettersOK PB' Tb INVM 12 NP = true)
  (hR : relsOK PB' Tb NP a3CodesL = true)

include hL in
theorem tb_lt : ∀ c < 12, ∀ p < NP, fieldAt PB' (Tb c) p < NP :=
  fun c hc p hp => ((CFSG.Certificates.TwDce3.lettersOK_sound hL c hc).2 p hp).1

include hL in
theorem tb_inv : ∀ c < 12, ∀ p < NP, fieldAt PB' (Tb (ivL INVM c)) (fieldAt PB' (Tb c) p) = p :=
  fun c hc p hp => ((CFSG.Certificates.TwDce3.lettersOK_sound hL c hc).2 p hp).2

@[expose] noncomputable def permT (c : ℕ) (hc : c < 12) : Equiv.Perm (Fin NP) where
  toFun p := ⟨fieldAt PB' (Tb c) p, tb_lt hL c hc p p.2⟩
  invFun p := ⟨fieldAt PB' (Tb (ivL INVM c)) p, tb_lt hL _ (ivl_lt hc) p p.2⟩
  left_inv p := Fin.ext (tb_inv hL c hc p p.2)
  right_inv q := by
    have hinj : Function.Injective (fun p : Fin NP =>
        (⟨fieldAt PB' (Tb c) p, tb_lt hL c hc p p.2⟩ : Fin NP)) := by
      intro p p' e
      have e' := congrArg (fun r : Fin NP => fieldAt PB' (Tb (ivL INVM c)) r.val) e
      simp only at e'
      rw [tb_inv hL c hc p p.2, tb_inv hL c hc p' p'.2] at e'
      exact Fin.ext e'
    obtain ⟨p, rfl⟩ := Finite.injective_iff_surjective.1 hinj q
    exact Fin.ext (congrArg (fieldAt PB' (Tb c)) (tb_inv hL c hc p p.2))

@[expose] noncomputable def gT (i : Fin 6) : (Equiv.Perm (Fin NP))ᵐᵒᵖ :=
  MulOpposite.op (permT hL (hcode i) (hcode_lt i))

theorem letterVal_apply (l : Fin 6 × Bool) (p : Fin NP) :
    ((letterVal (gT hL) l).unop p).val = fieldAt PB' (Tb (a3Letter l)) p.val := by
  obtain ⟨i, _ | _⟩ := l
  · simp only [letterVal, cond_false, a3Letter, gT, MulOpposite.unop_inv, MulOpposite.unop_op,
      Equiv.Perm.inv_def]
    rw [← hcode_inv i]
    rfl
  · simp only [letterVal, cond_true, a3Letter, gT, MulOpposite.unop_op, Nat.add_zero]
    rfl

theorem wordVal_apply : ∀ (w : List (Fin 6 × Bool)) (p : Fin NP),
    ((wordVal (gT hL) w).unop p).val =
      (w.map a3Letter).foldl (fun q c => fieldAt PB' (Tb c) q) p.val
  | [], _ => rfl
  | l :: w, p => by
    have e : wordVal (gT hL) (l :: w) = letterVal (gT hL) l * wordVal (gT hL) w := by
      simp [wordVal]
    rw [e, MulOpposite.unop_mul, Equiv.Perm.mul_apply, wordVal_apply w, List.map_cons,
      List.foldl_cons, letterVal_apply]

include hR in
theorem wordVal_gT_one {w : List (Fin 6 × Bool)} (hw : w ∈ phanA3Rels ++ [phanA3U1, phanA3U2]) :
    wordVal (gT hL) w = 1 := by
  apply MulOpposite.unop_injective
  ext p
  rw [wordVal_apply]
  exact (CFSG.Certificates.TwDce3.relsOK_sound hR codes_len _ (codes_mem hw)).2 p p.2

@[expose] noncomputable def rhoT : PhanA3Group →* (Equiv.Perm (Fin NP))ᵐᵒᵖ :=
  assignHom (gT hL) fun w hw => wordVal_gT_one hL hR (List.mem_append_left _ hw)

include hR in
theorem rhoT_u1 : rhoT hL hR u1 = 1 :=
  (assignHom_mk _ _ _).trans (wordVal_gT_one hL hR (by simp))

include hR in
theorem rhoT_u2 : rhoT hL hR u2 = 1 :=
  (assignHom_mk _ _ _).trans (wordVal_gT_one hL hR (by simp))

end Act

section Cert

theorem ker_le_of {X : Type*} [Group X] (φ : PhanA3Group →* X) (h1 : φ u1 = 1) (h2 : φ u2 = 1) :
    phanP.ker ≤ φ.ker := by
  have : Finite PhanA3Group := card_phanA3Group_le.1
  let f : Fin 3 × Fin 3 → phanP.ker := fun ij =>
    ⟨u1 ^ (ij.1.val : ℤ) * u2 ^ (ij.2.val : ℤ), by
      rw [MonoidHom.mem_ker, map_mul, map_zpow, map_zpow, u1, u2, phanP_mk_u1, phanP_mk_u2,
        one_zpow, one_zpow, mul_one]⟩
  have hinj : Function.Injective f := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hij
    have h : u1 ^ (i.val : ℤ) * u2 ^ (j.val : ℤ) =
        u1 ^ (i'.val : ℤ) * u2 ^ (j'.val : ℤ) := congrArg Subtype.val hij
    have h1 : u1 ^ ((i.val : ℤ) - i'.val) * u2 ^ ((j.val : ℤ) - j'.val) = 1 := by
      calc u1 ^ ((i.val : ℤ) - i'.val) * u2 ^ ((j.val : ℤ) - j'.val)
          = u1 ^ (-(i'.val : ℤ)) * (u1 ^ (i.val : ℤ) * u2 ^ (j.val : ℤ)) *
              u2 ^ (-(j'.val : ℤ)) := by group
        _ = u1 ^ (-(i'.val : ℤ)) * (u1 ^ (i'.val : ℤ) * u2 ^ (j'.val : ℤ)) *
              u2 ^ (-(j'.val : ℤ)) := by rw [h]
        _ = 1 := by group
    by_contra hne
    have hi := i.isLt
    have hi' := i'.isLt
    have hj := j.isLt
    have hj' := j'.isLt
    refine u_ne_one (s := (i.val : ℤ) - i'.val) (t := (j.val : ℤ) - j'.val)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ?_ h1
    intro hst
    simp only [Prod.mk.injEq] at hst
    obtain ⟨hs0, ht0⟩ := hst
    have e1 : i = i' := Fin.ext (by omega)
    have e2 : j = j' := Fin.ext (by omega)
    exact hne (by rw [e1, e2])
  have hbij : Function.Bijective f :=
    hinj.bijective_of_nat_card_le (by rw [card_ker_eq]; simp)
  intro e he
  obtain ⟨⟨i, j⟩, hij⟩ := hbij.2 ⟨e, he⟩
  have he' : e = u1 ^ (i.val : ℤ) * u2 ^ (j.val : ℤ) := (congrArg Subtype.val hij).symm
  rw [MonoidHom.mem_ker, he', map_mul, map_zpow, map_zpow, h1, h2, one_zpow, one_zpow, mul_one]

instance finite_QB : Finite QB := by
  have : Finite PhanA3Group := card_phanA3Group_le.1
  exact Finite.of_surjective _ QuotientGroup.mk_surjective

theorem card_QB : Nat.card QB = 13063680 := by
  rw [← card_su4]
  exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective phanP phanP_surjective).toEquiv

@[expose] noncomputable def piB : QB →* PC := QuotientGroup.lift _ a3Hom ker_le

@[expose] noncomputable def xQ (c : ℕ) : PhanA3Group :=
  if c < 12 then (if c % 2 = 0 then PresentedGroup.of (lGen c) else (PresentedGroup.of (lGen c))⁻¹)
  else 1

@[expose] noncomputable def xD (c : ℕ) : QB := (xQ c : QB)

theorem a3Hom_of (i : Fin 6) : a3Hom (PresentedGroup.of i) = a3Gens i := by
  unfold a3Hom assignHom
  exact PresentedGroup.toGroup.of _

theorem piB_xD (c : ℕ) : piB (xD c) = onX c := by
  rw [xD, piB, QuotientGroup.lift_mk, xQ, onX]
  split_ifs
  · exact a3Hom_of _
  · rw [map_inv, a3Hom_of]
  · exact map_one _

theorem range_piB : piB.range = phanR := by
  rw [← range_a3Hom]
  ext g
  constructor
  · rintro ⟨q, rfl⟩
    induction q using QuotientGroup.induction_on with
    | H q => exact ⟨q, rfl⟩
  · rintro ⟨q, rfl⟩
    exact ⟨(q : QB), QuotientGroup.lift_mk _ _ _⟩

theorem evalWord_onX (w : List ℕ) : evalWord onX w = piB (evalWord xD w) := by
  simp only [evalWord, map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun c _ => (piB_xD c).symm

section Act

variable {PB' NP : ℕ} {Tb : ℕ → ℕ} (hL : lettersOK PB' Tb INVM 12 NP = true)
  (hR : relsOK PB' Tb NP a3CodesL = true)

@[expose] noncomputable def rhoB : QB →* (Equiv.Perm (Fin NP))ᵐᵒᵖ :=
  QuotientGroup.lift _ (rhoT hL hR) (ker_le_of _ (rhoT_u1 hL hR) (rhoT_u2 hL hR))

@[expose] noncomputable def ptT (q : QB) (p : ℕ) : ℕ :=
  if h : p < NP then ((rhoB hL hR q).unop ⟨p, h⟩).val else p

theorem ptT_of_lt (q : QB) {p : ℕ} (hp : p < NP) :
    ptT hL hR q p = ((rhoB hL hR q).unop ⟨p, hp⟩).val :=
  dif_pos hp

theorem ptT_lt (q : QB) {p : ℕ} (hp : p < NP) : ptT hL hR q p < NP := by
  rw [ptT_of_lt _ _ _ hp]
  exact Fin.isLt _

theorem ptT_one (p : ℕ) : ptT hL hR 1 p = p := by
  by_cases h : p < NP
  · rw [ptT_of_lt _ _ _ h, map_one]
    rfl
  · exact dif_neg h

theorem ptT_mul (a b : QB) (p : ℕ) : ptT hL hR (a * b) p = ptT hL hR b (ptT hL hR a p) := by
  by_cases h : p < NP
  · rw [ptT_of_lt _ _ _ h, ptT_of_lt _ _ a h, ptT_of_lt _ _ _ (Fin.isLt _), map_mul,
      MulOpposite.unop_mul, Equiv.Perm.mul_apply]
  · simp [ptT, h]

theorem hxT : ∀ c < 12, ∀ p < NP, fieldAt PB' (Tb c) p = ptT hL hR (xD c) p := by
  intro c hc p hp
  rw [ptT_of_lt _ _ _ hp, xD, rhoB, QuotientGroup.lift_mk, xQ, if_pos hc]
  have e := hcode_lGen c hc
  split_ifs with h
  · rw [rhoT, assignHom, PresentedGroup.toGroup.of]
    rw [h, Nat.add_zero] at e
    change fieldAt PB' (Tb c) p = fieldAt PB' (Tb (hcode (lGen c))) p
    rw [e]
  · rw [map_inv, rhoT, assignHom, PresentedGroup.toGroup.of]
    have h1 : c % 2 = 1 := by omega
    rw [h1] at e
    change fieldAt PB' (Tb c) p = fieldAt PB' (Tb (ivL INVM (hcode (lGen c)))) p
    rw [hcode_inv, e]

theorem pt_eval : ∀ (w : List ℕ), (∀ c ∈ w, c < 12) → ∀ p < NP,
    ptT hL hR (evalWord xD w) p = w.foldl (fun p c => fieldAt PB' (Tb c) p) p
  | [], _, p, _ => ptT_one hL hR p
  | c :: w, hw, p, hp => by
    have hc := hw c List.mem_cons_self
    rw [evalWord_cons, ptT_mul, ← hxT hL hR c hc p hp, List.foldl_cons]
    exact pt_eval w (fun d hd => hw d (List.mem_cons_of_mem _ hd)) _ (tb_lt hL c hc p hp)

end Act

noncomputable abbrev pt2 : QB → ℕ → ℕ := ptT tab_letters tab_rels

theorem gens_ok : ∀ c ∈ CFSG.KC.LaneChain.getL CG 0, wBelow 12 (gWord INVM RW c) = true := by
  decide +kernel

theorem lens_ok : ∀ m ∈ chainLens ((gRegs INVM RW (CFSG.KC.LaneChain.getL CG 0)).map
    fun r => CFSG.KC.TwDce.wLen (r / 2)) (getLL CW 0), m < 2 ^ 32 := by
  decide +kernel

theorem base_ok : (∀ i < NB, CFSG.KC.TwDce.fld BS (16 * i) 65535 < 2160) ∧
    ∀ b ∈ getLL CB 0, ∃ i < NB,
      CFSG.KC.LaneChain.colDat 12 b / 2 = CFSG.KC.TwDce.fld BS (16 * i) 65535 := by
  decide +kernel

theorem cn0 : CFSG.KC.LaneChain.getN CN 0 = 13063680 := by decide +kernel

theorem chain_ok : chainBP 12 F 2160 (getLL CW 0) (getLL CB 0) (getLL CS 0) (getLL CT 0)
    (gRegs INVM RW (CFSG.KC.LaneChain.getL CG 0)) 13063680 = true := by
  have h := CFSG.Certificates.TwDce3.ChainP.stabRangeP_sound stab0 0 (by norm_num)
  rw [Nat.add_zero, cn0] at h
  exact (CFSG.Certificates.TwDce2.Words.kandB_iff.1 h).2

theorem pt_eq_one {q : QB} (hq : ∀ i < NB, pt2 q (CFSG.KC.TwDce.fld BS (16 * i) 65535) =
    CFSG.KC.TwDce.fld BS (16 * i) 65535) : q = 1 := by
  have hs := CFSG.Certificates.TwDce3.ChainP.chainBP_sound (G := QB) xD pt2
    (ptT_one tab_letters tab_rels) (ptT_mul tab_letters tab_rels) (tb_lt tab_letters)
    (hxT tab_letters tab_rels) ⊤ (fun c hc => ⟨gens_ok c hc, Subgroup.mem_top _⟩) lens_ok chain_ok
  rw [Subgroup.card_top, card_QB] at hs
  have : Finite {g : QB // g ∈ (⊤ : Subgroup QB) ∧ ∀ b ∈ getLL CB 0,
      pt2 g (CFSG.KC.LaneChain.colDat 12 b / 2) = CFSG.KC.LaneChain.colDat 12 b / 2} :=
    Subtype.finite
  have h1 : Nat.card {g : QB // g ∈ (⊤ : Subgroup QB) ∧ ∀ b ∈ getLL CB 0,
      pt2 g (CFSG.KC.LaneChain.colDat 12 b / 2) = CFSG.KC.LaneChain.colDat 12 b / 2} ≤ 1 := by
    omega
  have hsub := Finite.card_le_one_iff_subsingleton.1 h1
  have hmem : ∀ g : QB, (∀ i < NB, pt2 g (CFSG.KC.TwDce.fld BS (16 * i) 65535) =
      CFSG.KC.TwDce.fld BS (16 * i) 65535) → g ∈ (⊤ : Subgroup QB) ∧ ∀ b ∈ getLL CB 0,
        pt2 g (CFSG.KC.LaneChain.colDat 12 b / 2) = CFSG.KC.LaneChain.colDat 12 b / 2 := by
    intro g hg
    refine ⟨Subgroup.mem_top _, fun b hb => ?_⟩
    obtain ⟨i, hi, he⟩ := base_ok.2 b hb
    rw [he]
    exact hg i hi
  exact congrArg Subtype.val
    (hsub.elim ⟨q, hmem q hq⟩ ⟨1, hmem 1 fun i _ => ptT_one tab_letters tab_rels _⟩)

theorem hone : ∀ w : List ℕ, (∀ c ∈ w, c < 12) →
    (∀ i < NB, w.foldl (fun p c => fieldAt PB (F c) p) (CFSG.KC.TwDce.fld BS (16 * i) 65535) =
      CFSG.KC.TwDce.fld BS (16 * i) 65535) → evalWord onX w = 1 := by
  intro w hw hfix
  rw [pb_eq] at hfix
  rw [evalWord_onX, pt_eq_one (q := evalWord xD w) (fun i hi =>
    (pt_eval tab_letters tab_rels w hw _ (base_ok.1 i hi)).trans (hfix i hi)), map_one]

theorem factsP : ∃ X : ℕ → PC, X 0 = 1 ∧ ∀ r < 16625, dKind (RD r) < 5 ∧ dN1 (RD r) < 138 ∧
    dN2 (RD r) < 138 ∧
    (dKind (RD r) < 3 →
      X (dN1 (RD r)) * wVal onX (RW r) * onT * (X (dN2 (RD r)) * wVal onX (RA r))⁻¹ ∈ phanR) ∧
    (3 ≤ dKind (RD r) → X (dN1 (RD r)) * (X (dN2 (RD r)) * wVal onX (RW r))⁻¹ ∈ phanR) := by
  have hf := fold_ok
  rw [psf_eq, psb_eq] at hf
  exact CFSG.Certificates.TwDce3.dce_sound_comm hf (by norm_num) phanR onX onT hxH hinv
    (by rw [nt_eq]; norm_num) (fun c hc => hT c (by rw [nt_eq] at hc; exact hc)) hWD hone hlenR

end Cert

end CFSG.KD.PhanD4Dce

end
