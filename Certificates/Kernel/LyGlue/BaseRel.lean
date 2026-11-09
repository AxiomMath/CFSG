module

public import Certificates.Kernel.LyGlue.Facts2
public import Certificates.Kernel.LyGlue.Flat
public import Certificates.Kernel.LyBase.Facts
public import CFSG.Certificates.Kernel.LyGlue.SlpSound
public import CFSG.Certificates.Kernel.LyBase.Stab

public section

namespace CertificateChecks.KernelLy

open CFSG.KC.Enum CFSG.KS CFSG.KC.LyGlue CFSG.Sporadic.Recognition.LyonsSims Equiv
  CFSG.Sporadic.Recognition

@[expose] noncomputable def baseP (k : Nat) : Perm (Fin Ly0.deg) :=
  if k = 1 then Ly0.cG else if k = 2 then Ly0.dG else 1

theorem baseP_one : baseP 1 = Ly0.cG := by simp [baseP]

theorem baseP_two : baseP 2 = Ly0.dG := by simp [baseP]

theorem prodP_single (k : Nat) : prodP baseP [k] = baseP k := by
  simp [prodP]

theorem prodP_cdE (h : Ly0.tabCheck = true) :
    ∀ w : List Int, (∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 2) →
      prodP baseP (cdE w) = Ly0.wG Ly0.gens0 w
  | [], _ => by rw [Ly0.wG_nil]; rfl
  | l :: w, hw => by
    have hl := hw l List.mem_cons_self
    have ih := prodP_cdE h w (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    have e : cdE (l :: w) = cdIdx l ++ cdE w := by simp only [cdE, List.flatMap_cons]
    rw [e, prodP_append, ih, Ly0.wG_cons]
    refine congrArg (· * Ly0.wG Ly0.gens0 w) ?_
    have hci : Ly0.cG⁻¹ = Ly0.cG := inv_eq_of_mul_eq_one_right (c2 h)
    have hdi : Ly0.dG⁻¹ = Ly0.dG * Ly0.dG :=
      inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact d3 h)
    have hcases : l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · rw [show cdIdx 1 = [1] by decide +kernel, prodP_single, baseP_one,
        Ly0.letterG_pos _ (by norm_num), show ((1 : ℤ) - 1).toNat = 0 from rfl, Ly0.gens0_zero]
    · rw [show cdIdx (-1) = [1] by decide +kernel, prodP_single, baseP_one,
        Ly0.letterG_neg_of _ (by norm_num), show (-(-1 : ℤ) - 1).toNat = 0 from rfl,
        Ly0.gens0_zero, hci]
    · rw [show cdIdx 2 = [2] by decide +kernel, prodP_single, baseP_two,
        Ly0.letterG_pos _ (by norm_num), show ((2 : ℤ) - 1).toNat = 1 from rfl, Ly0.gens0_one]
    · rw [show cdIdx (-2) = [2, 2] by decide +kernel, Ly0.letterG_neg_of _ (by norm_num),
        show (-(-2 : ℤ) - 1).toNat = 1 from rfl, Ly0.gens0_one, hdi]
      simp [prodP, baseP_two]

theorem uWords_range' : ∀ k < 4, ∀ l ∈ Ly0.uWords.getD k [], l ≠ 0 ∧ l.natAbs ≤ 2 :=
  fun _ hk => uWords_range hk

theorem prodP_uE (h : Ly0.tabCheck = true) :
    ∀ w : List Int, (∀ l ∈ w, 0 < l ∧ l ≤ 4) →
      prodP baseP (uE w) = CFSG.Sporadic.Th.wordG (wordLetter Ly0.uG) w
  | [], _ => rfl
  | l :: w, hw => by
    have hl := hw l List.mem_cons_self
    have ih := prodP_uE h w (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    have e : uE (l :: w) = (if l = 1 then [1] else cdE (Ly0.uWords.getD (l.toNat - 1) [])) ++
        uE w := by simp only [uE, List.flatMap_cons]
    rw [e, prodP_append, ih]
    change _ = wordLetter Ly0.uG l * CFSG.Sporadic.Th.wordG (wordLetter Ly0.uG) w
    refine congrArg (· * CFSG.Sporadic.Th.wordG (wordLetter Ly0.uG) w) ?_
    have hwl : wordLetter Ly0.uG l = Ly0.uG (l.toNat - 1) := by
      unfold wordLetter
      rw [if_pos hl.1]
    rw [hwl, Ly0.uG_def]
    by_cases h1 : l = 1
    · subst h1
      rw [if_pos rfl, prodP_single, baseP_one]
      change Ly0.cG = Ly0.wG Ly0.gens0 Ly0.wordU1
      rw [show Ly0.wordU1 = [1] by decide +kernel, Ly0.wG_cons, Ly0.wG_nil, mul_one,
        Ly0.letterG_pos _ (by norm_num), show ((1 : ℤ) - 1).toNat = 0 from rfl, Ly0.gens0_zero]
    · rw [if_neg h1]
      exact prodP_cdE h _ (uWords_range (by omega))

theorem baseP_mem (k : Nat) : baseP k ∈ Ly0.B0 := by
  unfold baseP
  split_ifs
  · exact Ly0.cG_mem
  · exact Ly0.dG_mem
  · exact Ly0.B0.one_mem

theorem lyProdP_mem : ∀ L : List Nat, prodP baseP L ∈ Ly0.B0
  | [] => by
    have e : prodP baseP [] = 1 := by simp [prodP]
    rw [e]
    exact Ly0.B0.one_mem
  | k :: L => by
    have e : prodP baseP (k :: L) = baseP k * prodP baseP L := by simp [prodP]
    rw [e]
    exact Ly0.B0.mul_mem (baseP_mem k) (lyProdP_mem L)

theorem lyPtE_eq (h : Ly0.tabCheck = true) :
    ∀ (L : List Nat) (a : Fin Ly0.deg), lyPtE L a = (prodP baseP L a : Nat)
  | [], a => by simp [lyPtE, prodP]
  | k :: L, a => by
    have ih := lyPtE_eq h L a
    have e : prodP baseP (k :: L) = baseP k * prodP baseP L := by simp [prodP]
    change Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat) (lyPtE L a) (dL (lyPtE L a)) (Nat.beq k 2))
        (cL (lyPtE L a)) (Nat.beq k 1) = _
    rw [e, Perm.mul_apply, ih]
    cases h1 : Nat.beq k 1
    · cases h2 : Nat.beq k 2
      · have n1 : k ≠ 1 := Nat.ne_of_beq_eq_false h1
        have n2 : k ≠ 2 := Nat.ne_of_beq_eq_false h2
        simp [baseP, n1, n2]
      · rw [Nat.eq_of_beq_eq_true h2, baseP_two]
        exact dL_eq h _
    · rw [Nat.eq_of_beq_eq_true h1, baseP_one]
      exact cL_eq h _

open CertificateChecks.KernelLyBase in
theorem lyB0_eq (hM : Ly0.ModelChecks) {g h : Perm (Fin Ly0.deg)} (hg : g ∈ Ly0.B0)
    (hh : h ∈ Ly0.B0) (e0 : g p0 = h p0) (e3 : g p3 = h p3) (e1 : g p1 = h p1) : g = h := by
  have hc := cL_eq hM.tab
  have hd := dL_eq hM.tab
  have fx : ∀ {b : Fin Ly0.deg}, g b = h b → (h⁻¹ * g) b = b := fun {b} e => by
    rw [Perm.mul_apply, e]
    exact Equiv.symm_apply_apply h b
  have key := CFSG.KC.LyBase.eq_one_of_fix3 Ly0.B0 p0 p3 p1 (m₀ := 66825) (m₁ := 20160)
    (m₂ := 4) (by norm_num) ((Ly0.card_B0 hM.tab hM.cover hM.struct).le.trans (by norm_num))
    (orbit0_le hc hd) (orbit1_le hc hd) (orbit2_le hc hd)
    (Ly0.B0.mul_mem (Ly0.B0.inv_mem hh) hg) (fx e0) (fx e3) (fx e1)
  exact (inv_mul_eq_one.1 key).symm

@[expose] noncomputable def lyRelPt (j p : Nat) : Bool :=
  Nat.beq
    (lyPtE (expect.getD (conjList.getD j (0, 0, 0, 0)).1 [] ++
      expect.getD (conjList.getD j (0, 0, 0, 0)).2.1 []) p)
    (lyPtE (expect.getD (conjList.getD j (0, 0, 0, 0)).2.2.1 [] ++
      expect.getD (conjList.getD j (0, 0, 0, 0)).2.2.2 []) p)

@[expose] noncomputable def lyRelK (j : Nat) : Bool :=
  bAnd(lyRelPt j 0, bAnd(lyRelPt j 3, lyRelPt j 1))

theorem lyRel_ok : ∀ j < 9, lyRelK j = true := by
  intro j hj
  interval_cases j <;> decide +kernel

theorem lyConj_base (hM : Ly0.ModelChecks) {j : Nat} (hj : j < 9) :
    prodP baseP (expect.getD (conjList.getD j (0, 0, 0, 0)).1 []) *
        prodP baseP (expect.getD (conjList.getD j (0, 0, 0, 0)).2.1 []) =
      prodP baseP (expect.getD (conjList.getD j (0, 0, 0, 0)).2.2.1 []) *
        prodP baseP (expect.getD (conjList.getD j (0, 0, 0, 0)).2.2.2 []) := by
  rw [← prodP_append, ← prodP_append]
  have hr := lyRel_ok j hj
  unfold lyRelK at hr
  have pt : ∀ (b : Fin Ly0.deg), lyRelPt j b = true →
      prodP baseP (expect.getD (conjList.getD j (0, 0, 0, 0)).1 [] ++
        expect.getD (conjList.getD j (0, 0, 0, 0)).2.1 []) b =
      prodP baseP (expect.getD (conjList.getD j (0, 0, 0, 0)).2.2.1 [] ++
        expect.getD (conjList.getD j (0, 0, 0, 0)).2.2.2 []) b := fun b hb => by
    apply Fin.ext
    rw [← lyPtE_eq hM.tab, ← lyPtE_eq hM.tab]
    exact Nat.eq_of_beq_eq_true hb
  cases e0 : lyRelPt j 0 <;> cases e3 : lyRelPt j 3 <;> cases e1 : lyRelPt j 1 <;>
    rw [e0, e3, e1] at hr <;> try exact absurd hr Bool.false_ne_true
  exact lyB0_eq hM (lyProdP_mem _) (lyProdP_mem _) (pt KernelLyBase.p0 e0)
    (pt KernelLyBase.p3 e3) (pt KernelLyBase.p1 e1)

theorem lyProdP_eq_base (hM : Ly0.ModelChecks) {L M : List Nat}
    (e0 : Nat.beq (lyPtE L 0) (lyPtE M 0) = true) (e3 : Nat.beq (lyPtE L 3) (lyPtE M 3) = true)
    (e1 : Nat.beq (lyPtE L 1) (lyPtE M 1) = true) : prodP baseP L = prodP baseP M := by
  have pt : ∀ (b : Fin Ly0.deg), Nat.beq (lyPtE L b) (lyPtE M b) = true →
      prodP baseP L b = prodP baseP M b := fun b hb => by
    apply Fin.ext
    rw [← lyPtE_eq hM.tab, ← lyPtE_eq hM.tab]
    exact Nat.eq_of_beq_eq_true hb
  exact lyB0_eq hM (lyProdP_mem _) (lyProdP_mem _) (pt KernelLyBase.p0 e0)
    (pt KernelLyBase.p3 e3) (pt KernelLyBase.p1 e1)

theorem prodP_uEs (h : Ly0.tabCheck = true) :
    ∀ w : List Int, (∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 4) →
      prodP baseP (uEs w) = CFSG.Sporadic.Th.wordG (wordLetter Ly0.uG) w
  | [], _ => rfl
  | l :: w, hw => by
    have hl := hw l List.mem_cons_self
    have ih := prodP_uEs h w (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    have e : uEs (l :: w) = (if 0 < l then cdE (Ly0.uWords.getD (l.toNat - 1) [])
        else cdE (McLMultiplier.invW (Ly0.uWords.getD ((-l).toNat - 1) []))) ++ uEs w := by
      simp only [uEs, List.flatMap_cons]
    rw [e, prodP_append, ih]
    change _ = wordLetter Ly0.uG l * CFSG.Sporadic.Th.wordG (wordLetter Ly0.uG) w
    refine congrArg (· * CFSG.Sporadic.Th.wordG (wordLetter Ly0.uG) w) ?_
    unfold wordLetter
    by_cases hp : 0 < l
    · rw [if_pos hp, if_pos hp, Ly0.uG_def]
      exact prodP_cdE h _ (uWords_range (by omega))
    · have hk : (-l).toNat - 1 < 4 := by omega
      rw [if_neg hp, if_neg hp, Ly0.uG_def,
        ← Ly0.wG_invW Ly0.gens0 (fun l' hl' => (uWords_range hk l' hl').1)]
      refine prodP_cdE h _ (fun l' hl' => ?_)
      simp only [McLMultiplier.invW, List.mem_reverse, List.mem_map] at hl'
      obtain ⟨l'', hl'', rfl⟩ := hl'
      have := uWords_range hk l'' hl''
      omega

theorem prodP_txE (h : Ly0.tabCheck = true) :
    ∀ w : List Int, (∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 4) →
      prodP baseP (txE w) = CFSG.Sporadic.Th.wordG (wordLetter Glue.txG) w
  | [], _ => rfl
  | l :: w, hw => by
    have hl := hw l List.mem_cons_self
    have ih := prodP_txE h w (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    have e : txE (l :: w) = (if 0 < l then cdE (Glue.txWords.getD (l.toNat - 1) [])
        else cdE (McLMultiplier.invW (Glue.txWords.getD ((-l).toNat - 1) []))) ++ txE w := by
      simp only [txE, List.flatMap_cons]
    rw [e, prodP_append, ih]
    change _ = wordLetter Glue.txG l * CFSG.Sporadic.Th.wordG (wordLetter Glue.txG) w
    refine congrArg (· * CFSG.Sporadic.Th.wordG (wordLetter Glue.txG) w) ?_
    unfold wordLetter Glue.txG
    by_cases hp : 0 < l
    · rw [if_pos hp, if_pos hp]
      exact prodP_cdE h _ (Glue.txWords_getD_range (by omega))
    · have hk : (-l).toNat - 1 < 4 := by omega
      rw [if_neg hp, if_neg hp,
        ← Ly0.wG_invW Ly0.gens0 (fun l' hl' => (Glue.txWords_getD_range hk l' hl').1)]
      refine prodP_cdE h _ (fun l' hl' => ?_)
      simp only [McLMultiplier.invW, List.mem_reverse, List.mem_map] at hl'
      obtain ⟨l'', hl'', rfl⟩ := hl'
      have := Glue.txWords_getD_range hk l'' hl''
      omega

theorem prodP_cdInv (h : Ly0.tabCheck = true) :
    ∀ L : List Nat, prodP baseP (cdInv L) = (prodP baseP L)⁻¹
  | [] => by simp [cdInv, prodP]
  | k :: L => by
    have e : cdInv (k :: L) = cdInv L ++ (if k = 2 then [2, 2] else [k]) := by
      simp only [cdInv, List.reverse_cons, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
    have e2 : prodP baseP (k :: L) = baseP k * prodP baseP L := by simp [prodP]
    rw [e, prodP_append, prodP_cdInv h L, e2, mul_inv_rev]
    refine congrArg ((prodP baseP L)⁻¹ * ·) ?_
    by_cases h2 : k = 2
    · subst h2
      have hdi : Ly0.dG⁻¹ = Ly0.dG * Ly0.dG :=
        inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact d3 h)
      rw [if_pos rfl, baseP_two, hdi]
      simp [prodP, baseP_two]
    · rw [if_neg h2, prodP_single]
      by_cases h1 : k = 1
      · subst h1
        rw [baseP_one]
        exact (inv_eq_of_mul_eq_one_right (c2 h)).symm
      · simp [baseP, h1, h2]

theorem lyBase3_spec (hM : Ly0.ModelChecks) {A B : List Nat} (h : lyBase3 A B = true) :
    prodP baseP A = prodP baseP B := by
  unfold lyBase3 at h
  obtain ⟨h0, h2⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h1⟩ := (bAnd_iff _ _).1 h2
  exact lyProdP_eq_base hM h0 h3 h1

theorem lyConjK_spec (hM : Ly0.ModelChecks) {T L : List Nat} (h : lyConjK T L = true) :
    prodP baseP T * prodP baseP L * (prodP baseP T)⁻¹ = prodP baseP L ∨
      prodP baseP T * prodP baseP L * (prodP baseP T)⁻¹ = (prodP baseP L)⁻¹ := by
  unfold lyConjK at h
  cases h1 : lyBase3 (T ++ L) (L ++ T)
  · rw [h1] at h
    right
    have e := lyBase3_spec hM (A := T ++ L) (B := cdInv L ++ T) h
    rw [prodP_append, prodP_append, prodP_cdInv hM.tab] at e
    rw [e]
    group
  · left
    have e := lyBase3_spec hM h1
    rw [prodP_append, prodP_append] at e
    rw [e]
    group

end CertificateChecks.KernelLy

end
