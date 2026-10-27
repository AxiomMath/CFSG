
module

public import Certificates.Kernel.Sporadic.Fi24OrbL.Lv
public import Certificates.Kernel.Sporadic.Fi24ThreeO.Facts
public import Certificates.Data.Fi24Core

public section

namespace CertificateChecks.KernelFi24OrbL

open CFSG.Sporadic.Fi24 CFSG.Sporadic.Fi24.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Perm CFSG.Perm.Native CFSG.KC.Fi24Orb CFSG.KD.Fi24Net CFSG.KS.Fi24Net CFSG.KS.Fi24Kit
  CFSG.KC.Fi24ThreeO CFSG.KS.Fi24ThreeO CFSG.KC.Fi24NetPt CFSG.KS.Fi24NetPt

theorem OLe_eq (k : ℕ) : OrbL.OLe k = CFSG.KD.Fi24Orb.OL k := rfl

theorem tab_ap {g : ℕ → ℕ} (hg : ∀ e, g e < 2 ^ 32) {k : ℕ} (hk : k < 306936) :
    ap (OrbL.tab g) k = g (CFSG.KD.Fi24Orb.OL k) := by
  unfold OrbL.tab
  rw [ap_ofFn _ hk, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (hg _), OLe_eq]

theorem land_lt (e m : ℕ) (hm : m < 2 ^ 32) : Nat.land e m < 2 ^ 32 :=
  lt_of_le_of_lt Nat.and_le_right hm

theorem oA_lt (e : ℕ) : oA e < 2 ^ 32 := by unfold oA; exact land_lt _ _ (by norm_num)

theorem oB_lt (e : ℕ) : oB e < 2 ^ 32 := by unfold oB; exact land_lt _ _ (by norm_num)

theorem oPar_lt (e : ℕ) : oPar e < 2 ^ 32 := by unfold oPar; exact land_lt _ _ (by norm_num)

theorem oLab_lt (e : ℕ) : oLab e < 2 ^ 32 := by unfold oLab; exact land_lt _ _ (by norm_num)

theorem orb_alpha_orbL : ∀ x < 306936, ap orb.alpha x = oA (CFSG.KD.Fi24Orb.OL x) := by
  intro x hx
  dsimp only [orb]
  exact tab_ap oA_lt hx

theorem orb_beta_orbL : orb.beta.size = 306936 ∧
    ∀ x < 306936, ap orb.beta x = oB (CFSG.KD.Fi24Orb.OL x) := by
  dsimp only [orb]
  exact ⟨by unfold OrbL.tab; exact Array.size_ofFn, fun x hx => tab_ap oB_lt hx⟩

theorem orb_par_orbL : ∀ x < 306936, ap orb.par x = oPar (CFSG.KD.Fi24Orb.OL x) := by
  intro x hx
  dsimp only [orb]
  exact tab_ap oPar_lt hx

theorem orb_lab_orbL : ∀ x < 306936, ap orb.lab x = oLab (CFSG.KD.Fi24Orb.OL x) := by
  intro x hx
  dsimp only [orb]
  exact tab_ap oLab_lt hx

theorem letters_facts : (chainLetters orb).size = 26 ∧
    ∀ l < 26, ∀ x < 306936, ap (chainLetters orb)[l]! x = LN NW l x :=
  CFSG.KD.Fi24Net.letters orb orb_alpha_orbL orb_beta_orbL

theorem letters_LN : ∀ l < 26, ∀ x < 306936, ap (chainLetters orb)[l]! x = LN NW l x :=
  letters_facts.2

theorem LN_lt_N {l : ℕ} (hl : l < 26) {x : ℕ} (hx : x < 306936) : LN NW l x < 306936 := by
  have hj : l / 2 < 13 := by omega
  rcases Nat.mod_two_eq_zero_or_one l with h | h
  · have e : l = 2 * (l / 2) := by omega
    rw [e, LN_even]
    exact (nets hj hx).1
  · have e : l = 2 * (l / 2) + 1 := by omega
    rw [e, LN_odd]
    exact (nets hj hx).2.1

theorem xor_one_even (j : ℕ) : (2 * j) ^^^ 1 = 2 * j + 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor]
  rcases i with _ | i
  · simp [Nat.testBit_zero]
  · simp [Nat.testBit_succ, Nat.mul_add_div (by norm_num : 0 < 2), Nat.mul_div_cancel_left]

theorem xor_one_odd (j : ℕ) : (2 * j + 1) ^^^ 1 = 2 * j := by
  have := congrArg (· ^^^ 1) (xor_one_even j)
  simp only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at this
  exact this.symm

theorem LN_xor {l : ℕ} (hl : l < 26) {x : ℕ} (hx : x < 306936) :
    LN NW (l ^^^ 1) (LN NW l x) = x := by
  obtain ⟨j, rfl | rfl⟩ : ∃ j, l = 2 * j ∨ l = 2 * j + 1 :=
    ⟨l / 2, by rcases Nat.mod_two_eq_zero_or_one l with h | h <;> omega⟩
  · rw [xor_one_even, LN_odd, LN_even]
    exact (nets (by omega) hx).2.2.1
  · rw [xor_one_odd, LN_even, LN_odd]
    exact (nets (by omega) hx).2.2.2

open CFSG.KD.Fi24OrbL in
theorem bp_eq {i : ℕ} (hi : i < 6) : chainBase[i]! = bp i := by
  interval_cases i <;> decide

open CFSG.KD.Fi24OrbL in
theorem bp_lt {i : ℕ} : bp i < 306936 := by
  rcases i with _ | _ | _ | _ | _ | i <;> simp [bp]

open CFSG.KD.Fi24OrbL in
theorem lv_lt {i : ℕ} : ∀ l ∈ lv i, l < 26 := by
  intro l hl
  rcases i with _ | _ | _ | _ | _ | _ | i <;> simp [lv] at hl <;> omega

open CFSG.KD.Fi24OrbL in
theorem lv_xor {i : ℕ} : ∀ l ∈ lv i, l ^^^ 1 ∈ lv i := by
  rcases i with _ | _ | _ | _ | _ | _ | i
  all_goals first | decide | simp [lv]

open CFSG.KD.Fi24OrbL in
theorem levelLetters_eq : ∀ i ≤ 6, levelLetters (chainLetters orb) chainBase i = (lv i).toArray := by
  have hlv : ∀ i < 6, lv (i + 1) = (lv i).filter fun l => letN NW l (bp i) == bp i := by
    have h := Ck.lv_t
    unfold lvOK at h
    rw [List.all_eq_true] at h
    intro i hi
    exact beq_iff_eq.1 (h i (List.mem_range.2 hi))
  intro i
  induction i with
  | zero =>
    intro _
    rw [levelLetters, letters_facts.1]
    exact Array.toList_inj.1 (by rw [Array.toList_range]; rfl)
  | succ i ih =>
    intro hi
    rw [levelLetters, ih (by omega), hlv i (by omega), List.filter_toArray]
    congr 1
    apply List.filter_congr
    intro l hl
    rw [bp_eq (by omega), letters_LN l (lv_lt l hl) _ bp_lt, letN_eq]

open CFSG.KD.Fi24OrbL in
theorem wN_eq_foldr {lst : List ℕ} (hlst : ∀ l ∈ lst, l < 26) :
    ∀ (v : List ℕ), (∀ l ∈ v, l ∈ lst) → ∀ x < 306936,
      v.foldr (fun l z => ap (chainLetters orb)[l]! z) x = wN NW v x ∧ wN NW v x < 306936
  | [], _, x, hx => ⟨rfl, hx⟩
  | l :: v, hv, x, hx => by
    obtain ⟨e, hlt⟩ := wN_eq_foldr hlst v (fun l' h => hv l' (List.mem_cons_of_mem l h)) x hx
    have hl := hlst l (hv l List.mem_cons_self)
    change ap (chainLetters orb)[l]! (v.foldr _ x) = LN NW l (wN NW v x) ∧ LN NW l (wN NW v x) < _
    rw [e, letters_LN l hl _ hlt]
    exact ⟨rfl, LN_lt_N hl hlt⟩

theorem LN_pad {l : ℕ} (hl : l < 26) {x : ℕ} (hx1 : 306936 ≤ x) (hx2 : x < 524288) :
    306936 ≤ LN NW l x ∧ LN NW l x < 524288 := by
  have hj : l / 2 < 13 := by omega
  have hv := (CFSG.KS.Fi24Net.net_spec (nck_spec (l / 2) hj))
  refine ⟨?_, LN_lt hv.1 hx2⟩
  by_contra hc
  push Not at hc
  unfold LN at hc
  split_ifs at hc
  · exact absurd ((hv.2 _ hx2).1 hc) (by omega)
  · have e := (nets hj hc).1
    rw [pF_pR hv.1] at e
    omega

open CFSG.KD.Fi24OrbL in
theorem chainOrbit_of_orbOK {lst : List ℕ} (hlst : ∀ l ∈ lst, l < 26)
    (hxor : ∀ l ∈ lst, l ^^^ 1 ∈ lst) {d y c : ℕ} (hy : y < 306936)
    (h : orbOK NW lst d y c = true) : ChainOrbit (chainLetters orb) lst.toArray y c := by
  classical
  obtain ⟨P, hPy, hreach, hcl, hcard⟩ := orbOK_spec CFSG.KD.Fi24ThreeO.vn h
  have hpad : ∀ x, 306936 ≤ x → x < 524288 → P.testBit x = false := by
    intro x hx1 hx2
    cases hP : P.testBit x
    · rfl
    · exfalso
      obtain ⟨v, hv, hw⟩ := hreach x hP
      have key : ∀ v : List ℕ, (∀ l ∈ v, l ∈ lst) → 306936 ≤ wN NW v x ∧ wN NW v x < 524288 := by
        intro v hv
        induction v with
        | nil => exact ⟨hx1, hx2⟩
        | cons l v ih =>
          obtain ⟨h1, h2⟩ := ih (fun l' h => hv l' (List.mem_cons_of_mem l h))
          exact LN_pad (hlst l (hv l List.mem_cons_self)) h1 h2
      have := (key v hv).1
      omega
  have memP : ∀ x, x ∈ (Finset.range 524288).filter (fun x => P.testBit x = true) ↔
      x < 306936 ∧ P.testBit x = true := by
    intro x
    rw [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      by_contra hc
      rw [hpad x (by omega) h1] at h2
      exact absurd h2 (by decide)
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, h2⟩
  refine ⟨(Finset.range 524288).filter (fun x => P.testBit x = true), hcard,
    (memP y).2 ⟨hy, hPy⟩, fun x hx => ((memP x).1 hx).1, fun x hx l hl => ?_, fun x hx => ?_⟩
  · obtain ⟨hxN, hxP⟩ := (memP x).1 hx
    rw [List.mem_toArray] at hl
    have hl26 := hlst l hl
    rw [letters_LN l hl26 x hxN, memP]
    refine ⟨LN_lt_N hl26 hxN, hcl _ (by have := LN_lt_N hl26 hxN; omega) _ (hxor l hl) ?_⟩
    rw [LN_xor hl26 hxN]
    exact hxP
  · obtain ⟨hxN, hxP⟩ := (memP x).1 hx
    obtain ⟨v, hv, hw⟩ := hreach x hxP
    refine ⟨v, fun l h => List.mem_toArray.2 (hv l h), ?_⟩
    rw [(wN_eq_foldr hlst v hv x hxN).1, hw]

open CFSG.KD.Fi24OrbL in
theorem chain_orbits : ∀ i < 6, ChainOrbit (chainLetters orb)
    (levelLetters (chainLetters orb) chainBase i) chainBase[i]! chainSizes[i]! := by
  intro i hi
  rw [levelLetters_eq i (by omega), bp_eq hi]
  have ho : o i = true := by
    interval_cases i
    · exact Ck.o0
    · exact Ck.o1
    · exact Ck.o2
    · exact Ck.o3
    · exact Ck.o4
    · exact Ck.o5
  have hs : chainSizes[i]! = sz i := by interval_cases i <;> decide
  rw [hs]
  exact chainOrbit_of_orbOK lv_lt lv_xor (by interval_cases i <;> decide) ho

open CFSG.KD.Fi24OrbL in
theorem sub_orbit : ChainOrbit (chainLetters orb)
    (levelLetters (chainLetters orb) chainBase 1) 1 31671 := by
  rw [levelLetters_eq 1 (by omega)]
  exact chainOrbit_of_orbOK lv_lt lv_xor (by norm_num) Ck.oS

end CertificateChecks.KernelFi24OrbL
