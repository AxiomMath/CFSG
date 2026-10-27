module

public import Certificates.Kernel.Sporadic.Fi24FiveK.Head
public import Certificates.Kernel.Sporadic.Fi24FiveK.Blocks
public import Certificates.Kernel.Sporadic.Fi24FiveK.S0
public import Certificates.Kernel.Sporadic.Fi24FiveK.S1
public import Certificates.Kernel.Sporadic.Fi24FiveK.S2
public import Certificates.Kernel.Sporadic.Fi24FiveK.S3
public import Certificates.Kernel.Sporadic.Fi24FiveK.S4
public import Certificates.Kernel.Sporadic.Fi24FiveK.S5
public import Certificates.Kernel.Sporadic.Fi24FiveK.S6
public import Certificates.Kernel.Sporadic.Fi24FiveK.S7
public import Certificates.Kernel.Sporadic.Fi24FiveK.S8
public import Certificates.Kernel.Sporadic.Fi24FiveK.S9
public import Certificates.Kernel.Sporadic.Fi24FiveK.S10
public import Certificates.Kernel.Sporadic.Fi24FiveK.S11
public import Certificates.Kernel.Sporadic.Fi24Pump.Glue
public import Certificates.Kernel.Sporadic.Fi24OrbL.Facts
public import CFSG.LocalAnalysis.StandardType.GGSporKRestTwoCent
import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace CFSG.KD.Fi24FiveK

#kc_forall_tree let_all (fun j => CFSG.KD.Fi24FiveK.letc j = true) 17 CFSG.KD.Fi24FiveK.Ck.l
#kc_forall_tree stg_all (fun k => CFSG.KD.Fi24FiveK.stg k = true) 331 CFSG.KD.Fi24FiveK.Ck.s
#kc_forall_tree blk_all (fun i => CFSG.KD.Fi24FiveK.blk i = true) 11 CFSG.KD.Fi24FiveK.Ck.q

open CFSG.KC.Fi24FiveK CFSG.KC.Fi24PumpK CFSG.KC.Fi24Kn CFSG.KS.Fi24PumpK CFSG.KS.Fi24Net
  CFSG.KD.Fi24Pump CFSG.Sporadic.Th CFSG.Perm CFSG.Sporadic.Fi24.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three CFSG.StandardType.SporadicShape

theorem nthW_nil (i : ℕ) : nthW [] i = [] := rfl

theorem nthW_cons_zero (w : List ℕ) (l : List (List ℕ)) : nthW (w :: l) 0 = w := rfl

theorem nthW_cons_succ (w : List ℕ) (l : List (List ℕ)) (i : ℕ) :
    nthW (w :: l) (i + 1) = nthW l i := rfl

theorem nthW_mem_or : ∀ (l : List (List ℕ)) (i : ℕ), nthW l i ∈ l ∨ nthW l i = []
  | [], i => Or.inr (nthW_nil i)
  | w :: l, 0 => Or.inl (by rw [nthW_cons_zero]; exact List.mem_cons_self)
  | w :: l, i + 1 => by
    rw [nthW_cons_succ]
    rcases nthW_mem_or l i with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · exact Or.inr h

theorem nthW_ge : ∀ (l : List (List ℕ)) (i : ℕ), l.length ≤ i → nthW l i = []
  | [], i, _ => nthW_nil i
  | w :: l, 0, h => absurd h (by simp)
  | w :: l, i + 1, h => by
    rw [nthW_cons_succ]
    exact nthW_ge l i (by simp at h; omega)

theorem exists_nthW : ∀ (l : List (List ℕ)) (w : List ℕ), w ∈ l → ∃ k < l.length, nthW l k = w
  | [], _, h => absurd h List.not_mem_nil
  | v :: l, w, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨0, by simp, rfl⟩
    · obtain ⟨k, hk, e⟩ := exists_nthW l w h
      exact ⟨k + 1, by simp; omega, by rw [nthW_cons_succ, e]⟩

theorem lenLe_iff : ∀ (W : List (List ℕ)) (n : ℕ), lenLe W n = true ↔ W.length ≤ n
  | [], n => by simp [lenLe]
  | w :: W, 0 => by simp [lenLe]
  | w :: W, n + 1 => by
    change lenLe W n = true ↔ _
    rw [lenLe_iff W n, List.length_cons]
    omega

theorem allLt_iff :∀ W : List (List ℕ), allLt W = true ↔ ∀ w ∈ W, ∀ l ∈ w, l < 26
  | [] => by simp [allLt]
  | w :: W => by
    change (letLt w && allLt W) = true ↔ _
    rw [Bool.and_eq_true, letLt_iff, allLt_iff W, List.forall_mem_cons]

theorem nthW_lt {W : List (List ℕ)} (h : ∀ w ∈ W, ∀ l ∈ w, l < 26) (i : ℕ) :
    ∀ l ∈ nthW W i, l < 26 := by
  rcases nthW_mem_or W i with hm | hm
  · exact h _ hm
  · rw [hm]
    exact fun _ h => absurd h List.not_mem_nil

theorem expC_cons (M : List (List ℕ)) (k : ℕ) (c : List ℕ) :
    expC M (k :: c) = nthW M k ++ expC M c := rfl

theorem catW_cons (w : List ℕ) (R : List (List ℕ)) : catW (w :: R) = w ++ catW R := rfl

theorem expC_lt {M : List (List ℕ)} (h : ∀ w ∈ M, ∀ l ∈ w, l < 26) :
    ∀ c : List ℕ, ∀ l ∈ expC M c, l < 26
  | [] => fun _ h => absurd h List.not_mem_nil
  | k :: c => by
    rw [expC_cons]
    intro l hl
    rcases List.mem_append.1 hl with hl | hl
    · exact nthW_lt h k l hl
    · exact expC_lt h c l hl

theorem catW_lt : ∀ {R : List (List ℕ)}, (∀ w ∈ R, ∀ l ∈ w, l < 26) → ∀ l ∈ catW R, l < 26
  | [], _ => fun _ h => absurd h List.not_mem_nil
  | w :: R, h => by
    rw [catW_cons]
    intro l hl
    rcases List.mem_append.1 hl with hl | hl
    · exact h w List.mem_cons_self l hl
    · exact catW_lt (fun v hv => h v (List.mem_cons_of_mem _ hv)) l hl

theorem segC_succ (R : List (List ℕ)) (s n : ℕ) :
    segC R s (n + 1) = segC R s n ++ nthW R (s + n) := rfl

theorem segC_lt {R : List (List ℕ)} (h : ∀ m, ∀ l ∈ nthW R m, l < 26) (s : ℕ) :
    ∀ n, ∀ l ∈ segC R s n, l < 26
  | 0 => fun _ h => absurd h List.not_mem_nil
  | n + 1 => by
    rw [segC_succ]
    intro l hl
    rcases List.mem_append.1 hl with hl | hl
    · exact segC_lt h s n l hl
    · exact h _ l hl

theorem repW_lt{w : List ℕ} (h : ∀ l ∈ w, l < 26) (p : ℕ) : ∀ l ∈ repW w p, l < 26 :=
  fun l hl => h l (mem_repW p hl)

theorem append_lt {u v : List ℕ} (hu : ∀ l ∈ u, l < 26) (hv : ∀ l ∈ v, l < 26) :
    ∀ l ∈ u ++ v, l < 26 := fun l hl => by
  rcases List.mem_append.1 hl with h | h
  · exact hu l h
  · exact hv l h

theorem single_lt {l : ℕ} (h : l < 26) : ∀ x ∈ [l], x < 26 := fun x hx => by
  rw [List.mem_singleton.1 hx]
  exact h

theorem nil_lt : ∀ x ∈ ([] : List ℕ), x < 26 := fun _ h => absurd h List.not_mem_nil


theorem wordElt_mem_expC {L : Subgroup CFSG.Sporadic.Fi24.J} {M : List (List ℕ)}
    (h : ∀ k, wordElt (nthW M k) ∈ L) : ∀ c, wordElt (expC M c) ∈ L
  | [] => by
    change wordElt [] ∈ L
    rw [wordElt_nil]
    exact L.one_mem
  | k :: c => by
    rw [expC_cons, wordElt_append]
    exact L.mul_mem (h k) (wordElt_mem_expC h c)

theorem wordElt_mem_catW {L : Subgroup CFSG.Sporadic.Fi24.J} :
    ∀ {R : List (List ℕ)}, (∀ w ∈ R, wordElt w ∈ L) → wordElt (catW R) ∈ L
  | [], _ => by
    change wordElt [] ∈ L
    rw [wordElt_nil]
    exact L.one_mem
  | w :: R, h => by
    rw [catW_cons, wordElt_append]
    exact L.mul_mem (h w List.mem_cons_self)
      (wordElt_mem_catW fun v hv => h v (List.mem_cons_of_mem _ hv))

theorem wordElt_zero : wordElt [0] = CFSG.Sporadic.Fi24.a := by
  rw [wordElt_cons, wordElt_nil, mul_one]
  simp [pairG, CFSG.Sporadic.Fi24.gs_zero]

theorem wordElt_two : wordElt [2] = CFSG.Sporadic.Fi24.b := by
  rw [wordElt_cons, wordElt_nil, mul_one]
  simp [pairG, CFSG.Sporadic.Fi24.gs_one]

theorem val_five : (Nat.card ↥CFSG.Sporadic.Fi24.J).factorization 5 = 2 := by
  rw [CFSG.Sporadic.Fi24.card_J, Nat.factorization_def 1255205709190661721292800 (p := 5) (by norm_num)]
  have hc : padicValNat 5 50208228367626468851712 = 0 :=
    padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 5 ∣ 50208228367626468851712)
  have e1 : (1255205709190661721292800 : ℕ) = 5 * (5 * 50208228367626468851712) := by norm_num
  rw [e1, padicValNat_base_mul (by norm_num) (by norm_num),
    padicValNat_base_mul (by norm_num) (by norm_num), hc]

section Bridge

variable (hL : ∀ l < 26, ∀ p < 306936,
  idx 306936 (pairG CFSG.Sporadic.Fi24.gs l) p = LN CFSG.KD.Fi24Net.NW l p)
include hL

theorem E_eq_LN : E = CFSG.KC.Fi24Base.eqB (LN CFSG.KD.Fi24Net.NW) := by
  unfold E
  congr 1
  exact funext fun l => funext fun x => CFSG.KS.Fi24NetPt.letN_eq CFSG.KD.Fi24Net.NW l x

theorem eqw {u v : List ℕ} (hu : ∀ l ∈ u, l < 26) (hv : ∀ l ∈ v, l < 26) (h : E u v = true) :
    wordElt u = wordElt v := by
  rw [E_eq_LN hL] at h
  exact eq_of_foldr hL hu hv fun b hb => by
    have := (eqB_iff u v).1 h b hb
    rwa [apF_eq_foldr u hu, apF_eq_foldr v hv] at this

theorem E_of_eq {u v : List ℕ} (hu : ∀ l ∈ u, l < 26) (hv : ∀ l ∈ v, l < 26)
    (h : wordElt u = wordElt v) : E u v = true := by
  rw [E_eq_LN hL]
  refine (eqB_iff u v).2 fun b hb => ?_
  rw [apF_eq_foldr u hu, apF_eq_foldr v hv, ← idx_wordElt hL u hu b (chainBase_lt' b hb),
    ← idx_wordElt hL v hv b (chainBase_lt' b hb), h]

theorem comm_of {u v : List ℕ} (hu : ∀ l ∈ u, l < 26) (hv : ∀ l ∈ v, l < 26)
    (h : commB E u v = true) : wordElt u * wordElt v = wordElt v * wordElt u := by
  rw [← wordElt_append, ← wordElt_append]
  exact eqw hL (append_lt hu hv) (append_lt hv hu) h

theorem cover_of : SporKRestCover 5 ↥CFSG.Sporadic.Fi24.J := by
  have hH := Ck.head
  unfold head headOK at hH
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hH
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hM34, hR⟩, hMlt⟩, hHlt⟩, hp1⟩, hp2⟩, hne⟩, hc⟩, hcj⟩, ha⟩ := hH
  have hM34 := (lenLe_iff _ _).1 hM34
  have hR := (lenLe_iff _ _).1 hR
  have hMw := (allLt_iff _).1 hMlt
  have hHw := (letLt_iff _).1 hHlt
  have hRk : ∀ k < 331, letLt (nthW D.R k) = true ∧
      E (expC D.M (nthW D.C k)) (nthW D.R k) = true := by
    intro k hk
    have hs := stg_all k hk
    unfold stg stageOK at hs
    rwa [Bool.and_eq_true] at hs
  have hRw : ∀ w ∈ D.R, ∀ l ∈ w, l < 26 := by
    intro w hw
    obtain ⟨k, hk, rfl⟩ := exists_nthW _ w hw
    exact (letLt_iff _).1 (hRk k (by omega)).1
  have hn := nthW_lt hMw
  have h1 : wordElt (nthW D.M 0) ^ 5 = 1 := by
    rw [← wordElt_repW, ← wordElt_nil]
    exact eqw hL (repW_lt (hn 0) 5) nil_lt hp1
  have h2 : wordElt (nthW D.M 2) ^ 5 = 1 := by
    rw [← wordElt_repW, ← wordElt_nil]
    exact eqw hL (repW_lt (hn 2) 5) nil_lt hp2
  have hne1 : wordElt (nthW D.M 0) ≠ 1 := by
    intro h
    rw [← wordElt_nil] at h
    rw [E_of_eq hL (hn 0) nil_lt h] at hne
    exact Bool.noConfusion hne
  have hc' := comm_of hL (hn 0) (hn 2) hc
  have hh : wordElt (nthW D.M 0) * wordElt D.H = wordElt D.H * wordElt (nthW D.M 2) := by
    rw [← wordElt_append, ← wordElt_append]
    exact eqw hL (append_lt (hn 0) hHw) (append_lt hHw (hn 2)) hcj
  have ha' := comm_of hL (single_lt (by norm_num)) (hn 2) ha
  rw [wordElt_zero] at ha'
  let L : Subgroup CFSG.Sporadic.Fi24.J := Subgroup.closure
    ((Subgroup.centralizer {wordElt (nthW D.M 0)} : Set CFSG.Sporadic.Fi24.J) ∪
      Subgroup.centralizer {wordElt (nthW D.M 2)})
  have hcent : ∀ w : List ℕ, (∀ l ∈ w, l < 26) → (commB E w (nthW D.M 0) || commB E w (nthW D.M 2)) = true →
      wordElt w ∈ L := by
    intro w hw h
    rw [Bool.or_eq_true] at h
    apply Subgroup.subset_closure
    rcases h with h | h
    · exact Or.inl (Subgroup.mem_centralizer_singleton_iff.2 (comm_of hL hw (hn 0) h))
    · exact Or.inr (Subgroup.mem_centralizer_singleton_iff.2 (comm_of hL hw (hn 2) h))
  have hlet : ∀ k, wordElt (nthW D.M k) ∈ L := by
    intro k
    by_cases hk : k < 34
    · have hj := let_all (k / 2) (by change k / 2 < 17; omega)
      unfold letc letOK at hj
      rw [Bool.and_eq_true] at hj
      obtain ⟨hinv, hj⟩ := hj
      have hw := hcent _ (hn _) hj
      have hinv' := eqw hL (append_lt (hn _) (hn _)) nil_lt hinv
      rw [wordElt_append, wordElt_nil, mul_eq_one_iff_eq_inv] at hinv'
      rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
      · rwa [show 2 * j / 2 = j by omega] at hw
      · rw [show (2 * j + 1) / 2 = j by omega] at hw hinv'
        have h' := L.inv_mem hw
        rwa [hinv', inv_inv] at h'
    · rw [nthW_ge _ _ (by omega), wordElt_nil]
      exact L.one_mem
  have hstg : ∀ m, wordElt (nthW D.R m) ∈ L := by
    intro m
    by_cases hm : m < 331
    · rw [← eqw hL (expC_lt hMw _) (nthW_lt hRw m) (hRk m hm).2]
      exact wordElt_mem_expC hlet _
    · rw [nthW_ge _ _ (by omega), wordElt_nil]
      exact L.one_mem
  have hseg : ∀ s n, wordElt (segC D.R s n) ∈ L := by
    intro s n
    induction n with
    | zero =>
      change wordElt [] ∈ L
      rw [wordElt_nil]
      exact L.one_mem
    | succ n ih =>
      rw [segC_succ, wordElt_append]
      exact L.mul_mem ih (hstg _)
  have hQ := Ck.p
  unfold prd prodOK at hQ
  rw [Bool.and_eq_true] at hQ
  obtain ⟨hQ11, hQb⟩ := hQ
  have hQ11 := (lenLe_iff _ _).1 hQ11
  have hQk : ∀ i < 11, letLt (nthW DQ.Q i) = true ∧
      E (segC D.R (33 * i) 33) (nthW DQ.Q i) = true := by
    intro i hi
    have h := blk_all i hi
    unfold blk blkOK at h
    rwa [Bool.and_eq_true] at h
  have hQw : ∀ w ∈ DQ.Q, (∀ l ∈ w, l < 26) ∧ wordElt w ∈ L := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := exists_nthW _ w hw
    have hl := (letLt_iff _).1 (hQk i (by omega)).1
    refine ⟨hl, ?_⟩
    rw [← eqw hL (segC_lt (nthW_lt hRw) _ _) hl (hQk i (by omega)).2]
    exact hseg _ _
  have hb : CFSG.Sporadic.Fi24.b ∈ L := by
    rw [← wordElt_two, ← eqw hL (catW_lt fun w hw => (hQw w hw).1) (single_lt (by norm_num)) hQb]
    exact wordElt_mem_catW fun w hw => (hQw w hw).2
  have hgen : L = ⊤ := by
    rw [eq_top_iff, ← CFSG.Sporadic.Fi24.closure_ab, Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact Subgroup.subset_closure (Or.inr (Subgroup.mem_centralizer_singleton_iff.2 ha'))
    · exact hb
  exact sporKRest_cover_of_twoCent Nat.prime_five val_five hne1 h1 h2 hc' hh hgen

end Bridge

theorem sporKRestCover_J : SporKRestCover 5 ↥CFSG.Sporadic.Fi24.J :=
  cover_of CertificateChecks.KernelFi24OrbL.pairG_LN

end CFSG.KD.Fi24FiveK

end
