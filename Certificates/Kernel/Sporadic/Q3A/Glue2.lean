module

public import Certificates.Kernel.Sporadic.Q3A.Glue
import Mathlib.Data.Finset.Card

public section

namespace CertificateChecks.KernelSpor.Q3AG

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzRecog.Q3A.Check
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Q3AK
open CertificateChecks.KernelSpor.SuzTwCF (P p_comp eqA_P pidn_P)

local notation "pgk" => pg 11 (mask 11)
local notation "pc" => pcomp 1782 11 (mask 11)
local notation "Idn" => pidn 1782 11

theorem countK_eq (n : Nat) (p : Nat → Bool) : countK n p = ((List.range n).filter p).length := by
  unfold countK
  rw [CFSG.KC.Pack.foldN_eq]
  generalize List.range n = L
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.foldr_cons, ih, List.filter_cons, nIf_eq]
    cases p a <;> simp

theorem filter_range_eq {n : Nat} {p : Nat → Bool} {L : List Nat} (hs : L.Pairwise (· < ·))
    (hm : ∀ x ∈ L, x < n ∧ p x = true) (hc : ((List.range n).filter p).length = L.length) :
    (List.range n).filter p = L := by
  have hF : ((List.range n).filter p).Pairwise (· < ·) := List.pairwise_lt_range.filter _
  have hsub : L.toFinset ⊆ ((List.range n).filter p).toFinset := by
    intro x hx
    rw [List.mem_toFinset] at hx ⊢
    exact List.mem_filter.2 ⟨List.mem_range.2 (hm x hx).1, (hm x hx).2⟩
  have hcard : ((List.range n).filter p).toFinset.card ≤ L.toFinset.card := by
    rw [List.toFinset_card_of_nodup hF.nodup, List.toFinset_card_of_nodup hs.nodup, hc]
  have he := Finset.eq_of_subset_of_card_le hsub hcard
  refine List.Pairwise.eq_of_mem_iff hF hs fun x => ?_
  rw [← List.mem_toFinset, ← List.mem_toFinset, he]

theorem all_of_count {n : Nat} {p : Nat → Bool} (hc : countK n p = n) : ∀ i < n, p i = true := by
  rw [countK_eq] at hc
  intro i hi
  have h := List.length_filter_eq_length_iff.1 (by rw [hc, List.length_range])
  exact h i (List.mem_range.2 hi)

theorem pairwise_of_succ {n : Nat} {f : Nat → Nat} (h : ∀ a, a + 1 < n → f a < f (a + 1)) :
    ((List.range n).map f).Pairwise (· < ·) := by
  have mono : ∀ a b, a < b → b < n → f a < f b := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h' | h'
      · exact (ih h' (by omega)).trans (h b hb)
      · subst h'
        exact h a hb
  rw [List.pairwise_map]
  refine (List.pairwise_lt_range).imp_of_mem fun {a b} ha hb hab => mono a b hab ?_
  exact List.mem_range.1 hb

section Checks

variable (hv : ∀ i < 22880, vtOK i = true) (hf : ∀ i < 22880, frOK i = true)

include hf in
theorem fr_parts {i : Nat} (hi : i < 22880) :
    frootK i < 22880 ∧ frootK (frootK i) = frootK i ∧ (frootK i = i → fdepK i = 0) ∧
    (frootK i ≠ i → fparK i < 22880 ∧ flabK i < 2 ∧ fdepK (fparK i) < fdepK i ∧
      frootK (fparK i) = frootK i ∧ actK (XK (flabK i)) (fparK i) = i) := by
  have h := hf i hi
  unfold frOK at h
  rw [sB] at h
  obtain ⟨h1, h2⟩ := (band _ _).1 h
  obtain ⟨h2, h3⟩ := (band _ _).1 h2
  refine ⟨nblt.1 h1, nbeq.1 h2, fun e => ?_, fun e => ?_⟩
  · rw [bIf_eq, ite_eq_left (nbeq.2 e)] at h3
    exact nbeq.1 h3
  · rw [bIf_eq, ite_eq_right (fun e' => e (nbeq.1 e')), sB, sB] at h3
    obtain ⟨h4, h5⟩ := (band _ _).1 h3
    obtain ⟨h5, h6⟩ := (band _ _).1 h5
    obtain ⟨h6, h7⟩ := (band _ _).1 h6
    obtain ⟨h7, h8⟩ := (band _ _).1 h7
    exact ⟨nblt.1 h4, nblt.1 h5, nblt.1 h6, nbeq.1 h7, nbeq.1 h8⟩

theorem roots_parts : countK 22880 (fun i => Nat.beq (frootK i) i) = 5 ∧ frootK 0 = 0 ∧
    frootK 1 = 1 ∧ frootK 2 = 2 ∧ frootK 10 = 10 ∧ frootK 202 = 202 := by
  have h := kRoots
  unfold rootsOK at h
  simp only [band, nbeq] at h
  exact h

theorem roots_list : (List.range 22880).filter (fun i => Nat.beq (frootK i) i) = [0, 1, 2, 10, 202] := by
  obtain ⟨hc, h0, h1, h2, h10, h202⟩ := roots_parts
  refine filter_range_eq (by decide) (fun x hx => ?_) (by rw [← countK_eq, hc]; rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> refine ⟨by norm_num, nbeq.2 ?_⟩ <;> assumption

include hf in
theorem froot_root {y : Nat} (hy : y < 22880) :
    frootK y = 0 ∨ frootK y = 1 ∨ frootK y = 2 ∨ frootK y = 10 ∨ frootK y = 202 := by
  obtain ⟨hlt, hrr, -⟩ := fr_parts hf hy
  have hm : frootK y ∈ (List.range 22880).filter (fun i => Nat.beq (frootK i) i) :=
    List.mem_filter.2 ⟨List.mem_range.2 hlt, nbeq.2 hrr⟩
  rw [roots_list] at hm
  simpa using hm

theorem roots_eq : roots = #[0, 1, 2, 10, 202] := by
  apply Array.ext'
  unfold roots
  rw [Array.toList_filter, Array.toList_range, List.toList_toArray]
  exact (List.filter_congr fun i hi => by rw [froot_get (List.mem_range.1 hi), beqN]).trans
    roots_list

theorem isInvol_P {g : Array Nat} {G : Nat} (h : P g G) : isInvol g = invoK G := by
  unfold isInvol invoK
  rw [eqA_P (p_comp h h) pidn_P, eqA_P h pidn_P]
  cases Nat.beq (pc G G) Idn <;> cases Nat.beq G Idn <;> rfl

include hv in
theorem adj0_eq {r : Nat} (hr : r < 22880) : adj0 r = adj0K r := by
  have hq : P (qArr r) (pc (cA r) (pc RHO (cIA r))) :=
    p_comp (p_cArr hr) (p_comp pRho (p_cArrInv hv hr))
  have hq2 := p_comp hq hq
  have e1 : rhoPow 1 = CFSG.Sporadic.SuzRecog.LevelTwoData.rhoArr := ite_eq_left rfl
  have e2 : rhoPow 2 = compA 1782 CFSG.Sporadic.SuzRecog.LevelTwoData.rhoArr
      CFSG.Sporadic.SuzRecog.LevelTwoData.rhoArr := ite_eq_right (by decide)
  have h1 : P (rhoPow 1) RHO := by
    rw [e1]
    exact pRho
  have h2 : P (rhoPow 2) (pc RHO RHO) := by
    rw [e2]
    exact p_comp pRho pRho
  have e3 : adj0 r = ((r != 0) && ((isInvol (compA 1782 (rhoPow 1) (qArr r)) ||
      isInvol (compA 1782 (rhoPow 1) (compA 1782 (qArr r) (qArr r)))) ||
      (isInvol (compA 1782 (rhoPow 2) (qArr r)) ||
      isInvol (compA 1782 (rhoPow 2) (compA 1782 (qArr r) (qArr r)))))) := by
    simp only [adj0, List.any_cons, List.any_nil, Bool.or_false]
  rw [e3]
  rw [isInvol_P (p_comp h1 hq), isInvol_P (p_comp h1 hq2), isInvol_P (p_comp h2 hq),
    isInvol_P (p_comp h2 hq2)]
  unfold adj0K
  rw [sB, sB, sB, bne, beqN]
  cases Nat.beq r 0 <;> cases invoK (pc RHO (pc (cA r) (pc RHO (cIA r)))) <;>
    cases invoK (pc RHO (pc (pc (cA r) (pc RHO (cIA r))) (pc (cA r) (pc RHO (cIA r))))) <;>
    cases invoK (pc (pc RHO RHO) (pc (cA r) (pc RHO (cIA r)))) <;> rfl

theorem kroot_bool {r : Nat} (h : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 10 ∨ r = 202) :
    Nat.beq (frootK r) r = true := by
  obtain ⟨-, h0, h1, h2, h10, h202⟩ := roots_parts
  rcases h with rfl | rfl | rfl | rfl | rfl <;> exact nbeq.2 (by assumption)

include hv hf in
theorem isNbr0_eq (y : Nat) : isNbr0 y = bAnd(Nat.blt y 22880, Nat.beq (frootK y) 10) := by
  unfold isNbr0
  by_cases hy : y < 22880
  · have hyb : decide (y < 22880) = true := decide_eq_true hy
    rw [hyb, Bool.true_and, (nblt.2 hy : Nat.blt y 22880 = true), froot_get hy]
    have hr := froot_root hf hy
    have hrl : frootK y < 22880 := (fr_parts hf hy).1
    unfold adj0Arr
    rw [getElem!_pos _ _ (by simpa using hrl), Array.getElem_map, Array.getElem_range,
      froot_get hrl, beqN, kroot_bool hr, Bool.true_and, adj0_eq hv hrl]
    rcases hr with h | h | h | h | h <;> rw [h]
    · rfl
    · rw [nbeq_false (by decide : (1 : Nat) ≠ 10)]
      simpa using kA1
    · rw [nbeq_false (by decide : (2 : Nat) ≠ 10)]
      simpa using kA2
    · rw [kA10]
      rfl
    · rw [nbeq_false (by decide : (202 : Nat) ≠ 10)]
      simpa using kA202
  · have hyb : decide (y < 22880) = false := decide_eq_false hy
    rw [hyb, Bool.false_and, Bool.eq_false_iff.2 fun e => hy (nblt.1 e)]

end Checks

end CertificateChecks.KernelSpor.Q3AG

end
