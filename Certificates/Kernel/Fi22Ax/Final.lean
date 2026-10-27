module

public import Certificates.Kernel.Fi22Ax.Checks
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import CFSG.Certificates.Kernel.Spor.PcompFacts
public import CFSG.Certificates.Kernel.Spor.DistinctSound
public import CFSG.Certificates.Kernel.Misc.PairCountSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Ax

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.Co2Shape
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.FischerOddCore CFSG.EvenSporadicStandard.TwoFi22.DS81
open CertificateChecks.KernelSpor

theorem idK3510 : idK 3510 12 (mask 12) = true := by quickRfl

theorem cnId : cn (pidn 3510 12) = true := by quickRfl

theorem cn_pc {p q : Nat} (hp : cn p = true) (hq : cn q = true) : cn (pc p q) = true :=
  canonK_pcomp hp hq

theorem unpack_pc {p q : Nat} (hp : cn p = true) (hq : cn q = true) :
    compA 3510 (unpack 3510 12 p) (unpack 3510 12 q) = unpack 3510 12 (pc p q) :=
  compA_unpack hp hq

section Check

variable {G Ginv : Array (Array Nat)}
  (hG : ∀ k < 10, G[k]! = unpack 3510 12 (Fi22ExtT.L (11 + k)))
  (hGi : ∀ k < 10, Ginv[k]! = unpack 3510 12 (Fi22E2067.EI (11 + k)))
include hG hGi

theorem letter_eq {l : Nat × Bool} (hl : l.1 < 10) :
    axLetterTab G Ginv l = unpack 3510 12 (axLetK l) ∧ cn (axLetK l) = true := by
  obtain ⟨k, b⟩ := l
  have hc := (bAnd_iff _ _).1 (allN_spec cnL k hl)
  cases b
  · exact ⟨hG k hl, hc.1⟩
  · exact ⟨hGi k hl, hc.2⟩

theorem word_eq : ∀ w : List (Nat × Bool), (∀ l ∈ w, l.1 < 10) →
    axWordTab G Ginv w = unpack 3510 12 (axWordK w) ∧ cn (axWordK w) = true
  | [], _ => ⟨(idK_sound idK3510).symm, cnId⟩
  | l :: w, h => by
    obtain ⟨ih1, ih2⟩ := word_eq w fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    obtain ⟨hl1, hl2⟩ := letter_eq hG hGi (h l List.mem_cons_self)
    have e1 : axWordTab G Ginv (l :: w) = compA 3510 (axLetterTab G Ginv l) (axWordTab G Ginv w) :=
      rfl
    have e2 : axWordK (l :: w) = pc (axLetK l) (axWordK w) := rfl
    rw [e1, e2, ih1, hl1]
    exact ⟨unpack_pc hl2 ih2, cn_pc hl2 ih2⟩

omit hG hGi in
theorem words_lt : ∀ i < 10, ∀ l ∈ axBasWords[i]!, l.1 < 10 := by
  have h : (List.range 10).all (fun i => axBasWords[i]!.all fun l => decide (l.1 < 10)) = true := by
    decide
  intro i hi l hl
  have h1 := List.all_eq_true.1 h i (List.mem_range.2 hi)
  exact of_decide_eq_true (List.all_eq_true.1 h1 l hl)

theorem basis_eq {i : Nat} (hi : i < 10) :
    (axBasWords.map (axWordTab G Ginv))[i]! = unpack 3510 12 (BT i) ∧ cn (BT i) = true := by
  have hsz : i < (axBasWords.map (axWordTab G Ginv)).size := by
    rw [Array.size_map]
    exact Nat.lt_of_lt_of_le hi (by decide)
  have hsz' : i < axBasWords.size := by simpa using hsz
  have e : (axBasWords.map (axWordTab G Ginv))[i]! = axWordTab G Ginv axBasWords[i]! := by
    rw [getElem!_pos _ i hsz, Array.getElem_map, getElem!_pos _ i hsz']
  obtain ⟨h1, h2⟩ := word_eq hG hGi _ (words_lt i hi)
  rw [Nat.eq_of_beq_eq_true (allN_spec btOK i hi)]
  exact ⟨e.trans h1, h2⟩

end Check

section Phi

variable {B : Array (Array Nat)} (hB : ∀ i < 10, B[i]! = unpack 3510 12 (BT i) ∧ cn (BT i) = true)
include hB

theorem phi_eq (m : Nat) : ∀ l : List Nat, (∀ i ∈ l, i < 10) →
    l.foldr (fun i P => if m.testBit i then compA 3510 B[i]! P else P) (idA 3510) =
      unpack 3510 12 (l.foldr (fun i P => if m.testBit i then pc (BT i) P else P) (pidn 3510 12)) ∧
    cn (l.foldr (fun i P => if m.testBit i then pc (BT i) P else P) (pidn 3510 12)) = true
  | [], _ => ⟨(idK_sound idK3510).symm, cnId⟩
  | i :: l, h => by
    obtain ⟨ih1, ih2⟩ := phi_eq m l fun j hj => h j (List.mem_cons_of_mem _ hj)
    obtain ⟨hb1, hb2⟩ := hB i (h i List.mem_cons_self)
    simp only [List.foldr_cons]
    by_cases hm : m.testBit i = true
    · rw [if_pos hm, if_pos hm, ih1, hb1]
      exact ⟨unpack_pc hb2 ih2, cn_pc hb2 ih2⟩
    · rw [if_neg hm, if_neg hm]
      exact ⟨ih1, ih2⟩

omit hB in
theorem img_eq (m : Nat) : ∀ l : List Nat,
    pg 12 (mask 12) (l.foldr (fun i P => if m.testBit i then pc (BT i) P else P) (pidn 3510 12)) 0 =
      l.foldr (fun i x => if m.testBit i then pg 12 (mask 12) (BT i) x else x) 0
  | [] => CFSG.KS.PF.pg_pidn (by norm_num) (by norm_num) (by norm_num)
  | i :: l => by
    simp only [List.foldr_cons]
    by_cases hm : m.testBit i = true
    · rw [if_pos hm, if_pos hm, ← img_eq m l]
      exact CFSG.KS.PF.pg_pcomp (by norm_num) (by norm_num)
    · rw [if_neg hm, if_neg hm]
      exact img_eq m l

theorem phiTab_eq (m : Nat) : axPhiTab B m = unpack 3510 12 (axPhiK m) ∧ cn (axPhiK m) = true :=
  phi_eq hB m (List.range 10) fun _ hi => List.mem_range.1 hi

theorem phiTab_zero (m : Nat) : (axPhiTab B m)[0]! = axImgK m := by
  rw [(phiTab_eq hB m).1, CFSG.KC.Misc.PairCount.unpack_get (by norm_num)]
  exact img_eq m (List.range 10)

end Phi

theorem check_ok {G Ginv : Array (Array Nat)} (hGs : G.size = 10) (hGis : Ginv.size = 10)
    (hG : ∀ k < 10, G[k]! = unpack 3510 12 (Fi22ExtT.L (11 + k)))
    (hGi : ∀ k < 10, Ginv[k]! = unpack 3510 12 (Fi22E2067.EI (11 + k))) :
    axPermCheckT G Ginv axBasWords axGc = true := by
  have hB := fun i (hi : i < 10) => basis_eq hG hGi hi
  have hc : ∀ k < 10, cn (Fi22ExtT.L (11 + k)) = true := fun k hk =>
    ((bAnd_iff _ _).1 (allN_spec cnL k hk)).1
  have hci : ∀ k < 10, cn (Fi22E2067.EI (11 + k)) = true := fun k hk =>
    ((bAnd_iff _ _).1 (allN_spec cnL k hk)).2
  have hcj : ∀ k < 10, axConjSl k = true := by
    intro k hk
    interval_cases k
    exacts [cj0, cj1, cj2, cj3, cj4, cj5, cj6, cj7, cj8, cj9]
  have hinj := List.inj_on_of_nodup_map (distinctL_sound distOK).1
  unfold axPermCheckT
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨hGs, hGis⟩, by decide +kernel⟩, ?_⟩, by simp [axBasWords]⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro k hk
    rw [hG k hk, hGi k hk]
    exact (invEqK_sound (Fi22E2067.perm3510 (by omega))).2
  · intro i hi
    obtain ⟨h1, h2⟩ := hB i hi
    rw [h1, unpack_pc h2 h2, ← idK_sound idK3510, eqA_unpack (cn_pc h2 h2) cnId]
    exact allN_spec sqOK i hi
  · intro i hi j hj
    obtain ⟨h1, h2⟩ := hB i hi
    obtain ⟨h3, h4⟩ := hB j hj
    rw [h1, h3, unpack_pc h2 h4, unpack_pc h4 h2, eqA_unpack (cn_pc h2 h4) (cn_pc h4 h2)]
    rcases Nat.lt_trichotomy j i with hji | rfl | hij
    · exact allN_spec (allN_spec commOK i hi) j hji
    · exact Nat.beq_refl _
    · have h := allN_spec (allN_spec commOK j hj) i hij
      rw [Nat.eq_of_beq_eq_true h]
      exact Nat.beq_refl _
  · intro k hk i hi
    obtain ⟨h1, h2⟩ := hB i hi
    obtain ⟨h5, h6⟩ := phiTab_eq hB ((axGc[k]!)[i]!)
    rw [hG k hk, h1, h5, unpack_pc (hc k hk) h2, unpack_pc h6 (hc k hk),
      eqA_unpack (cn_pc (hc k hk) h2) (cn_pc h6 (hc k hk))]
    exact allN_spec (hcj k hk) i hi
  · intro m hm m' hm'
    have e : ∀ x < 1024, ((Array.range 1024).map fun m =>
        (axPhiTab (axBasWords.map (axWordTab G Ginv)) m)[0]!)[x]! = axImgK x := by
      intro x hx
      rw [getElem!_pos _ x (by simpa using hx), Array.getElem_map, Array.getElem_range]
      exact phiTab_zero hB x
    rw [e m hm, e m' (by omega), bne_iff_ne]
    intro he
    have := hinj (List.mem_range.2 hm) (List.mem_range.2 (by omega)) he
    omega

theorem ax_ok : axPermCertificate = true := by
  have hG : ∀ k < 10, ((Array.range 10).map fun k => fi22ExtArr (11 + k))[k]! =
      unpack 3510 12 (Fi22ExtT.L (11 + k)) := by
    intro k hk
    rw [getElem!_pos _ k (by simpa using hk), Array.getElem_map, Array.getElem_range]
    exact Fi22E2067.ext_eq (by omega)
  refine check_ok (by simp) (by simp) hG fun k hk => ?_
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_map, ← getElem!_pos _ k (by simpa using hk),
    hG k hk]
  exact (invEqK_sound (Fi22E2067.perm3510 (by omega))).1

end CertificateChecks.KernelFi22Ax

end
