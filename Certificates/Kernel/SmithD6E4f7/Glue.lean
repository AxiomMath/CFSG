module

public import Certificates.Kernel.SmithD6E4f7.Checks
public import Certificates.Kernel.SmithD6Reps.Glue
public import Certificates.Kernel.SmithD6Uw.Model
public import CFSG.Certificates.Kernel.SmithD6E4f7Sound
import all Certificates.Data.SmithD6Model
import all Certificates.Data.SmithD6Facts

public section

namespace CertificateChecks.SmithD6E4f7

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KD.SmithD6 CFSG.KD.SmithD6Stab CFSG.KD.SmithD6Reps
  CFSG.KD.SmithD6E4 CFSG.GF2Type.SmithTypeE.DMod CertificateChecks.SmithD6Stab
  CertificateChecks.SmithD6Reps

theorem e4_xor_cancel (x y w : Nat) : (x ^^^ w) ^^^ (y ^^^ w) = x ^^^ y := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases x.testBit i <;> cases y.testBit i <;> cases w.testBit i <;> rfl

theorem e4_xor_swap (x y a b : Nat) : (x ^^^ y) ^^^ (a ^^^ b) = (x ^^^ a) ^^^ (y ^^^ b) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases x.testBit i <;> cases y.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> rfl

theorem e4_mf7ApAux_xor(cols : Array Nat) (a b : Nat) : ∀ n,
    mf7ApAux cols (a ^^^ b) n = mf7ApAux cols a n ^^^ mf7ApAux cols b n
  | 0 => by simp [mf7ApAux]
  | n + 1 => by
    simp only [mf7ApAux, Nat.testBit_xor, e4_mf7ApAux_xor cols a b n]
    generalize mf7ApAux cols a n = x
    generalize mf7ApAux cols b n = y
    generalize cols[n]! = w
    cases a.testBit n <;> cases b.testBit n <;> simp [e4_xor_cancel] <;> ac_rfl

theorem e4_applyCols_xor (cols : Array Nat) (a b : Nat) :
    applyCols cols (a ^^^ b) = applyCols cols a ^^^ applyCols cols b := by
  rw [← mf7Ap_eq, ← mf7Ap_eq, ← mf7Ap_eq]
  exact e4_mf7ApAux_xor cols a b _

theorem e4_mf7ApAux_two_pow (cols : Array Nat) (m : Nat) : ∀ n,
    mf7ApAux cols (2 ^ m) n = if m < n then cols[m]! else 0
  | 0 => by simp [mf7ApAux]
  | n + 1 => by
    rw [mf7ApAux, e4_mf7ApAux_two_pow cols m n, Nat.testBit_two_pow]
    by_cases h : m = n
    · subst h
      simp
    · simp only [h, decide_false, Bool.false_eq_true, if_false, Nat.xor_zero]
      by_cases hm : m < n
      · have : m < n + 1 := by omega
        simp [hm, this]
      · have : ¬ m < n + 1 := by omega
        simp [hm, this]

theorem e4_applyCols_two_pow {cols : Array Nat} {m : Nat} (hm : m < cols.size) :
    applyCols cols (2 ^ m) = cols[m]! := by
  rw [← mf7Ap_eq, mf7Ap, e4_mf7ApAux_two_pow, if_pos hm]

theorem comm_of_commL {A B : Array Nat} (hA : A.size = 32) (hB : B.size = 32)
    (h : commL A B = true) : ∀ c < 2 ^ 32,
      applyCols B (applyCols A c) = applyCols A (applyCols B c) := by
  intro c hc
  refine eq_of_xor_of_two_pow (F := fun c => applyCols B (applyCols A c))
    (G := fun c => applyCols A (applyCols B c)) (fun a b => ?_) (fun a b => ?_) (fun m hm => ?_) hc
  · simp only [e4_applyCols_xor]
  · simp only [e4_applyCols_xor]
  · unfold commL at h
    have h' := List.all_eq_true.1 h m (List.mem_range.2 hm)
    rw [beq_iff_eq, mf7Ap_eq, mf7Ap_eq] at h'
    beta_reduce
    rw [e4_applyCols_two_pow (hA ▸ hm), e4_applyCols_two_pow (hB ▸ hm)]
    exact h'.symm

theorem head_parts : (List.range 4).all e4GenOK = true ∧ e4BasisOK = true ∧
    e4WordsOK (J.wtC.flatten.getD 1 0) JE.e4W = true := by
  have h : ((List.range 4).all e4GenOK && e4BasisOK &&
      e4WordsOK (J.wtC.flatten.getD 1 0) JE.e4W) = true := e4_head
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

section Model

variable (hK : lineKeys.toList = J.lineKeysC.flatten)
include hK

theorem inE0_mask : ∀ c < 2 ^ 32, (applyCols (tvCols 0) c ^^^ c) &&& e4Out = 0 := by
  have hb : e4BasisOK = true := head_parts.2.1
  intro c hc
  refine eq_of_xor_of_two_pow (F := fun c => (applyCols (tvCols 0) c ^^^ c) &&& e4Out)
    (G := fun _ => 0) (fun a b => ?_) (fun _ _ => by simp) (fun m hm => ?_) hc
  · beta_reduce
    rw [← xor_and_distrib, e4_applyCols_xor, e4_xor_swap]
  · unfold e4BasisOK at hb
    have h' := List.all_eq_true.1 hb m (List.mem_range.2 hm)
    rw [beq_iff_eq, mf7Ap_eq, ← tvCols_zero hK] at h'
    exact h'

theorem gen_facts {g : Nat} (hg : g < 4) :
    e4Pos.getD g 0 < 365211 ∧ tvCols (e4Pos.getD g 0) = e4Cols g ∧
      ∀ c < 2 ^ 32, applyCols (tvCols (e4Pos.getD g 0)) (applyCols (tvCols 0) c) =
        applyCols (tvCols 0) (applyCols (tvCols (e4Pos.getD g 0)) c) := by
  have hg' := List.all_eq_true.1 head_parts.1 g (List.mem_range.2 hg)
  unfold e4GenOK at hg'
  rw [Bool.and_eq_true, beq_iff_eq] at hg'
  obtain ⟨-, hkey⟩ := key_of_find hg'.1
  have hcols : tvCols (e4Pos.getD g 0) = e4Cols g := by
    rw [tvCols_eq, linePair_eq hK, hkey]
    rfl
  refine ⟨?_, hcols, ?_⟩
  · obtain rfl | rfl | rfl | rfl : g = 0 ∨ g = 1 ∨ g = 2 ∨ g = 3 := by omega
    all_goals decide
  · have hc : commL (tvCols 0) (tvCols (e4Pos.getD g 0)) = true := by
      rw [hcols, tvCols_zero hK]
      exact hg'.2
    exact comm_of_commL (tvCols_size 0) (tvCols_size _) hc

theorem foldr_e4Pos (w : List Nat) (hw : ∀ g ∈ w, g < 4) (c : Nat) :
    (w.map fun g => e4Pos.getD g 0).foldr (fun r c => applyCols (tvCols r) c) c = e4Ap w c := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    rw [List.map_cons, List.foldr_cons, ih (fun g' hg' => hw g' (List.mem_cons_of_mem _ hg')),
      (gen_facts hK (hw g List.mem_cons_self)).2.1, e4Ap, mf7Ap_eq]

theorem e4f7Word_of_pinned (hW : wtArr.toList = J.wtC.flatten) :
    ∃ r₀ < 75735, ∀ i < 75735, (∃ c < 2 ^ 32, applyCols (tvCols 0) c ^^^ c = wt i) →
      ∃ w : List Nat, (∀ r ∈ w, r < 365211 ∧ ∀ c < 2 ^ 32,
        applyCols (tvCols r) (applyCols (tvCols 0) c) =
          applyCols (tvCols 0) (applyCols (tvCols r) c)) ∧
        w.foldr (fun r c => applyCols (tvCols r) c) (wt r₀) = wt i := by
  have hl := SmithD6Wt.wtC_flatten_length
  have hwt : ∀ j < 75735, wt j = J.wtC.flatten.getD j 0 := fun j hj => by
    rw [SmithD6Uw.wt_eq hW (hl ▸ hj), List.getD_eq_getElem _ _ (hl ▸ hj)]
  refine ⟨1, by decide, fun i hi ⟨c, hc, hce⟩ => ?_⟩
  have hmem : wt i ∈ J.wtC.flatten := by
    rw [SmithD6Uw.wt_eq hW (hl ▸ hi)]
    exact List.getElem_mem _
  have hm : wt i &&& e4Out = 0 := by
    rw [← hce]
    exact inE0_mask hK c hc
  obtain ⟨w, hw⟩ := e4AllOK_sound e4_all _ hmem hm
  obtain ⟨hlt, hap⟩ := e4WordsOK_sound head_parts.2.2 _ hw
  refine ⟨w.map fun g => e4Pos.getD g 0, fun r hr => ?_, ?_⟩
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hr
    obtain ⟨h1, -, h3⟩ := gen_facts hK (hlt g hg)
    exact ⟨h1, h3⟩
  · rw [foldr_e4Pos hK w hlt, hwt 1 (by decide)]
    exact hap

end Model

end CertificateChecks.SmithD6E4f7

end
