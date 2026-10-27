module

public import Certificates.Kernel.ONSeven.G17390Defs
public import Certificates.Kernel.ONSeven.Words
public import CFSG.RankThree.Native.ONSevenRestrict

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONS

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.RankThree.Native CFSG.KS.TW CFSG.Sporadic.ON
open CertificateChecks.KernelSpor.ON (TT qon_SA SA_get)
open CertificateChecks.KernelSpor.ON3 (LetM invW)


theorem letM_of_pletters {w : List Int} (h : plettersOK 7 w = true) : LetM 7 w := by
  intro l hl
  simp only [plettersOK, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at h
  exact h l hl

theorem evalS_apply {w : List Int} (hw : plettersOK 7 w = true) (x : Fin N) :
    ((evalS w x : Fin N) : Nat) = WW w x := by
  rw [← prep_onSevenArr hw x, arr_get (letM_of_pletters hw) x.2]

theorem evalS_inv_apply {w : List Int} (hw : plettersOK 7 w = true) (y : Fin N) :
    (((evalS w)⁻¹ y : Fin N) : Nat) = WW (invW w) y := by
  have hlt : WW (invW w) y < N := WW_lt y.2
  have h1 : evalS w ⟨WW (invW w) y, hlt⟩ = y :=
    Fin.ext (by rw [evalS_apply hw]; exact WW_inv' (letM_of_pletters hw) y.2)
  have h2 : (evalS w)⁻¹ y = ⟨WW (invW w) y, hlt⟩ := by
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact h1.symm
  rw [h2]

theorem gW17390_letters : ∀ i < 12, plettersOK 7 (gW17390 i) = true := by
  decide

theorem evalWord_apply : ∀ u : List Int, plettersOK 12 u = true → ∀ x : Fin N,
    ((Quiver.SchreierGraph.evalWord (fun h : Fin 12 => evalS (gW17390 h.val))
      (ptoLetters 12 u) x : Fin N) : Nat) = WN17390 u x := by
  intro u
  induction u with
  | nil =>
    intro _ x
    simp [ptoLetters, WN17390]
  | cons l u ih =>
    intro hu x
    simp only [plettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hu
    obtain ⟨⟨hl0, hlj⟩, hu⟩ := hu
    have hu' : plettersOK 12 u = true := by
      simpa [plettersOK, List.all_eq_true] using hu
    have hcons : ptoLetters 12 (l :: u) = (⟨l.natAbs - 1, by omega⟩, decide (0 < l)) ::
        ptoLetters 12 u := by
      simp [ptoLetters, hl0, hlj]
    have hW : WN17390 (l :: u) x =
        GZ (fun i => WW (gW17390 i)) (fun i => WW (invW (gW17390 i))) l (WN17390 u x) := rfl
    have hg := gW17390_letters (l.natAbs - 1) (by omega)
    rw [hcons, hW]
    unfold GZ
    by_cases hp : 0 < l
    · rw [decide_eq_true hp, Quiver.SchreierGraph.evalWord_cons_true, Equiv.Perm.mul_apply,
        if_pos hp, evalS_apply hg, ih hu' x, show l.toNat - 1 = l.natAbs - 1 by omega]
    · rw [show decide (0 < l) = false by simpa using hp, Quiver.SchreierGraph.evalWord_cons_false,
        Equiv.Perm.mul_apply, if_neg hp, evalS_inv_apply hg, ih hu' x,
        show (-l).toNat - 1 = l.natAbs - 1 by omega]

theorem sgen_apply {j : Nat} (hj : j < 7) (x : Fin N) : ((sgen j x : Fin N) : Nat) = TT j x := by
  rw [← (onSeven_prep_strong hj).1 x, qon_SA, SA_get hj x.2]

theorem evalWord_mem_Pv (u : List Int) :
    Quiver.SchreierGraph.evalWord (fun h : Fin 12 => evalS (gW17390 h.val)) (ptoLetters 12 u) ∈
      Pv :=
  (Subgroup.closure_le _).2 (by rintro _ ⟨h, rfl⟩; exact evalS_mem _)
    (Quiver.SchreierGraph.evalWord_mem_closure _ _)

theorem evalWord_eq_sgen {u : List Int} (hu : plettersOK 12 u = true) {j : Nat} (hj : j < 7)
    (h0 : WN17390 u 0 = TT j 0) (h1 : WN17390 u 227759 = TT j 227759)
    (h2 : WN17390 u 100817 = TT j 100817) :
    Quiver.SchreierGraph.evalWord (fun h : Fin 12 => evalS (gW17390 h.val)) (ptoLetters 12 u) =
      sgen j := by
  refine eq_of_three (evalWord_mem_Pv u) (sgen_mem j) ?_ ?_ ?_ <;> apply Fin.ext <;>
    rw [evalWord_apply u hu, sgen_apply hj]
  · exact h0
  · exact h1
  · exact h2

abbrev centSet17390 : Set (Equiv.Perm (Fin N)) :=
  {g | ∃ r : Fin 3, g ∈ evalList onSevenCentWords[(r : ℕ)]!}

theorem mem_closure_of_word (u : List Int) :
    Quiver.SchreierGraph.evalWord (fun h : Fin 12 => evalS (gW17390 h.val)) (ptoLetters 12 u) ∈
      Subgroup.closure centSet17390 := by
  have hsz : ∀ i < 12, i % 4 < (onSevenCentWords[i / 4]!).size := by decide
  refine Subgroup.closure_mono ?_ (Quiver.SchreierGraph.evalWord_mem_closure _ _)
  rintro _ ⟨h, rfl⟩
  exact ⟨⟨h.val / 4, by omega⟩, mem_evalList_iff.2 ⟨h.val % 4, hsz h.val h.isLt, rfl⟩⟩

theorem closure_cent_eq_Pv {u v : List Int} (hu : plettersOK 12 u = true)
    (hv : plettersOK 12 v = true) (c0 : ch17390 u v 0 = true) (c1 : ch17390 u v 227759 = true)
    (c2 : ch17390 u v 100817 = true) : Subgroup.closure centSet17390 = Pv := by
  simp only [ch17390, Bool.and_eq_true] at c0 c1 c2
  have hA := evalWord_eq_sgen hu (j := 0) (by norm_num) (Nat.eq_of_beq_eq_true c0.1)
    (Nat.eq_of_beq_eq_true c1.1) (Nat.eq_of_beq_eq_true c2.1)
  have hB := evalWord_eq_sgen hv (j := 1) (by norm_num) (Nat.eq_of_beq_eq_true c0.2)
    (Nat.eq_of_beq_eq_true c1.2) (Nat.eq_of_beq_eq_true c2.2)
  obtain ⟨-, -, -, -, -, hs0, hs1, -⟩ := cert_on_schreier_action_data
  refine le_antisymm ((Subgroup.closure_le _).2 ?_) ((Subgroup.closure_le _).2 ?_)
  · rintro g ⟨r, hr⟩
    exact evalList_mem hr
  · rintro _ (rfl | rfl)
    · rw [← hs0, ← hA]
      exact mem_closure_of_word u
    · rw [← hs1, ← hB]
      exact mem_closure_of_word v

end CertificateChecks.KernelSpor.ONS

end
