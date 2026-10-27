module

public import Certificates.Kernel.Sporadic.ON8.Defs
public import Certificates.Kernel.Sporadic.ON3.Elements
public import Certificates.Kernel.Sporadic.ON.Final
public import CFSG.Certificates.Kernel.Spor.ONLinWords
public import CFSG.Certificates.Kernel.Spor.ImgEnumSound
public import CFSG.Sporadic.Schreier.ONCheckR3EInputs
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import Certificates.Kernel.Sporadic.ON5.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON8

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.ONLin CFSG.KS.IE CFSG.KS.TW CFSG.KS.Words
open CertificateChecks.KernelSpor.ON (TT UU TT_lt UU_lt TT_UU perm_facts' canon_key pt_of list_eq
  canon_of listA listB colsAK colsBK sortAll trAll mvAll)
open CertificateChecks.KernelSpor.ON3 (ZT QT CT CIT DT D1T D2T D3T D4T M2T M3T mG trW tab_facts
  c_CI word_pair tr_word tr_inv wordL let7 LetM letM_invW invW)

noncomputable abbrev KK : Nat → Nat := key CertificateChecks.KernelSpor.ONV.K

abbrev L (f : Nat → Nat) : Prop := Lin 245520 KK f

theorem strictB_v (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem orbit : Orbit 245520 KK :=
  ⟨canon_key, sort_distinct (pt_of sortAll fun _ => rfl)⟩

theorem spans' : Spans 245520 KK sp := CertificateChecks.KernelSpor.ON.spans canon_key

theorem agree {F G : Nat → Nat} (hF : L F) (hG : L G) (h : onP F G = true) :
    ∀ x < 245520, F x = G x :=
  Lin.eq_of_span orbit spans' hF hG fun t ht => Nat.eq_of_beq_eq_true (allN_spec h t ht)

theorem agree' {F G : Nat → Nat} (hF : L F) (hG : L G) (h : ∀ t < 154, F (sp t) = G (sp t)) :
    ∀ x < 245520, F x = G x :=
  Lin.eq_of_span orbit spans' hF hG h

theorem mv_facts {h : Nat} (hh : h < 245520) :
    tab CertificateChecks.KernelSpor.ONV.A h < 245520 ∧ tab CertificateChecks.KernelSpor.ONV.B h < 245520 ∧
      KK (tab CertificateChecks.KernelSpor.ONV.A h) = mv CertificateChecks.KernelSpor.ONV.LA (KK h) ∧
      KK (tab CertificateChecks.KernelSpor.ONV.B h) = mv CertificateChecks.KernelSpor.ONV.LB (KK h) := by
  have e := pt_of mvAll (fun _ => rfl) h hh
  unfold mvAt at e
  simp only [strictB_v, bAnd_iff, Nat.beq_eq] at e
  obtain ⟨-, a, b, c, d⟩ := e
  exact ⟨Nat.blt_eq.mp a, Nat.blt_eq.mp b, c, d⟩

theorem lin_A : L (TT 0) := by
  have hla := list_eq _ _ (allN_spec listA)
  exact lin_of_mv orbit rfl (canon_of colsAK hla) fun i hi => ⟨(mv_facts hi).1, (mv_facts hi).2.2.1⟩

theorem lin_B : L (TT 1) := by
  have hlb := list_eq _ _ (allN_spec listB)
  exact lin_of_mv orbit rfl (canon_of colsBK hlb) fun i hi => ⟨(mv_facts hi).2.1, (mv_facts hi).2.2.2⟩

theorem strong_dec : ((List.range 5).all fun k =>
    decide (decW (CertificateChecks.KernelSpor.ONV.WC (k + 2)) (CertificateChecks.KernelSpor.ONV.WL (k + 2)) =
      CFSG.ONSchreier.Data.strongWords[k + 2]!) &&
    (CFSG.ONSchreier.Data.strongWords[k + 2]!).all fun l => l != 0 && decide (l.natAbs ≤ k + 2)) =
    true := by
  decide +kernel

theorem lin_strong' : ∀ h < 7, L (TT h) ∧ L (UU h) := by
  refine lin_strong spans' lin_A lin_B (words := CFSG.ONSchreier.Data.strongWords) (nT := 7)
    (fun x hx h hh => perm_facts' x hx h hh) fun j hj h2 => ?_
  have hd := List.all_eq_true.1 strong_dec (j - 2) (List.mem_range.2 (by omega))
  rw [show j - 2 + 2 = j by omega] at hd
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
  obtain ⟨hdec, hlet⟩ := hd
  refine ⟨fun l hl => ?_, fun x hx => ?_⟩
  · have := List.all_eq_true.1 hlet l hl
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at this
    exact this
  · have h := pt_of trAll (fun _ => rfl) x hx
    unfold trAt at h
    have h2 := allBlk_spec ((bAnd_iff _ _).1 h).2 (j - 2) (by change j - 2 < 7 - 2; omega)
    rw [Nat.add_eq, show 2 + (j - 2) = j by omega] at h2
    rw [Nat.eq_of_beq_eq_true h2, trace_eq, hdec]

theorem lin_TT {h : Nat} (hh : h < 7) : L (TT h) := (lin_strong' h hh).1
theorem lin_UU {h : Nat} (hh : h < 7) : L (UU h) := (lin_strong' h hh).2

theorem lin_word7 {w : List Int} (hw : LetM 7 w) : L fun x => w.foldr (GZ TT UU) x :=
  lin_word (m := 7) (fun _ hh => ⟨lin_TT hh, lin_UU hh⟩) w hw

theorem lin_trW {k : Nat} (hk : k < 17) : L (trW k) :=
  (lin_word7 (let7 hk)).congr fun x _ => (tr_word TT UU (by omega) x).symm

theorem lin_trWI {k : Nat} (hk : k < 17) : L (trW (k + 23)) :=
  (lin_word7 (letM_invW (let7 hk))).congr fun x _ => (tr_inv TT UU (by omega) x).symm

theorem lin_ZT : L ZT := (lin_trW (k := 0) (by norm_num)).congr fun _ hx => (tab_facts hx).1.symm
theorem lin_QT : L QT := (lin_trW (k := 1) (by norm_num)).congr fun _ hx => (tab_facts hx).2.1.symm
theorem lin_CT : L CT := (lin_trW (k := 2) (by norm_num)).congr fun _ hx => (tab_facts hx).2.2.1.symm
theorem lin_M2T : L M2T :=
  (lin_trW (k := 7) (by norm_num)).congr fun _ hx => (tab_facts hx).2.2.2.2.2.2.2.2.1.symm
theorem lin_M3T : L M3T :=
  (lin_trW (k := 8) (by norm_num)).congr fun _ hx => (tab_facts hx).2.2.2.2.2.2.2.2.2.1.symm

theorem lin_CIT : L CIT :=
  Lin.inv spans' lin_CT fun x hx =>
    ⟨(CertificateChecks.KernelSpor.ON3.ci_get x hx).2, (tab_facts hx).2.2.2.1⟩

theorem lin_DT {j : Nat} (hj : j < 4) : L (DT j) := by
  interval_cases j
  · exact (lin_trW (k := 3) (by norm_num)).congr fun x hx => (tab_facts hx).2.2.2.2.1.symm
  · exact (lin_trW (k := 4) (by norm_num)).congr fun x hx => (tab_facts hx).2.2.2.2.2.1.symm
  · exact (lin_trW (k := 5) (by norm_num)).congr fun x hx => (tab_facts hx).2.2.2.2.2.2.1.symm
  · exact (lin_trW (k := 6) (by norm_num)).congr fun x hx => (tab_facts hx).2.2.2.2.2.2.2.1.symm

theorem lin_mG {j : Nat} (hj : j < 3) : L (mG j) := by
  interval_cases j
  · exact lin_ZT
  · exact lin_M2T
  · exact lin_M3T

theorem lin_dcK {j : Nat} (hj : j < 4) : L (dcK j) := by
  unfold dcK
  exact Lin.comp lin_CIT (Lin.comp (lin_DT hj) lin_CT)

theorem lin_dcIK {j : Nat} (hj : j < 4) : L (dcIK j) := by
  have h : L (dIK j) := by
    have := lin_trWI (k := 3 + j) (by omega)
    unfold dIK
    refine this.congr fun x _ => ?_
    rw [show 3 + j + 23 = Nat.add 26 j by simp only [Nat.add_eq]; omega]
  unfold dcIK
  exact Lin.comp lin_CIT (Lin.comp h lin_CT)

theorem lin_hIK : L hIK := lin_trWI (k := 7) (by norm_num)

theorem nIf_lt {j : Nat} (hj : j < 4) (t e : Nat) : nIf(Nat.blt j 4, t, e) = t := by
  rw [Nat.blt_eq.mpr hj]

theorem nIf_ge {j : Nat} (hj : ¬ j < 4) (t e : Nat) : nIf(Nat.blt j 4, t, e) = e := by
  rw [Bool.eq_false_iff.2 fun h => hj (Nat.blt_eq.mp h)]

theorem lin_dhG {j : Nat} : L (dhG j) := by
  by_cases h4 : j < 4
  · exact (lin_dcK h4).congr fun x _ => (nIf_lt h4 _ _).symm
  · exact lin_M2T.congr fun x _ => (nIf_ge h4 _ _).symm

theorem lin_dhI {j : Nat} : L (dhI j) := by
  by_cases h4 : j < 4
  · exact (lin_dcIK h4).congr fun x _ => (nIf_lt h4 _ _).symm
  · exact lin_hIK.congr fun x _ => (nIf_ge h4 _ _).symm

@[expose] def words8 : List (List Int) :=
  CFSG.ONSchreier.hWordsDH.toList ++ [CFSG.ONSchreier.liftWordDH] ++ CFSG.ONSchreier.mWordsDH.toList

theorem words8_dec : ((List.range 8).all fun k =>
    decide (decW (ON8W.WC k) (ON8W.WL k) = words8.getD k []) &&
    (words8.getD k []).all fun l => l != 0 && decide (l.natAbs ≤ 5)) = true := by
  decide +kernel

theorem wDH_eq {k : Nat} (hk : k < 8) (x : Nat) :
    wDH k x = (words8.getD k []).foldr (GZ dhG dhI) x := by
  have h := List.all_eq_true.1 words8_dec k (List.mem_range.2 hk)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  unfold wDH
  rw [trace_eq, h.1]

theorem let5 {k : Nat} (hk : k < 8) : ∀ l ∈ words8.getD k [], l ≠ 0 ∧ l.natAbs ≤ 5 := by
  have h := List.all_eq_true.1 words8_dec k (List.mem_range.2 hk)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  intro l hl
  have := List.all_eq_true.1 h.2 l hl
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at this
  exact this

theorem lin_wDH {k : Nat} (hk : k < 8) : L (wDH k) :=
  (lin_word (m := 5) (fun _ _ => ⟨lin_dhG, lin_dhI⟩) _ (let5 hk)).congr
    fun x _ => (wDH_eq hk x).symm

theorem lin_vK : L vK := by
  unfold vK
  exact Lin.comp lin_CIT (Lin.comp lin_ZT lin_CT)

theorem eD_eq (k x : Nat) : eD k x = elt dcK PD LD k x := eltR_eq _ _ _ k k x
theorem eH_eq (k x : Nat) : eH k x = elt hGK PH LH k x := eltR_eq _ _ _ k k x

end CertificateChecks.KernelSpor.ON8

end
