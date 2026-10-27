
module

public import Certificates.Kernel.Sporadic.ONNQ.Facts
public import CFSG.Certificates.Kernel.Spor.ONNQPerm
public import CFSG.Certificates.Kernel.Spor.SlpCard
public import CFSG.Sporadic.ONOddCore.PrimBase
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.Sporadic.ONOddCore.FaithfulProj
public import CFSG.Sporadic.ONOddCore.PrimPt
public import CFSG.Sporadic.ONOddCore.TreeOrbit
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CertificateChecks.KernelSpor.ONNQ

open CFSG.KS CFSG.KS.ONNQ CFSG.KS.SC CFSG.KS.Words CFSG.ONSchreier CFSG.ONSchreier.Native
  CFSG.Sporadic.ONOddCore
open CFSG.LocalAnalysis.RankThreeTheoremC.ONPair

set_option maxRecDepth 400000

attribute [local irreducible] nqRho nqRhoA nqSig nqSigA nqAP nqL2 d0 d1 dArr0 dArr1 permF

@[expose] noncomputable def nqP (h : ℕ) : Equiv.Perm (Fin 122760) := permF 122760 (TT h)

theorem nqP_permF {h : ℕ} (hh : h < 8) : PermF 122760 (TT h) :=
  ⟨fun x hx => (nq_perm x hx h hh).1, fun x hx y hy e => by
    rw [← (nq_perm x hx h hh).2.2, ← (nq_perm y hy h hh).2.2, e]⟩

theorem TT_eq {h : ℕ} (hh : h < 8) (x : Fin 122760) : TT h x = (nqP h x : ℕ) := by
  unfold nqP
  exact (permF_val (nqP_permF hh) x).symm

theorem UU_eq {h : ℕ} (hh : h < 8) (x : Fin 122760) : UU h x = ((nqP h)⁻¹ x : ℕ) := by
  have hi := permF_inv (nqP_permF hh) (fun x hx => (nq_perm x hx h hh).2.1)
    (fun x hx => (nq_perm x hx h hh).2.2)
  unfold nqP
  rw [← hi.2, permF_val hi.1]

theorem twH_zero_lt : ∀ h < 8, twH 0 h < 8 := fun _ hh => hh

theorem twH_vals : twH 0 0 = 0 ∧ twH 0 1 = 1 ∧ twH 0 2 = 2 ∧ twH 0 3 = 3 ∧ twH 1 0 = 5 ∧
    twH 1 1 = 1 ∧ twH 1 2 = 6 ∧ twH 1 3 = 7 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem twH_one_lt : ∀ h < 8, twH 1 h < 8 := by
  intro h hh
  interval_cases h <;> decide

theorem ev2 {b : ℕ} (hb : ∀ h < 8, twH b h < 8) {w : List ℤ} (hw : plettersOK 2 w = true)
    (x : Fin 122760) : ev TT UU b w x = (nqEv2 (nqP (twH b 0)) (nqP (twH b 1)) w x : ℕ) := by
  rw [ev_eq8 (f := nqP) (fun h hh y => TT_eq hh y) (fun h hh y => UU_eq hh y) hb
    (plettersOK_mono (by norm_num) w hw) x]
  exact congrArg (fun P : Equiv.Perm (Fin 122760) => (P x : ℕ))
    (evalWord_le_two (j := 8) (by norm_num) (fun h => nqP (twH b h)) hw)

theorem evh {b : ℕ} (hb : ∀ h < 8, twH b h < 8) {w : List ℤ} (hw : plettersOK 2 w = true)
    (x : Fin 122760) :
    ev TT UU b (w.map (relab (· + 2))) x = (nqEv2 (nqP (twH b 2)) (nqP (twH b 3)) w x : ℕ) := by
  rw [ev_eq8 (f := nqP) (fun h hh y => TT_eq hh y) (fun h hh y => UU_eq hh y) hb
    (plettersOK_relab (fun h hh => by omega) w hw) x]
  exact congrArg (fun P : Equiv.Perm (Fin 122760) => (P x : ℕ))
    (evalWord_relab_two (j := 8) (fun h => nqP (twH b h)) (μ := (· + 2)) (by norm_num)
      (by norm_num) hw)

theorem nqP_word {j : ℕ} (hj : j < 8) (h2 : 2 ≤ j)
    (hw : plettersOK 8 (decW (ONQ.WC j) (ONQ.WL j)) = true) :
    nqP j = Quiver.SchreierGraph.evalWord (fun h : Fin 8 => nqP h)
      (ptoLetters 8 (decW (ONQ.WC j) (ONQ.WL j))) :=
  Equiv.ext fun x => Fin.ext (by
    rw [← TT_eq hj x, nq_trace x x.isLt j hj h2]
    exact foldr_GZ_eq (T := TT) (U := UU) (f := nqP) (fun h hh y => TT_eq hh y)
      (fun h hh y => UU_eq hh y) _ hw x)

section Tables

theorem nqP_zero : nqP 0 = d0 := Equiv.ext fun x => Fin.ext (by
  have e1 : TT 0 x = (nqP 0 x : ℕ) := TT_eq (h := 0) (by norm_num) x
  have e2 : dArr0[(x : ℕ)]! = TT 0 x := (nq_tab01 x x.isLt).1
  have e3 : dArr0[(x : ℕ)]! = (d0 x : ℕ) := prep_dArr0 x
  rw [← e1, ← e2, e3])

theorem nqP_one : nqP 1 = d1 := Equiv.ext fun x => Fin.ext (by
  have e1 : TT 1 x = (nqP 1 x : ℕ) := TT_eq (h := 1) (by norm_num) x
  have e2 : dArr1[(x : ℕ)]! = TT 1 x := (nq_tab01 x x.isLt).2
  have e3 : dArr1[(x : ℕ)]! = (d1 x : ℕ) := prep_dArr1 x
  rw [← e1, ← e2, e3])

theorem nqP_two : nqP 2 = nqRho h1Word := by
  rw [nqP_word (j := 2) (by norm_num) (by norm_num) (by rw [nq_tabWords.1]; decide),
    nq_tabWords.1, evalWord_le_two (by norm_num) nqP (by decide +kernel), nqP_zero, nqP_one,
    nqRho]

theorem nqP_three : nqP 3 = nqRho h2Word := by
  rw [nqP_word (j := 3) (by norm_num) (by norm_num) (by rw [nq_tabWords.2.1]; decide),
    nq_tabWords.2.1, evalWord_le_two (by norm_num) nqP (by decide +kernel), nqP_zero, nqP_one,
    nqRho]

theorem nqP_four : nqP 4 = nqRho alphaW1 := by
  have hw4 : decW (ONQ.WC 4) (ONQ.WL 4) = alphaW1 := nq_tabWords.2.2.1
  rw [nqP_word (j := 4) (by norm_num) (by norm_num) (by rw [hw4]; decide +kernel),
    hw4, evalWord_le_two (by norm_num) nqP (by decide +kernel), nqP_zero, nqP_one, nqRho]

theorem nqP_five : nqP 5 = nqAP := by
  rw [nqP_word (j := 5) (by norm_num) (by norm_num)
      (by rw [nq_tabWords.2.2.2.1]; decide +kernel),
    nq_tabWords.2.2.2.1,
    show ([5, 5, 5, 5, 5] : List ℤ) = [1, 1, 1, 1, 1].map (relab fun _ => 4) by decide +kernel,
    evalWord_relab_two nqP (μ := fun _ => 4) (by norm_num) (by norm_num) (by decide +kernel)]
  have h5 : ([1, 1, 1, 1, 1] : List ℤ) = [1] ++ ([1] ++ ([1] ++ ([1] ++ [1]))) := rfl
  have ha : alphaWordA = alphaW1 ++ (alphaW1 ++ (alphaW1 ++ (alphaW1 ++ alphaW1))) := rfl
  have h4 : nqEv2 d0 d1 alphaW1 = nqP 4 := by rw [nqP_four, nqRho]
  rw [h5, nqEv2_append, nqEv2_append, nqEv2_append, nqEv2_append, nqEv2_one, nqAP, nqRho, ha,
    nqEv2_append, nqEv2_append, nqEv2_append, nqEv2_append, h4]

theorem nqP_six : nqP 6 = nqRhoA h1Word := by
  rw [nqP_word (j := 6) (by norm_num) (by norm_num) (by rw [nq_tabWords.2.2.2.2.1]; decide),
    nq_tabWords.2.2.2.2.1,
    show h1Word.map (fun l => if l = 1 then 6 else if l = -1 then -6 else l) =
      h1Word.map (relab fun h => if h = 0 then 5 else 1) by decide +kernel,
    evalWord_relab_two nqP (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  change nqEv2 (nqP 5) (nqP 1) h1Word = _
  rw [nqP_five, nqP_one, nqRhoA]

theorem nqP_seven : nqP 7 = nqRhoA h2Word := by
  rw [nqP_word (j := 7) (by norm_num) (by norm_num) (by rw [nq_tabWords.2.2.2.2.2]; decide),
    nq_tabWords.2.2.2.2.2,
    show h2Word.map (fun l => if l = 1 then 6 else if l = -1 then -6 else l) =
      h2Word.map (relab fun h => if h = 0 then 5 else 1) by decide +kernel,
    evalWord_relab_two nqP (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  change nqEv2 (nqP 5) (nqP 1) h2Word = _
  rw [nqP_five, nqP_one, nqRhoA]

@[expose] def nqUnsh (w : List ℤ) : List ℤ := w.map fun l => if 0 < l then l - 2 else l + 2

theorem letG {a : ℕ} (ha : a < 36) : plettersOK 2 (wd (ONQ.D a)) = true := by
  have h := List.all_eq_true.1 (nq_letters.1 a ha)
  refine List.all_eq_true.2 fun l hl => ?_
  have hl' := h l hl
  simp only [ne_eq, decide_eq_true_eq] at hl'
  simp only [bne_iff_ne, ne_eq, Bool.and_eq_true, decide_eq_true_eq]
  exact hl'

theorem letH {v : ℕ} (hv1 : 36 ≤ v) (hv2 : v < 496) :
    plettersOK 2 (nqUnsh (wd (ONQ.D v))) = true ∧
      (nqUnsh (wd (ONQ.D v))).map (relab (· + 2)) = wd (ONQ.D v) := by
  have h := nq_letters.2 (v - 36) (by omega)
  rw [show 36 + (v - 36) = v by omega] at h
  have h' := List.all_eq_true.1 h
  refine ⟨List.all_eq_true.2 fun l hl => ?_, ?_⟩
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hl
    have hz' := h' z hz
    simp only [decide_eq_true_eq] at hz'
    have hc : z = 3 ∨ z = 4 ∨ z = -3 ∨ z = -4 := by omega
    rcases hc with rfl | rfl | rfl | rfl <;> decide
  · unfold nqUnsh
    rw [List.map_map]
    conv_rhs => rw [← List.map_id (wd (ONQ.D v))]
    refine List.map_congr_left fun z hz => ?_
    have hz' := h' z hz
    simp only [decide_eq_true_eq] at hz'
    have hc : z = 3 ∨ z = 4 ∨ z = -3 ∨ z = -4 := by omega
    rcases hc with rfl | rfl | rfl | rfl <;> decide

theorem let8 {v : ℕ} (hv : v < 496) : plettersOK 8 (wd (ONQ.D v)) = true := by
  rcases Nat.lt_or_ge v 36 with h | h
  · exact plettersOK_mono (by norm_num) _ (letG h)
  · rw [← (letH h hv).2]
    exact plettersOK_relab (fun h hh => by omega) _ (letH h hv).1

theorem evR0 {w : List ℤ} (hw : plettersOK 2 w = true) (x : Fin 122760) :
    ev TT UU 0 w x = (nqRho w x : ℕ) := by
  rw [ev2 twH_zero_lt hw x, twH_vals.1, twH_vals.2.1, nqP_zero, nqP_one, nqRho]

theorem evR1 {w : List ℤ} (hw : plettersOK 2 w = true) (x : Fin 122760) :
    ev TT UU 1 w x = (nqRhoA w x : ℕ) := by
  rw [ev2 twH_one_lt hw x, twH_vals.2.2.2.2.1, twH_vals.2.2.2.2.2.1, nqP_five, nqP_one, nqRhoA]

theorem evG0 {a : ℕ} (ha : a < 36) (x : Fin 122760) :
    ev TT UU 0 (wd (ONQ.D a)) x = (nqRho (wd (ONQ.D a)) x : ℕ) :=
  evR0 (letG ha) x

theorem evG1 {a : ℕ} (ha : a < 36) (x : Fin 122760) :
    ev TT UU 1 (wd (ONQ.D a)) x = (nqRhoA (wd (ONQ.D a)) x : ℕ) :=
  evR1 (letG ha) x

theorem evH0' {w : List ℤ} (hw : plettersOK 2 w = true) (x : Fin 122760) :
    ev TT UU 0 (w.map (relab (· + 2))) x = (nqSig w x : ℕ) := by
  rw [evh twH_zero_lt hw x, twH_vals.2.2.1, twH_vals.2.2.2.1, nqP_two, nqP_three, nqSig]

theorem evH1' {w : List ℤ} (hw : plettersOK 2 w = true) (x : Fin 122760) :
    ev TT UU 1 (w.map (relab (· + 2))) x = (nqSigA w x : ℕ) := by
  rw [evh twH_one_lt hw x, twH_vals.2.2.2.2.2.2.1, twH_vals.2.2.2.2.2.2.2, nqP_six, nqP_seven,
    nqSigA]

theorem evH0 {v : ℕ} (hv1 : 36 ≤ v) (hv2 : v < 496) (x : Fin 122760) :
    ev TT UU 0 (wd (ONQ.D v)) x = (nqSig (nqUnsh (wd (ONQ.D v))) x : ℕ) := by
  conv_lhs => rw [← (letH hv1 hv2).2]
  exact evH0' (letH hv1 hv2).1 x

theorem evH1 {v : ℕ} (hv1 : 36 ≤ v) (hv2 : v < 496) (x : Fin 122760) :
    ev TT UU 1 (wd (ONQ.D v)) x = (nqSigA (nqUnsh (wd (ONQ.D v))) x : ℕ) := by
  conv_lhs => rw [← (letH hv1 hv2).2]
  exact evH1' (letH hv1 hv2).1 x

theorem fin0 : ((0 : Fin 122760) : ℕ) = 0 := rfl

theorem nqL2_val : (nqL2 : ℕ) = 58818 := by
  have h := nq_head.1
  rw [nq_items.2.2.2.2] at h
  have e := evR0 (w := u2Word) (by decide +kernel) 0
  rw [fin0, h] at e
  unfold nqL2
  exact e.symm

theorem hsh_relab : ∀ w : List ℤ, plettersOK 2 w = true → hsh w = w.map (relab (· + 2))
  | [], _ => rfl
  | l :: w, hw => by
    obtain ⟨⟨hl0, hl2⟩, hw'⟩ := plettersOK_cons hw
    have ih := hsh_relab w hw'
    unfold hsh at ih ⊢
    rw [List.map_cons, List.map_cons, ih]
    congr 1
    unfold relab
    dsimp only
    split_ifs <;> omega

end Tables

theorem nq_facts : OnanNQFacts := by
  refine ⟨fun a => wd (ONQ.D a), fun k => nqUnsh (wd (ONQ.D (36 + k))),
    fun i => nqUnsh (wd (ONQ.D (40 + i))), fun a i => (wcodes ONQ.D a i).map wcl, ?_⟩
  have hL := nqL2_val
  constructor
  · intro k hk
    apply Fin.ext
    rw [← evH1 (v := 36 + k) (by omega) (by omega) nqL2, hL]
    exact nq_head.2.2.1 k hk
  · apply Fin.ext
    rw [← evG0 (a := 0) (by norm_num) 0, fin0]
    exact nq_head.2.1
  · intro y
    obtain ⟨ks, hks, a, ha, hy⟩ := nq_forest y y.isLt
    refine ⟨ks, hks, a, ha, Fin.ext ?_⟩
    have hb := evG0 ha 0
    rw [fin0] at hb
    rw [hb] at hy
    rw [hy]
    clear hy hb
    induction ks with
    | nil => simp
    | cons k ks ih =>
      have hk : k < 4 := hks k List.mem_cons_self
      rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, List.foldr_cons,
        ← ih fun k' hk' => hks k' (List.mem_cons_of_mem k hk')]
      exact (evH0 (v := 36 + k) (by omega) (by omega) _).symm
  · apply Fin.ext
    rw [← evH1 (v := 40) (by norm_num) (by norm_num) nqL2, hL]
    exact nq_head.2.2.2.1
  · intro e
    apply nq_head.2.2.2.2
    have h := congrArg Fin.val e
    rw [← evH1 (v := 41) (by norm_num) (by norm_num) nqL2, hL] at h
    exact h
  · intro i hi q hq
    have hq4 : ∃ qi < 4, wd (ONQ.D (18736 + qi)) = hsh q ∧ plettersOK 2 q = true := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact ⟨0, by norm_num, nq_items.1, by decide +kernel⟩
      · exact ⟨1, by norm_num, nq_items.2.1, by decide +kernel⟩
      · exact ⟨2, by norm_num, nq_items.2.2.1, by decide +kernel⟩
      · exact ⟨3, by norm_num, nq_items.2.2.2.1, by decide +kernel⟩
    obtain ⟨qi, hqi4, hwq, hpq⟩ := hq4
    obtain ⟨j, hj, e⟩ := nq_coset i hi qi hqi4
    refine ⟨j, hj, Fin.ext ?_⟩
    rw [← hL] at e
    rw [evH1 (v := 40 + i) (by omega) (by omega) nqL2, evH1 (v := 40 + j) (by omega) (by omega) nqL2,
      hwq, hsh_relab q hpq, evH1' hpq] at e
    exact e
  · intro a ha i hi
    have hW : ∀ b, (∀ h < 8, twH b h < 8) → ∀ (S R : List ℤ → Equiv.Perm (Fin 122760)),
        (∀ v, 36 ≤ v → v < 496 → ∀ x : Fin 122760,
          ev TT UU b (wd (ONQ.D v)) x = (S (nqUnsh (wd (ONQ.D v))) x : ℕ)) →
        (∀ x : Fin 122760, ev TT UU b (wd (ONQ.D (a + 1))) x = (R (wd (ONQ.D (a + 1))) x : ℕ)) →
        ∀ x : Fin 122760, ev TT UU b (wit ONQ.D a i) x =
          (Quiver.SchreierGraph.evalWord
            (nqWitL S R (fun a => wd (ONQ.D a)) (fun k => nqUnsh (wd (ONQ.D (36 + k))))
              (fun i => nqUnsh (wd (ONQ.D (40 + i)))) a i)
            ((wcodes ONQ.D a i).map wcl) x : ℕ) := by
      intro b hb S R hS hR
      exact ev_wit (f := nqP) (fun h hh y => TT_eq hh y) (fun h hh y => UU_eq hh y) hb S R _ _ _
        (fun k hk => let8 (v := 36 + k) (by omega)) (let8 (v := 40 + i) (by omega))
        (let8 (v := a + 1) (by omega))
        (fun k hk x => hS (36 + k) (by omega) (by omega) x) (hS (40 + i) (by omega) (by omega))
        hR (wcodes ONQ.D a i)
    have h0 := hW 0 twH_zero_lt nqSig nqRho (fun v h1 h2 x => evH0 h1 h2 x)
      (evG0 (a := a + 1) (by omega))
    have h1 := hW 1 twH_one_lt nqSigA nqRhoA (fun v h1 h2 x => evH1 h1 h2 x)
      (evG1 (a := a + 1) (by omega))
    have h00 := h0 0
    rw [fin0] at h00
    have h1L := h1 nqL2
    have hw := nq_wit a ha i hi
    rw [← hL, h00, h1L] at hw
    rcases hw with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inl ⟨Fin.ext (e1.trans fin0.symm), fun e => e2 (congrArg Fin.val e)⟩
    · exact Or.inr ⟨Fin.ext e1, fun e => e2 ((congrArg Fin.val e).trans fin0)⟩

end CertificateChecks.KernelSpor.ONNQ

end
