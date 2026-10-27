
module

public import CFSG.Sporadic.Ru
public import CFSG.Sporadic.Bridge.VecSurj
public import CFSG.Sporadic.Presentation.RuExact
public import Certificates.Data.CFSGNative.Bridge.SurjD
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import Certificates.Kernel.CosetJ.RuTab
public import CFSG.Certificates.Kernel.Orders.Ru.RelsBind
public import CFSG.Certificates.Kernel.Orders.Ru.Checks.R
public import CFSG.Certificates.Kernel.Spor.WordsTxtSound
public import Certificates.Kernel.Sporadic.ON2.GenWords
public meta import Certificates.Data.CFSGNative.Bridge.SurjD
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.RuSurjT CFSG.Sporadic.Bridge.SurjD.Native.ruSurjText

#lc_words CertificateChecks.KernelSpor.RuSurjT CFSG.Sporadic.Bridge.SurjD.Native.ruSurjText

namespace CertificateChecks.KernelSpor.RuRels

meta def surjM : Array (List Int) := CFSG.Sporadic.Bridge.SurjD.Native.ruSpec.surjWords

end CertificateChecks.KernelSpor.RuRels

#kon_words CertificateChecks.KernelSpor.RuSurjW CertificateChecks.KernelSpor.RuRels.surjM

namespace CertificateChecks.KernelSpor.RuRels

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KC.GMSW CFSG.Sporadic.SmallF2 CFSG.Sporadic.Bridge
  CFSG.Sporadic.Bridge.VecSurj CertificateChecks.KernelCosetJ.RuTab
open CertificateChecks.KernelSpor.SmallF2Rels (mat mat_mul mat_one mat_injective mat_inv)

local notation "Dt" => CFSG.Sporadic.Ru.Native.ruData

local notation "MUL" => CFSG.KC.Ord.mulR (nat_lit 2) (nat_lit 6) (nat_lit 168) (nat_lit 28)
  (nat_lit 4) CFSG.KD.OrdRu.L CFSG.KD.OrdRu.H CFSG.KD.OrdRu.CM CFSG.KD.OrdRu.RM

@[expose] noncomputable def RR : List (List (Nat × Bool)) := mkNatK CFSG.KD.OrdRu.rels

@[expose] noncomputable def RS : List (List (Nat × Bool)) := mkSurjK RuSurjT.W (nat_lit 0)

theorem RR_bd : relsBounded RR (nat_lit 5) = true := by quickRfl

theorem RR_len : Nat.beq (lenRels RR) (nat_lit 12) = true := by quickRfl

theorem RR_all :
    relsAll RG MUL RR (nat_lit 5) CFSG.KD.OrdRu.ONE (nat_lit 0) (nat_lit 12) = true := by
  quickRfl

theorem surj_words : CFSG.KS.Words.wordsK RuSurjT.chars RuSurjW.WC RuSurjW.WL 2 = true := by
  quickRfl

theorem surj_list : ((List.ofFn (n := 2) fun k => CFSG.KS.Words.decW (RuSurjW.WC k.val)
    (RuSurjW.WL k.val)) == RuSurjT.W) = true := by
  quickRfl

theorem RS_bd : relsBounded RS (nat_lit 5) = true := by quickRfl

theorem RS_len : Nat.beq (lenRels RS) (nat_lit 2) = true := by quickRfl

theorem RS_all :
    relsAll RG MUL RS (nat_lit 5) CFSG.KD.OrdRu.ONE (nat_lit 0) (nat_lit 2) = true := by
  quickRfl

theorem neg_rel :
    notB (relOK RG MUL [[(2, true)]] (nat_lit 5) CFSG.KD.OrdRu.ONE (nat_lit 0)) = true := by
  quickRfl

theorem neg_surj : notB (relOK RG MUL [appK (sgnWordK (RuSurjT.W.getD 0 [])) [(1, false)]]
    (nat_lit 5) CFSG.KD.OrdRu.ONE (nat_lit 0)) = true := by
  quickRfl

theorem wordProd_phi_eq_one {R : List (List (Nat × Bool))} {n : Nat} (hb : relsBounded R 5 = true)
    (hall : relsAll RG MUL R 5 CFSG.KD.OrdRu.ONE 0 n = true) (hn : Nat.beq (lenRels R) n = true)
    {v : List (Nat × Bool)} (hv : v ∈ R) : wordProd phi v = 1 := by
  apply mat_injective Dt
  rw [mat_one, mat_wordProd le_rfl mat_phi v (CFSG.KS.Ord.relsBounded_spec hb v hv)]
  exact (hom hb hall hn).2 v hv

theorem wordProd_natLetK : ∀ v : List (Nat × Bool), (∀ l ∈ v, l.1 < 3) →
    wordProd (img CFSG.Sporadic.Bridge.SurjD.Native.ruSpec (seedG Dt)) v =
      wordProd phi (v.map natLetK)
  | [], _ => rfl
  | (k, s) :: v, h => by
    have hk : k < 3 := h (k, s) List.mem_cons_self
    have ih := wordProd_natLetK v fun l hl => h l (List.mem_cons_of_mem _ hl)
    have e : natLetK (k, s) = (k + 2, s) := (natLetK_of_ne (by
      have e' : natLetK (k, s) = Bool.rec (motive := fun _ => Nat × Bool) badLet
          (Nat.add k 2, s) (Nat.blt k 7) := rfl
      rw [e', blt_true (by omega)]
      intro h'
      have := congrArg Prod.fst h'
      simp [badLet] at this
      omega)).2
    simp only [wordProd, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, e, phi_img]

theorem relators : ∀ v ∈ TauCeti.Sporadic.ruPresentation.relatorLetters,
    wordProd (img CFSG.Sporadic.Bridge.SurjD.Native.ruSpec (seedG Dt)) v = 1 := by
  rw [CFSG.KD.OrdRu.rels_eq]
  intro v hv
  have hvR : v.map natLetK ∈ RR := by
    rw [RR, mkNatK_eq]
    exact List.mem_map_of_mem hv
  rw [wordProd_natLetK v (CFSG.KS.Ord.relsBounded_spec CFSG.KD.OrdRu.relB v hv)]
  exact wordProd_phi_eq_one RR_bd RR_all RR_len hvR

theorem surjWords_eq : CFSG.Sporadic.Bridge.SurjD.Native.ruSpec.surjWords = RuSurjT.W.toArray := by
  have h := CFSG.KS.Words.wordsK_sound surj_words
  rw [← RuSurjT.eq] at h
  have e : CFSG.Sporadic.Bridge.SurjD.Native.ruSpec.surjWords =
      CFSG.Sporadic.Bridge.ONGPL.Native.parseWords CFSG.Sporadic.Bridge.SurjD.Native.ruSurjText :=
    rfl
  rw [e, h, ← Array.toList_inj, Array.toList_ofFn, List.toList_toArray]
  exact beq_iff_eq.mp surj_list

theorem surjWords_getElem (i : ℕ) :
    CFSG.Sporadic.Bridge.SurjD.Native.ruSpec.surjWords[i]! = RuSurjT.W.getD i [] := by
  rw [surjWords_eq, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, ← Array.getElem?_toList,
    ← List.getD_eq_getElem?_getD, List.toList_toArray]
  rfl

theorem imgG_eq {z : Int} (h : sgnLetK z ≠ badLet) :
    imgG CFSG.Sporadic.Bridge.SurjD.Native.ruSpec (seedG Dt) z =
      if (sgnLetK z).2 then phi (sgnLetK z).1 else (phi (sgnLetK z).1)⁻¹ := by
  obtain ⟨-, -, e⟩ := sgnLetK_of_ne h
  rw [e]
  by_cases hz : 0 < z
  · simp only [imgG, hz, ↓reduceIte]
    rw [phi_img]
  · simp only [imgG, hz, ↓reduceIte, Bool.false_eq_true]
    rw [phi_img]

theorem wordG_imgG (w : List Int) (h : ∀ z ∈ w, sgnLetK z ≠ badLet) :
    CFSG.Sporadic.Th.wordG (imgG CFSG.Sporadic.Bridge.SurjD.Native.ruSpec (seedG Dt)) w =
      wordProd phi (w.map sgnLetK) := by
  induction w with
  | nil => rfl
  | cons z w ih =>
    simp only [CFSG.Sporadic.Th.wordG, wordProd, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih fun z' hz' => h z' (List.mem_cons_of_mem _ hz'), imgG_eq (h z List.mem_cons_self)]

theorem surj_mem {i : ℕ} (hi : i < 2) : (RuSurjT.W.getD i []).map sgnLetK ++ [(i, false)] ∈ RS := by
  rw [RS, mkSurjK_eq]
  exact List.mem_map.2 ⟨i, List.mem_range.2 (by
    have hl : RuSurjT.W.length = 2 := by decide +kernel
    omega), by rw [Nat.zero_add]⟩

theorem surj_ne_bad {i : ℕ} (hi : i < 2) : ∀ z ∈ RuSurjT.W.getD i [], sgnLetK z ≠ badLet :=
  fun _ hz => ne_bad RS_bd (surj_mem hi) (List.mem_append_left _ (List.mem_map_of_mem hz))

theorem surj_letters {i : ℕ} (hi : i < 2) :
    ∀ z ∈ CFSG.Sporadic.Bridge.SurjD.Native.ruSpec.surjWords[i]!, z ≠ 0 ∧ z.natAbs ≤ 3 := by
  rw [surjWords_getElem]
  intro z hz
  obtain ⟨h0, -, e⟩ := sgnLetK_of_ne (surj_ne_bad hi z hz)
  have hb := CFSG.KS.Ord.relsBounded_spec RS_bd _ (surj_mem hi) (sgnLetK z)
    (List.mem_append_left _ (List.mem_map_of_mem hz))
  rw [e] at hb
  refine ⟨h0, ?_⟩
  by_cases hz0 : 0 < z
  · simp only [hz0, ↓reduceIte] at hb
    omega
  · simp only [hz0, ↓reduceIte] at hb
    omega

theorem surj {i : ℕ} (hi : i < 2) :
    CFSG.Sporadic.Th.wordG (imgG CFSG.Sporadic.Bridge.SurjD.Native.ruSpec (seedG Dt))
      CFSG.Sporadic.Bridge.SurjD.Native.ruSpec.surjWords[i]! = phi i := by
  have h1 := wordProd_phi_eq_one RS_bd RS_all RS_len (surj_mem hi)
  rw [CertificateChecks.KernelGMS78.W.wordProd_append] at h1
  rw [surjWords_getElem, wordG_imgG _ (surj_ne_bad hi)]
  have h2 : wordProd phi [(i, false)] = (phi i)⁻¹ := by simp [wordProd]
  rw [h2] at h1
  exact mul_inv_eq_one.1 h1

theorem facts : (∀ v ∈ TauCeti.Sporadic.ruPresentation.relatorLetters,
      wordProd (img CFSG.Sporadic.Bridge.SurjD.Native.ruSpec (seedG Dt)) v = 1) ∧
    (∀ i < 2, ∀ z ∈ CFSG.Sporadic.Bridge.SurjD.Native.ruSpec.surjWords[i]!,
      z ≠ 0 ∧ z.natAbs ≤ 3) ∧
    CFSG.Sporadic.Th.wordG (imgG CFSG.Sporadic.Bridge.SurjD.Native.ruSpec (seedG Dt))
      CFSG.Sporadic.Bridge.SurjD.Native.ruSpec.surjWords[0]! = a Dt ∧
    CFSG.Sporadic.Th.wordG (imgG CFSG.Sporadic.Bridge.SurjD.Native.ruSpec (seedG Dt))
      CFSG.Sporadic.Bridge.SurjD.Native.ruSpec.surjWords[1]! = b Dt := by
  refine ⟨relators, fun i hi => surj_letters hi, ?_, ?_⟩
  · rw [surj (by norm_num)]
    simp [phi]
  · rw [surj (by norm_num)]
    simp [phi]

end CertificateChecks.KernelSpor.RuRels

end
