module

public import Certificates.Kernel.Schur.Basic
public import CFSG.Certificates.Kernel.McL.Model
public import CFSG.Certificates.Kernel.McL.RangeX
import CFSG.Certificates.Kernel.McLModelSound
import Certificates.Kernel.McL.Words
public import Mathlib.Data.List.GetD
import CFSG.Sporadic.Presentation.Common
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CertificateChecks.KernelSchur

open CFSG.Certificates CFSG.Certificates.KB CFSG.KC TauCeti

theorem lift_mk_eq_sword {H : Type*} [Group H] {n : ℕ} (z : ℕ → H) (w : List (Fin n × Bool)) :
    FreeGroup.lift (fun i : Fin n => z i.val) (FreeGroup.mk w) =
      sword z (w.map fun l => (l.1.val, l.2)) := by
  rw [FreeGroup.lift_mk, sword, List.map_map]
  congr 1
  apply List.map_congr_left
  rintro ⟨a, b⟩ _
  cases b <;> simp

theorem card_closure_le (P : GroupPresentation) [Finite P.Group] {H : Type*} [Group H]
    (z : ℕ → H) (hz : ∀ r ∈ P.relatorLetters, sword z r = 1) :
    Nat.card (Subgroup.closure (z '' {i | i < P.generatorCount})) ≠ 0 ∧
      Nat.card (Subgroup.closure (z '' {i | i < P.generatorCount})) ≤ Nat.card P.Group := by
  set f : Fin P.generatorCount → H := fun i => z i.val
  have hrel : ∀ r ∈ P.relatorSet, FreeGroup.lift f r = 1 := by
    intro r hr
    rw [CFSG.Sporadic.Presentation.relatorSet_eq] at hr
    simp only [Set.mem_ofPred_eq, List.mem_map] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    rw [lift_mk_eq_sword]
    apply hz
    rw [GroupPresentation.relatorLetters_def]
    exact List.mem_map_of_mem hw
  set φ := PresentedGroup.toGroup hrel
  have hrange : φ.range = Subgroup.closure (z '' {i | i < P.generatorCount}) := by
    rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure]
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_range, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨j.val, j.isLt, by simp [φ, f, PresentedGroup.toGroup.of]⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨_, ⟨⟨i, hi⟩, rfl⟩, by simp [φ, f, PresentedGroup.toGroup.of]⟩
  rw [← hrange]
  have hle : Nat.card φ.range ≤ Nat.card P.Group :=
    Nat.card_le_card_of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have : Finite φ.range := Finite.of_surjective _ φ.rangeRestrict_surjective
  exact ⟨Nat.card_pos.ne', hle⟩

@[expose] noncomputable def ent (w : List (ℕ × Bool)) : ℕ := 4 * w.length + 2 ^ 12 * Schur.Pack.pk w

theorem wLen_ent {w : List (ℕ × Bool)} (h : w.length < 1024) :
    LceS.wLen (ent w) = w.length := by
  rw [LceS.wLen, ent]
  change ((4 * w.length + 2 ^ 12 * Schur.Pack.pk w) >>> 2) &&& (2 ^ 10 - 1) = w.length
  rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem wWord_ent (w : List (ℕ × Bool)) (h : w.length < 1024) :
    LceS.wWord (ent w) = Schur.Pack.pk w := by
  rw [LceS.wWord, ent]
  change (4 * w.length + 2 ^ 12 * Schur.Pack.pk w) >>> 12 = Schur.Pack.pk w
  rw [Nat.shiftRight_eq_div_pow]
  omega

theorem bval_rel {G : Type*} [Group G] (y : ℕ → G) {REL : ℕ → ℕ} {rels : List (List (ℕ × Bool))}
    (hb : ∀ r < rels.length, REL r = ent (rels.getD r []))
    (hl : ∀ w ∈ rels, w.length < 1024 ∧ ∀ x ∈ w, x.1 < 127) :
    ∀ r < rels.length, LCE.bval y (LceS.wWord (REL r)) (LceS.wLen (REL r)) = sword y (rels.getD r []) := by
  intro r hr
  have hm : rels.getD r [] ∈ rels := by
    rw [List.getD_eq_getElem _ _ hr]
    exact List.getElem_mem hr
  rw [hb r hr, wWord_ent _ (hl _ hm).1, wLen_ent (hl _ hm).1]
  exact bval_pk y _ (hl _ hm).2

theorem sword_rels_iff {G : Type*} [Group G] (y : ℕ → G) {REL : ℕ → ℕ}
    {rels : List (List (ℕ × Bool))}
    (hb : ∀ r < rels.length, REL r = ent (rels.getD r []))
    (hl : ∀ w ∈ rels, w.length < 1024 ∧ ∀ x ∈ w, x.1 < 127) :
    (∀ r < rels.length, LCE.bval y (LceS.wWord (REL r)) (LceS.wLen (REL r)) = 1) ↔
      ∀ w ∈ rels, sword y w = 1 := by
  constructor
  · intro h w hw
    obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hw
    rw [← List.getD_eq_getElem _ [] hr, ← bval_rel y hb hl r hr]
    exact h r hr
  · intro h r hr
    rw [bval_rel y hb hl r hr]
    apply h
    rw [List.getD_eq_getElem _ _ hr]
    exact List.getElem_mem hr

theorem model_reads (P : GroupPresentation) [Finite P.Group] (hn : P.generatorCount = 2)
    {rels : List (List (ℕ × Bool))} (hrels : P.relatorLetters = rels)
    {MG REL EP ED OM OJ ON : ℕ → ℕ} {BP nE N0 nLev : ℕ}
    (hb : ∀ r < rels.length, REL r = ent (rels.getD r []))
    (hl : ∀ w ∈ rels, w.length < 1024 ∧ ∀ x ∈ w, x.1 < 127)
    (hgens : McL.Sub.gensOK MG 24 2 = true) (hR : McL.Sub.relsHold MG REL 24 rels.length = true)
    (hlet : McL.RangeX.entsBelow REL rels.length 4 = true)
    (hents : McL.Model.elemsOK MG EP ED 24 2 BP nE = true)
    (hwrap : ∀ e < 4096, EP e = 0 ∨ ∃ e' < nE, EP e = EP e' ∧ ED e = ED e')
    (horb : ∀ l < nLev, McL.Model.orbCount (McL.Model.orbitRun EP ED BP l (OM l) (OJ l)) = ON l ∧
      McL.Model.bpt BP l < 24)
    (hprod : N0 ≤ ∏ l ∈ Finset.range nLev, ON l) (hcard : Nat.card P.Group ≤ N0)
    {G : Type*} [Group G] (y : ℕ → G) (hy : ∀ w ∈ rels, sword y w = 1)
    (w : List (ℕ × Bool)) (hw : ∀ x ∈ w, x.1 < 2) {n : ℕ} (hwn : w.length = n)
    (h : Nat.beq (McL.evalW MG 24 (Schur.Pack.pk w) n) (McL.pid 24) = true) :
    sword y w = 1 := by
  have hQ : ∀ (H : Type) [Group H] (z : ℕ → H),
      (∀ r < rels.length, LCE.bval z (LceS.wWord (REL r)) (LceS.wLen (REL r)) = 1) →
        Nat.card (Subgroup.closure (z '' {i | i < 2})) ≠ 0 ∧
          Nat.card (Subgroup.closure (z '' {i | i < 2})) ≤ N0 := by
    intro H _ z hz
    have hz' := (sword_rels_iff z hb hl).1 hz
    have hc := card_closure_le P z (by rw [hrels]; exact hz')
    rw [hn] at hc
    exact ⟨hc.1, hc.2.trans hcard⟩
  obtain ⟨ψ, I, ⟨-, hid⟩, -, -, -, hW⟩ := McLM.model_sound y (by norm_num) hgens hR
    (CertificateChecks.KernelMcL.entsBelow_sound hlet) hents hwrap horb hprod hQ
    ((sword_rels_iff y hb hl).2 hy)
  exact sword_eq_one_of_evalW hid hW w hw (by norm_num) hwn h

end CertificateChecks.KernelSchur

end
