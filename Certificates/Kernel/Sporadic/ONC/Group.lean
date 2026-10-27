
module

public import Certificates.Kernel.Sporadic.ONC.GroupBase
import all Certificates.Kernel.Sporadic.ONC.GroupBase

public import Certificates.Kernel.Bounds.ONBridge
public import CFSG.Sporadic.Bridge.ONSurjBase1
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CertificateChecks.KernelSpor.ONC

open Matrix CFSG.Sporadic.ON CFSG.Sporadic.ON.Native CFSG.F3.Native CFSG.Sporadic.Fi23.Native
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Bridge
open CFSG.Sporadic.Bridge.ON CFSG.Sporadic.Bridge.ONGPL.Native TauCeti CFSG.Sporadic.ON.Kernel

theorem rep_img0 {k : ℕ} (hk : k < 7) : Rep nPts imgT[k]! (img0 k) := by
  rw [imgT_getElem hk]
  exact Rep.wordT nPts_lt _ fun l _ => rep_genT0 l

theorem rep_img_inv0 {k : ℕ} (hk : k < 7) :
    Rep nPts imgTv[k]! (img0 k)⁻¹ := by
  have hk' : k < imgT.size := by rw [Array.size_map, bridge_facts.sizeImg]; exact hk
  have e : imgTv[k]! = invT nPts imgT[k]! := by
    rw [getElem!_pos imgTv k (by rw [Array.size_map]; exact hk'), Array.getElem_map,
      getElem!_pos imgT k hk']
  rw [e]
  exact Rep.inv_of_invOK (rep_img0 hk) (by rw [← e]; exact bridge_facts.inv k hk)

theorem rep_imgLetter0 {z : ℤ} (hz : z.natAbs ≤ 7) :
    Rep nPts (imgLetter imgT imgTv z) (imgG0 z) := by
  unfold imgLetter imgG0
  split_ifs with h
  · exact rep_img0 (by omega)
  · exact rep_img_inv0 (by omega)

theorem relators_eval0 :
    ∀ v ∈ Sporadic.onanPresentation.relatorLetters, wordProd img0 v = 1 := by
  rw [relatorLetters_eq]
  intro v hv
  have hlt : ∀ l ∈ v, l.1 < 7 := by
    revert v; unfold rels; decide
  have hrep : Rep nPts (wordT nPts (imgLetter imgT imgTv) (v.map letterOf))
      (wordG imgG0 (v.map letterOf)) := by
    apply Rep.wordT nPts_lt
    intro z hz
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hz
    exact rep_imgLetter0 (by rw [letterOf_natAbs]; exact hlt l hl)
  rw [← wordG_map_letterOf0]
  exact eq_one_of_tupleEq0 hrep (bridge_facts.rels v hv)

@[expose] noncomputable def toJ0 :
    Sporadic.onanPresentation.Group →* J0 :=
  presHom Sporadic.onanPresentation img0 relators_eval0

theorem toJ0_presLetter {z : ℤ} (hz : z.natAbs ≤ 7) :
    toJ0 (presLetter z) = imgG0 z := by
  unfold presLetter imgG0 toJ0
  split_ifs with h
  · exact presHom_presGen _ _ _ (by rw [generatorCount_eq]; omega)
  · rw [map_inv, presHom_presGen _ _ _ (by rw [generatorCount_eq]; omega)]

theorem wordG_imgG0_mem {w : List ℤ} (hw : ∀ z ∈ w, z.natAbs ≤ 7) :
    wordG imgG0 w ∈ toJ0.range := by
  refine ⟨wordG presLetter w, ?_⟩
  unfold wordG
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro z hz
  exact toJ0_presLetter (hw z hz)

theorem rep_surjWord0 {i : ℕ} (hi : i < 2) :
    Rep nPts (wordT nPts (imgLetter imgT imgTv) surjWords[i]!) (wordG imgG0 surjWords[i]!) :=
  Rep.wordT nPts_lt _ fun z hz => rep_imgLetter0 (bridge_facts.letters _ (surjWords_mem hi) z hz).2

theorem toJ0_surjective : Function.Surjective toJ0 := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_gab0, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · rw [← eq_of_tupleEq0 (rep_surjWord0 (by decide)) rep_ga0 bridge_facts.surjA]
    exact wordG_imgG0_mem fun z hz => (bridge_facts.letters _ (surjWords_mem (by decide)) z hz).2
  · rw [← eq_of_tupleEq0 (rep_surjWord0 (by decide)) rep_gb0 bridge_facts.surjB]
    exact wordG_imgG0_mem fun z hz => (bridge_facts.letters _ (surjWords_mem (by decide)) z hz).2

theorem card_J0_le : Nat.card J0 ≤ 460815505920 := by
  obtain ⟨hfin, hcard⟩ := CertificateChecks.KernelBounds.onan
  have hfin' : Finite Sporadic.onanPresentation.Group := by
    rw [← presentation_eq0]; exact hfin
  have hcard' : Nat.card Sporadic.onanPresentation.Group ≤ 460815505920 := by
    rw [← presentation_eq0]; exact hcard
  exact (Nat.card_le_card_of_surjective _ toJ0_surjective).trans hcard'

end CertificateChecks.KernelSpor.ONC

end
