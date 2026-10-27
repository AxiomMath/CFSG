module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Certificates.Kernel.LceSTabSound
import Certificates.Kernel.J3.Facts
import Certificates.Kernel.J3.Words
import Certificates.Kernel.Ru.Words
import CFSG.Certificates.Kernel.LceSHeRuSound
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CertificateChecks.KernelJ3

open CFSG.KC CFSG.KC.LceS CFSG.Certificates CFSG.Certificates.LCE TauCeti
open CertificateChecks.KernelHe CertificateChecks.KernelRu

theorem gens_eq : Sporadic.j3Presentation.generatorCount = 2 := by
  simp [GroupPresentation.generatorCount, Sporadic.j3Presentation_generatorNames]

theorem bval_one' {G : Type*} [Group G] (g : ℕ → G) (c : ℕ) (hc : c < 256) :
    bval g c 1 = letV g c := by
  rw [bval_succ, bval_zero, mul_one]
  congr 1
  have h := wLet_zero (W := 0) hc
  rwa [Nat.mul_zero, Nat.add_zero] at h

theorem bval_two' {G : Type*} [Group G] (g : ℕ → G) (c c' : ℕ) (hc : c < 256) (hc' : c' < 256) :
    bval g (c + 256 * c') 2 = letV g c * letV g c' := by
  rw [bval_succ, wLet_zero hc, bval_one' g _ (by omega)]
  congr 2
  omega

theorem card_inv_le {G : Type*} [Group G] {x : G} (hx : x * x = 1) :
    Nat.card (Subgroup.closure ({x} : Set G)) ≠ 0 ∧
      Nat.card (Subgroup.closure ({x} : Set G)) ≤ 2 := by
  rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
  have hd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hx])
  exact ⟨fun h => by rw [h] at hd; norm_num at hd, Nat.le_of_dvd (by norm_num) hd⟩

theorem j3 : Finite SporadicName.J3.Group ∧ Nat.card SporadicName.J3.Group ≤ 50232960 := by
  let gen := KB.tcGen Sporadic.j3Presentation
  have hT : (Subgroup.closure ((fun j => bval gen (wWord (CFSG.KD.J3AT.selST j))
        (wLen (CFSG.KD.J3AT.selST j))) '' {j | j < 2})).relIndex
        (Subgroup.closure (gen '' {g | 2 * g < 4})) ≠ 0 ∧
      (Subgroup.closure ((fun j => bval gen (wWord (CFSG.KD.J3AT.selST j))
        (wLen (CFSG.KD.J3AT.selST j))) '' {j | j < 2})).relIndex
        (Subgroup.closure (gen '' {g | 2 * g < 4})) ≤ CFSG.KD.J3AT.nLive :=
    lceOk_sound T.ok gen (fun r _ => (rel_ok r).2)
  let w : ℕ → Sporadic.j3Presentation.Group := fun j =>
    bval gen (wWord (CFSG.KD.J3AT.selST j)) (wLen (CFSG.KD.J3AT.selST j))
  have hTL : ∀ {c wid R k : ℕ}, c < 2 ^ 20 → wid < 256 →
      CFSG.KC.LabF.cycOK CFSG.KD.J3AT.blk CFSG.KD.J3AT.selWT CFSG.KD.J3AT.LB 39270 c wid R
        (CFSG.KC.LabF.entStk (CFSG.KD.J3AB.selRT k)) = true →
      bval w (wWord (CFSG.KD.J3AB.selRT k)) (wLen (CFSG.KD.J3AB.selRT k)) = 1 :=
    fun hc0 hwid hc => LS.LabF.labOk_sound gen w TL.ok (fun r _ => (rel_ok r).2) (fun j _ => rfl)
      hc0 hwid hc
  have hBrel : ∀ r < 30, bval w (wWord (CFSG.KD.J3AB.selRT r)) (wLen (CFSG.KD.J3AB.selRT r)) = 1 := by
    intro r hr
    interval_cases r
    · exact hTL (by norm_num) (by norm_num) CFSG.KD.J3AT.sY0
    · exact hTL (by norm_num) (by norm_num) CFSG.KD.J3AT.sY1
    · exact hTL (by norm_num) (by norm_num) CFSG.KD.J3AT.sY2
    · exact hTL (by norm_num) (by norm_num) CFSG.KD.J3AT.sY3
    · exact hTL (by norm_num) (by norm_num) CFSG.KD.J3AT.sY4
    · exact hTL (by norm_num) (by norm_num) CFSG.KD.J3AT.sY5
    · exact hTL (by norm_num) (by norm_num) CFSG.KD.J3AT.sY6
    · exact hTL (by norm_num) (by norm_num) CFSG.KD.J3AT.sY7
    · exact hTL (by norm_num) (by norm_num) CFSG.KD.J3AT.sY8
    · exact hTL (by norm_num) (by norm_num) CFSG.KD.J3AT.sY9
    · exact hTL (by norm_num) (by norm_num) CFSG.KD.J3AT.sY10
    · exact hTL (by norm_num) (by norm_num) CFSG.KD.J3AT.sY11
    · exact hTL (by norm_num) (by norm_num) CFSG.KD.J3AT.sY12
    · exact hTL (by norm_num) (by norm_num) CFSG.KD.J3AT.sY13
    · exact hTL (by norm_num) (by norm_num) CFSG.KD.J3AT.sY14
    · exact hTL (by norm_num) (by norm_num) CFSG.KD.J3AT.sY15
    · exact hTL (by norm_num) (by norm_num) CFSG.KD.J3AT.sY16
    · exact hTL (by norm_num) (by norm_num) CFSG.KD.J3AT.sY17
    · exact hTL (by norm_num) (by norm_num) CFSG.KD.J3AT.sY18
    · exact hTL (by norm_num) (by norm_num) CFSG.KD.J3AT.sY19
    · exact hTL (by norm_num) (by norm_num) CFSG.KD.J3AT.sY20
    · exact hTL (by norm_num) (by norm_num) CFSG.KD.J3AT.sY21
    · exact hTL (by norm_num) (by norm_num) CFSG.KD.J3AT.sY22
    · exact hTL (by norm_num) (by norm_num) CFSG.KD.J3AT.sY23
    · exact hTL (by norm_num) (by norm_num) CFSG.KD.J3AT.sY24
    · exact hTL (by norm_num) (by norm_num) CFSG.KD.J3AT.sY25
    · exact hTL (by norm_num) (by norm_num) CFSG.KD.J3AT.sY26
    · exact hTL (by norm_num) (by norm_num) CFSG.KD.J3AT.sY27
    · exact hTL (by norm_num) (by norm_num) CFSG.KD.J3AT.sY28
    · exact hTL (by norm_num) (by norm_num) CFSG.KD.J3AT.sY29
  have hB : (Subgroup.closure ((fun j => bval w (wWord (CFSG.KD.J3AB.selST j))
        (wLen (CFSG.KD.J3AB.selST j))) '' {j | j < 1})).relIndex
        (Subgroup.closure (w '' {g | 2 * g < 4})) ≠ 0 ∧
      (Subgroup.closure ((fun j => bval w (wWord (CFSG.KD.J3AB.selST j))
        (wLen (CFSG.KD.J3AB.selST j))) '' {j | j < 1})).relIndex
        (Subgroup.closure (w '' {g | 2 * g < 4})) ≤ CFSG.KD.J3AB.nLive :=
    lceOk_sound B.ok w hBrel
  have hBsub : (fun j => bval w (wWord (CFSG.KD.J3AB.selST j)) (wLen (CFSG.KD.J3AB.selST j))) ''
      {j | j < 1} = {w 0} := by
    have e : {j : ℕ | j < 1} = {0} := by
      ext j
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      omega
    rw [e, Set.image_singleton, Nat.eq_of_beq_eq_true CFSG.KC.J3A.Route.bot_sub,
      (by decide : wWord 4 = 0), (by decide : wLen 4 = 1), bval_one' w 0 (by norm_num)]
    simp [letV]
  rw [hBsub] at hB
  have hw00 : w 0 * w 0 = 1 := by
    have h := hBrel 0 (by norm_num)
    rw [Nat.eq_of_beq_eq_true CFSG.KC.J3A.Route.bot_pow, (by decide : wWord 8 = 0 + 256 * 0),
      (by decide : wLen 8 = 2), bval_two' w 0 0 (by norm_num) (by norm_num)] at h
    simpa [letV] using h
  have cB := card_le_step' hB (card_inv_le hw00)
  have eW : w '' {g | 2 * g < 4} =
      (fun j => bval gen (wWord (CFSG.KD.J3AT.selST j)) (wLen (CFSG.KD.J3AT.selST j))) ''
        {j | j < 2} := by
    have e : {g : ℕ | 2 * g < 4} = {j | j < 2} := by
      ext g
      simp only [Set.mem_ofPred_eq]
      omega
    rw [e]
  rw [eW] at cB
  have cT := card_le_step' hT cB
  have e24 : {g : ℕ | 2 * g < 4} = {g | g < Sporadic.j3Presentation.generatorCount} := by
    ext g
    simp only [Set.mem_ofPred_eq, gens_eq]
    omega
  have htop : Subgroup.closure (gen '' {g | 2 * g < 4}) = ⊤ := by
    rw [e24]
    exact KB.closure_tcGen _
  have hord : CFSG.KD.J3AT.nLive * (CFSG.KD.J3AB.nLive * 2) = 50232960 := by
    rw [← Nat.mul_assoc]
    exact Nat.eq_of_beq_eq_true CFSG.KC.J3A.Route.order
  rw [hord] at cT
  exact KB.finite_card_le_of_top htop cT

end CertificateChecks.KernelJ3

end
