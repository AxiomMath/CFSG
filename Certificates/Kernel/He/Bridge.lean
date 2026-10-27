module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import Certificates.Kernel.He.Facts
import Certificates.Kernel.He.Words
import CFSG.Certificates.Kernel.LceSHeRuSound
public import CFSG.Certificates.Kernel.LceSTabSound
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CertificateChecks.KernelHe

open CFSG.KC CFSG.KC.LceS CFSG.Certificates CFSG.Certificates.LCE TauCeti

theorem gens_eq : Sporadic.hePresentation.generatorCount = 2 := by
  simp [GroupPresentation.generatorCount, Sporadic.hePresentation_generatorNames]

theorem bval_one {G : Type*} [Group G] (gen : ℕ → G) (c : ℕ) (hc : c < 256) :
    bval gen c 1 = letV gen c := by
  rw [bval_succ, bval_zero, mul_one]
  congr 1
  have h := wLet_zero (W := 0) hc
  rwa [Nat.mul_zero, Nat.add_zero] at h

theorem he : Finite SporadicName.He.Group ∧ Nat.card SporadicName.He.Group ≤ 4030387200 := by
  let gen := KB.tcGen Sporadic.hePresentation
  let g1 : Sporadic.hePresentation.Group := bval gen (wWord (HeB.sub 1)) (wLen (HeB.sub 1))
  let u : ℕ → Sporadic.hePresentation.Group := fun k =>
    if k = 0 then gen 0 else if k = 1 then g1 else 1
  have hu0 : u 0 = gen 0 := rfl
  have hu1 : u 1 = g1 := rfl
  have hS0 : HeB.sub 0 = 4 := rfl
  have ha : bval gen (wWord (HeB.sub 0)) (wLen (HeB.sub 0)) = gen 0 := by
    rw [hS0, (by decide : wWord 4 = 0), (by decide : wLen 4 = 1), bval_one gen 0 (by norm_num)]
    simp [letV]
  have haa : gen 0 * gen 0 = 1 := by
    have h := (rel_ok 0).2
    have e8 : HeB.rel 0 = 8 := rfl
    rw [e8, (by decide : wWord 8 = 0), (by decide : wLen 8 = 2),
      bval_succ, bval_one gen (0 / 256) (by norm_num)] at h
    simpa [letV, wLet_eq] using h
  have hu : u 0 * u 0 = 1 := haa
  have hC : ∀ {c wid R k : ℕ}, c < 2 ^ 20 → wid < 2048 →
      HeB.cycOK CFSG.KD.HeBC.blk CFSG.KD.HeBC.selWT CFSG.KD.HeBC.LB 1628 c wid R
        (HeB.entStk (CFSG.KD.HeBQ.selRT k)) = true →
      bval u (wWord (CFSG.KD.HeBQ.selRT k)) (wLen (CFSG.KD.HeBQ.selRT k)) = 1 :=
    fun hc0 hwid hc => LS.He.coneOk_sound gen u hu C.ok (fun r => rel_ok r) ha rfl hc0 hwid hc
  have hQrel : ∀ r < 6, bval u (wWord (CFSG.KD.HeBQ.selRT r)) (wLen (CFSG.KD.HeBQ.selRT r)) = 1 := by
    intro r hr
    interval_cases r
    · rw [Nat.eq_of_beq_eq_true HeB.Route.q_sq, (by decide : wWord 8 = 0),
        (by decide : wLen 8 = 2), bval_succ, bval_one u (0 / 256) (by norm_num)]
      simpa [letV, wLet_eq] using hu
    · exact hC (by norm_num) (by norm_num) CFSG.KD.HeBC.sY0
    · exact hC (by norm_num) (by norm_num) CFSG.KD.HeBC.sY1
    · exact hC (by norm_num) (by norm_num) CFSG.KD.HeBC.sY2
    · exact hC (by norm_num) (by norm_num) CFSG.KD.HeBC.sY3
    · exact hC (by norm_num) (by norm_num) CFSG.KD.HeBC.sY4
  have hQ : (Subgroup.closure ((fun j => bval u (wWord (CFSG.KD.HeBQ.selST j))
        (wLen (CFSG.KD.HeBQ.selST j))) '' {j | j < 1})).relIndex
        (Subgroup.closure (u '' {g | 2 * g < 4})) ≠ 0 ∧
      (Subgroup.closure ((fun j => bval u (wWord (CFSG.KD.HeBQ.selST j))
        (wLen (CFSG.KD.HeBQ.selST j))) '' {j | j < 1})).relIndex
        (Subgroup.closure (u '' {g | 2 * g < 4})) ≤ CFSG.KD.HeBQ.nLive :=
    lceOk_sound Q.ok u hQrel
  have hQsub : (fun j => bval u (wWord (CFSG.KD.HeBQ.selST j)) (wLen (CFSG.KD.HeBQ.selST j))) ''
      {j | j < 1} = {g1} := by
    have e : {j : ℕ | j < 1} = {0} := by
      ext j
      simp
    rw [e, Set.image_singleton, Nat.eq_of_beq_eq_true HeB.Route.q_sub,
      (by decide : wWord 8196 = 2), (by decide : wLen 8196 = 1), bval_one u 2 (by norm_num)]
    simp [letV, u]
  rw [hQsub] at hQ
  have hg6 : g1 ^ 6 = 1 := by
    have h := hQrel 1 (by norm_num)
    rw [Nat.eq_of_beq_eq_true HeB.Route.q_pow,
      (by decide : wLen 13563782407139352 = 6),
      bval_const u 3 6 _ (by decide)] at h
    simpa [letV, u] using h
  have hcard6 : Nat.card (Subgroup.closure ({g1} : Set _)) ≠ 0 ∧
      Nat.card (Subgroup.closure ({g1} : Set _)) ≤ 6 := by
    rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
    have hd : orderOf g1 ∣ 6 := orderOf_dvd_of_pow_eq_one hg6
    exact ⟨(Nat.pos_of_dvd_of_pos hd (by norm_num)).ne', Nat.le_of_dvd (by norm_num) hd⟩
  have hle : Subgroup.closure ({g1} : Set _) ≤ Subgroup.closure (u '' {g | 2 * g < 4}) := by
    rw [Subgroup.closure_le, Set.singleton_subset_iff]
    exact Subgroup.subset_closure ⟨1, by norm_num, rfl⟩
  have cQ := KB.card_le_step ⟨hle, hQ⟩ hcard6
  have hP : (Subgroup.closure ((fun j => bval gen (wWord (CFSG.KD.HeBP.selST j))
        (wLen (CFSG.KD.HeBP.selST j))) '' {j | j < 2})).relIndex
        (Subgroup.closure (gen '' {g | 2 * g < 4})) ≠ 0 ∧
      (Subgroup.closure ((fun j => bval gen (wWord (CFSG.KD.HeBP.selST j))
        (wLen (CFSG.KD.HeBP.selST j))) '' {j | j < 2})).relIndex
        (Subgroup.closure (gen '' {g | 2 * g < 4})) ≤ CFSG.KD.HeBP.nLive :=
    lceOk_sound P.ok gen (fun r _ => (rel_ok r).2)
  have e24 : {g : ℕ | 2 * g < 4} = {g | g < Sporadic.hePresentation.generatorCount} := by
    ext g
    simp only [Set.mem_ofPred_eq, gens_eq]
    omega
  have htop : Subgroup.closure (gen '' {g | 2 * g < 4}) = ⊤ := by
    rw [e24]
    exact KB.closure_tcGen _
  have hPsub : (fun j => bval gen (wWord (CFSG.KD.HeBP.selST j)) (wLen (CFSG.KD.HeBP.selST j))) ''
      {j | j < 2} = u '' {g | 2 * g < 4} := by
    have e : {j : ℕ | j < 2} = {g | 2 * g < 4} := by
      ext j
      simp only [Set.mem_ofPred_eq]
      omega
    rw [e]
    apply Set.image_congr
    intro j hj
    have hj2 : j < 2 := by
      simp only [Set.mem_ofPred_eq] at hj
      omega
    interval_cases j
    · exact ha
    · rfl
  rw [htop, hPsub] at hP
  have cP := KB.card_le_step ⟨le_top, hP⟩ cQ
  have hord : CFSG.KD.HeBP.nLive * (CFSG.KD.HeBQ.nLive * 6) = 4030387200 := by
    rw [← Nat.mul_assoc]
    exact Nat.eq_of_beq_eq_true HeB.Route.order
  rw [hord] at cP
  exact KB.finite_card_le_of_top rfl cP

end CertificateChecks.KernelHe

end
