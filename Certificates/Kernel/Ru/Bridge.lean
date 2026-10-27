module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Certificates.Kernel.LceSTabSound
public import CFSG.Certificates.Kernel.McL.Lab
import Certificates.Kernel.Ru.Facts
import CFSG.Certificates.Kernel.LceSHeRuSound
import CFSG.Certificates.Kernel.McLLabSound
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CertificateChecks.KernelRu

open CFSG.KC CFSG.KC.LceS CFSG.KC.Loop CFSG.Certificates CFSG.Certificates.LCE TauCeti
open CertificateChecks.KernelHe

theorem gens_eq : Sporadic.ruPresentation.generatorCount = 3 := by
  simp [GroupPresentation.generatorCount, Sporadic.ruPresentation_generatorNames]

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem mlab_append (FB WT SL : Nat → Nat) (INV rw d lw lm nC L : Nat) :
    ∀ (l1 l2 : List Nat) (x : Nat),
    McL.Lab.runFacts FB WT SL INV rw d lw lm nC L (List.append l1 l2) x =
      McL.Lab.runFacts FB WT SL INV rw d lw lm nC L l2
        (McL.Lab.runFacts FB WT SL INV rw d lw lm nC L l1 x)
  | [], _, _ => rfl
  | C :: l1, l2, x => by
    change strictN (McL.Lab.runChunk FB WT SL INV rw d lw lm nC L C x)
        (McL.Lab.runFacts FB WT SL INV rw d lw lm nC L (List.append l1 l2)) =
      McL.Lab.runFacts FB WT SL INV rw d lw lm nC L l2
        (strictN (McL.Lab.runChunk FB WT SL INV rw d lw lm nC L C x)
          (McL.Lab.runFacts FB WT SL INV rw d lw lm nC L l1))
    rw [strictN_eq, strictN_eq]
    exact mlab_append FB WT SL INV rw d lw lm nC L l1 l2 _

theorem mlab_join {FB WT SL : Nat → Nat} {INV rw d lw lm nC L : Nat} {l1 l2 : List Nat}
    {x y z : Nat} (h1 : Nat.beq (McL.Lab.runFacts FB WT SL INV rw d lw lm nC L l1 x) y = true)
    (h2 : Nat.beq (McL.Lab.runFacts FB WT SL INV rw d lw lm nC L l2 y) z = true) :
    Nat.beq (McL.Lab.runFacts FB WT SL INV rw d lw lm nC L (List.append l1 l2) x) z = true := by
  rw [Nat.beq_eq] at h1 h2 ⊢
  rw [mlab_append, h1, h2]

theorem bval_one {G : Type*} [Group G] (g : ℕ → G) (c : ℕ) (hc : c < 256) :
    bval g c 1 = letV g c := by
  rw [bval_succ, bval_zero, mul_one]
  congr 1
  have h := wLet_zero (W := 0) hc
  rwa [Nat.mul_zero, Nat.add_zero] at h

theorem bval_two {G : Type*} [Group G] (g : ℕ → G) (c c' : ℕ) (hc : c < 256) (hc' : c' < 256) :
    bval g (c + 256 * c') 2 = letV g c * letV g c' := by
  rw [bval_succ, wLet_zero hc, bval_one g _ (by omega)]
  congr 2
  omega

theorem ru : Finite SporadicName.Ru.Group ∧ Nat.card SporadicName.Ru.Group ≤ 145926144000 := by
  let gen := KB.tcGen Sporadic.ruPresentation
  let u : ℕ → Sporadic.ruPresentation.Group := fun k =>
    if k = 0 then gen 0 else if k = 1 then gen 2 else 1
  have hu0 : u 0 = gen 0 := rfl
  have hu1 : u 1 = gen 2 := rfl
  have hS0 : RuB.sub 0 = 4 := rfl
  have hS1 : RuB.sub 1 = 16388 := rfl
  have hsu : bval gen (wWord (RuB.sub 0)) (wLen (RuB.sub 0)) = u 0 := by
    rw [hS0, (by decide : wWord 4 = 0), (by decide : wLen 4 = 1), bval_one gen 0 (by norm_num)]
    simp [letV, u]
  have hst : bval gen (wWord (RuB.sub 1)) (wLen (RuB.sub 1)) = u 1 := by
    rw [hS1, (by decide : wWord 16388 = 4), (by decide : wLen 16388 = 1),
      bval_one gen 4 (by norm_num)]
    simp [letV, u]
  have htt : gen 2 * gen 2 = 1 := by
    have h := (rel_ok 1).2
    have e : RuB.rel 1 = 4 * 2 + 4096 * (4 + 256 * 4) := rfl
    rw [e, (by decide : wWord (4 * 2 + 4096 * (4 + 256 * 4)) = 4 + 256 * 4),
      (by decide : wLen (4 * 2 + 4096 * (4 + 256 * 4)) = 2), bval_two gen 4 4 (by norm_num)
      (by norm_num)] at h
    simpa [letV] using h
  have hu : u 1 * u 1 = 1 := htt
  have hC : ∀ {c wid R k : ℕ}, c < 2 ^ 20 → wid < 512 →
      RuB.cycOK CFSG.KD.RuBC.blk CFSG.KD.RuBC.selWT CFSG.KD.RuBC.LB 64 c wid R
        (RuB.entStk (CFSG.KD.RuBAM.selRT k)) = true →
      bval u (wWord (CFSG.KD.RuBAM.selRT k)) (wLen (CFSG.KD.RuBAM.selRT k)) = 1 :=
    fun hc0 hwid hc => LS.Ru.coneOk_sound gen u hu C.ok (fun r => rel_ok r) hsu hst hc0 hwid hc
  have hA := McLLab.targets_sound gen (fun r _ => rel_ok r) (wtPer0_sound A.per0)
    CFSG.KD.RuBA.wd CFSG.KD.RuBA.inv (by decide) (by decide)
    (Nat.eq_of_beq_eq_true CFSG.KD.RuBA.one) (by decide) CFSG.KD.RuBA.anc (by decide) rfl
    (mlab_join (mlab_join (mlab_join CFSG.KD.RuBA.f0 CFSG.KD.RuBA.f1) CFSG.KD.RuBA.f2)
      CFSG.KD.RuBA.f3) rfl (by decide) CFSG.KD.RuBA.tg rfl rfl rfl
  have hletter : ∀ c < 4, letV gen (c + (c &&& 2)) = letV u c := by
    intro c hc
    interval_cases c <;> simp [letV, u]
  have hD : ∀ k < 9, bval u (wWord (CFSG.KD.RuBAM.selRT (7 + k)))
      (wLen (CFSG.KD.RuBAM.selRT (7 + k))) = 1 := by
    intro k hk
    have hq : A.qOK k = true := by
      interval_cases k
      · exact A.q0
      · exact A.q1
      · exact A.q2
      · exact A.q3
      · exact A.q4
      · exact A.q5
      · exact A.q6
      · exact A.q7
      · exact A.q8
    have hd : CFSG.KC.RuBA.derivedOK k = true := by
      interval_cases k
      · exact CFSG.KC.RuBA.Route.derived_0
      · exact CFSG.KC.RuBA.Route.derived_1
      · exact CFSG.KC.RuBA.Route.derived_2
      · exact CFSG.KC.RuBA.Route.derived_3
      · exact CFSG.KC.RuBA.Route.derived_4
      · exact CFSG.KC.RuBA.Route.derived_5
      · exact CFSG.KC.RuBA.Route.derived_6
      · exact CFSG.KC.RuBA.Route.derived_7
      · exact CFSG.KC.RuBA.Route.derived_8
    have hd' : andB (Nat.beq (CFSG.KC.RuBA.qToP (CFSG.KD.RuBAM.selRT (Nat.add 7 k)))
        (CFSG.KD.RuBA.TW k)) (Nat.beq (CFSG.KD.RuBA.TL k) (McL.pid CFSG.KD.RuBA.d)) = true := hd
    rw [andB_true_iff, Nat.beq_eq, Nat.beq_eq] at hd'
    have hT := hA k (by
      rw [Nat.eq_of_beq_eq_true CFSG.KC.RuBA.Route.a_nT]
      exact hk) hd'.2
    have hq' : andB (Nat.beq (wLen (CFSG.KD.RuBA.TW k))
        (wLen (CFSG.KD.RuBAM.selRT (Nat.add 7 k))))
        (qlet (wWord (CFSG.KD.RuBA.TW k)) (wWord (CFSG.KD.RuBAM.selRT (Nat.add 7 k)))
          (wLen (CFSG.KD.RuBAM.selRT (Nat.add 7 k)))) = true := hq
    rw [andB_true_iff, Nat.beq_eq] at hq'
    rw [hq'.1] at hT
    rw [← hT]
    symm
    apply bval_congr
    intro i hi
    obtain ⟨h4, he⟩ := qlet_sound hq'.2 i hi
    rw [he, hletter _ h4]
    rfl
  have hQrel : ∀ r < 16, bval u (wWord (CFSG.KD.RuBAM.selRT r)) (wLen (CFSG.KD.RuBAM.selRT r)) = 1 := by
    intro r hr
    rcases Nat.lt_or_ge r 7 with h7 | h7
    · interval_cases r
      · rw [Nat.eq_of_beq_eq_true CFSG.KC.RuBA.Route.q_sq,
          (by decide : wWord 2105352 = 2 + 256 * 2), (by decide : wLen 2105352 = 2),
          bval_two u 2 2 (by norm_num) (by norm_num)]
        simpa [letV, u] using hu
      · exact hC (by norm_num) (by norm_num) CFSG.KD.RuBC.sY0
      · exact hC (by norm_num) (by norm_num) CFSG.KD.RuBC.sY1
      · exact hC (by norm_num) (by norm_num) CFSG.KD.RuBC.sY2
      · exact hC (by norm_num) (by norm_num) CFSG.KD.RuBC.sY3
      · exact hC (by norm_num) (by norm_num) CFSG.KD.RuBC.sY4
      · exact hC (by norm_num) (by norm_num) CFSG.KD.RuBC.sY5
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h7
      exact hD k (by omega)
  let w : ℕ → Sporadic.ruPresentation.Group := fun j =>
    bval u (wWord (CFSG.KD.RuBAM.selST j)) (wLen (CFSG.KD.RuBAM.selST j))
  have hM : (Subgroup.closure ((fun j => bval u (wWord (CFSG.KD.RuBAM.selST j))
        (wLen (CFSG.KD.RuBAM.selST j))) '' {j | j < 10})).relIndex
        (Subgroup.closure (u '' {g | 2 * g < 4})) ≠ 0 ∧
      (Subgroup.closure ((fun j => bval u (wWord (CFSG.KD.RuBAM.selST j))
        (wLen (CFSG.KD.RuBAM.selST j))) '' {j | j < 10})).relIndex
        (Subgroup.closure (u '' {g | 2 * g < 4})) ≤ CFSG.KD.RuBAM.nLive :=
    lceOk_sound M.ok u hQrel
  have hML : ∀ {c wid R k : ℕ}, c < 2 ^ 20 → wid < 256 →
      CFSG.KC.LabF.cycOK CFSG.KD.RuBAM.blk CFSG.KD.RuBAM.selWT CFSG.KD.RuBAM.LB 3510 c wid R
        (CFSG.KC.LabF.entStk (CFSG.KD.RuBAB.selRT k)) = true →
      bval w (wWord (CFSG.KD.RuBAB.selRT k)) (wLen (CFSG.KD.RuBAB.selRT k)) = 1 :=
    fun hc0 hwid hc => LS.LabF.labOk_sound u w ML.ok hQrel (fun j _ => rfl) hc0 hwid hc
  have hBrel : ∀ r < 81, bval w (wWord (CFSG.KD.RuBAB.selRT r)) (wLen (CFSG.KD.RuBAB.selRT r)) = 1 := by
    intro r hr
    interval_cases r
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY0
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY1
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY2
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY3
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY4
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY5
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY6
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY7
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY8
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY9
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY10
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY11
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY12
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY13
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY14
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY15
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY16
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY17
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY18
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY19
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY20
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY21
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY22
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY23
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY24
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY25
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY26
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY27
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY28
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY29
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY30
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY31
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY32
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY33
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY34
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY35
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY36
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY37
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY38
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY39
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY40
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY41
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY42
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY43
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY44
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY45
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY46
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY47
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY48
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY49
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY50
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY51
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY52
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY53
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY54
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY55
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY56
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY57
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY58
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY59
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY60
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY61
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY62
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY63
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY64
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY65
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY66
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY67
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY68
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY69
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY70
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY71
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY72
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY73
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY74
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY75
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY76
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY77
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY78
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY79
    · exact hML (by norm_num) (by norm_num) CFSG.KD.RuBAM.sY80
  have hB : (Subgroup.closure ((fun j => bval w (wWord (CFSG.KD.RuBAB.selST j))
        (wLen (CFSG.KD.RuBAB.selST j))) '' {j | j < 2})).relIndex
        (Subgroup.closure (w '' {g | 2 * g < 20})) ≠ 0 ∧
      (Subgroup.closure ((fun j => bval w (wWord (CFSG.KD.RuBAB.selST j))
        (wLen (CFSG.KD.RuBAB.selST j))) '' {j | j < 2})).relIndex
        (Subgroup.closure (w '' {g | 2 * g < 20})) ≤ CFSG.KD.RuBAB.nLive :=
    lceOk_sound B.ok w hBrel
  have hBsub : (fun j => bval w (wWord (CFSG.KD.RuBAB.selST j)) (wLen (CFSG.KD.RuBAB.selST j))) ''
      {j | j < 2} = {w 0, w 1} := by
    have e : {j : ℕ | j < 2} = {0, 1} := by
      ext j
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      omega
    rw [e, Set.image_pair, Nat.eq_of_beq_eq_true CFSG.KC.RuBA.Route.bot_sub0,
      Nat.eq_of_beq_eq_true CFSG.KC.RuBA.Route.bot_sub1, (by decide : wWord 4 = 0),
      (by decide : wLen 4 = 1), (by decide : wWord 8196 = 2), (by decide : wLen 8196 = 1),
      bval_one w 0 (by norm_num), bval_one w 2 (by norm_num)]
    simp [letV]
  rw [hBsub] at hB
  have hw00 : w 0 * w 0 = 1 := by
    have h := hBrel 0 (by norm_num)
    rw [Nat.eq_of_beq_eq_true CFSG.KC.RuBA.Route.bot_p0sq, (by decide : wWord 8 = 0 + 256 * 0),
      (by decide : wLen 8 = 2), bval_two w 0 0 (by norm_num) (by norm_num)] at h
    simpa [letV] using h
  have hw11 : w 1 * w 1 = 1 := by
    have h := hBrel 1 (by norm_num)
    rw [Nat.eq_of_beq_eq_true CFSG.KC.RuBA.Route.bot_p1sq,
      (by decide : wWord 2105352 = 2 + 256 * 2), (by decide : wLen 2105352 = 2),
      bval_two w 2 2 (by norm_num) (by norm_num)] at h
    simpa [letV] using h
  have hw01 : w 0 * w 1 * (w 0 * w 1) = 1 := by
    have h := hBrel 4 (by norm_num)
    rw [Nat.eq_of_beq_eq_true CFSG.KC.RuBA.Route.bot_p0p1sq,
      (by decide : wWord 137441050640 = 0 + 256 * (2 + 256 * (0 + 256 * (2 + 256 * 0)))),
      (by decide : wLen 137441050640 = 4), bval_succ, bval_succ, bval_succ,
      bval_one w _ (by norm_num), wLet_zero (by norm_num)] at h
    simp only [wLet_eq] at h
    norm_num [letV] at h
    simpa [mul_assoc] using h
  have cB := card_le_step' hB (card_klein_le hw00 hw11 hw01)
  have eW : w '' {g | 2 * g < 20} =
      (fun j => bval u (wWord (CFSG.KD.RuBAM.selST j)) (wLen (CFSG.KD.RuBAM.selST j))) ''
        {j | j < 10} := by
    have e : {g : ℕ | 2 * g < 20} = {j | j < 10} := by
      ext g
      simp only [Set.mem_ofPred_eq]
      omega
    rw [e]
  rw [eW] at cB
  have cM := card_le_step' hM cB
  have hP : (Subgroup.closure ((fun j => bval gen (wWord (CFSG.KD.RuBP.selST j))
        (wLen (CFSG.KD.RuBP.selST j))) '' {j | j < 2})).relIndex
        (Subgroup.closure (gen '' {g | 2 * g < 6})) ≠ 0 ∧
      (Subgroup.closure ((fun j => bval gen (wWord (CFSG.KD.RuBP.selST j))
        (wLen (CFSG.KD.RuBP.selST j))) '' {j | j < 2})).relIndex
        (Subgroup.closure (gen '' {g | 2 * g < 6})) ≤ CFSG.KD.RuBP.nLive :=
    lceOk_sound P.ok gen (fun r _ => (rel_ok r).2)
  have e26 : {g : ℕ | 2 * g < 6} = {g | g < Sporadic.ruPresentation.generatorCount} := by
    ext g
    simp only [Set.mem_ofPred_eq, gens_eq]
    omega
  have htop : Subgroup.closure (gen '' {g | 2 * g < 6}) = ⊤ := by
    rw [e26]
    exact KB.closure_tcGen _
  have hPsub : (fun j => bval gen (wWord (CFSG.KD.RuBP.selST j)) (wLen (CFSG.KD.RuBP.selST j))) ''
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
    · exact hsu
    · exact hst
  rw [htop, hPsub] at hP
  have cP := card_le_step' hP cM
  have hord : CFSG.KD.RuBP.nLive * (CFSG.KD.RuBAM.nLive * (CFSG.KD.RuBAB.nLive * 4)) =
      145926144000 := by
    rw [← Nat.mul_assoc, ← Nat.mul_assoc]
    exact Nat.eq_of_beq_eq_true CFSG.KC.RuBA.Route.order
  rw [hord] at cP
  exact KB.finite_card_le_of_top rfl cP

end CertificateChecks.KernelRu

end
