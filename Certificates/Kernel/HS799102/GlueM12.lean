module

public import Certificates.Kernel.HS799102.GlueBasic
public import Certificates.Kernel.HS799102.M12Checks
public import CFSG.Certificates.Kernel.PCentSubCheck
import CFSG.Certificates.Kernel.Misc.ArrEnumUnpack
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHS799102

open CFSG.KC.PCent CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin
open CFSG.KC.Misc.ArrEnum (pp_of_permB)
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.RankThree.PartTwo.Sec21.Holder214Theta
open scoped commutatorElement


theorem card_M3_le : Nat.card (hs100P ⊓ Subgroup.centralizer {permOfArr 100 hsThV3} :
    Subgroup (Equiv.Perm (Fin 100))) ≤ 2880 := by
  have h := card_centralizer_le_of_classK pp_pG (pp_TH 4 (by norm_num)) ch799102_c3
  rw [lens.2.2, card_pG 15400 2880 (by norm_num), closure_pG, toPerm_v 4 (by norm_num)] at h
  exact Nat.le_of_mul_le_mul_left h (by norm_num : 0 < 15400)

theorem mem_M12_of_memK {g : Nat} (hg : PP 100 7 g) (h1 : memK g (TH.F 2) = true)
    (h2 : memK g (TH.F 3) = true) :
    toPerm 100 7 g ∈ hs100P ⊓ Subgroup.centralizer {permOfArr 100 hsThV1} ⊓
      Subgroup.centralizer {permOfArr 100 hsThV2} := by
  have m1 := mem_of_memK hg (pp_TH 2 (by norm_num)) h1
  have m2 := mem_of_memK hg (pp_TH 3 (by norm_num)) h2
  rw [closure_pG, toPerm_v 2 (by norm_num)] at m1
  rw [closure_pG, toPerm_v 3 (by norm_num)] at m2
  exact Subgroup.mem_inf.2 ⟨m1, (Subgroup.mem_inf.1 m2).2⟩

theorem card_M12_le : Nat.card (hs100P ⊓ Subgroup.centralizer {permOfArr 100 hsThV1} ⊓
    Subgroup.centralizer {permOfArr 100 hsThV2} : Subgroup (Equiv.Perm (Fin 100))) ≤ 1440 := by
  set M := hs100P ⊓ Subgroup.centralizer {permOfArr 100 hsThV1} ⊓
    Subgroup.centralizer {permOfArr 100 hsThV2}
  set M3 := hs100P ⊓ Subgroup.centralizer {permOfArr 100 hsThV3}
  have hv3 : permOfArr 100 hsThV3 = permOfArr 100 hsThV1 * permOfArr 100 hsThV2 :=
    basic_facts.2.2.2.2.2.2.2.2.2.1
  have hle : M ≤ M3 := by
    intro x hx
    obtain ⟨hx12, hx2⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨hxP, hx1⟩ := Subgroup.mem_inf.1 hx12
    have c1 := Subgroup.mem_centralizer_singleton_iff.1 hx1
    have c2 := Subgroup.mem_centralizer_singleton_iff.1 hx2
    refine Subgroup.mem_inf.2 ⟨hxP, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [hv3, ← mul_assoc, c1, mul_assoc, c2, ← mul_assoc]
  obtain ⟨hM3, -⟩ := mem_parts (o := 13) (ng := 4) (o' := 17) tperm.2.2 (pp_TH 4 (by norm_num))
    (by norm_num) (by norm_num) ch799102_mem3
  obtain ⟨hy4, hy⟩ := band ch799102_m12y
  have hY : Y12 < 4 := Nat.blt_eq.mp hy4
  obtain ⟨hyp, hyP, hyc⟩ := hM3 Y12 hY
  have e4 : toPerm 100 7 (TH.F 4) = permOfArr 100 hsThV3 := toPerm_v 4 (by norm_num)
  have e2 : permOfArr 100 hsThV1 = toPerm 100 7 (TH.F 2) := (toPerm_v 2 (by norm_num)).symm
  have hyM3 : toPerm 100 7 (TV3.F (13 + Y12)) ∈ M3 := by
    rw [closure_pG] at hyP
    rw [e4] at hyc
    exact Subgroup.mem_inf.2 ⟨hyP, Subgroup.mem_centralizer_singleton_iff.2 hyc⟩
  have hyM : toPerm 100 7 (TV3.F (13 + Y12)) ∉ M := fun hm => by
    have c1 := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1
      (Subgroup.mem_inf.1 hm).1).2
    rw [e2] at c1
    have e := toPerm_injective ((pp_TH 2 (by norm_num)).mul hyp)
      (hyp.mul (pp_TH 2 (by norm_num)))
      (by rw [toPerm_mul (pp_TH 2 (by norm_num)) hyp, toPerm_mul hyp (pp_TH 2 (by norm_num))]
          exact c1.symm)
    change (!Nat.beq (pcomp 100 7 (mask 7) (TV3.F (13 + Y12)) (TH.F 2))
      (pcomp 100 7 (mask 7) (TH.F 2) (TV3.F (13 + Y12)))) = true at hy
    rw [← e] at hy
    simp at hy
  have hne : M ≠ M3 := fun e => hyM (e ▸ hyM3)
  obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hle
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [Nat.mul_zero] at hc
    exact Nat.card_pos.ne' hc
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [Nat.mul_one] at hc
    exact hne (Subgroup.eq_of_le_of_card_ge hle hc.le)
  have h2 : 2 * Nat.card M ≤ Nat.card M3 := by
    rw [hc, Nat.mul_comm]
    exact Nat.mul_le_mul_left _ (by omega : 2 ≤ c)
  have h3 : Nat.card M3 ≤ 2880 := card_M3_le
  omega

theorem o2_v12 : ∀ Q : Subgroup (Equiv.Perm (Fin 100)), IsPGroup 2 Q →
    Q ≤ ⁅hs100P ⊓ Subgroup.centralizer {permOfArr 100 hsThV1} ⊓
        Subgroup.centralizer {permOfArr 100 hsThV2},
      hs100P ⊓ Subgroup.centralizer {permOfArr 100 hsThV1} ⊓
        Subgroup.centralizer {permOfArr 100 hsThV2}⁆ →
    ⁅hs100P ⊓ Subgroup.centralizer {permOfArr 100 hsThV1} ⊓
        Subgroup.centralizer {permOfArr 100 hsThV2},
      hs100P ⊓ Subgroup.centralizer {permOfArr 100 hsThV1} ⊓
        Subgroup.centralizer {permOfArr 100 hsThV2}⁆ ≤
        Subgroup.normalizer (Q : Set (Equiv.Perm (Fin 100))) → Q = ⊥ := by
  obtain ⟨hpg, hpa⟩ := band ch799102_m12perm
  obtain ⟨hmg, hma⟩ := band ch799102_m12mem
  obtain ⟨hn12, hprod⟩ := band ch799102_m12n
  obtain ⟨hn, hb⟩ := band hn12
  have hA : ∀ j < 4, PP 100 7 (aW12 j) ∧ toPerm 100 7 (aW12 j) ∈
      hs100P ⊓ Subgroup.centralizer {permOfArr 100 hsThV1} ⊓
        Subgroup.centralizer {permOfArr 100 hsThV2} := fun j hj => by
    have hp := pp_of_permB gl_sz (Orb.allN_iff.1 hpa j hj)
    obtain ⟨h1, h2⟩ := band (Orb.allN_iff.1 hma j hj)
    exact ⟨hp, mem_M12_of_memK hp h1 h2⟩
  refine eq_bot_of_card_checks (Mg := mG12) (Dg := dG12) (nm := 2) (x := X12) (m := 1440)
    (RO := O12) (L := N12) (WS := W12) gl_sz (Nat.eq_of_beq_eq_true hprod) card_M12_le
    (fun k hk => ?_) hn hb (fun k hk => ?_) ch799102_m12w ch799102_m12o
  · have hp := pp_of_permB gl_sz (Orb.allN_iff.1 hpg k hk)
    obtain ⟨h1, h2⟩ := band (Orb.allN_iff.1 hmg k hk)
    exact ⟨hp, mem_M12_of_memK hp h1 h2⟩
  · have i0 : Nat.add 0 (Nat.mul 2 k) < 4 := by
      simp only [Nat.add_eq, Nat.mul_eq]
      omega
    have i1 : Nat.add 0 (Nat.add (Nat.mul 2 k) 1) < 4 := by
      simp only [Nat.add_eq, Nat.mul_eq]
      omega
    obtain ⟨ha, haM⟩ := hA _ i0
    obtain ⟨hb', hbM⟩ := hA _ i1
    exact ⟨_, _, ha, hb', haM, hbM, by rw [dG12, dGen, commK_eq]⟩

end CertificateChecks.KernelHS799102

end
