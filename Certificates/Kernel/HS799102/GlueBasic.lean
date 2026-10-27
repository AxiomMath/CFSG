module

public import Certificates.Kernel.HS799102.Glue
public import Certificates.Kernel.HS799102.BasicChecks
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHS799102

open CFSG.KC.PCent CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.RankThree.PartTwo.Sec21.Holder214Theta
open scoped commutatorElement

theorem toPerm_mulB {x y : Nat} (hx : PP 100 7 x) (hy : PP 100 7 y) :
    toPerm 100 7 (mulB x y) = toPerm 100 7 x * toPerm 100 7 y := toPerm_mul hx hy

theorem eq_of_beq {x y : Nat} (h : Nat.beq x y = true) : toPerm 100 7 x = toPerm 100 7 y := by
  rw [Nat.eq_of_beq_eq_true h]

theorem ne_of_beq {x y : Nat} (hx : PP 100 7 x) (hy : PP 100 7 y) (h : (!Nat.beq x y) = true) :
    toPerm 100 7 x ≠ toPerm 100 7 y := fun e => by
  rw [toPerm_injective hx hy e] at h
  simp at h

theorem comm_of_commB {x y : Nat} (hx : PP 100 7 x) (hy : PP 100 7 y) (h : commB x y = true) :
    toPerm 100 7 x * toPerm 100 7 y = toPerm 100 7 y * toPerm 100 7 x := by
  rw [← toPerm_mul hx hy, ← toPerm_mul hy hx]
  exact eq_of_beq h


theorem mem_of_siftB {g : Nat} (hg : PP 100 7 g) (h : siftB g = true) : toPerm 100 7 g ∈ hs100P :=
  mem_hs100P_of_sift (rep_toPerm hg) (CertificateChecks.KernelHS100.siftP rfl h)

theorem basic_facts :
    permOfArr 100 (hsThArr 0) ∈ hs100P ∧ permOfArr 100 (hsThArr 1) ∈ hs100P ∧
      permOfArr 100 (hsThArr 0) ^ 3 = 1 ∧ permOfArr 100 (hsThArr 1) ^ 3 = 1 ∧
      permOfArr 100 (hsThArr 0) * permOfArr 100 (hsThArr 1) =
        permOfArr 100 (hsThArr 1) * permOfArr 100 (hsThArr 0) ∧
      permOfArr 100 (hsThArr 0) ≠ 1 ∧ permOfArr 100 (hsThArr 1) ≠ 1 ∧
      permOfArr 100 (hsThArr 1) ≠ permOfArr 100 (hsThArr 0) ∧
      permOfArr 100 (hsThArr 1) ≠ permOfArr 100 (hsThArr 0) ^ 2 ∧
      permOfArr 100 (hsThArr 4) = permOfArr 100 (hsThArr 2) * permOfArr 100 (hsThArr 3) ∧
      (∀ i < 4, permOfArr 100 (hsThArr (5 + i)) ∈ hs100P ∧
        permOfArr 100 (hsThArr (5 + i)) * permOfArr 100 (hsThArr 2) =
          permOfArr 100 (hsThArr 2) * permOfArr 100 (hsThArr (5 + i)) ∧
        permOfArr 100 (hsThArr (5 + i)) * permOfArr 100 (hsThArr 3) =
          permOfArr 100 (hsThArr 3) * permOfArr 100 (hsThArr (5 + i))) ∧
      ⁅permOfArr 100 (hsThArr 5), permOfArr 100 (hsThArr 6)⁆ = permOfArr 100 (hsThArr 0) ∧
      ⁅permOfArr 100 (hsThArr 7), permOfArr 100 (hsThArr 8)⁆ = permOfArr 100 (hsThArr 1) := by
  have p := fun k (hk : k < 9) => pp_TH k hk
  have e := fun k (hk : k < 9) => (toPerm_v k hk).symm
  have hid : toPerm 100 7 (pidn 100 7) = 1 := toPerm_pidn gl_sz
  have pid : PP 100 7 (pidn 100 7) := PP.id gl_sz
  obtain ⟨s0, s1⟩ := band ch799102_bsift
  obtain ⟨h7, hv3⟩ := band ch799102_bc
  obtain ⟨h6, hc2c1sq⟩ := band h7
  obtain ⟨h5, hc2c1⟩ := band h6
  obtain ⟨h4, hc2⟩ := band h5
  obtain ⟨h3, hc1⟩ := band h4
  obtain ⟨h2, hcomm⟩ := band h3
  obtain ⟨hcub1, hcub2⟩ := band h2
  obtain ⟨b1, b2⟩ := band ch799102_bcomm
  have p0 := p 0 (by norm_num)
  have p1 := p 1 (by norm_num)
  have p00 : PP 100 7 (mulB (TH.F 0) (TH.F 0)) := p0.mul p0
  have p11 : PP 100 7 (mulB (TH.F 1) (TH.F 1)) := p1.mul p1
  have hw : ∀ i < 4, PP 100 7 (TH.F (5 + i)) ∧ siftB (TH.F (5 + i)) = true ∧
      commB (TH.F (5 + i)) (TH.F 2) = true ∧ commB (TH.F (5 + i)) (TH.F 3) = true := by
    intro i hi
    obtain ⟨h12, h3⟩ := band (Orb.allN_iff.1 ch799102_bw i hi)
    obtain ⟨h1, h2⟩ := band h12
    exact ⟨p (5 + i) (by omega), h1, h2, h3⟩
  rw [e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num),
    e 4 (by norm_num), e 5 (by norm_num), e 6 (by norm_num), e 7 (by norm_num),
    e 8 (by norm_num)]
  refine ⟨mem_of_siftB p0 s0, mem_of_siftB p1 s1, ?_, ?_, comm_of_commB p0 p1 hcomm, ?_, ?_,
    ne_of_beq p1 p0 hc2c1, ?_, ?_, fun i hi => ?_, ?_, ?_⟩
  · have h := eq_of_beq hcub1
    rw [toPerm_mulB p0 p00, toPerm_mulB p0 p0, hid] at h
    rw [pow_three]
    exact h
  · have h := eq_of_beq hcub2
    rw [toPerm_mulB p1 p11, toPerm_mulB p1 p1, hid] at h
    rw [pow_three]
    exact h
  · rw [← hid]
    exact ne_of_beq p0 pid hc1
  · rw [← hid]
    exact ne_of_beq p1 pid hc2
  · have h := ne_of_beq p1 p00 hc2c1sq
    rw [toPerm_mulB p0 p0] at h
    rw [pow_two]
    exact h
  · have h := eq_of_beq hv3
    rw [toPerm_mulB (p 2 (by norm_num)) (p 3 (by norm_num))] at h
    exact h
  · obtain ⟨pw, hs, h2, h3⟩ := hw i hi
    rw [← toPerm_v (5 + i) (by omega)]
    exact ⟨mem_of_siftB pw hs, comm_of_commB pw (p 2 (by norm_num)) h2,
      comm_of_commB pw (p 3 (by norm_num)) h3⟩
  · rw [← toPerm_commP (p 5 (by norm_num)) (p 6 (by norm_num))]
    exact eq_of_beq b1
  · rw [← toPerm_commP (p 7 (by norm_num)) (p 8 (by norm_num))]
    exact eq_of_beq b2

end CertificateChecks.KernelHS799102

end
