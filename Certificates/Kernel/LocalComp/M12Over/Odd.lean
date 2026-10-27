module

public import Certificates.Kernel.LocalComp.M12Over.S4
public import Certificates.Kernel.LocalComp.M12Over.S5
public import Certificates.Kernel.SporSch.Mathieu.M12MFacts
public import CFSG.Certificates.Kernel.SporSch.ChainKOddConj
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12OverOdd
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic

public section

namespace CertificateChecks.KernelLC.M12Over

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.SporSch.MOC CFSG.Monster.B.Co2
open CFSG.Certificates CFSG.ComponentClassification.RankTwoSporadic.M12 CertificateChecks.KernelSporSch
open CFSG.RankThree.Native

theorem counts : ∀ k₀ < rcnt (M12DQ.LR 0), ∀ k₁ < rcnt (M12DQ.LR 1),
    cntOddBad2K 24 5 (mask 5) (24 * 5) (pidn 24 5) M12DQ.LR M12DQ.TR 5 eb wsP k₀ k₁ = 0 := by
  rw [kCnt.1, kCnt.2]
  intro k₀ hk₀ k₁ hk₁
  refine Nat.eq_of_beq_eq_true (?_ : cK k₀ k₁ = true)
  interval_cases k₀
  exacts [s0 k₁ hk₁, s1 k₁ hk₁, s2 k₁ hk₁, s3 k₁ hk₁, s4 k₁ hk₁, s5 k₁ hk₁, s6 k₁ hk₁, s7 k₁ hk₁,
    s8 k₁ hk₁, s9 k₁ hk₁, s10 k₁ hk₁, s11 k₁ hk₁]

theorem permOK_wsP : allPairsK (fun c ci => permOK 24 5 (mask 5) (24 * 5) c ci) wsP = true := by
  have h := allPairsK_spec kWit
  suffices ∀ ws : List (Nat × Nat), (∀ p ∈ ws, witOK p.1 p.2 = true) →
      allPairsK (fun c ci => permOK 24 5 (mask 5) (24 * 5) c ci) ws = true from this wsP h
  intro ws hws
  induction ws with
  | nil => rfl
  | cons p ws ih =>
    obtain ⟨c, ci⟩ := p
    rw [allPairsK_cons, Bool.and_eq_true]
    have h1 := hws (c, ci) List.mem_cons_self
    simp only [witOK, Bool.and_eq_true] at h1
    exact ⟨h1.1.1.1, ih fun p hp => hws p (List.mem_cons_of_mem _ hp)⟩

theorem prep_T0 : PRep 24 5 T0 (permOfArr 24 (m12T0 m12E0)) := by
  have hv : validA 24 (m12T0 m12E0) = true := by decide +kernel
  have h := rep_of_validA hv
  have e := unpack_eq_of_bindArrK kT0
  refine prep_of_rep fun x => ?_
  rw [← e]
  exact h x

theorem odd : m12OverOdd := by
  intro y hy hy1 hy15
  have hQ := M12MOC.chainQ
  obtain ⟨p, hp, hne⟩ := chainK_oddConj hQ (by decide) (by decide) (by decide) permOK_wsP counts
    hy hy1 (by rw [bval_eb]; exact hy15)
  rw [bval_eb] at hne
  have hw := allPairsK_spec kWit p hp
  simp only [witOK, Bool.and_eq_true] at hw
  obtain ⟨⟨⟨hpo, hcan⟩, hsift⟩, hcomm⟩ := hw
  have pc := (prep_witP hpo).1
  refine ⟨witP 24 5 p, ?_, ?_, hne⟩
  · have hs := chainK_sift (by decide) (by decide) hQ (imageList_of_prep pc) hcan hsift
    exact (RawSchreierDatum.sift_eq_true_iff_mem_original _
      (chainK_valid hQ (by decide) (by decide)) _).1 hs
  · rw [beq_pcomp_iff (by norm_num) (by norm_num) pc prep_T0 prep_T0 pc] at hcomm
    exact of_decide_eq_true hcomm

end CertificateChecks.KernelLC.M12Over

end
