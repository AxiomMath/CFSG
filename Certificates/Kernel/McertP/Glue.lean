module

public import Certificates.Kernel.McertP.Ly
public import Certificates.Kernel.McertP.HN
public import Certificates.Kernel.McertP.F2
public import Certificates.Kernel.MatCert.Glue
public import CFSG.Certificates.Kernel.OpsLayMcertSoundP
import all CFSG.Blueprint.NativeSporadic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMP

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.KC.OpsLayK
open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.AGLEmbedding.R3
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal CFSG.Blueprint

theorem cert40340 :
    MGen.checkBase (ops2 112) NativeSporadic.J4Seed1 NativeSporadic.J4Seed2 j4_23_claims = true ∧
      MGen.checkBase (opsP 5 111) NativeSporadic.LySeed1 NativeSporadic.LySeed2 ly_31_claims =
        true := by
  refine ⟨?_, ?_⟩
  · rw [MGen.checkBase, j4_23_wf,
      mcertCheck_of_N (hom2 112 (by norm_num)) KernelMC.j4A KernelMC.j4B trivial trivial j4_23_K]
    rfl
  · rw [MGen.checkBase, Ly.ly31_wf, mcertLP_sound (p := 5) (d := 111) Ly.lay_ok rfl rfl
      Ly.decA Ly.decB Ly.LA_eq Ly.LB_eq Ly.ly31_K]
    rfl

theorem cert40342 :
    BClaim.check (opsP 5 111) NativeSporadic.LySeed1 NativeSporadic.LySeed2 ly_7_claims = true := by
  rw [BClaim.check, Ly.ly7_wf, mcertLP_sound (p := 5) (d := 111) Ly.lay_ok rfl rfl
    Ly.decA Ly.decB Ly.LA_eq Ly.LB_eq Ly.ly7_K]
  rfl

theorem cert40345 :
    GClaim.check (opsP 5 133) NativeSporadic.HNSeed1 NativeSporadic.HNSeed2 hn_7_claims = true := by
  rw [GClaim.check, HN.hn7_wf,
    mcertLP_sound (p := 5) (d := 133) HN.lay_ok rfl rfl HN.decA HN.decB HN.LA_eq HN.LB_eq HN.hn7_K]
  rfl

theorem cert9598 : modCheckE (opsP 5 133) NativeSporadic.HNSeed1 NativeSporadic.HNSeed2
    AlphaHN.hnNregs AlphaHN.hnProg 3 AlphaHN.hnMod AlphaHN.hnTops AlphaHN.hnGs AlphaHN.hnCf
    AlphaHN.hnCi AlphaHN.hnCt = true := by
  have hm := mcertLP_sound (p := 5) (d := 133) HN.lay_ok rfl rfl HN.decA HN.decB HN.LA_eq HN.LB_eq
    HN.alpha_K
  have hA := HN.alpha_restA
  unfold modCheckE
  simp only [Bool.and_eq_true] at hA ⊢
  exact ⟨⟨⟨⟨⟨⟨⟨⟨hm, hA.1.1.1⟩, hA.1.1.2⟩, hA.1.2⟩, hA.2⟩, HN.alpha_grp⟩, HN.alpha_rank⟩,
    HN.alpha_fun⟩, HN.alpha_alt⟩

theorem pairwise_zip_tail {R : Nat → Nat → Prop} :
    ∀ {l : List Nat}, l.Pairwise R → ∀ x ∈ l.zip l.tail, R x.1 x.2
  | [], _, x, hx => by simp at hx
  | [_], _, x, hx => by simp at hx
  | a :: b :: t, h, x, hx => by
    rw [List.pairwise_cons] at h
    simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact h.1 b List.mem_cons_self
    · exact pairwise_zip_tail h.2 x hx

theorem wChk_of {p n s : Nat} {L : List (List Nat)} (hd : (L.map (codeL p)).Nodup)
    (hc : decide (p ^ s ≤ L.length * p ^ n) = true) : wChk p n s L = true := by
  unfold wChk
  rw [hc, Bool.and_true, List.all_eq_true]
  have hp := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at hab hbc ⊢; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) (L.map (codeL p))
  have hn := (List.mergeSort_perm (L.map (codeL p)) fun a b : Nat => decide (a ≤ b)).nodup_iff.2 hd
  have hlt := (hp.and hn).imp fun h => Nat.lt_of_le_of_ne (of_decide_eq_true h.1) h.2
  intro x hx
  exact decide_eq_true (pairwise_zip_tail hlt x hx)

theorem wOK_of {p : Nat} {m : NMod} {tops : List Pc} {tidx : List Nat} {s : Nat}
    (h1 : tidx.all (fun i => decide (i < m.acts.length) &&
      tops.any (·.reg == (m.acts.getD i default).reg)) = true)
    (h2 : ((wordsL p m.basis.length (tidx.map fun i => (m.acts.getD i default).mat)).map
      (codeL p)).Nodup)
    (h3 : decide (p ^ s ≤ (wordsL p m.basis.length
      (tidx.map fun i => (m.acts.getD i default).mat)).length * p ^ m.basis.length) = true) :
    m.wOK p tops tidx s = true := by
  unfold NMod.wOK
  rw [h1, wChk_of h2 h3]
  rfl

theorem cert9601 : modCheckW (opsP 5 111) NativeSporadic.LySeed1 NativeSporadic.LySeed2
    AlphaLy.lyNregs AlphaLy.lyProg 3 AlphaLy.lyMod AlphaLy.lyTops AlphaLy.lyTidx 7 AlphaLy.lyCf
    AlphaLy.lyCi AlphaLy.lyCt = true := by
  have hm := mcertLP_sound (p := 5) (d := 111) Ly.lay_ok rfl rfl Ly.decA Ly.decB Ly.LA_eq Ly.LB_eq
    Ly.alpha_K
  have hW : AlphaLy.lyMod.wOK 3 AlphaLy.lyTops AlphaLy.lyTidx 7 = true :=
    wOK_of Ly.alpha_wTops Ly.alpha_wNodup Ly.alpha_wCount
  have hA := Ly.alpha_restA
  have hB := Ly.alpha_restB
  unfold modCheckW
  simp only [Bool.and_eq_true] at hA hB ⊢
  exact ⟨⟨⟨⟨⟨⟨⟨hm, hA.1.1⟩, hA.1.2⟩, hA.2⟩, hW⟩, hB.1.1⟩, hB.1.2⟩, hB.2⟩

end CertificateChecks.KernelMP

end
