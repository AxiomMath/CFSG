module

public import Certificates.Kernel.HeLoc.QCent
public import Certificates.Kernel.HeLoc.FiveLFacts
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.HeFiveQCentInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHeLoc.Five

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.HeLoc
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier CFSG.RankThree.Native CFSG.RankThree.PartOne
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch


theorem commA_false {i w k : Nat} (hi : i < 600) (hw : w < 8330) (hk : k < 2)
    (h : Nat.beq (tv i (FiveL.pa k w)) (FiveL.pa k (tv i w)) = false) :
    commA 8330 (treeArr 8330 heFiveC0Gens C0.P C0.L i) heFiveQGens[k]! = false := by
  rw [Bool.eq_false_iff]
  intro hc
  have hR : RepF 8330 (tv i) (treePerm gp C0.P C0.L i) := repF_trV tree hg 600 i hi.le hi
  have e := (commA_iff (rep_treeArr tree hgs i hi) (FiveL.qgs k hk)).1 hc
  have h1 := (hR.comp (FiveL.qg k hk)) w hw
  have h2 := ((FiveL.qg k hk).comp hR) w hw
  rw [e] at h1
  have e2 : tv i (FiveL.pa k w) = FiveL.pa k (tv i w) := h1.trans h2.symm
  rw [e2] at h
  exact absurd h (by simp)

theorem qcent : CFSG.HardMathSupport.Dickson.I271.heFiveQCentOK () = true := by
  unfold CFSG.HardMathSupport.Dickson.I271.heFiveQCentOK
  dsimp only
  rw [pts_eq, allLt_iff]
  intro i hi
  rw [Array.size_ofFn] at hi
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  have hp : Rep 8330 (treeArr 8330 heFiveC0Gens C0.P C0.L i) (treePerm gp C0.P C0.L i) :=
    rep_treeArr tree hgs i hi
  have hR : RepF 8330 (tv i) (treePerm gp C0.P C0.L i) := repF_trV tree hg 600 i hi.le hi
  have hc : qcAtW i (QW.getD i 0) = true := by
    have h := allN_spec kQC i hi
    unfold qcAt at h
    rwa [strictB_val] at h
  unfold qcAtW at hc
  rw [Bool.or_eq_true, Bool.not_eq_true']
  cases hw : Nat.beq (QW.getD i 0) 8330
  · rw [hw] at hc
    dsimp only at hc
    obtain ⟨hlt, hne⟩ := (bAnd_iff _ _).1 hc
    have hx : QW.getD i 0 < 8330 := Nat.blt_eq.mp hlt
    left
    rw [Bool.and_eq_false_iff]
    cases h0 : Nat.beq (tv i (FiveL.pa 0 (QW.getD i 0))) (FiveL.pa 0 (tv i (QW.getD i 0)))
    · exact Or.inl (commA_false hi hx (by norm_num) h0)
    · rw [h0] at hne
      dsimp only at hne
      cases h1 : Nat.beq (tv i (FiveL.pa 1 (QW.getD i 0))) (FiveL.pa 1 (tv i (QW.getD i 0)))
      · exact Or.inr (commA_false hi hx (by norm_num) h1)
      · rw [h1] at hne
        exact absurd hne (by decide)
  · rw [hw] at hc
    dsimp only at hc
    obtain ⟨hq0, hfix⟩ := (bAnd_iff _ _).1 hc
    right
    obtain ⟨-, huP, -⟩ := trQ_spec tree (fun a ha b hb => he_mul_mem_iff ha hb) gp_mem gp_par q_lt
      600 i hi.le hi
    have hu : treePerm gp C0.P C0.L i ∈ heP := huP.2 (Nat.eq_of_beq_eq_true hq0)
    have hu5 : treePerm gp C0.P C0.L i ^ 5 = 1 := by
      refine (fixL_iff he_baseFaithful he_bs_lt (RepF.powF hR 5) ?_).1 hfix
      rw [← heP_eq_originalSubgroup]
      exact heP.pow_mem hu 5
    exact (eqA_iff (CFSG.Monster.B.Mathieu.rep_powArr hp 5) rep_idA).2 hu5

end CertificateChecks.KernelHeLoc.Five

end
