
module

public import Certificates.Kernel.Sporadic.L2.G5
public import Certificates.Kernel.Sporadic.Q3A.Tits

public section

namespace CertificateChecks.KernelSpor.L2G

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.FpBfs
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzRecog.LevelTwo
open CFSG.Sporadic.SuzRecog.LevelTwoData CFSG.Sporadic.SuzRecog.ElimCert CFSG.Sporadic.SuzRecog
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.L2K
open CertificateChecks.KernelSpor.SuzTwCF (P p_comp eqA_P pidn_P)

local notation "pgk" => pg 11 (mask 11)
local notation "pc" => pcomp 1782 11 (mask 11)

theorem basicK_parts : RHO ≠ pidn 1782 11 ∧ memXK RHO = true ∧ memXK T1 = true ∧
    invEqK 1782 11 (mask 11) (1782 * 11) T1 T1 = true ∧
    invEqK 1782 11 (mask 11) (1782 * 11) W0 W0 = true ∧ commK2 W0 T1 = true ∧
    commK2 W0 (pc RHO (pc W0 RHOI)) = true ∧ W0 ≠ pc RHO (pc W0 RHOI) := by
  have h := kBasic
  unfold basicK at h
  rw [band, band, band, band, band, band, band] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨fun e => by rw [nbeq.2 e] at h1; exact Bool.false_ne_true h1, h2, h3, h4, h5, h6,
    h7, fun e => by rw [nbeq.2 e] at h8; exact Bool.false_ne_true h8⟩

theorem pW1 : P (rhoConj w0Arr) (pc RHO (pc W0 RHOI)) := p_conj pRho pRhoI pW0

theorem commA_P2 {a b : Array Nat} {A B : Nat} (ha : P a A) (hb : P b B) :
    commA a b = commK2 A B := SuzTwCF.commA_P ha hb

theorem pX_comm {s : Nat} (hs : s < 2) : commK2 (XG s) RHO = true ∧ OddCore.msift (XG s) = true := by
  interval_cases s
  · have h := Q3AK.kX0
    rw [band] at h
    exact h
  · have h := Q3AK.kX1
    rw [band] at h
    exact h

theorem basicOK_true : basicOK = true := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := basicK_parts
  have E : (allLt 2 fun s => isInvA 1782 gens[s]! gensInv[s]! && commA gens[s]! rhoArr &&
      CFSG.Sporadic.SuzOddCore.inM gens[s]!) = true := allLt_iff.2 fun s hs => by
    obtain ⟨c1, c2⟩ := pX_comm hs
    rw [Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨?_, by rw [commA_P2 (pG hs) pRho]; exact c1⟩, ?_⟩
    · rw [gensInv_get hs, gens_get hs]
      exact (Q3AG.pXI hs).2
    · rw [OddCore.inM_eq (pG hs).1 (pG hs).2]
      exact c2
  unfold basicOK
  simp only [Bool.and_eq_true, Bool.not_eq_true', E, and_true, true_and]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨Q3AG.pRhoI.2, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [eqA_P (p_comp pRho (p_comp pRho pRho)) pidn_P]
    exact Q3AK.kRho3
  · rw [eqA_P pRho pidn_P]
    exact Q3AG.nbeq_false b1
  · exact L2XCG.memX_of pRho.1 pRho.2 b2
  · rw [pT1.1]
    exact (invEqK_sound b4).2
  · exact L2XCG.memX_of pT1.1 pT1.2 b3
  · rw [pW0.1]
    exact (invEqK_sound b5).2
  · rw [commA_P2 pW0 pT1]
    exact b6
  · rw [commA_P2 pW0 pW1]
    exact b7
  · rw [eqA_P pW0 pW1]
    exact Q3AG.nbeq_false b8

theorem classOK_true : classOK = true := by
  have hS := Q3AG.pS1
  have hi := invEqK_sound Q3AG.tinv.2.2.2.1
  have hSI : P (invCand 1782 ModelGroupsData.s1Arr) (Q3AI 11) :=
    ⟨by rw [hS.1]; exact hi.1, Q3AG.cI (by norm_num)⟩
  unfold classOK
  simp only [Bool.and_eq_true]
  have hinv : isInvA 1782 ModelGroupsData.s1Arr (invCand 1782 ModelGroupsData.s1Arr) = true := by
    rw [hSI.1, hS.1]
    exact hi.2
  refine ⟨⟨⟨Q3AG.q3aOK_true, hinv⟩, ?_⟩, ?_⟩
  · rw [OddCore.inM_eq hS.1 hS.2]
    exact Q3AG.tmem.2.2.2.1
  · rw [conjEq_P hS hSI pRho (p_comp pRho pRho)]
    exact kClass

end CertificateChecks.KernelSpor.L2G

end
