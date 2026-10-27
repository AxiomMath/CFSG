module

public import Certificates.Kernel.Fi22E9.Defs
public import Certificates.Kernel.Fi22Guest.Final
import Certificates.Kernel.Fi22E9.Checks
import Certificates.Kernel.Fi22Core.OrbData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22E9

open CFSG.KC.Enum CFSG.KS CFSG.KS.TW CFSG.KS.Fi22L CFSG.KS.RelTR CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Bridge.TwoGen.Native CFSG.Sporadic.Fi22.Native
  CFSG.AGLEmbedding.KFactProofs.Fi22Guest CertificateChecks.KernelFi22Rho
  CertificateChecks.KernelFi22Guest CFSG.LocalAnalysis.RankThreeUC.AGL81C.Fi22Cent

theorem sData_ok : ∀ s ∈ uData ++ vData, s ≠ 0 ∧ s.natAbs ≤ 18 := by decide +kernel

theorem sTab_TR {l : List Int} (hl : ∀ s ∈ l, s ≠ 0 ∧ s.natAbs ≤ 18) :
    TR 3510 (signedTab 3510 orbL.alpha orbL.alpha orbL.beta (invT 3510 orbL.beta) l)
      (sComp l) :=
  eFold_TR hl

theorem qTab_TR {j : Nat} (hj : j ≤ 5) :
    TR 3510 (wordTab 3510 orbL.alpha orbL.alpha orbL.beta (invT 3510 orbL.beta) (qWord j))
      (qMap j) :=
  TR_congr (wordTab_TR (by norm_num) hL _) fun _ hy => (qWord_eq hj hy).symm

theorem uTab_TR : TR 3510 (signedTab 3510 orbL.alpha orbL.alpha orbL.beta (invT 3510 orbL.beta) uData)
    (sComp uData) :=
  sTab_TR fun s hs => sData_ok s (List.mem_append_left _ hs)

theorem vTab_TR : TR 3510 (signedTab 3510 orbL.alpha orbL.alpha orbL.beta (invT 3510 orbL.beta) vData)
    (sComp vData) :=
  sTab_TR fun s hs => sData_ok s (List.mem_append_right _ hs)

theorem cent3_pt {x : Nat} (hx : x < 3510) :
    iterK (sComp uData) 3 x = x ∧ iterK (sComp vData) 3 x = x := by
  have h := allN_spec cent3_ok x hx
  rw [bAnd_iff] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem centComm_pt {x : Nat} (hx : x < 3510) :
    sComp uData (sComp vData x) = sComp vData (sComp uData x) ∧
      sComp uData (qMap iC x) = qMap iC (sComp uData x) ∧
      sComp vData (qMap jC x) = qMap jC (sComp vData x) := by
  have h := allN_spec centComm_ok x hx
  rw [bAnd_iff, bAnd_iff] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2.1, Nat.eq_of_beq_eq_true h.2.2⟩

theorem qMoves {j : Nat} (hj : j ≤ 5) (h : movesK (qMap j) = true) :
    movesPt 3510 (wordTab 3510 orbL.alpha orbL.alpha orbL.beta (invT 3510 orbL.beta)
      (qWord j)) = true := by
  obtain ⟨w, hw, hf⟩ := movesK_spec h
  exact movesPt_of (qTab_TR hj) hw hf

theorem two_checks : twoChecks 3510
    (signedTab 3510 orbL.alpha orbL.alpha orbL.beta (invT 3510 orbL.beta) uData)
    (signedTab 3510 orbL.alpha orbL.alpha orbL.beta (invT 3510 orbL.beta) vData)
    (wordTab 3510 orbL.alpha orbL.alpha orbL.beta (invT 3510 orbL.beta) (qWord iC))
    (wordTab 3510 orbL.alpha orbL.alpha orbL.beta (invT 3510 orbL.beta) (qWord jC)) = true := by
  have hQi := qTab_TR (j := iC) (by decide)
  have hQj := qTab_TR (j := jC) (by decide)
  unfold twoChecks
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [beq_iff_eq]
    exact eq_idT_of_TR (by norm_num) (powT_TR (by norm_num) uTab_TR 3) fun y hy => (cent3_pt hy).1
  · rw [beq_iff_eq]
    exact eq_idT_of_TR (by norm_num) (powT_TR (by norm_num) vTab_TR 3) fun y hy => (cent3_pt hy).2
  · rw [beq_iff_eq]
    exact eq_of_TR (compT_TR' uTab_TR vTab_TR) (compT_TR' vTab_TR uTab_TR) fun y hy => (centComm_pt hy).1
  · rw [beq_iff_eq]
    exact eq_of_TR (compT_TR' uTab_TR hQi) (compT_TR' hQi uTab_TR) fun y hy => (centComm_pt hy).2.1
  · rw [beq_iff_eq]
    exact eq_of_TR (compT_TR' vTab_TR hQj) (compT_TR' hQj vTab_TR) fun y hy => (centComm_pt hy).2.2
  · have hp : ∀ a < 3, ∀ b < 3, (a == 0 && b == 0) = false →
        movesPt 3510 (compT 3510
          (powT 3510 a (signedTab 3510 orbL.alpha orbL.alpha orbL.beta (invT 3510 orbL.beta)
            uData))
          (powT 3510 b (signedTab 3510 orbL.alpha orbL.alpha orbL.beta (invT 3510 orbL.beta)
            vData))) = true := by
      intro a ha b hb hz
      have ht : 0 < 3 * a + b := by
        rcases Nat.eq_zero_or_pos (3 * a + b) with h | h
        · have h0 : a = 0 ∧ b = 0 := by omega
          obtain ⟨rfl, rfl⟩ := h0
          exact absurd hz (by decide)
        · exact h
      have h8 : 3 * a + b - 1 < 8 := by omega
      have hm := allN_spec centProd_ok (3 * a + b - 1) h8
      rw [Nat.succ_eq_add_one, Nat.sub_add_cancel ht] at hm
      obtain ⟨w, hw, hf⟩ := movesK_spec hm
      have hT := compT_TR' (powT_TR (by norm_num) uTab_TR a) (powT_TR (by norm_num) vTab_TR b)
      refine movesPt_of hT hw fun e => hf ?_
      unfold centProd
      have e1 : Nat.div (3 * a + b) 3 = a := by
        change (3 * a + b) / 3 = a
        omega
      have e2 : Nat.mod (3 * a + b) 3 = b := by
        change (3 * a + b) % 3 = b
        omega
      rw [e1, e2]
      exact e
    refine List.all_eq_true.2 fun a ha => List.all_eq_true.2 fun b hb => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    have ha' : a < 3 := by omega
    have hb' : b < 3 := by omega
    rw [Bool.or_eq_true]
    cases hz : (a == 0 && b == 0)
    · exact Or.inr (hp a ha' b hb' hz)
    · exact Or.inl rfl

theorem cent_check : fi22CentCheck = true := by
  unfold fi22CentCheck
  rw [CertificateChecks.KernelFi22C.orbitData_eq]
  unfold centCheck
  have hq := centQMv_ok
  unfold centQMvChk at hq
  rw [bAnd_iff] at hq
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨?_, qMoves (by decide) hq.1⟩, qMoves (by decide) hq.2⟩, two_checks⟩
  refine relCheck_of_TR (by norm_num) hL ?_
  intro v hv x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl
  · exact rel_x5 hx
  · exact rel_y5 hx
  · exact rel_comm hx

end CertificateChecks.KernelFi22E9

end
