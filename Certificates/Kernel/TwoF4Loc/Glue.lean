module

public import Certificates.Data.TwoF4LocCheck
public import CFSG.Sporadic.Schreier.TitsActionCheckInputs
public import CFSG.Sporadic.Schreier.TitsCentralCheckInputs
import Certificates.Kernel.TwoF4Loc.Checks
import Certificates.Kernel.TwoF4Lie.Checks
import CFSG.Certificates.Kernel.TwoF4LocSound

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTwoF4Loc

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.TwoF4LieK CFSG.KC.TwoF4LocK CFSG.KC.TwoF4LocSound
  CFSG.KD.TwoF4Loc CFSG.TwoF4Loc CFSG.TwoF4Lie CFSG.RuF45 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Tits CertificateChecks.KernelSporSch.TitsAction
  CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.TitsCommon
  CertificateChecks.KernelSpor.Tits2264

theorem hG : titsGenArrs.size = 4 ∧ ∀ j < 4, titsGenArrs[j]! = unpack 1755 11 (F j) :=
  ⟨by simp [titsGenArrs, titsField1755], fun _ hj => gen_eq hj⟩

theorem hFI : allN 4 (fun j => permOK 1755 11 (mask 11) (1755 * 11) (F j) (FI j)) = true :=
  CertificateChecks.KernelTwoF4Lie.invG

theorem hpts : ∀ i < 8775, titsLinePtArr[i]! = lpK i := fun _ hi => lp_get hi

theorem baseF :
    wordIs F FI tWord (TT 0) = true ∧ wordIs F FI cWord (TC 0) = true ∧
      wordIs F FI locQWord (TQ 0) = true ∧
      mul (mul (TC 0) TitsZ) (mul (TC 0) (TC 0)) = TZ 0 ∧
      mul (mul (mul (TC 0) (TC 0)) TitsZ) (TC 0) = TZ 1 ∧ cn (TZ 0) = true ∧ cn (TZ 1) = true ∧
      lineK lpK (TC 0) = true ∧ vK TitsZ (TZ 0) (TZ 1) = true ∧
      qK (TT 0) TitsZ (TZ 0) (TQ 0) = true ∧ collK lpK (TT 0) = true ∧
      (∀ f : Nat → Bool, cl.all f = (colK lpK).all f) ∧ fixL (TT 0) = fx ∧ fx.length = 27 := by
  have h := base
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩,
    h15⟩ := h
  refine ⟨h1, h2, h3, Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5, h6, h7, h8, h9, h10,
    h11, all_of_mem ?_ ?_, h14, h15⟩
  · simpa using h12
  · simpa using h13

public theorem check : twoF4LocCheck titsLinePtArr titsGenArrs titsZArr = true := by
  obtain ⟨hT, hC, hQ, e1, e2, hZ1, hZ2, hL, hV, hQK, hcoll, hcl, hfx, hfx27⟩ := baseF
  obtain ⟨-, eT, cT⟩ := word_U hG hFI hT
  obtain ⟨-, eC, cC⟩ := word_U hG hFI hC
  obtain ⟨wQ, eQ, cQ⟩ := word_U hG hFI hQ
  have cZ : cn TitsZ = true := canonZ
  have et : tArr titsGenArrs (invArrs 1755 titsGenArrs) = unpack 1755 11 (TT 0) := eT
  have ec : cArr titsGenArrs (invArrs 1755 titsGenArrs) = unpack 1755 11 (TC 0) := eC
  have ez1 : compA 1755 (compA 1755 (unpack 1755 11 (TC 0)) (unpack 1755 11 TitsZ))
      (compA 1755 (unpack 1755 11 (TC 0)) (unpack 1755 11 (TC 0))) = unpack 1755 11 (TZ 0) := by
    rw [comp_U cC cZ, comp_U cC cC, comp_U (cn_mul cC cZ) (cn_mul cC cC), e1]
  have ez2 : compA 1755 (compA 1755 (compA 1755 (unpack 1755 11 (TC 0)) (unpack 1755 11 (TC 0)))
      (unpack 1755 11 TitsZ)) (unpack 1755 11 (TC 0)) = unpack 1755 11 (TZ 1) := by
    rw [comp_U cC cC, comp_U (cn_mul cC cC) cZ, comp_U (cn_mul (cn_mul cC cC) cZ) cC, e2]
  unfold twoF4LocCheck
  simp only [et, ec, z_eq, ez1, ez2]
  rw [locLineOK_U hpts cC, locVOK_U cZ hZ1 hZ2, wQ, eQ, locQOK_U cT cZ hZ1 cQ,
    locCollFixed_U hpts cT, hL, hV, hQK, hcoll]
  simp only [Bool.true_and]
  unfold locFixOK
  rw [locFix_U cT, hfx, hfx27]
  unfold allLt
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  rintro ⟨k, hk27⟩ _
  simp only []
  have hk := allN_spec rows k hk27
  have hidx : ∀ e ∈ ch.getD k [], e.2 < cws.length := by
    have h := chainIdx
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
    intro e he
    have hl : k < ch.length := by rw [h.1]; exact hk27
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some] at he
    exact h.2 _ (List.getElem_mem hl) e he
  have hr := row_U hG hFI hpts hcl cZ cT hZ1 hZ2 words hidx hk
  have ech : locChains[k]! = (ch.getD k []).map fun e => (e.1, cws.getD e.2 "") := by
    rw [chains, List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases ch[k]? <;> rfl
  have ew : locWords[k]! = locWords.getD k "" := by
    rw [List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rfl
  have ef : fx[k]! = fx.getD k 0 := by
    rw [List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rfl
  rw [ech, ew, ef]
  exact hr

end CertificateChecks.KernelTwoF4Loc
