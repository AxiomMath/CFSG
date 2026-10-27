module

public import Certificates.Kernel.J4Q.QT2A
public import Certificates.Kernel.J4Q.QT2AData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A

theorem z_chk : Nat.beq ZM (etaK c rm one Us 1131) = true := by quickRfl

theorem zR_enc : WfA (zR ()) ∧ encR (zR ()) = ZM := by
  obtain ⟨h1, h2⟩ := eta_enc 1131
  exact ⟨h1, h2.trans (Nat.eq_of_beq_eq_true z_chk).symm⟩

theorem phiR_enc : WfA (phiR ()) ∧ encR (phiR ()) = Nat.xor ZM one := by
  obtain ⟨h1, h2⟩ := enc_addRows zR_enc.1 wf_idRows
  exact ⟨h1, by rw [phiR, h2, zR_enc.2, enc_idRows hK]⟩

theorem p_pack : packOK PM pRows.toList = true := by quickRfl

theorem p_canon : canonJ pad PM = true := by quickRfl

theorem qt2a_pRows_enc : WfA pRows ∧ encR pRows = PM := packOK_sound hK p_pack p_canon

@[expose] noncomputable def CVs : List Nat :=
  [CV_0, CV_1, CV_2, CV_3, CV_4, CV_5, CV_6, CV_7, CV_8, CV_9, CV_10, CV_11]

theorem cv_chk : allR 12 (fun j => andB (Nat.blt (v2N compV[j]!) (Nat.shiftLeft 1 112))
    (Nat.beq (v2N compV[j]!) (getN 0 CVs j))) = true := by quickRfl

theorem compV_enc : ∀ j < 12, (compV[j]!).wf = true ∧ v2N compV[j]! = getN 0 CVs j := by
  intro j hj
  have h := allR_spec cv_chk j hj
  rw [andB_eq, Bool.and_eq_true] at h
  refine ⟨wf_of_lt ?_, Nat.eq_of_beq_eq_true h.2⟩
  exact lt_of_blt h.1

theorem triv_eq {X : Array V2} {x : Nat} (hX : WfA X ∧ encR X = x) :
    trivOnComp X = trivK rm PM CVs x := by
  rw [trivOnComp_eq hK qt2a_pRows_enc compV_enc hX.1, hX.2]

theorem cmz_eq' {X : Array V2} {x : Nat} (hX : WfA X ∧ encR X = x) :
    cmz X = Nat.beq (mulJ c rm x ZM) (mulJ c rm ZM x) := by
  rw [cmz_eq hK zR_enc hX.1, hX.2]

@[expose] def bRow (i : Nat) : V2 :=
  if i < 50 then (phiR ())[kIdx[i]!]! else if i < 62 then compV[i - 50]! else (idRows ())[kIdx[i - 62]!]!

theorem b_chk : Nat.beq BRM (rowsJ fun i => if i < 50 then rowJ rm (Nat.xor ZM one) kIdx[i]!
    else if i < 62 then getN 0 CVs (i - 50) else rowJ rm one kIdx[i - 62]!) = true := by quickRfl

theorem bRows_enc : WfA (bRows ()) ∧ encR (bRows ()) = BRM := by
  have hf : ∀ i < 112, (bRow i).wf = true := by
    intro i hi
    unfold bRow
    split_ifs with h1 h2
    · exact wf_getElem! phiR_enc.1 _
    · exact (compV_enc _ (by omega)).1
    · exact wf_getElem! wf_idRows _
  obtain ⟨h1, h2⟩ := enc_ofFn bRow hf
  refine ⟨h1, h2.trans ((rowsJ_congr ?_).trans (Nat.eq_of_beq_eq_true b_chk).symm)⟩
  intro i hi
  unfold bRow
  split_ifs with h1 h2
  · rw [v2N_getElem! hK phiR_enc.1, phiR_enc.2]
  · exact (compV_enc _ (by omega)).2
  · rw [v2N_getElem! hK wf_idRows, enc_idRows hK]

@[expose] def patRow (i : Nat) : V2 := if 62 ≤ i then (idRows ())[i - 62]! else V2.zero

theorem patRows_enc : WfA patRows ∧
    encR patRows = rowsJ fun i => if 62 ≤ i then rowJ rm one (i - 62) else 0 := by
  have hf : ∀ i < 112, (patRow i).wf = true := by
    intro i _
    unfold patRow
    split_ifs
    · exact wf_getElem! wf_idRows _
    · rfl
  obtain ⟨h1, h2⟩ := enc_ofFn patRow hf
  refine ⟨h1, h2.trans (rowsJ_congr ?_)⟩
  intro i _
  unfold patRow
  split_ifs
  · rw [v2N_getElem! hK wf_idRows, enc_idRows hK]
  · rfl

theorem bInv_enc : WfA (invRows (bRows ())) ∧ encR (invRows (bRows ())) = BRI :=
  invRows_enc hK bRows_enc.1 (by quickRfl) (by rw [bRows_enc.2]; quickRfl)

theorem qt2a_pInv_enc : WfA (invRows pRows) ∧ encR (invRows pRows) = PI :=
  invRows_enc hK qt2a_pRows_enc.1 (by quickRfl) (by rw [qt2a_pRows_enc.2]; quickRfl)

theorem ya_chk : Nat.beq YA (wordJ c rm one G5 G5i aK) = true := by quickRfl

theorem yb_chk : Nat.beq YB (wordJ c rm one G5 G5i bK) = true := by quickRfl

theorem yc_chk :
    Nat.beq YC (wordJ c rm one G5 G5i (negRev aK ++ negRev bK ++ aK ++ bK)) = true := by quickRfl

theorem ya_enc : WfA (wR aDw) ∧ encR (wR aDw) = YA :=
  ⟨(wR_enc _).1, by rw [(wR_enc _).2, aDw_eq]; exact (Nat.eq_of_beq_eq_true ya_chk).symm⟩

theorem yb_enc : WfA (wR bDw) ∧ encR (wR bDw) = YB :=
  ⟨(wR_enc _).1, by rw [(wR_enc _).2, bDw_eq]; exact (Nat.eq_of_beq_eq_true yb_chk).symm⟩

theorem yc_enc : WfA (wR cDw) ∧ encR (wR cDw) = YC :=
  ⟨(wR_enc _).1, by
    rw [(wR_enc _).2, cDw, aDw_eq, bDw_eq, invW_eq, invW_eq]
    exact (Nat.eq_of_beq_eq_true yc_chk).symm⟩

@[expose] noncomputable def YEs : List Nat :=
  [YE_0, YE_1, YE_2, YE_3, YE_4, YE_5, YE_6, YE_7, YE_8, YE_9, YE_10, YE_11, YE_12, YE_13, YE_14,
    YE_15, YE_16, YE_17, YE_18, YE_19, YE_20, YE_21, YE_22, YE_23, YE_24, YE_25, YE_26]

theorem ye_chk : allR 27 (fun n => Nat.beq (getN one YEs n) (mulJ c rm (mulJ c rm
    (powJ c rm one YA (n / 9)) (powJ c rm one YB (n / 3 % 3))) (powJ c rm one YC (n % 3)))) = true := by
  quickRfl

theorem yEl_enc {n : Nat} (hn : n < 27) : WfA (yEl n) ∧ encR (yEl n) = getN one YEs n := by
  have h := mul_enc hK (mul_enc hK (pow_enc hK ya_enc (n / 9)) (pow_enc hK yb_enc (n / 3 % 3)))
    (pow_enc hK yc_enc (n % 3))
  exact ⟨h.1, h.2.trans (Nat.eq_of_beq_eq_true (allR_spec ye_chk n hn)).symm⟩

theorem y5_chk : Nat.beq YP5 (powJ c rm one (wordJ c rm one G5 G5i y5K) y5e) = true := by quickRfl

theorem y7_chk : Nat.beq YP7 (powJ c rm one (wordJ c rm one G5 G5i y7K) y7e) = true := by quickRfl

theorem y11_chk : Nat.beq YP11 (powJ c rm one (wordJ c rm one G5 G5i y11K) y11e) = true := by
  quickRfl

theorem y5_enc : WfA (y5R ()) ∧ encR (y5R ()) = YP5 :=
  ⟨y5R_enc.1, y5R_enc.2.trans (Nat.eq_of_beq_eq_true y5_chk).symm⟩

theorem y7_enc : WfA (y7R ()) ∧ encR (y7R ()) = YP7 :=
  ⟨y7R_enc.1, y7R_enc.2.trans (Nat.eq_of_beq_eq_true y7_chk).symm⟩

theorem y11_enc : WfA (y11R ()) ∧ encR (y11R ()) = YP11 :=
  ⟨y11R_enc.1, y11R_enc.2.trans (Nat.eq_of_beq_eq_true y11_chk).symm⟩

@[expose] noncomputable def QAs : List Nat :=
  [QA_0, QA_1, QA_2, QA_3, QA_4, QA_5, QA_6, QA_7, QA_8, QA_9, QA_10, QA_11]

@[expose] noncomputable def QIs : List Nat :=
  [QI_0, QI_1, QI_2, QI_3, QI_4, QI_5, QI_6, QI_7, QI_8, QI_9, QI_10, QI_11]

theorem qa_chk : allR 12 (fun k =>
    Nat.beq (getN one QAs k) (wordJ c rm one G5 G5i (qGenK.getD k []))) = true := by quickRfl

theorem qi_chk : allR 12 (fun k =>
    Nat.beq (getN one QIs k) (wordJ c rm one G5 G5i (negRev (qGenK.getD k [])))) = true := by quickRfl

theorem qR_enc {k : Nat} (hk : k < 12) : WfA (qR k) ∧ encR (qR k) = getN one QAs k :=
  ⟨(wR_enc _).1, by
    rw [qR, (wR_enc _).2, qGenW_eq]
    exact (Nat.eq_of_beq_eq_true (allR_spec qa_chk k hk)).symm⟩

theorem qRi_enc {k : Nat} (hk : k < 12) :
    WfA (wR (invW (qGenW.getD k []))) ∧ encR (wR (invW (qGenW.getD k []))) = getN one QIs k :=
  ⟨(wR_enc _).1, by
    rw [(wR_enc _).2, qGenW_eq, invW_eq]
    exact (Nat.eq_of_beq_eq_true (allR_spec qi_chk k hk)).symm⟩

end CertificateChecks.KernelJ4Q

end
