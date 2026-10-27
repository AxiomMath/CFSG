module

public import CFSG.Certificates.Kernel.MonsterB.FischerWordSound
public import Certificates.Kernel.Sporadic.SuzI301K.GlueInv

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzI301K

open CFSG.KC.Enum CFSG.KC.LinRep CFSG.KC.LinRepSound CFSG.KC.LinRepCheck CFSG.KC.SuzI301Lin
open CFSG.KC.SuzI301K CFSG.KD.SuzI301 CFSG.PSL3Four.Native CFSG.Sporadic.SuzI301
  CFSG.Monster.B.Co2.Native CFSG.RankThree.Native

theorem validA_lin {w iv : Nat} (h : ∀ i < 6, ev (col iv) (col w i) = 2 ^ i)
    (h' : ∀ i < 6, ev (col w) (col iv i) = 2 ^ i) :
    validA 64 (linTab (col w)) = true := by
  have hw : ∀ i < 6, col w i < 64 := fun i _ => col_lt w i
  have hv : ∀ i < 6, col iv i < 64 := fun i _ => col_lt iv i
  have hlt : ∀ v < 64, (linTab (col w))[v]! < 64 := fun v hv => by
    rw [linTab_get _ hv]
    exact ev_lt hw v
  have h1 : ∀ v < 64, (linTab (col w))[v]! < 64 ∧ ev (col iv) ((linTab (col w))[v]!) = v :=
    fun v hv' => ⟨hlt v hv', by rw [linTab_get _ hv', ev_ev, ev_congr h]; exact ev_id v hv'⟩
  have h2 : ∀ x < 64, ev (col iv) x < 64 ∧ (linTab (col w))[ev (col iv) x]! = x := fun x hx =>
    ⟨ev_lt hv x, by rw [linTab_get _ (ev_lt hv x), ev_ev, ev_congr h']; exact ev_id x hx⟩
  unfold validA isInvA
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro i hi
  rw [CFSG.KC.FischerE.invCand_get h1 h2 (hlt i hi)]
  simp [hlt i hi, (h1 i hi).2]

theorem iv_col {c : Nat} (hc : c < 4) :
    (∀ i < 6, ev (col (nthN IV c)) (col (nthN CW c) i) = 2 ^ i) ∧
      ∀ i < 6, ev (col (nthN CW c)) (col (nthN IV c) i) = 2 ^ i := by
  have e := CFSG.KS.allN_spec kIV c hc
  beta_reduce at e
  obtain ⟨e1, e2⟩ := band e
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · rw [← col_mulW _ _ hi, Nat.eq_of_beq_eq_true e1]
    exact col_idW i hi
  · rw [← col_mulW _ _ hi, Nat.eq_of_beq_eq_true e2]
    exact col_idW i hi

theorem mat64_cw_T : mat64 (sTau ()) = linTab (col (nthN CW 3)) := by
  rw [mat64_T]
  exact linTab_congr fun i hi => (cw_col (by norm_num) hi).symm

theorem valid64_facts : validA 64 (mat64 (sD ())) = true ∧ validA 64 (mat64 (sB2 ())) = true ∧
    validA 64 (mat64 (sB3 ())) = true ∧ validA 64 (mat64 (sTau ())) = true := by
  rw [mat64_cw_D, mat64_cw_B2, mat64_cw_B3, mat64_cw_T]
  obtain ⟨a0, b0⟩ := iv_col (c := 0) (by norm_num)
  obtain ⟨a1, b1⟩ := iv_col (c := 1) (by norm_num)
  obtain ⟨a2, b2⟩ := iv_col (c := 2) (by norm_num)
  obtain ⟨a3, b3⟩ := iv_col (c := 3) (by norm_num)
  exact ⟨validA_lin a0 b0, validA_lin a1 b1, validA_lin a2 b2, validA_lin a3 b3⟩

end CertificateChecks.KernelSpor.SuzI301K

end
