module

public import Certificates.Kernel.YoshQ.GlueRec
public import Certificates.Kernel.YoshQ.Words4
public import Certificates.Kernel.YoshQ.Words5

public section

namespace CertificateChecks.KernelYoshQ

open CFSG.KC.YoshQ CFSG.EvenSporadicStandard.M12Std.Yosh CFSG.EvenSporadicStandard.Fin76b

theorem yEl_eq : yEl = (Y.RL.map (tabN 14 5)).toArray :=
  y_ok.closure_fst (by decide) (by decide) (by decide) (Nat.le_refl _)

theorem xDetermined_true : xDetermined = true := by
  have e : xDetermined = xDeterminedOn yEl := rfl
  rw [e, yEl_eq]
  exact w_xDet

theorem cvCheck_true : cvCheck = true := by
  have e : cvCheck = cvCheckOn yEl := rfl
  rw [e, yEl_eq]
  exact w_cv

theorem qCheck_of {α β : Nat} {GS RL : List Nat} {cnt EP PL POS : Nat} {SM SF : List Nat}
    (R : RecOK 24 5 24 4000 (qGens α β) GS RL cnt EP PL POS SM SF)
    (hg : gensOK 24 5 (qGens α β) GS = true ∧ wordsOK 24 8 (qGens α β) (rel4 α β) = true)
    (hc : cnt = 1536) : qCheck α β = true := by
  have he := R.enumOK (size := 1536) (by decide) (by decide) (by decide) (Nat.le_refl _)
    (gensOK_spec hg.1).2 hc
  have := modelCheck_of he hg.2
  exact this

theorem lemma4Check_true : lemma4Check = true := by
  have q00 := qCheck_of q00_ok g_q00 (by decide)
  have q01 := qCheck_of q01_ok g_q01 (by decide)
  have q10 := qCheck_of q10_ok g_q10 (by decide)
  have q11 := qCheck_of q11_ok g_q11 (by decide)
  simp only [lemma4Check, List.all_cons, List.all_nil, List.any_cons, List.any_nil, w_relP, w_step0,
    w_step1, w_x0, w_x1, w_z00, w_z01, w_z10, w_z11, xDetermined_true, q00, q01, q10, q11,
    Bool.and_self]

theorem nCheck_of {α k : Nat} {GS RL : List Nat} {cnt EP PL POS : Nat} {SM SF : List Nat}
    (R : RecOK 16 5 16 4000 (nGens α k) GS RL cnt EP PL POS SM SF)
    (hg : gensOK 16 5 (nGens α k) GS = true ∧ wordsOK 16 9 (nGens α k) (relN α α k) = true)
    (hc : cnt = 3072) : nCheck α k = true := by
  have he := R.enumOK (size := 3072) (by decide) (by decide) (by decide) (Nat.le_refl _)
    (gensOK_spec hg.1).2 hc
  exact modelCheck_of he hg.2

theorem kCheck_true : kCheck = true := by
  have he := k_ok.enumOK (size := 384) (by decide) (by decide) (by decide) (Nat.le_refl _)
    (gensOK_spec g_k).2 (by decide)
  unfold kCheck
  rw [he, w_kWords]
  rfl

theorem rCheck_true : rCheck = true :=
  r_ok.enumOK (size := 64) (by decide) (by decide) (by decide) (Nat.le_refl _)
    (gensOK_spec g_r).2 (by decide)

theorem eCheck_true : eCheck = true :=
  modelCheck_of (eg_ok.enumOK (size := 128) (by decide) (by decide) (by decide) (Nat.le_refl _)
    (gensOK_spec g_eg.1).2 (by decide)) g_eg.2

theorem lemma5Check_true : lemma5Check = true := by
  have n00 := nCheck_of n00_ok g_n00 (by decide)
  have n01 := nCheck_of n01_ok g_n01 (by decide)
  have n10 := nCheck_of n10_ok g_n10 (by decide)
  have n11 := nCheck_of n11_ok g_n11 (by decide)
  simp only [lemma5Check, List.all_cons, List.all_nil, w_sAct, kCheck_true, rCheck_true, w_wMem,
    cvCheck_true, eCheck_true, w_relNQ00, w_relNQ01, w_relNQ10, w_relNQ11, w_fix00, w_fix01,
    w_fix10, w_fix11, w_inner00, w_inner01, w_inner10, w_inner11, n00, n01, n10, n11,
    Bool.and_self]

end CertificateChecks.KernelYoshQ

end
