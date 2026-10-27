
module

public import CFSG.Sporadic.HNOddCore.CRecBase
public import CFSG.Sporadic.HNOddCore.XCheckInputs
public import CFSG.Certificates.Kernel.SporSch.BfsParSound

public section

namespace CertificateChecks.KernelSporSch.HNCTab

open CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native CFSG.Sporadic.HNSchreier
open CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.KS.BfsPar
open CFSG.Sporadic.F5.Native CFSG.Sporadic.Th.Native

theorem letters_inner : plettersOK 17 LocalData.innerWord = true := by decide +kernel

theorem prep_dTab' :
    PRep hnsData.n dTab (permJ (hWordJ LocalData.innerWord)) := by
  rw [dTab_eq]
  exact prep_hWord letters_inner

theorem uInv :
    PRep hnsData.n (pinvCand hnsData.n uTab) (permJ (seedWordJ LocalData.outerWord))⁻¹ ∧
      pisInv hnsData.n uTab (pinvCand hnsData.n uTab) = true :=
  prep_pinvCand prep_uTab

theorem prep_kTab' :
    PRep hnsData.n kTab (permJ dJ) := by
  rw [kTab_eq, dJ, map_mul, map_inv]
  exact prep_pcomp prep_dTab' uInv.1

theorem kInv :
    PRep hnsData.n (pinvCand hnsData.n kTab) (permJ dJ)⁻¹ ∧
      pisInv hnsData.n kTab (pinvCand hnsData.n kTab) = true :=
  prep_pinvCand prep_kTab'

theorem wInv :
    PRep hnsData.n (pinvCand hnsData.n wTab) (permJ wJ)⁻¹ ∧
      pisInv hnsData.n wTab (pinvCand hnsData.n wTab) = true :=
  prep_pinvCand prep_wTab

theorem prep_cATab' :
    PRep hnsData.n cABTab.1 (permJ (conjC aJ)) := by
  rw [cATab_eq, conjC_aJ, map_mul, map_mul, map_inv, mul_assoc]
  exact prep_pcomp prep_kTab' (prep_pcomp prep_aTab kInv.1)

theorem prep_cBTab' :
    PRep hnsData.n cABTab.2 (permJ (conjC bJ)) := by
  rw [cBTab_eq, conjC_bJ, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
  have := prep_pcomp prep_kTab' (prep_pcomp wInv.1 (prep_pcomp prep_bTab
    (prep_pcomp prep_wTab kInv.1)))
  simpa only [mul_assoc] using this

@[expose] noncomputable def cIdx
    (j : ℕ) : ℕ :=
  if h : j < hnsData.n then ((cR • (⟨j, h⟩ : X) : X) : ℕ) else 0

theorem cIdx_of (y : X) :
    cIdx y.val = ((cR • y : X) : ℕ) := by
  rw [cIdx, dif_pos y.isLt]

theorem alpha_get {i : ℕ} (hi : i < hnsData.n) :
    (natTab (hnsData.orbit ()).alpha)[i]! = ap alphaT i :=
  natTab_getElem! (by rw [hnsBase.alpha_size]; exact hi)

theorem beta_get {i : ℕ} (hi : i < hnsData.n) :
    (natTab (hnsData.orbit ()).beta)[i]! = ap betaT i :=
  natTab_getElem! (by rw [hnsBase.beta_size]; exact hi)

theorem cIdx_step {g : JH}
    {t ct : Array ℕ} (ht : PRep hnsData.n t (permJ g)) (hct : PRep hnsData.n ct (permJ (conjC g)))
    {i : ℕ} (hi : i < hnsData.n) : cIdx t[i]! = ct[cIdx i]! := by
  have hy : (⟨t[i]!, ht.lt hi⟩ : X) = g • (⟨i, hi⟩ : X) :=
    Fin.ext ((ht.apply hi).trans (congrArg Fin.val (permJ_apply g _)))
  have hc : cIdx i = ((cR • (⟨i, hi⟩ : X) : X) : ℕ) := cIdx_of ⟨i, hi⟩
  rw [cIdx, dif_pos (ht.lt hi), hy, cR_smul_conj, hc, hct.apply (cR • (⟨i, hi⟩ : X)).isLt,
    permJ_apply]

theorem cRec_facts :
    cRec.size = hnsData.n ∧
      (∀ j < hnsData.n, cRec[j]! = cIdx j) ∧
      cRecOK hnsData.n (natTab (hnsData.orbit ()).alpha) (natTab (hnsData.orbit ()).beta) parTab
        cABTab.1 cABTab.2 cRec = true := by
  rw [cRec_eq, parTab_eq]
  refine cRec_spec (α := ap alphaT) (β := ap betaT) (fun i hi => alpha_get hi)
    (fun i hi => beta_get hi) (fun i hi => ⟨(matA_PK hi).1, (matB_PK hi).1⟩) hns_bfsOrder ?_
    (fun i hi => ?_) (fun i hi => ?_)
  · rw [cIdx, dif_pos (by decide)]
    exact congrArg Fin.val cR_smul_x0
  · rw [← alpha_get hi]
    exact cIdx_step prep_aTab prep_cATab' hi
  · rw [← beta_get hi]
    exact cIdx_step prep_bTab prep_cBTab' hi

theorem prep_cRec' :
    PRep hnsData.n cRec (CFSG.Sporadic.HNOddCore.permR cR) :=
  fun x => by
    rw [cRec_facts.2.1 x.val x.isLt, cIdx_of, CFSG.Sporadic.HNOddCore.permR_apply]

theorem cTab_eq :
    cTab hnsData.n (natTab (hnsData.orbit ()).alpha) (natTab (hnsData.orbit ()).beta)
      hStrongArr = cRec := by
  rw [cRec_eq, cABTab_eq, parTab_eq, kTab_eq, wTab_eq, dTab_eq, uTab_eq]
  rfl

theorem cTab_prep :
    PRep hnsData.n (cTab hnsData.n (natTab (hnsData.orbit ()).alpha)
      (natTab (hnsData.orbit ()).beta) hStrongArr) (CFSG.Sporadic.HNOddCore.permR cR) := by
  rw [cTab_eq]
  exact prep_cRec'

theorem cChecks_ok :
    cChecksO (hnsData.orbit ()) = true := by
  unfold cChecksO cChecks cChecksR cChecksH cChecksDU cChecksK
  simp only [Bool.and_eq_true]
  rw [← hRegs_eq, ← hStrongArr_eq, ← dTab_eq, ← uTab_eq, ← kTab_eq, ← wTab_eq, ← cABTab_eq,
    ← parTab_eq, ← cRec_eq]
  exact ⟨letters_inner, uInv.2, ⟨kInv.2, wInv.2⟩, cRec_facts.2.2⟩

end CertificateChecks.KernelSporSch.HNCTab
