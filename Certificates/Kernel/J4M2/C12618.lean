module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4CentCEData
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4CentCEData
public import Certificates.Kernel.J4M2.C12618Checks
public import Certificates.Kernel.J4M2.C12620
public import Certificates.Kernel.J4M2.C12608
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4M2

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT2A
  CFSG.Quasithin.J4M2 CertificateChecks.KernelJ4Q CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

theorem inv_enc : WfA (invRows ()) ∧ encR (invRows ()) = invK :=
  wg_enc invWord (by decide)

theorem eta12K_eq (m : Nat) : eta12K m = pK m := by
  unfold eta12K pK
  refine foldl_congr_mem _ _ fun j hj acc => ?_
  have hj' : j < 12 := List.mem_range.1 hj
  have e : gmK j = getN one qaL j := by
    unfold gmK
    rw [if_pos hj']
    rfl
  rw [e]

theorem rowsEq {X Y : Array V2} {x : Nat} (hX : WfA X ∧ encR X = x) (hY : WfA Y ∧ encR Y = x) :
    X = Y :=
  CFSG.Sporadic.J4.eqRows_iff.1 (by rw [eqRows_of hX hY]; exact Nat.beq_refl x)

theorem zc_rows : mulRows zM cMat = mulRows cMat zM := by
  have h := mul_enc hK zM_enc cMat_encK
  exact rowsEq ⟨h.1, h.2.trans (Nat.eq_of_beq_eq_true c12618zc)⟩ (mul_enc hK cMat_encK zM_enc)

theorem zz_rows : mulRows zM zM = idRows () := by
  have h := mul_enc hK zM_enc zM_enc
  exact rowsEq ⟨h.1, h.2.trans (Nat.eq_of_beq_eq_true c12618zz)⟩ (id_enc hK)

theorem zcomm {P : Array V2} (hP : WfA P)
    (h : mulRows (mulRows zM P) cMat = mulRows cMat (mulRows zM P)) :
    mulRows P cMat = mulRows cMat P := by
  have wz := zM_enc.1
  have wc := cMat_encK.1
  have e := congrArg (mulRows zM) h
  rw [mulRows_assoc wz hP wc, ← mulRows_assoc wz wz (wf_mulRows hP wc), zz_rows,
    idRows_mulRows (wf_mulRows hP wc), ← mulRows_assoc wc wz hP, ← zc_rows,
    mulRows_assoc wz wc hP, ← mulRows_assoc wz wz (wf_mulRows wc hP), zz_rows,
    idRows_mulRows (wf_mulRows wc hP)] at e
  exact e

theorem qNF0_rows (m : Nat) : qNFRows false m = etaRows12 m := by
  change mulRows (idRows ()) (etaRows12 m) = _
  exact idRows_mulRows (eta12_enc m).1

theorem eta12_encP (m : Nat) : WfA (etaRows12 m) ∧ encR (etaRows12 m) = pK m :=
  ⟨(eta12_enc m).1, (eta12_enc m).2.trans (eta12K_eq m)⟩

theorem ncomm {m : Nat} (hm : m < 4096) (h0 : m ≠ 0) :
    eqRows (mulRows (etaRows12 m) cMat) (mulRows cMat (etaRows12 m)) = false := by
  have hc := commC_all hm
  unfold commC at hc
  have hb : Nat.beq m 0 = false := by
    cases hm' : Nat.beq m 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hm') h0
  rw [hb, orB_false, strictB_eq, andB_eq, Bool.and_eq_true] at hc
  rw [eqRows_of (mul_enc hK (eta12_encP m) cMat_encK) (mul_enc hK cMat_encK (eta12_encP m))]
  exact triK_spec hc.1 0 (by omega)

theorem invChk_ok : invChk () = true := by
  unfold invChk
  rw [Bool.and_eq_true]
  constructor
  · rw [eqRows_of (mul_enc hK inv_enc cMat_encK)
      (mul_enc hK (mul_enc hK cMat_encK cMat_encK) inv_enc)]
    exact c12618inv
  · rw [List.all_eq_true]
    intro m hm
    have hm' := List.mem_range.1 hm
    by_cases h0 : m = 0
    · simp [h0]
    · have h1 := ncomm hm' h0
      have h2 : eqRows (mulRows (qNFRows true m) cMat) (mulRows cMat (qNFRows true m)) = false := by
        cases hq : eqRows (mulRows (qNFRows true m) cMat) (mulRows cMat (qNFRows true m))
        · rfl
        · have e := zcomm (eta12_encP m).1 (CFSG.Sporadic.J4.eqRows_iff.1 hq)
          rw [e, eqRows_of (mul_enc hK cMat_encK (eta12_encP m)) (mul_enc hK cMat_encK (eta12_encP m)),
            Nat.beq_refl] at h1
          exact absurd h1 (by decide)
      rw [qNF0_rows, h1, h2]
      simp [h0]

open CFSG.AGLEmbeddingD2.Wilson.NormalizerAction in
theorem c12618 : invChk () = true := invChk_ok

end CertificateChecks.KernelJ4M2

end
