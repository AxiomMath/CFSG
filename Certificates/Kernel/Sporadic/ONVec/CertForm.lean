module

public import Certificates.Kernel.Sporadic.ONVec.CertOrb
public import Certificates.Kernel.Sporadic.ONVec.MatT
public import Certificates.Kernel.Sporadic.ONVec.MatP
public import Certificates.Kernel.Sporadic.ONVec.MatI
public import Certificates.Kernel.Sporadic.ONVec.MatF
public import Certificates.Kernel.Sporadic.ONVec.MatG
public import Certificates.Kernel.Sporadic.ONVec.Gram
public import CFSG.Certificates.Kernel.ONOut.InvVSound
public import CFSG.Sporadic.Fi23.WideSpec
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.PackFld
import Mathlib.Tactic.NormNum

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONVec

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.F3.Native CFSG.Sporadic.Fi23.Native
open CFSG.Sporadic.ON.Native CFSG.ONSchreier.Native CFSG.Sporadic.Th.Native CFSG.KS.ONOut
open CertificateChecks.KernelSpor

theorem cm_canon : ∀ j < 154, canon (at0 CM j) = true := (colsK_transpose formK).1

theorem cm_list : CM.length = 154 ∧ ∀ j < 154, CM.getD j 0 = at0 CM j := by
  refine ⟨?_, fun _ _ => rfl⟩
  have h := lensK
  simp only [bAnd_iff] at h
  exact Nat.eq_of_beq_eq_true h.1

theorem form_eq : rowsOf 154 CFSG.ONSchreier.Data.formPayload = rowsV (at0 CM) := by
  rw [ONForm.eq]
  exact rowsOf_eq formK symK

theorem idM_size : (idM 154).size = 154 := by
  unfold idM
  exact Array.size_ofFn

theorem rowsV_unit : rowsV (fun i => vmk (2 ^ i) 0) = idM 154 := by
  refine arr_ext' (rowsV_size _) idM_size fun i hi => ?_
  rw [rowsV_get hi, vOf_vmk (Nat.pow_lt_pow_right (by omega) (by omega))]
  unfold idM
  rw [getElem!_ofFn' hi, Nat.one_shiftLeft]

theorem xi_canon : ∀ k < 154, canon (at0 XI k) = true := fun k hk => (unitK_spec invK k hk).1

theorem xm_eq : mul 154 (rowsV (at0 XI)) (rowsV (at0 CM)) = idM 154 := by
  rw [mul_rowsV cm_list cm_canon rfl (D := fun i => vmk (2 ^ i) 0) fun i hi => (unitK_spec invK i hi).2,
    rowsV_unit]

theorem invV_eq : invV 154 (rowsV (at0 CM)) = rowsV (at0 XI) := by
  have hc := canonM_rowsV cm_canon
  have hx := canonM_rowsV xi_canon
  have hsx : transpose 154 (rowsV (at0 XI)) = rowsV (at0 XI) := transpose_rowsV symXK
  have hsm : transpose 154 (rowsV (at0 CM)) = rowsV (at0 CM) := transpose_rowsV symK
  have h1 : toMat 154 (rowsV (at0 XI)) * toMat 154 (rowsV (at0 CM)) = 1 := by
    rw [← toMat_mul (rowsV_size _) (RowsWF.of_canonM hx) (RowsWF.of_canonM hc), xm_eq, toMat_idM]
  have h2 : toMat 154 (rowsV (at0 CM)) * toMat 154 (rowsV (at0 XI)) = 1 := by
    have e := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, Matrix.transpose_one, ← toMat_transpose, ← toMat_transpose, hsx,
      hsm] at e
    exact e
  obtain ⟨h3, h4⟩ := invV_sound hc h2
  exact eq_of_canonM h3 hx h4

theorem formA_eq : mul 154 (mul 154 (transpose 154 (rowsA ())) (rowsV (at0 CM))) (rowsA ()) =
    rowsV (at0 CM) := by
  have hT : transpose 154 (rowsA ()) = rowsV ONV.CA := by
    unfold rowsA
    rw [ONSeedA.eq]
    exact (colsK_transpose ON.colsAK).2
  have hR : rowsA () = rowsV (at0 RA) := by
    unfold rowsA
    rw [ONSeedA.eq]
    exact rowsOf_eq ON.colsAK rowsAK
  have hl : RA.length = 154 ∧ ∀ j < 154, RA.getD j 0 = at0 RA j := by
    refine ⟨?_, fun _ _ => rfl⟩
    have h := lensK
    simp only [bAnd_iff] at h
    exact Nat.eq_of_beq_eq_true h.2.2.1
  rw [hT, mul_rowsV cm_list cm_canon rfl (D := fun i => mv CM (ONV.CA i)) fun _ _ => rfl, hR,
    mul_rowsV hl (tposK_spec rowsAK).2.1 rfl (D := at0 CM) fun i hi =>
      Nat.eq_of_beq_eq_true (allN_spec formAK i hi)]

theorem formB_eq : mul 154 (mul 154 (transpose 154 (rowsB ())) (rowsV (at0 CM))) (rowsB ()) =
    rowsV (at0 CM) := by
  have hT : transpose 154 (rowsB ()) = rowsV ONV.CB := by
    unfold rowsB
    rw [ONSeedB.eq]
    exact (colsK_transpose ON.colsBK).2
  have hR : rowsB () = rowsV (at0 RB) := by
    unfold rowsB
    rw [ONSeedB.eq]
    exact rowsOf_eq ON.colsBK rowsBK
  have hl : RB.length = 154 ∧ ∀ j < 154, RB.getD j 0 = at0 RB j := by
    refine ⟨?_, fun _ _ => rfl⟩
    have h := lensK
    simp only [bAnd_iff] at h
    exact Nat.eq_of_beq_eq_true h.2.2.2.1
  rw [hT, mul_rowsV cm_list cm_canon rfl (D := fun i => mv CM (ONV.CB i)) fun _ _ => rfl, hR,
    mul_rowsV hl (tposK_spec rowsBK).2.1 rfl (D := at0 CM) fun i hi =>
      Nat.eq_of_beq_eq_true (allN_spec formBK i hi)]

theorem form_ok : formOK (rowsOf 154 CFSG.ONSchreier.Data.formPayload)
    (invV 154 (rowsOf 154 CFSG.ONSchreier.Data.formPayload)) = true := by
  have hT : transpose 154 (rowsV (at0 CM)) = rowsV (at0 CM) := transpose_rowsV symK
  rw [form_eq, invV_eq]
  unfold formOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨by rw [hT]; exact eqM_self (rowsV_size _), rowsV_size _⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · unfold wfM
    rw [Array.all_eq_true]
    intro i hi
    have hi' : i < 154 := by rwa [rowsV_size] at hi
    have e := rowsV_get (R := at0 XI) hi'
    rw [getElem!_pos _ i hi] at e
    rw [e]
    exact CFSG.KS.ONLin.wf_vOf (xi_canon i hi')
  · rw [xm_eq]
    exact eqM_self idM_size
  · rw [formA_eq]
    exact eqM_self (rowsV_size _)
  · rw [formB_eq]
    exact eqM_self (rowsV_size _)

theorem toV_wOfK {X : Nat} (h : canon X = true) : (wOfK X).toV = vOf X := by
  obtain ⟨-, hp, hm⟩ := canon_bits h
  have hp' : (vOf X).p < 2 ^ 256 :=
    lt_of_lt_of_le hp (Nat.pow_le_pow_right (by norm_num) (by norm_num))
  have hm' : (vOf X).m < 2 ^ 256 :=
    lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (by norm_num))
  exact W.toV_ofV hp' hm'

theorem toVM_eq : toVM (spanRows (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits))
    CFSG.ONSchreier.Data.spanIdx) = rowsV (at0 ON.SKL) := by
  refine arr_ext' (by unfold toVM; rw [Array.size_map, hSR.1]) (rowsV_size _) fun t ht => ?_
  rw [rowsV_get ht]
  unfold toVM
  rw [getElem!_map' (by rw [hSR.1]; exact ht), spanRows_get ht]
  exact toV_wOfK (skl_canon t ht)

theorem gram_eq : gram (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits))
    CFSG.ONSchreier.Data.spanIdx (rowsOf 154 CFSG.ONSchreier.Data.formPayload) = gramV := by
  have hcu : CU.length = 154 ∧ ∀ j < 154, CU.getD j 0 = at0 CU j := by
    refine ⟨?_, fun _ _ => rfl⟩
    have h := lensK
    simp only [bAnd_iff] at h
    exact Nat.eq_of_beq_eq_true h.2.2.2.2.1
  unfold gram
  dsimp only
  rw [toVM_eq, form_eq, mul_rowsV cm_list cm_canon rfl (D := fun t => mv CM (at0 ON.SKL t))
    fun _ _ => rfl, transpose_rowsV cuK, mul_rowsV hcu (tposK_spec cuK).2.1 rfl (D := at0 GR)
    fun i hi => (imgK_spec gramK i hi).2]
  rfl

theorem gram_ok : gramConnOK (gram (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits))
      CFSG.ONSchreier.Data.spanIdx (rowsOf 154 CFSG.ONSchreier.Data.formPayload))
    (gramTree (gram (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits))
      CFSG.ONSchreier.Data.spanIdx (rowsOf 154 CFSG.ONSchreier.Data.formPayload))).1
    (gramTree (gram (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits))
      CFSG.ONSchreier.Data.spanIdx (rowsOf 154 CFSG.ONSchreier.Data.formPayload))).2 = true := by
  rw [gram_eq]
  exact gramConnK

end CertificateChecks.KernelSpor.ONVec

end
