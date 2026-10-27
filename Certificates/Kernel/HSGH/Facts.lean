module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitGHCertElems
public import CFSG.Certificates.Kernel.TabMatGrpSound
import Certificates.Kernel.HSGH.Check
import Certificates.Kernel.HSMult.TabK

public section

namespace CertificateChecks.KernelHSGH

open CFSG.KC.TabMatGrp CFSG.ComponentClassification.HSFLit.GHCert CFSG.Sporadic.SmallF2
  CFSG.Sporadic.Th CFSG.Certificates CFSG.KC.VecK CFSG.Sporadic.SmallF2.Native
open CFSG.Sporadic.HS.Native (hsData)

private theorem andB_eq' (a b : Bool) : CFSG.KLie.CT.andB a b = (a && b) := by
  cases a <;> rfl

private theorem seeds_bind :
    CFSG.KC.M1F2.m1Bind KernelVec.HS.csA 20 KernelVec.HS.MA = true ∧
      CFSG.KC.M1F2.m1Bind KernelVec.HS.csB 20 KernelVec.HS.MB = true := by
  have h := CertificateChecks.KernelHSMult.hseed
  unfold seedK at h
  simp only [andB_eq', Bool.and_eq_true] at h
  exact ⟨h.2.2.2.2.1, h.2.2.2.2.2.1⟩

private theorem MatP_MA : MatP 20 KernelVec.HS.MA = mA hsData := by
  unfold MatP
  rw [← CFSG.KC.Co1F2.bind_sound seeds_bind.1, ← KernelVec.HS.hA]
  exact rowsMatrix_rowsOfPayload _ _

private theorem MatP_MB : MatP 20 KernelVec.HS.MB = mB hsData := by
  unfold MatP
  rw [← CFSG.KC.Co1F2.bind_sound seeds_bind.2, ← KernelVec.HS.hB]
  exact rowsMatrix_rowsOfPayload _ _

private theorem dets : (mA hsData).det ≠ 0 ∧ (mB hsData).det ≠ 0 := by
  rw [← MatP_MA, ← MatP_MB]
  exact seedsK_det chk

private theorem hA : MatP 20 KernelVec.HS.MA = matOf (J hsData).subtype (![a hsData, b hsData] 0) := by
  rw [show (![a hsData, b hsData] 0 : J hsData) = a hsData from rfl, matOf,
    Subgroup.subtype_apply, a, Subtype.coe_mk, gA, dif_pos dets.1,
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero, MatP_MA]

private theorem hB : MatP 20 KernelVec.HS.MB = matOf (J hsData).subtype (![a hsData, b hsData] 1) := by
  rw [show (![a hsData, b hsData] 1 : J hsData) = b hsData from rfl, matOf,
    Subgroup.subtype_apply, b, Subtype.coe_mk, gB, dif_pos dets.2,
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero, MatP_MB]

private theorem genG_eq : genG hsData = fun z => if z = 1 then a hsData else if z = -1 then
    (a hsData)⁻¹ else if z = 2 then b hsData else (b hsData)⁻¹ := rfl

private theorem getD_segs (i : ℕ) : segs.getD i [] = (abWords.getD i []).map pairLetter := by
  unfold segs
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases abWords[i]? <;> rfl

private theorem ghG_eq (i : ℕ) : ghG i = segVal ![a hsData, b hsData] segs i := by
  unfold ghG segVal
  rw [getD_segs, wordG, genG_eq]
  exact prod_pairLetter _ _ _

theorem rels : ∀ r ∈ ghWordsD, FreeGroup.lift (fun i : Fin 9 => ghG i.val) (FreeGroup.mk r) = 1 := by
  intro r hr
  have h := grpK_sound Subtype.val_injective hA hB segs (by rfl) ps chk (r, [])
    (List.mem_map.2 ⟨r, hr, rfl⟩)
  rw [signedProd_nil, mul_one] at h
  rw [lift_mk_eq_signedProd]
  simpa only [ghG_eq] using h

private theorem mem_nfCodes' {k : ℕ} {c : ℤ} (hc : c ∈ nfCodes k) :
    ∃ i : ℕ, i < 9 ∧ c = (i : ℤ) + 1 := by
  simp only [nfCodes, List.mem_filterMap, List.mem_range] at hc
  obtain ⟨i, hi, h⟩ := hc
  split_ifs at h with hb
  · exact ⟨i, hi, (Option.some.inj h).symm⟩

private theorem prod_codes : ∀ w : List ℤ, (∀ c ∈ w, ∃ i : ℕ, i < 9 ∧ c = (i : ℤ) + 1) →
    wordG gensG9 w =
      signedProd (fun l : Fin 9 => segVal ![a hsData, b hsData] segs l.val) (w.map posLetter)
  | [], _ => rfl
  | c :: w, h => by
    obtain ⟨i, hi, rfl⟩ := h c List.mem_cons_self
    rw [List.map_cons, signedProd_cons, ← prod_codes w fun c hc => h c (List.mem_cons_of_mem _ hc)]
    have e : (((i : ℤ) + 1).toNat - 1) % 9 = i := by omega
    simp only [wordG, List.map_cons, List.prod_cons, posLetter, ↓reduceIte, e]
    congr 1
    rw [← ghG_eq]
    simp [gensG9]

private theorem nfG_eq (k : ℕ) :
    nfG k = signedProd (fun l : Fin 9 => segVal ![a hsData, b hsData] segs l.val) (nfW k) :=
  prod_codes _ fun _ hc => mem_nfCodes' hc

theorem nf_inj : ∀ k < 512, ∀ k' < 512, nfG k = nfG k' → k = k' := by
  intro k hk k' hk' e
  by_contra hne
  have hl : nfs.length = 512 := by simp [nfs]
  have h := distK_sound hA hB segs (by rfl) nfs dst k (by omega) k' (by omega) hne
  simp only [nfs, List.getElem_map, List.getElem_range] at h
  rw [← nfG_eq, ← nfG_eq] at h
  exact h e

end CertificateChecks.KernelHSGH

end
