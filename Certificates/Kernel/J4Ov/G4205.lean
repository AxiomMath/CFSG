
module

public import Certificates.Kernel.J4Ov.C4205
public import Certificates.Kernel.J4Ov.Enc4204
public import CFSG.Certificates.Kernel.J4Q.LettersAZ
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4OvGenEBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Ov

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KD.J4Ov CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native
  CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2 CertificateChecks.KernelJ4Q CFSG.Quasithin.J4Ov

theorem eMats_enc4205 {ℓ : Nat} (h1 : 1 ≤ ℓ) (h7 : ℓ < 7) :
    ∀ k, WfA ((eMats ℓ)[k]?.getD (idRows ())) ∧
      encR ((eMats ℓ)[k]?.getD (idRows ())) = getN one (List.append Us (conj4205 ℓ)) k := by
  obtain ⟨hkR, huR, -⟩ := kR_enc4204 h1 h7
  exact cat_enc4204 (by rw [uBasis, uTab_size]; rfl) us_enc4204 (conjMap_enc4204 huR hkR)

theorem ew_decode4205 {t : Nat} (ht : t < 12) :
    decodeWord (CFSG.Quasithin.J4Ov.eData.getD t ("", 0)).1 = ew4205.getD t [] := by
  have e : (CFSG.Quasithin.J4Ov.eData.getD t ("", 0)).1 =
      (CFSG.Quasithin.J4Ov.eData.map Prod.fst).getD t "" :=
    (List.getD_map (l := CFSG.Quasithin.J4Ov.eData) (n := t) (d := ("", 0)) Prod.fst).symm
  rw [e, eData_strs4205]
  interval_cases t <;> exact decodeWord_ofList _

theorem eOK4205 {ℓ i : Nat} (h1 : 1 ≤ ℓ) (h4 : ℓ ≤ 4) (hi : i < 3) : eOK ℓ i = true := by
  have ht : 3 * (ℓ - 1) + i < 12 := by omega
  have h := ch4205.all _ ht
  have e1 : Nat.succ (Nat.div (3 * (ℓ - 1) + i) 3) = ℓ := by
    change (3 * (ℓ - 1) + i) / 3 + 1 = ℓ
    omega
  have e2 : Nat.mod (3 * (ℓ - 1) + i) 3 = i := by
    change (3 * (ℓ - 1) + i) % 3 = i
    omega
  unfold ch4205K at h
  rw [e1, e2, ← ew_decode4205 ht] at h
  unfold eChk4205 em4205 at h
  rw [andB_eq, Bool.and_eq_true] at h
  obtain ⟨hc, heq⟩ := h
  have hm := eMats_enc4205 h1 (by omega)
  have hw := enc_wordRows hK hm hm (decodeWord (CFSG.Quasithin.J4Ov.eData.getD (3 * (ℓ - 1) + i) ("", 0)).1)
  unfold eOK
  rw [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨Nat.le_of_ble_eq_true hc,
    (eqRows_of (mul_enc hK hw (loc_invs i)) (eta_enc _)).trans heq⟩

theorem move4205 {ℓ : Nat} (h1 : 1 ≤ ℓ) (h4 : ℓ ≤ 4) : ∃ j < 11,
    differs (frApply (frTable (conjBy (uR ℓ) ((uTab (locMats ()) (locInvs ()))[j]?.getD (idRows ()))
      (kR ℓ))) rootV) rootV = true := by
  have h := allR_spec mv4205_ok (ℓ - 1) (by omega)
  rw [andB_eq, Bool.and_eq_true] at h
  obtain ⟨hj, hmv⟩ := h
  have e : Nat.succ (ℓ - 1) = ℓ := by omega
  rw [e] at hmv
  refine ⟨getN 0 mvJ4205 (ℓ - 1), Nat.le_of_ble_eq_true hj, ?_⟩
  obtain ⟨hkR, huR, -⟩ := kR_enc4204 h1 (by omega)
  have hu := uTab_enc _ (Nat.le_of_ble_eq_true hj)
  have hr : rootV.wf = true := by decide
  rw [conjBy, vec_mulRows (wf_mulRows huR.1 hu.1) hkR.1 hr, vec_mulRows huR.1 hu.1 hr,
    differs_eq (wf_frApply hkR.1 _) hr, v2N_frApply hK hkR.1 (wf_frApply hu.1 _),
    v2N_frApply hK hu.1 (wf_frApply huR.1 _), v2N_frApply hK huR.1 hr, hkR.2, hu.2, huR.2]
  exact hmv

theorem genE4205 (hM : MatFacts) {ℓ : Nat} (h1 : 1 ≤ ℓ)
    (h4 : ℓ ≤ 4) :
    Hj ≤ Eg uJ 11 ⊔ (Eg uJ 11).map (MulAut.conj (uEl ℓ)).toMonoidHom ∧
      ∃ j < 11, uEl ℓ * uJ j * (uEl ℓ)⁻¹ ∉ Hj := by
  have hℓ : ℓ < 7 := by omega
  obtain ⟨-, -, hinv⟩ := kR_enc4204 h1 hℓ
  refine ⟨?_, ?_⟩
  · have hgs : ∀ m, eGs ℓ m ∈ Eg uJ 11 ⊔ (Eg uJ 11).map (MulAut.conj (uEl ℓ)).toMonoidHom := by
      intro m
      unfold eGs
      split_ifs with h1' h2'
      · exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨m, h1', rfl⟩)
      · exact Subgroup.mem_sup_right (Subgroup.mem_map.2
          ⟨uJ (m - 11), Subgroup.subset_closure ⟨m - 11, by omega, rfl⟩, rfl⟩)
      · exact Subgroup.one_mem _
    rw [Subgroup.closure_le]
    intro x hx
    have hx' : ∃ i < 3, x = xJ i := by
      rcases hx with h | h | h
      · exact ⟨0, by norm_num, h⟩
      · exact ⟨1, by norm_num, h⟩
      · exact ⟨2, by norm_num, h⟩
    obtain ⟨i, hi, rfl⟩ := hx'
    obtain ⟨c, -, hW⟩ := eOK_spec hM hℓ hinv (eOK4205 h1 h4 hi)
    have hWD := wordProd_mem _ hgs (decodeWord (eData.getD (3 * (ℓ - 1) + i) ("", 0)).1)
    have e : xJ i = (eta uJ 11 c)⁻¹ *
        wordProd (eGs ℓ) (decodeWord (eData.getD (3 * (ℓ - 1) + i) ("", 0)).1) := by
      rw [← hW]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _
      (Subgroup.mem_sup_left (eta_mem_Eg 11 le_rfl c))) hWD
  · obtain ⟨j, hj, hd⟩ := move4205 h1 h4
    refine ⟨j, hj, fun hmem => ?_⟩
    have hmx : Mx (uEl ℓ * uJ j * (uEl ℓ)⁻¹) = rowsMatrix (conjBy (uR ℓ)
        ((uTab (locMats ()) (locInvs ()))[j]?.getD (idRows ())) (kR ℓ)) := by
      rw [conjBy, rowsMatrix_mulRows, rowsMatrix_mulRows, map_mul, map_mul, Mx_uEl hM hℓ hinv,
        Mx_uEl_inv hM hℓ, Mx_uJ hM hj]
    exact not_mem_Hj_of_rows_move hM hmx hd hmem

end CertificateChecks.KernelJ4Ov

end
