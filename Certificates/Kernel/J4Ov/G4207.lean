module

public import Certificates.Kernel.J4Ov.C4207
public import Certificates.Kernel.J4Ov.Enc4204
public import Certificates.Kernel.J4Q.C4025
public import CFSG.Certificates.Kernel.J4Q.LettersAZ
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4OvGenPFam

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Ov

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KD.J4Ov CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native
  CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2 CertificateChecks.KernelJ4Q CFSG.Quasithin.J4Ov

theorem orB_eq4207 (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem rep_l4207 : ∀ i < 49, (repData.getD i ⟨0, "", true, 0⟩).exc = false →
    1 ≤ (repData.getD i ⟨0, "", true, 0⟩).l ∧ (repData.getD i ⟨0, "", true, 0⟩).l < 7 := by
  decide

theorem rep_l4207' {i : Nat} (h : (repData.getD i ⟨0, "", true, 0⟩).exc = false) :
    1 ≤ (repData.getD i ⟨0, "", true, 0⟩).l ∧ (repData.getD i ⟨0, "", true, 0⟩).l < 7 := by
  by_cases hi : i < 49
  · exact rep_l4207 i hi h
  · rw [List.getD_eq_default _ _ (by rw [show repData.length = 49 from rfl]; omega)] at h
    exact absurd h (by decide)

theorem decode_map4207 : ∀ (L : List (List Char)) (i : Nat),
    decodeWord ((L.map String.ofList).getD i "") = (L.map lettersAZ).getD i []
  | [], _ => rfl
  | cs :: _, 0 => decodeWord_ofList cs
  | _ :: L, i + 1 => decode_map4207 L i

theorem rx_decode4207 (i : Nat) :
    decodeWord (repData.getD i ⟨0, "", true, 0⟩).xw = rx4207.getD i [] := by
  have e : (repData.getD i ⟨0, "", true, 0⟩).xw = (repData.map RepEntry.xw).getD i "" :=
    (List.getD_map (l := repData) (n := i) (d := ⟨0, "", true, 0⟩) RepEntry.xw).symm
  rw [e, repData_strs4207]
  exact decode_map4207 [R4207.s43, R4207.s44, R4207.s45, R4207.s46, R4207.s47, R4207.s48,
    R4207.s37, R4207.s38, R4207.s39, R4207.s40, R4207.s41, R4207.s42, R4207.s31, R4207.s32,
    R4207.s33, R4207.s34, R4207.s35, R4207.s36, R4207.s25, R4207.s26, R4207.s27, R4207.s28,
    R4207.s29, R4207.s30, R4207.s19, R4207.s20, R4207.s21, R4207.s22, R4207.s23, R4207.s24,
    R4207.s13, R4207.s14, R4207.s15, R4207.s16, R4207.s17, R4207.s18, R4207.s7, R4207.s8,
    R4207.s9, R4207.s10, R4207.s11, R4207.s12, R4207.s0, R4207.s1, R4207.s2, R4207.s3,
    R4207.s4, R4207.s5, R4207.s6] i

theorem pw_decode4207 (t : Nat) :
    decodeWord (pData.getD t ⟨0, "", 0, 0⟩).w = pw4207.getD t [] := by
  have e : (pData.getD t ⟨0, "", 0, 0⟩).w = (pData.map PEntry.w).getD t "" :=
    (List.getD_map (l := pData) (n := t) (d := ⟨0, "", 0, 0⟩) PEntry.w).symm
  rw [e, pData_strs4207]
  exact decode_map4207 [P4207.s39, P4207.s40, P4207.s41, P4207.s42, P4207.s43, P4207.s33,
    P4207.s34, P4207.s35, P4207.s36, P4207.s37, P4207.s38, P4207.s28, P4207.s29, P4207.s30,
    P4207.s31, P4207.s32, P4207.s22, P4207.s23, P4207.s24, P4207.s25, P4207.s26, P4207.s27,
    P4207.s17, P4207.s18, P4207.s19, P4207.s20, P4207.s21, P4207.s11, P4207.s12, P4207.s13,
    P4207.s14, P4207.s15, P4207.s16, P4207.s6, P4207.s7, P4207.s8, P4207.s9, P4207.s10,
    P4207.s0, P4207.s1, P4207.s2, P4207.s3, P4207.s4, P4207.s5] t

theorem kT_enc4207 : ∀ k, WfA (kT[k]?.getD (idRows ())) ∧
    encR (kT[k]?.getD (idRows ())) = getN one km4207 k := by
  intro k
  by_cases h : k < 4
  · rw [show kT = kRowsTab () from rfl, kTab_get h]
    exact kRows_enc h
  · have e : kT[k]? = none := by
      rw [Array.getElem?_eq_none_iff, kT_size]
      omega
    rw [e, Option.getD_none, getN_ge4204 (by change 4 ≤ k; omega)]
    exact id_enc hK

theorem kTi_enc4207 : ∀ k, WfA (kTi[k]?.getD (idRows ())) ∧
    encR (kTi[k]?.getD (idRows ())) = getN one [ki4207 0, ki4207 1, ki4207 2, ki4207 3] k := by
  intro k
  by_cases h : k < 4
  · have hk := allR_spec kinv4207_ok k h
    rw [andB_eq, Bool.and_eq_true] at hk
    have hlt : k < kT.size := by rw [kT_size]; exact h
    rw [kTi, Array.getElem?_map, Array.getElem?_eq_getElem hlt, Option.map_some, Option.getD_some]
    have hr := kRows_enc h
    have e1 : kT[k] = kRows k := by
      have := kTab_get h
      rw [Array.getElem?_eq_getElem (by rw [← show kT = kRowsTab () from rfl]; exact hlt),
        Option.getD_some] at this
      exact this
    rw [e1]
    have e2 : getN one [ki4207 0, ki4207 1, ki4207 2, ki4207 3] k = ki4207 k := by
      interval_cases k <;> rfl
    rw [e2]
    exact invRows_enc hK hr.1 hk.1 (by rw [hr.2]; exact hk.2)
  · have e : kTi[k]? = none := by
      rw [Array.getElem?_eq_none_iff, kTi_size]
      omega
    rw [e, Option.getD_none, getN_ge4204 (by change 4 ≤ k; omega)]
    exact id_enc hK

theorem wfA_mem4207 {X : Array V2} (h : WfA X) : ∀ x ∈ X, x.wf = true := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hx
  exact Array.all_eq_true.1 h.2 i hi

section Grp

variable (hM : MatFacts)
include hM

theorem not_mem_Eg4207 {s : J} {R : Array V2} (hs : Mx s = rowsMatrix R) {p c : Nat}
    (hp : p = 11 ∨ p = 23) (hpow : s ^ p = eta uJ 11 c)
    (hne : rowsMatrix R ≠ rowsMatrix (etaRows (uTab (locMats ()) (locInvs ())) 11 c)) :
    s ∉ Eg uJ 11 := by
  intro hmem
  obtain ⟨c', -, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 hmem
  have hsq := eta_sq (elem_uJ hM) c'
  obtain ⟨k, rfl⟩ : ∃ k, p = 2 * k + 1 := by
    rcases hp with rfl | rfl
    · exact ⟨5, rfl⟩
    · exact ⟨11, rfl⟩
  rw [pow_succ, pow_mul, sq, hsq, one_pow, one_mul] at hpow
  apply hne
  rw [← hs, hpow, Mx_eta hM 11 le_rfl]

end Grp

@[expose] noncomputable def cv4207 (i : Nat) : List Nat :=
  smapK (fun U => mulJ c rm (mulJ c rm (zi4207 i) U) (z4207 i)) Us

theorem entry4207 (hF : J4Facts) {i : Nat} {w : String}
    {wk : List Int} {p m : Nat} (hw : decodeWord w = wk) (h : pChk4207 i wk p m = true) :
    (rep4207 i).exc = false ∧
    (∃ s ∈ P0 ⊔ (Eg uJ 11).map (MulAut.conj (zEl (rep4207 i))⁻¹).toMonoidHom,
      s ∈ Hj ∧ s ∉ Eg uJ 11 ∧ ∃ p, (p = 11 ∨ p = 23) ∧ s ^ p ∈ Eg uJ 11) ∧
    ∃ j < 11, (zEl (rep4207 i))⁻¹ * uJ j * zEl (rep4207 i) ∉ Hj := by
  have hM := hF.mat
  unfold pChk4207 pFacts4207 at h
  simp only [andB_eq, orB_eq4207, Bool.and_eq_true, Bool.or_eq_true, strictB_eq, notB_eq,
    Bool.not_eq_true'] at h
  obtain ⟨hexc, hZZi, hcan, hfix, hp, -, hpow, hne, hmove⟩ := h
  have hl := rep_l4207' hexc
  have hkR := (kR_enc4204 hl.1 hl.2).1
  obtain ⟨hXw, hXe⟩ := enc_wordRows hK loc_gens loc_invs (decodeWord (rep4207 i).xw)
  have hXe' : encR (wordRows (locMats ()) (locInvs ()) (decodeWord (rep4207 i).xw)) =
      wordJ c rm one [L0, L1, L2] [L0i, L1i, L2i] (rx4207.getD i []) := by
    rw [hXe]
    exact congrArg _ (rx_decode4207 i)
  have hZ : WfA (repZ (rep4207 i)) ∧ encR (repZ (rep4207 i)) = z4207 i :=
    mul_enc hK hkR ⟨hXw, hXe'⟩
  have hZi : WfA (invRows (repZ (rep4207 i))) ∧ encR (invRows (repZ (rep4207 i))) = zi4207 i :=
    invRows_enc hK hZ.1 hcan (by rw [hZ.2]; exact hZZi)
  have hA : uBasis.size = 11 := by rw [uBasis, uTab_size]
  have hm : ∀ k, WfA ((uBasis ++ kT ++ pConj (invRows (repZ (rep4207 i))) (repZ (rep4207 i)))[k]?.getD
        (idRows ())) ∧
      encR ((uBasis ++ kT ++ pConj (invRows (repZ (rep4207 i))) (repZ (rep4207 i)))[k]?.getD
        (idRows ())) = getN one (Us ++ km4207 ++ cv4207 i) k :=
    cat_enc4204 (by rw [Array.size_append, hA, kT_size]; rfl)
      (cat_enc4204 (by rw [hA]; rfl) us_enc4204 kT_enc4207) (conjMap_enc4204 hZi hZ)
  have hi : ∀ k, WfA ((uBasis ++ kTi ++ pConj (invRows (repZ (rep4207 i))) (repZ (rep4207 i)))[k]?.getD
        (idRows ())) ∧
      encR ((uBasis ++ kTi ++ pConj (invRows (repZ (rep4207 i))) (repZ (rep4207 i)))[k]?.getD
        (idRows ())) = getN one (Us ++ [ki4207 0, ki4207 1, ki4207 2, ki4207 3] ++ cv4207 i) k :=
    cat_enc4204 (by rw [Array.size_append, hA, kTi_size]; rfl)
      (cat_enc4204 (by rw [hA]; rfl) us_enc4204 kTi_enc4207) (conjMap_enc4204 hZi hZ)
  obtain ⟨hWw, hWe⟩ := enc_wordRows hK hm hi (decodeWord w)
  have hWe' : encR (wordRows (uBasis ++ kT ++ pConj (invRows (repZ (rep4207 i))) (repZ (rep4207 i)))
      (uBasis ++ kTi ++ pConj (invRows (repZ (rep4207 i))) (repZ (rep4207 i))) (decodeWord w)) =
      wordJ c rm one (List.append Us (List.append km4207 (cv4207 i)))
        (List.append Us (List.append [ki4207 0, ki4207 1, ki4207 2, ki4207 3] (cv4207 i))) wk := by
    rw [hWe, hw, List.append_assoc, List.append_assoc]
    rfl
  have hr : rootV.wf = true := by decide
  have hz : eqRows (mulRows (repZ (rep4207 i)) (invRows (repZ (rep4207 i)))) (idRows ()) = true :=
    (eqRows_of (mul_enc hK hZ hZi) (id_enc hK)).trans hZZi
  have hk : ∀ k < 4, eqRows (mulRows ((kRowsTab ())[k]?.getD (idRows ())) (kTi[k]?.getD (idRows ())))
      (idRows ()) = true := by
    intro k hk4
    have hk' := allR_spec kinv4207_ok k hk4
    rw [andB_eq, Bool.and_eq_true] at hk'
    have e2 : getN one [ki4207 0, ki4207 1, ki4207 2, ki4207 3] k = ki4207 k := by
      interval_cases k <;> rfl
    refine (eqRows_of (mul_enc hK (kT_enc4207 k) (kTi_enc4207 k)) (id_enc hK)).trans ?_
    rw [e2]
    exact hk'.2
  have hfam := pFam hM hl.2 hz hk
  have hMx : Mx (wordProd (pGs (rep4207 i)) (decodeWord w)) = rowsMatrix (wordRows
      (uBasis ++ kT ++ pConj (invRows (repZ (rep4207 i))) (repZ (rep4207 i)))
      (uBasis ++ kTi ++ pConj (invRows (repZ (rep4207 i))) (repZ (rep4207 i))) (decodeWord w)) :=
    hfam.mx_wordProd (decodeWord w)
  have hfixB : (frApply (frTable (wordRows (uBasis ++ kT ++ pConj (invRows (repZ (rep4207 i)))
      (repZ (rep4207 i))) (uBasis ++ kTi ++ pConj (invRows (repZ (rep4207 i))) (repZ (rep4207 i)))
      (decodeWord w))) rootV).beq rootV = true := by
    rw [beq_v2N, v2N_frApply hK hWw hr, hWe']
    exact hfix
  have hpowR := (eqRows_of (pow_enc hK ⟨hWw, hWe'⟩ p) (eta_enc m)).trans hpow
  have hspow : wordProd (pGs (rep4207 i)) (decodeWord w) ^ p = eta uJ 11 m := by
    apply Mx_injective
    rw [map_pow, hMx, ← rowsMatrix_powRows, rowsMatrix_eq_of_eqRows hpowR, Mx_eta hM 11 le_rfl]
  have hp' : p = 11 ∨ p = 23 := by
    rcases hp with h | h
    · exact Or.inl (Nat.eq_of_beq_eq_true h)
    · exact Or.inr (Nat.eq_of_beq_eq_true h)
  have hneR : rowsMatrix (wordRows (uBasis ++ kT ++ pConj (invRows (repZ (rep4207 i)))
      (repZ (rep4207 i))) (uBasis ++ kTi ++ pConj (invRows (repZ (rep4207 i))) (repZ (rep4207 i)))
      (decodeWord w)) ≠ rowsMatrix (etaRows (uTab (locMats ()) (locInvs ())) 11 m) := by
    have hne' : Nat.beq (wordJ c rm one (List.append Us (List.append km4207 (cv4207 i)))
        (List.append Us (List.append [ki4207 0, ki4207 1, ki4207 2, ki4207 3] (cv4207 i))) wk)
        (etaK c rm one Us m) = false := by
      unfold neN at hne
      rw [notB_eq, Bool.not_eq_true'] at hne
      exact hne
    exact rowsMatrix_ne_of_eqRows_false hWw.1 (eta_enc m).1.1 (wfA_mem4207 hWw)
      (wfA_mem4207 (eta_enc m).1) ((eqRows_of ⟨hWw, hWe'⟩ (eta_enc m)).trans hne')
  rw [allR_eq, List.all_eq_false] at hmove
  obtain ⟨j, hj, hjf⟩ := hmove
  have hj' : j < 11 := List.mem_range.1 hj
  have hCj := conjMap_enc4204 hZi hZ j
  have e3 : ((uTab (locMats ()) (locInvs ())).map fun U =>
      conjBy (invRows (repZ (rep4207 i))) U (repZ (rep4207 i)))[j]? =
      some (conjBy (invRows (repZ (rep4207 i))) ((uTab (locMats ()) (locInvs ()))[j]?.getD
        (idRows ())) (repZ (rep4207 i))) := pConj_get _ _ hj'
  rw [e3, Option.getD_some] at hCj
  have hdiff : differs (frApply (frTable (conjBy (invRows (repZ (rep4207 i)))
      ((uTab (locMats ()) (locInvs ()))[j]?.getD (idRows ())) (repZ (rep4207 i)))) rootV)
      rootV = true := by
    rw [differs_eq (wf_frApply hCj.1 _) hr, v2N_frApply hK hCj.1 hr, hCj.2]
    unfold neN
    rw [notB_eq, Bool.not_eq_true']
    exact Bool.eq_false_iff.2 hjf
  refine ⟨hexc, ⟨wordProd (pGs (rep4207 i)) (decodeWord w), ?_, mem_Hj_of_rows_fix hF hMx hfixB,
    not_mem_Eg4207 hM hMx hp' hspow hneR, p, hp', ?_⟩, j, hj', ?_⟩
  · refine wordProd_mem _ (fun k => ?_) _
    unfold pGs
    split_ifs with h1 h2 h3
    · exact Subgroup.mem_sup_left (Eg_le_P0 (Subgroup.subset_closure ⟨k, h1, rfl⟩))
    · exact Subgroup.mem_sup_left (kJ_mem_P0 (by omega))
    · refine Subgroup.mem_sup_right (Subgroup.mem_map.2
        ⟨uJ (k - 15), Subgroup.subset_closure ⟨k - 15, by omega, rfl⟩, ?_⟩)
      simp [MulAut.conj_apply]
    · exact Subgroup.one_mem _
  · rw [hspow]
    exact eta_mem_Eg 11 le_rfl m
  · intro hmem
    have hZmx : Mx (zEl (rep4207 i)) = rowsMatrix (repZ (rep4207 i)) := Mx_zEl hM hl.2
    have hZimx : Mx (zEl (rep4207 i))⁻¹ = rowsMatrix (invRows (repZ (rep4207 i))) :=
      Mx_inv_of_rows hZmx hz
    have hmx : Mx ((zEl (rep4207 i))⁻¹ * uJ j * zEl (rep4207 i)) =
        rowsMatrix (conjBy (invRows (repZ (rep4207 i)))
          ((uTab (locMats ()) (locInvs ()))[j]?.getD (idRows ())) (repZ (rep4207 i))) := by
      rw [conjBy, rowsMatrix_mulRows, rowsMatrix_mulRows, map_mul, map_mul, hZimx, hZmx,
        Mx_uJ hM hj']
    exact not_mem_Hj_of_rows_move hM hmx hdiff hmem

theorem genP4207 (hF : J4Facts) {i : Nat} (hi : i < 49)
    (hexc : (repData.getD i ⟨0, "", true, 0⟩).exc = false) :
    (∃ s ∈ P0 ⊔ (Eg uJ 11).map
        (MulAut.conj (zEl (repData.getD i ⟨0, "", true, 0⟩))⁻¹).toMonoidHom,
      s ∈ Hj ∧ s ∉ Eg uJ 11 ∧ ∃ p, (p = 11 ∨ p = 23) ∧ s ^ p ∈ Eg uJ 11) ∧
    ∃ j < 11, (zEl (repData.getD i ⟨0, "", true, 0⟩))⁻¹ * uJ j *
      zEl (repData.getD i ⟨0, "", true, 0⟩) ∉ Hj := by
  have hc := cover4207_ok
  rw [andB_eq, Bool.and_eq_true] at hc
  obtain ⟨hlen, hall⟩ := hc
  have h := allR_spec hall i hi
  rw [orB_eq4207, Bool.or_eq_true] at h
  rcases h with h | h
  · exact absurd (hexc.symm.trans h) (by decide)
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hei⟩ := h
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem he
    have hlen' : pData.length = 44 := Nat.eq_of_beq_eq_true hlen
    have ht44 : t < 44 := by omega
    have hent := entry4207 hF (i := (pData.getD t ⟨0, "", 0, 0⟩).idx)
      (p := (pData.getD t ⟨0, "", 0, 0⟩).p) (m := (pData.getD t ⟨0, "", 0, 0⟩).c)
      (pw_decode4207 t) (ch4207.all t ht44)
    have e1 : (pData.getD t ⟨0, "", 0, 0⟩).idx = i := by
      rw [List.getD_eq_getElem _ _ ht]
      exact Nat.eq_of_beq_eq_true hei
    rw [e1] at hent
    exact hent.2

end CertificateChecks.KernelJ4Ov

end
