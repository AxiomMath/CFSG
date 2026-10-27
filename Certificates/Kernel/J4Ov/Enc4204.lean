module

public import Certificates.Kernel.J4Q.LocM
public import Certificates.Data.J4Ov.Fam
public import CFSG.Sporadic.J4.QTProof

public section

namespace CertificateChecks.KernelJ4Ov

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2
  CertificateChecks.KernelJ4Q CFSG.Quasithin.J4Ov

theorem getN_getD4204 (d : Nat) : ∀ (l : List Nat) (k : Nat), getN d l k = l.getD k d
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, k + 1 => getN_getD4204 d l k

theorem getN_ge4204 {d : Nat} {l : List Nat} {k : Nat} (h : l.length ≤ k) : getN d l k = d := by
  rw [getN_getD4204, List.getD_eq_default _ _ h]

theorem getN_map4204 {d : Nat} (f : Nat → Nat) {l : List Nat} {k : Nat} (h : k < l.length) :
    getN d (l.map f) k = f (getN d l k) := by
  rw [getN_getD4204, getN_getD4204, List.getD_eq_getElem _ _ (by simpa using h),
    List.getD_eq_getElem _ _ h, List.getElem_map]

theorem cat_enc4204 {A B : Array (Array V2)} {as bs : List Nat} (hs : A.size = as.length)
    (ha : ∀ k, WfA (A[k]?.getD (idRows ())) ∧ encR (A[k]?.getD (idRows ())) = getN one as k)
    (hb : ∀ k, WfA (B[k]?.getD (idRows ())) ∧ encR (B[k]?.getD (idRows ())) = getN one bs k) :
    ∀ k, WfA ((A ++ B)[k]?.getD (idRows ())) ∧
      encR ((A ++ B)[k]?.getD (idRows ())) = getN one (as ++ bs) k := by
  intro k
  rw [getN_append]
  by_cases h : k < A.size
  · rw [Array.getElem?_append_left h, if_pos (hs ▸ h)]
    exact ha k
  · rw [Array.getElem?_append_right (by omega), if_neg (hs ▸ h), hs]
    exact hb _

theorem one_enc4204 {X : Array V2} {x : Nat} (h : WfA X ∧ encR X = x) :
    ∀ k, WfA ((#[X] : Array (Array V2))[k]?.getD (idRows ())) ∧
      encR ((#[X] : Array (Array V2))[k]?.getD (idRows ())) = getN one [x] k
  | 0 => h
  | k + 1 => by
    have e : (#[X] : Array (Array V2))[k + 1]? = none := by simp
    rw [e, Option.getD_none]
    exact id_enc hK

theorem us_enc4204 : ∀ k, WfA ((uTab (locMats ()) (locInvs ()))[k]?.getD (idRows ())) ∧
    encR ((uTab (locMats ()) (locInvs ()))[k]?.getD (idRows ())) = getN one Us k := by
  intro k
  by_cases h : k < 11
  · exact uTab_enc k h
  · have e : (uTab (locMats ()) (locInvs ()))[k]? = none := by
      rw [Array.getElem?_eq_none_iff, uTab_size]
      omega
    rw [e, Option.getD_none, getN_ge4204 (by rw [Us_length]; omega)]
    exact id_enc hK

theorem conjMap_enc4204 {L R : Array V2} {l r : Nat} (hL : WfA L ∧ encR L = l)
    (hR : WfA R ∧ encR R = r) :
    ∀ k, WfA (((uTab (locMats ()) (locInvs ())).map fun U => conjBy L U R)[k]?.getD (idRows ())) ∧
      encR (((uTab (locMats ()) (locInvs ())).map fun U => conjBy L U R)[k]?.getD (idRows ())) =
        getN one (smapK (fun U => mulJ c rm (mulJ c rm l U) r) Us) k := by
  intro k
  rw [smapK_eq]
  by_cases h : k < 11
  · have hlt : k < (uTab (locMats ()) (locInvs ())).size := by rw [uTab_size]; exact h
    rw [Array.getElem?_map, Array.getElem?_eq_getElem hlt, Option.map_some, Option.getD_some,
      getN_map4204 _ (by rw [Us_length]; exact h)]
    have hu := uTab_enc k h
    rw [Array.getElem?_eq_getElem hlt, Option.getD_some] at hu
    exact mul_enc hK (mul_enc hK hL hu) hR
  · have e : ((uTab (locMats ()) (locInvs ())).map fun U => conjBy L U R)[k]? = none := by
      rw [Array.getElem?_eq_none_iff, Array.size_map, uTab_size]
      omega
    rw [e, Option.getD_none, getN_ge4204 (by rw [List.length_map, Us_length]; omega)]
    exact id_enc hK

theorem kR_enc4204 {ℓ : Nat} (h1 : 1 ≤ ℓ) (h7 : ℓ < 7) :
    (WfA (kR ℓ) ∧ encR (kR ℓ) = getN one MLs (ℓ - 1)) ∧
    (WfA (uR ℓ) ∧ encR (uR ℓ) = getN one MLIs (ℓ - 1)) ∧
    eqRows (mulRows (kR ℓ) (uR ℓ)) (idRows ()) = true := by
  have e : 1 + 1 * (ℓ - 1) = ℓ := by omega
  have hM := pathM_enc (i := ℓ - 1) (by omega)
  have hMi := pathMi_enc (i := ℓ - 1) (by omega)
  rw [e] at hM hMi
  refine ⟨hM, ⟨hMi.1, hMi.2.1⟩, ?_⟩
  exact (eqRows_of (mul_enc hK hM ⟨hMi.1, hMi.2.1⟩) (id_enc hK)).trans hMi.2.2

end CertificateChecks.KernelJ4Ov

end
