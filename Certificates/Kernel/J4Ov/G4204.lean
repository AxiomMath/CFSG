
module

public import Certificates.Kernel.J4Ov.C4204
public import Certificates.Kernel.J4Ov.Enc4204
public import CFSG.Certificates.Kernel.J4Q.LettersAZ
public import CFSG.Certificates.Kernel.J4Q.WordVJ
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4OvMaxBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Ov

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KD.J4Ov CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native
  CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2 CertificateChecks.KernelJ4Q CFSG.Quasithin.J4Ov

theorem maxOK_of4204 {ℓ k : Nat} (h1 : 1 ≤ ℓ) (h7 : ℓ < 7) {w : String}
    (h : max4204K ℓ k (decodeWord w) = true) : maxOK ℓ k w = true := by
  obtain ⟨hkR, huR, -⟩ := kR_enc4204 h1 h7
  have hs : (locMats ()).size = 3 := matFacts.locSize
  have hsi : (locInvs ()).size = 3 := by rw [locInvs, Array.size_map]; exact hs
  have hm : ∀ k, WfA ((maxMats ℓ)[k]?.getD (idRows ())) ∧ encR ((maxMats ℓ)[k]?.getD (idRows ())) =
      getN one [L0, L1, L2, getN one MLIs (ℓ - 1)] k :=
    cat_enc4204 (as := [L0, L1, L2]) hs loc_gens (one_enc4204 huR)
  have hi : ∀ k, WfA ((maxInvs ℓ)[k]?.getD (idRows ())) ∧ encR ((maxInvs ℓ)[k]?.getD (idRows ())) =
      getN one [L0i, L1i, L2i, getN one MLs (ℓ - 1)] k :=
    cat_enc4204 (as := [L0i, L1i, L2i]) hsi loc_invs (one_enc4204 hkR)
  obtain ⟨hpw, hpv⟩ := pathVec_enc (repPaths.getD k [])
  have hrv : rV k = pathVec (repPaths.getD k []) := rfl
  unfold maxOK
  rw [hrv, beq_v2N, wordVJ_frApply hK hm hi _ hpw, hpv]
  exact h

theorem mt_decode4204 {ℓ : Nat} (h : ℓ < 7) : decodeWord (maxToTwo.getD ℓ "") = mt4204.getD ℓ [] := by
  rw [maxToTwo_strs4204]
  interval_cases ℓ <;> exact decodeWord_ofList _

theorem mf_decode4204 {k : Nat} (h : k < 7) : decodeWord (maxFromTwo.getD k "") = mf4204.getD k [] := by
  rw [maxFromTwo_strs4204]
  interval_cases k <;> exact decodeWord_ofList _

theorem maxTo4204 (hF : J4Facts) {ℓ : Nat} (hℓ : ℓ < 7) (h0 : ℓ ≠ 0) (h2 : ℓ ≠ 2) :
    uEl 2 ∈ Hj ⊔ Subgroup.zpowers (uEl ℓ) := by
  have hok : maxOK ℓ 2 (maxToTwo.getD ℓ "") = true := by
    apply maxOK_of4204 (by omega) hℓ
    rw [mt_decode4204 hℓ]
    interval_cases ℓ
    · exact absurd rfl h0
    · exact ch4204.t0
    · exact absurd rfl h2
    · exact ch4204.t1
    · exact ch4204.t2
    · exact ch4204.t3
    · exact ch4204.t4
  exact uEl_mem_of_word hF hℓ (by norm_num) (kR_enc4204 (by omega) hℓ).2.2 hok le_sup_left
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

theorem maxFrom4204 (hF : J4Facts) {k : Nat} (hk : k < 7) (h0 : k ≠ 0) (h2 : k ≠ 2) :
    uEl k ∈ Hj ⊔ Subgroup.zpowers (uEl 2) := by
  have hok : maxOK 2 k (maxFromTwo.getD k "") = true := by
    apply maxOK_of4204 (by norm_num) (by norm_num)
    rw [mf_decode4204 hk]
    interval_cases k
    · exact absurd rfl h0
    · exact ch4204.t5
    · exact absurd rfl h2
    · exact ch4204.t6
    · exact ch4204.t7
    · exact ch4204.t8
    · exact ch4204.t9
  exact uEl_mem_of_word hF (by norm_num) hk (kR_enc4204 (by norm_num) (by norm_num)).2.2 hok
    le_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

end CertificateChecks.KernelJ4Ov

end
