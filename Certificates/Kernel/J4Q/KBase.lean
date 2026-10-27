module

public import Certificates.Kernel.J4Q.QT2A
public import Certificates.Kernel.J4Q.KOrbData
public import CFSG.Sporadic.J4.QT2LocX0KNative
import Certificates.Kernel.J4Q.Strs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#j4q_strs CFSG.KD.J4Q.KW5 CFSG.Sporadic.J4.QT2.kStrings

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A
  CFSG.Sporadic.J4.QT2

@[expose] noncomputable def kWK : List (List Int) :=
  [w5K KW5.s0, w5K KW5.s1, w5K KW5.s2, w5K KW5.s3, w5K KW5.s4, w5K KW5.s5]

theorem kqWords_eq : CFSG.Sporadic.J4.QT2.kWords = kWK := by
  rw [CFSG.Sporadic.J4.QT2.kWords, KW5.eq]
  simp only [List.map_cons, List.map_nil, w5_ofList]
  rfl

theorem kg_chk : allR 6 (fun i => andB (Nat.beq (getN one KG i) (wordJ c rm one G5 G5i (kWK.getD i [])))
    (andB (canonJ pad (getN one KG (i + 6))) (Nat.beq (mulJ c rm (getN one KG i) (getN one KG (i + 6))) one))) =
    true := by
  quickRfl

theorem kGen_size : kGenRows.size = 6 := by
  rw [kGenRows, kqWords_eq]
  rfl

theorem kGen_get {i : Nat} (hi : i < 6) : kGenRows[i]! = wR (kWK.getD i []) := by
  have hl : i < kWK.length := hi
  rw [kGenRows, kqWords_eq]
  simp [hl]

theorem kGen_enc {i : Nat} (hi : i < 6) :
    WfA (kGenRows[i]!) ∧ encR (kGenRows[i]!) = getN one KG i := by
  have h := allR_spec kg_chk i hi
  simp only [andB_eq, Bool.and_eq_true] at h
  rw [kGen_get hi]
  exact ⟨(wR_enc _).1, (wR_enc _).2.trans (Nat.eq_of_beq_eq_true h.1).symm⟩

theorem kInv_enc {i : Nat} (hi : i < 6) :
    WfA (kInvRows[i]!) ∧ encR (kInvRows[i]!) = getN one KG (i + 6) := by
  have h := allR_spec kg_chk i hi
  simp only [andB_eq, Bool.and_eq_true] at h
  have hg := kGen_enc hi
  have hs : i < kGenRows.size := by
    rw [kGen_size]
    exact hi
  have : kInvRows[i]! = invRows (kGenRows[i]!) := by
    simp [kInvRows, hs]
  rw [this]
  exact invRows_enc hK hg.1 h.2.1 (by rw [hg.2]; exact h.2.2)

theorem kInv_size : kInvRows.size = 6 := by
  simp [kInvRows, kGen_size]

theorem kAll_enc {g : Nat} (hg : g < 12) :
    WfA (kAllRows[g]!) ∧ encR (kAllRows[g]!) = getN one KG g := by
  have hs := kGen_size
  have hsi := kInv_size
  have hlt : g < (kGenRows ++ kInvRows).size := by
    rw [Array.size_append, hs, hsi]
    exact hg
  by_cases h : g < 6
  · have : kAllRows[g]! = kGenRows[g]! := by
      rw [kAllRows, getElem!_pos (kGenRows ++ kInvRows) g hlt,
        Array.getElem_append_left (by rw [hs]; exact h), getElem!_pos kGenRows g (by rw [hs]; exact h)]
    rw [this]
    exact kGen_enc h
  · have : kAllRows[g]! = kInvRows[g - 6]! := by
      rw [kAllRows, getElem!_pos (kGenRows ++ kInvRows) g hlt,
        Array.getElem_append_right (by rw [hs]; omega)]
      have e : g - kGenRows.size = g - 6 := by rw [hs]
      simp only [e]
      rw [getElem!_pos kInvRows (g - 6) (by rw [hsi]; omega)]
    rw [this]
    have h6 := kInv_enc (i := g - 6) (by omega)
    have e : g - 6 + 6 = g := by omega
    rw [e] at h6
    exact h6

theorem kStep_enc (X : Array V2) (g : Nat) (hX : WfA X) (hg : g < 12) :
    WfA (kStep X g) ∧ encR (kStep X g) = mulJ c rm (encR X) (getN one KG g) := by
  unfold kStep
  exact mul_enc hK ⟨hX, rfl⟩ (kAll_enc hg)

end CertificateChecks.KernelJ4Q

end
