module

public import Certificates.Kernel.J4Q.QT2A
public import Certificates.Kernel.J4Q.X0OrbData
public import CFSG.Sporadic.J4.QT2LocX0Native
import Certificates.Kernel.J4Q.Strs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#j4q_strs CFSG.KD.J4Q.X0W CFSG.Sporadic.J4.QT2.x0Strings

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A
  CFSG.Sporadic.J4.QT2

@[expose] noncomputable def x0WK : List (List Int) :=
  [w5K X0W.s0, w5K X0W.s1, w5K X0W.s2, w5K X0W.s3, w5K X0W.s4, w5K X0W.s5, w5K X0W.s6, w5K X0W.s7]

theorem x0Words_eq : x0Words = x0WK := by
  rw [x0Words, X0W.eq]
  simp only [List.map_cons, List.map_nil, w5_ofList]
  rfl

theorem xg_chk : allR 8 (fun i => andB (Nat.beq (getN one XG i) (wordJ c rm one G5 G5i (x0WK.getD i [])))
    (andB (canonJ pad (getN one XG (i + 8))) (Nat.beq (mulJ c rm (getN one XG i) (getN one XG (i + 8))) one))) =
    true := by
  quickRfl

theorem x0Gen_get {i : Nat} (hi : i < 8) : x0GenRows[i]! = wR (x0WK.getD i []) := by
  have hl : i < x0WK.length := hi
  rw [x0GenRows, x0Words_eq]
  simp [hl]

theorem x0Gen_enc {i : Nat} (hi : i < 8) :
    WfA (x0GenRows[i]!) ∧ encR (x0GenRows[i]!) = getN one XG i := by
  have h := allR_spec xg_chk i hi
  simp only [andB_eq, Bool.and_eq_true] at h
  rw [x0Gen_get hi]
  exact ⟨(wR_enc _).1, (wR_enc _).2.trans (Nat.eq_of_beq_eq_true h.1).symm⟩

theorem x0Inv_enc {i : Nat} (hi : i < 8) :
    WfA (x0InvRows[i]!) ∧ encR (x0InvRows[i]!) = getN one XG (i + 8) := by
  have h := allR_spec xg_chk i hi
  simp only [andB_eq, Bool.and_eq_true] at h
  have hg := x0Gen_enc hi
  have hlen : x0WK.length = 8 := rfl
  have hs : i < x0GenRows.size := by
    rw [x0GenRows, x0Words_eq]
    simp [hlen, hi]
  have : x0InvRows[i]! = invRows (x0GenRows[i]!) := by
    simp [x0InvRows, hs]
  rw [this]
  exact invRows_enc hK hg.1 h.2.1 (by rw [hg.2]; exact h.2.2)

theorem x0All_enc {g : Nat} (hg : g < 16) :
    WfA (x0AllRows[g]!) ∧ encR (x0AllRows[g]!) = getN one XG g := by
  have hs : x0GenRows.size = 8 := by
    rw [x0GenRows, x0Words_eq]
    rfl
  have hsi : x0InvRows.size = 8 := by
    simp [x0InvRows, hs]
  have hlt : g < (x0GenRows ++ x0InvRows).size := by
    rw [Array.size_append, hs, hsi]
    exact hg
  by_cases h : g < 8
  · have : x0AllRows[g]! = x0GenRows[g]! := by
      rw [x0AllRows, getElem!_pos (x0GenRows ++ x0InvRows) g hlt,
        Array.getElem_append_left (by rw [hs]; exact h), getElem!_pos x0GenRows g (by rw [hs]; exact h)]
    rw [this]
    exact x0Gen_enc h
  · have : x0AllRows[g]! = x0InvRows[g - 8]! := by
      rw [x0AllRows, getElem!_pos (x0GenRows ++ x0InvRows) g hlt,
        Array.getElem_append_right (by rw [hs]; omega)]
      have e : g - x0GenRows.size = g - 8 := by rw [hs]
      simp only [e]
      rw [getElem!_pos x0InvRows (g - 8) (by rw [hsi]; omega)]
    rw [this]
    have h8 := x0Inv_enc (i := g - 8) (by omega)
    have e : g - 8 + 8 = g := by omega
    rw [e] at h8
    exact h8

theorem x0Step_enc (X : Array V2) (g : Nat) (hX : WfA X) (hg : g < 16) :
    WfA (x0Step X g) ∧ encR (x0Step X g) = mulJ c rm (encR X) (getN one XG g) := by
  unfold x0Step
  exact mul_enc hK ⟨hX, rfl⟩ (x0All_enc hg)

theorem x0CStep_enc (X : Array V2) (g : Nat) (hX : WfA X) (hg : g < 16) :
    WfA (x0CStep X g) ∧ encR (x0CStep X g) =
      mulJ c rm (mulJ c rm (getN one XG ((g + 8) % 16)) (encR X)) (getN one XG g) := by
  unfold x0CStep
  exact mul_enc hK (mul_enc hK (x0All_enc (Nat.mod_lt _ (by decide))) ⟨hX, rfl⟩) (x0All_enc hg)

end CertificateChecks.KernelJ4Q

end
