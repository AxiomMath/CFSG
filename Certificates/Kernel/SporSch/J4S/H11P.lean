
module

public import Certificates.Kernel.SporSch.J4S.H11
public import CFSG.Certificates.Kernel.SporSch.J4SPrimesSound
public import CFSG.Certificates.Kernel.SporSch.J4SPowSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.J4H11

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.C11
open CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2.Native CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.J4XY

theorem sB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem bIf_eq (c t e : Bool) : Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem poly_eq (w : Nat) : h11Poly w = unpack11 (polyK w) := by
  rw [polyK, polyA, unpack11_packK_p _ (fun j _ => appK_lt_p _ _), h11Poly, wordCols_eq']
  refine Array.ext (by simp) (fun i h1 _ => ?_)
  have hi : i < 11 := by simpa using h1
  simp only [Array.getElem_ofFn]
  rw [powKF_eq 4 _ i (by norm_num; omega), app_eq]

theorem hB : h11B = unpack11 J4HB := bindW_sound J4HB.bind

theorem hBI : h11Binv = unpack11 J4HBI := bindW_sound J4HBI.bind

theorem hX_eq (w : Nat) : h11X w = unpack11 (xK w) := by
  rw [h11X, poly_eq, hBI, comp_eq, xK]

theorem facts : (h11B = h11Poly 1 ∧ comp11 h11B h11Binv = idRows 11 ∧ Bounded h11B ∧
      Bounded h11Binv)
    ∧ (∀ w < 2048, Bounded (h11Poly w))
    ∧ (∀ w < 2048, powCols (h11X w) 1024 = h11X w)
    ∧ (∀ w < 2048, powCols (h11X w) 3 = idRows 11 →
      h11X w = idRows 11 ∨ fixCount (h11X w) < 4)
    ∧ (∀ k < 27, 0 < k → 4 ≤ fixCount q3Cols[k]!)
    ∧ (Bounded (idRows 11)) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, fun w _ => ?_, fun w hw => ?_, fun w hw h3 => ?_, fun k hk hk0 => ?_, ?_⟩
  · rw [hB, poly_eq, Nat.eq_of_beq_eq_true b1]
  · rw [hB, hBI, comp_eq, CFSG.KS.SporSch.C11.id_eq, Nat.eq_of_beq_eq_true binv]
  · rw [hB]
    exact unpack11_bounded _
  · rw [hBI]
    exact unpack11_bounded _
  · rw [poly_eq]
    exact unpack11_bounded _
  · have h := allN_spec p1024 w hw
    rw [p1024K, sB] at h
    rw [hX_eq, powKF_eq 11 _ 1024 (by norm_num), Nat.eq_of_beq_eq_true h]
  · have h := allN_spec ord3 w hw
    rw [ord3K, sB, sB] at h
    rw [hX_eq, powKF_eq 2 _ 3 (by norm_num), CFSG.KS.SporSch.C11.id_eq] at h3
    rw [hX_eq, CFSG.KS.SporSch.C11.id_eq]
    by_cases hY : Nat.beq (powKF 2 (xK w) 3) pidK = true
    · rw [bIf_eq, if_pos hY, bIf_eq] at h
      by_cases hX : Nat.beq (xK w) pidK = true
      · exact Or.inl (by rw [Nat.eq_of_beq_eq_true hX])
      · rw [if_neg hX] at h
        right
        rw [fix_sound (Nat.beq_refl _)]
        exact J4Three.lt_of_blt h
    · rw [bIf_eq, if_neg hY] at h
      exact absurd h3 (ne_sound h)
  · have h := allN_spec q3fix k hk
    rw [bIf_eq, if_neg (by rw [J4Three.beq_ne hk0]; exact Bool.false_ne_true)] at h
    rw [J4Three.C_eq hk, fix_sound (Nat.beq_refl _)]
    exact Nat.le_of_ble_eq_true h
  · rw [CFSG.KS.SporSch.C11.id_eq]
    exact unpack11_bounded _

end CertificateChecks.KernelSporSch.J4H11

end
