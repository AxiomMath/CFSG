module

public import Certificates.Kernel.LocalComp.L34F9460
import CFSG.Certificates.Kernel.L34KSnd.Tab
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34F946

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34Norm
open CFSG.KC.L34SelWord CertificateChecks.KernelLC.L34Cert CFSG.PSL3Four.Native
open CFSG.ComponentClassification.PSL3Four
open CFSG.KLie.CT (fget andB orB notB anyN)

theorem tgt_spec {X : ℕ} (hX : canonK 42 6 (mask 6) (42 * 6) X = true) {x z : Equiv.Perm (Fin 42)}
    (hx : TabRep (unpack 42 6 X) x) (hz : TabRep (unpack 42 6 (L34N.K 2)) z) (t : ℕ) :
    canonK 42 6 (mask 6) (42 * 6) (tgt t X) = true ∧ ∃ y, (y = z ∨ y = x ∨ y = z * x ∨
      y = z ^ 2 * x) ∧ TabRep (unpack 42 6 (tgt t X)) y := by
  have hK := L34N.canonK' (j := 2) (by decide)
  unfold tgt
  cases Nat.beq t 0
  · cases Nat.beq t 1
    · cases Nat.beq t 2
      · have h := (hz.comp hz).comp hx
        rw [CFSG.KC.L34KSnd.comp_unpack' hK hK,
          CFSG.KC.L34KSnd.comp_unpack' (canonK_pcomp hK hK) hX] at h
        exact ⟨canonK_pcomp (canonK_pcomp hK hK) hX, z * z * x,
          Or.inr (Or.inr (Or.inr (by rw [pow_two]))), h⟩
      · have h := hz.comp hx
        rw [CFSG.KC.L34KSnd.comp_unpack' hK hX] at h
        exact ⟨canonK_pcomp hK hX, z * x, Or.inr (Or.inr (Or.inl rfl)), h⟩
    · exact ⟨hX, x, Or.inr (Or.inl rfl), hx⟩
  · exact ⟨hK, z, Or.inl rfl, hz⟩

theorem spec9461 :
    ∃ z₀ ∈ S, z₀ ^ 3 = 1 ∧ z₀ ≠ 1 ∧
      ∀ x ∈ R, x ^ 3 = 1 → x * z₀ = z₀ * x → x ∉ S →
        ∀ Y : Subgroup (Equiv.Perm (Fin 42)),
          (∀ c ∈ S, c * z₀ = z₀ * c ∨ c * x = x * c ∨ c * (z₀ * x) = z₀ * x * c ∨
            c * (z₀ ^ 2 * x) = z₀ ^ 2 * x * c → c ∈ Y) → S ≤ Y := by
  obtain ⟨z, hzS, hz, hz1, hz3⟩ := const_rep (j := 2) (by decide)
  refine ⟨z, hzS, hz3, hz1, fun x hxR hx3 hxz hxS Y hY => ?_⟩
  obtain ⟨i, hi, hx⟩ := L34N3.exists_T hxR
  have hx1 : x ≠ 1 := fun e => hxS (e ▸ S.one_mem)
  have hbit : L34N.code (pidn 42 6) i / 2 % 2 = 1 := by
    have hc := ((hx.comp hz).eq_iff (hz.comp hx)).2 hxz
    rw [L34N.K_tabs.2.2.1] at hc
    obtain ⟨q, hq, hqi, hJ⟩ := (L34N.centZ_iff hi).1 hc
    have h := (L34N.listed_iff (B := fun v => Nat.beq (v / 2 % 2) 1) rfl hi).2
      ⟨q, hq, hqi, by
        change Nat.beq (L34N.J q % 32 / 2 % 2) 1 = true
        rw [Nat.beq_eq]
        omega⟩
    exact Nat.eq_of_beq_eq_true h
  have hP : predZ (L34N.code (pidn 42 6) i) = true := by
    unfold predZ
    rw [CFSG.KC.L34KSnd.andB_iff, CFSG.KC.L34KSnd.notB_iff, Nat.beq_eq]
    exact ⟨hbit, beq_false (code_div8_ne hi hx hx1 hx3)⟩
  obtain ⟨q, hq, hqi, hPq⟩ := listed_of (B := predZ) rfl hi hP
  obtain ⟨m, -, -, hok⟩ := selK_sound kZ hq hPq
  rw [hqi] at hok
  unfold okZ at hok
  rw [strictB_eq, CFSG.KC.L34KSnd.orB_iff] at hok
  rcases hok with hin | hok
  · exact absurd (mem_S_of_inS hx hin) hxS
  rw [strictB_eq, strictB_eq, CFSG.KC.L34KSnd.andB_iff, CFSG.KC.L34KSnd.andB_iff] at hok
  obtain ⟨⟨hj0, hj1⟩, hok⟩ := hok
  have hj0' := Nat.le_of_ble_eq_true hj0
  have hj1' := Nat.le_of_ble_eq_true hj1
  rw [strictB_eq, strictB_eq, CFSG.KC.L34KSnd.andB_iff, CFSG.KC.L34KSnd.andB_iff] at hok
  obtain ⟨⟨hc0, hc1⟩, hw⟩ := hok
  have letter : ∀ {j t : ℕ}, j < 20160 →
      commPt 42 6 (L34S.T j) (tgt t (L34R.T i)) = true →
      ∃ c ∈ Y, TabRep (unpack 42 6 (L34S.T j)) c := by
    intro j t hj hct
    obtain ⟨c, hcS, hc⟩ := S_rep hj
    obtain ⟨hcan, y, hy, hyr⟩ := tgt_spec (L34N.canonT hi) hx hz t
    have hcy : c * y = y * c := ((hc.comp hyr).eq_iff (hyr.comp hc)).1
      ((CFSG.KC.L34KSnd.commPt_iff (canonS hj) hcan).1 hct)
    refine ⟨c, hY c hcS ?_, hc⟩
    rcases hy with rfl | rfl | rfl | rfl
    exacts [Or.inl hcy, Or.inr (Or.inl hcy), Or.inr (Or.inr (Or.inl hcy)),
      Or.inr (Or.inr (Or.inr hcy))]
  have hY0 := letter hj0' hc0
  have hY1 := letter hj1' hc1
  have hS' : S = Subgroup.closure ({g₁, g₂, g₃} : Set (Equiv.Perm (Fin 42))) := rfl
  rw [hS', Subgroup.closure_le]
  intro a ha
  obtain ⟨k, hk, hka⟩ := gensS_cover a ha
  have hk3 : k < 3 := hk
  unfold wordsOK at hw
  have hwk := Nat.eq_of_beq_eq_true (CFSG.KS.Raw.Orb.allN_iff.1 hw k hk3)
  obtain ⟨b, hbY, hb⟩ := wordK_rep (canonS hj0') (canonS hj1') hY0 hY1 hwk
  rw [← bindS.2 k hk3] at hb
  rw [hka.perm_eq hb]
  exact hbY

end CertificateChecks.KernelLC.L34F946

end
