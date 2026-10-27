module

public import Certificates.Kernel.Sporadic.SuzI301K.GlueEnum

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzI301K

open CFSG.KC.Enum CFSG.KC.LinRep CFSG.KC.LinRepSound CFSG.KC.LinRepCheck CFSG.KC.SuzI301Lin
open CFSG.KC.SuzI301K CFSG.KD.SuzI301 CFSG.PSL3Four.Native CFSG.Sporadic.SuzI301
  CFSG.ComponentClassification.AS81.SuzB0

theorem appW_lt' (a v : Nat) : appW a v < 64 := CFSG.KC.LinRepCheck.appW_lt a v

theorem col_mulW (a b : Nat) {i : Nat} (hi : i < 6) : col (mulW a b) i = ev (col a) (col b i) := by
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := col_w6 (appW_lt' a (c6 b 0)) (appW_lt' a (c6 b 1))
    (appW_lt' a (c6 b 2)) (appW_lt' a (c6 b 3)) (appW_lt' a (c6 b 4)) (appW_lt' a (c6 b 5))
  have hm : mulW a b = w6 (appW a (c6 b 0)) (appW a (c6 b 1)) (appW a (c6 b 2)) (appW a (c6 b 3))
      (appW a (c6 b 4)) (appW a (c6 b 5)) := rfl
  rw [hm]
  rcases six_cases hi with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [e0, appW_eq_ev]
    rfl
  · rw [e1, appW_eq_ev]
    rfl
  · rw [e2, appW_eq_ev]
    rfl
  · rw [e3, appW_eq_ev]
    rfl
  · rw [e4, appW_eq_ev]
    rfl
  · rw [e5, appW_eq_ev]
    rfl

theorem w6_lt {x0 x1 x2 x3 x4 x5 : Nat} (h0 : x0 < 64) (h1 : x1 < 64) (h2 : x2 < 64)
    (h3 : x3 < 64) (h4 : x4 < 64) (h5 : x5 < 64) : w6 x0 x1 x2 x3 x4 x5 < 2 ^ 36 := by
  have e : w6 x0 x1 x2 x3 x4 x5 =
      x0 + 64 * (x1 + 64 * (x2 + 64 * (x3 + 64 * (x4 + 64 * x5)))) := rfl
  rw [e]
  norm_num
  omega

theorem mulW_lt (a b : Nat) : mulW a b < 2 ^ 36 :=
  w6_lt (appW_lt' _ _) (appW_lt' _ _) (appW_lt' _ _) (appW_lt' _ _) (appW_lt' _ _) (appW_lt' _ _)

theorem col_big {w i : Nat} (hw : w < 2 ^ 36) (hi : 6 ≤ i) : col w i = 0 := by
  rw [col_eq]
  have hp : 2 ^ 36 ≤ 2 ^ (6 * i) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [Nat.div_eq_of_lt (by omega)]

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem nB_eq (b : Bool) : nB b = !b := by cases b <;> rfl

theorem invW_sound {HL : Array Tab} {Y0 Y1 g iw : Nat} (hg : g < 2 ^ 36) (hs : 2 ≤ HL.size)
    (hY0 : HL[0]! = linTab (col Y0)) (hY1 : HL[1]! = linTab (col Y1))
    (h : invW Y0 Y1 g iw = true) : invTest HL (linTab (col g)) = true := by
  have hgl : ∀ i < 6, col g i < 64 := fun i _ => col_lt g i
  unfold invW at h
  cases h6 : Nat.blt iw 6
  · cases he : Nat.beq iw 6
    · have h' : bAnd(Nat.beq (mulW g g) idW,
          strictB (Nat.land (Nat.sub iw 8) 7) fun c =>
            strictB (nIf(Nat.blt (Nat.sub iw 8) 8, Y0, Y1)) fun Y =>
              strictB (mulW Y (mulW g (mulW Y Y))) fun Z =>
                nB (Nat.beq (appW g (c6 Z c)) (appW Z (c6 g c)))) = true := by
        rw [h6, he] at h
        exact h
      obtain ⟨-, h⟩ := band h'
      simp only [strictB_eq', nB_eq, Bool.not_eq_true'] at h
      have hY : ∀ Y : Nat, (Y = Y0 ∨ Y = Y1) →
          ∃ k < HL.size, HL[k]! = linTab (col Y) := fun Y hY => by
        rcases hY with rfl | rfl
        · exact ⟨0, by omega, hY0⟩
        · exact ⟨1, by omega, hY1⟩
      obtain ⟨k, hk, hYk⟩ := hY (nIf(Nat.blt (Nat.sub iw 8) 8, Y0, Y1)) (by
        cases Nat.blt (Nat.sub iw 8) 8
        · exact Or.inr rfl
        · exact Or.inl rfl)
      generalize nIf(Nat.blt (Nat.sub iw 8) 8, Y0, Y1) = Y at h hYk
      generalize Nat.land (Nat.sub iw 8) 7 = c at h
      have hZ : mulW Y (mulW g (mulW Y Y)) < 2 ^ 36 := mulW_lt _ _
      by_cases hc : c < 6
      · refine invTest_lin_comm hgl (fun i _ => col_lt Y i) hk hYk hc ?_
        intro heq
        apply Bool.false_ne_true
        rw [← h]
        rw [appW_eq_ev, appW_eq_ev, c6_eq_col, c6_eq_col, col_mulW _ _ hc, col_mulW _ _ hc,
          col_mulW _ _ hc]
        have hz : ∀ i < 6, col (mulW Y (mulW g (mulW Y Y))) i =
            ev (col Y) (ev (col g) (ev (col Y) (col Y i))) := fun i hi => by
          rw [col_mulW _ _ hi, col_mulW _ _ hi, col_mulW _ _ hi]
        rw [ev_congr hz, heq]
        simp
      · have hc6 : 6 ≤ c := by omega
        rw [c6_eq_col, c6_eq_col, col_big hZ hc6, col_big hg hc6, appW_eq_ev, appW_eq_ev, ev_zero,
          ev_zero] at h
        simp at h
    · have h' : Nat.beq g idW = true := by
        rw [h6, he] at h
        exact h
      have e := Nat.eq_of_beq_eq_true h'
      exact invTest_lin_id (by rw [e]; exact col_idW)
  · have hc : iw < 6 := Nat.blt_eq.mp h6
    have h' : nB (Nat.beq (appW g (c6 g iw)) (Nat.shiftLeft 1 iw)) = true := by
      rw [h6] at h
      exact h
    refine invTest_lin_sq hgl hc ?_
    intro heq
    have e1 : Nat.shiftLeft 1 iw = 2 ^ iw := Nat.one_shiftLeft iw
    rw [nB_eq, appW_eq_ev, c6_eq_col, heq, e1] at h'
    simp at h'

theorem hwK_spec {C H : List Nat} (k : hwK C H = true) :
    Nat.beq (nthN H 0) (mulW (nthN C 0) (mulW (nthN C 1) (mulW (nthN C 2) (nthN C 2)))) = true ∧
    Nat.beq (nthN H 1) (mulW (nthN C 1) (mulW (nthN C 1) (mulW (nthN C 2) (nthN C 2)))) = true ∧
    (allN 2 fun a => strictB (nthN H a) fun Y => Nat.beq (mulW Y (mulW Y Y)) idW) = true := by
  unfold hwK at k
  obtain ⟨k1, k⟩ := band k
  obtain ⟨k2, k3⟩ := band k
  exact ⟨k1, k2, k3⟩

theorem mat64_cw_D : mat64 (sD ()) = linTab (col (nthN CW 0)) := by
  rw [mat64_D]
  exact linTab_congr fun i hi => (cw_col (by norm_num) hi).symm

theorem mat64_cw_B2 : mat64 (sB2 ()) = linTab (col (nthN CW 1)) := by
  rw [mat64_B2]
  exact linTab_congr fun i hi => (cw_col (by norm_num) hi).symm

theorem mat64_cw_B3 : mat64 (sB3 ()) = linTab (col (nthN CW 2)) := by
  rw [mat64_B3]
  exact linTab_congr fun i hi => (cw_col (by norm_num) hi).symm

theorem comp3_words (a b c : Nat) :
    comp 64 (linTab (col a)) (comp 64 (linTab (col b)) (comp 64 (linTab (col c)) (linTab (col c)))) =
      linTab (col (mulW a (mulW b (mulW c c)))) := by
  rw [comp3_linTab (fun i _ => col_lt b i) (fun i _ => col_lt c i)]
  refine linTab_congr fun i hi => ?_
  rw [col_mulW _ _ hi, col_mulW _ _ hi, col_mulW _ _ hi]

@[expose] def HLt : Array Tab :=
  #[comp 64 (mat64 (sD ())) (comp 64 (mat64 (sB2 ())) (comp 64 (mat64 (sB3 ())) (mat64 (sB3 ())))),
    comp 64 (mat64 (sB2 ())) (comp 64 (mat64 (sB2 ())) (comp 64 (mat64 (sB3 ())) (mat64 (sB3 ()))))]

theorem hl0 : HLt[0]! = linTab (col (nthN HW 0)) := by
  have e : HLt[0]! = comp 64 (mat64 (sD ())) (comp 64 (mat64 (sB2 ()))
      (comp 64 (mat64 (sB3 ())) (mat64 (sB3 ())))) := rfl
  rw [e, mat64_cw_D, mat64_cw_B2, mat64_cw_B3, comp3_words, ← Nat.eq_of_beq_eq_true (hwK_spec kHW).1]

theorem hl1 : HLt[1]! = linTab (col (nthN HW 1)) := by
  have e : HLt[1]! = comp 64 (mat64 (sB2 ())) (comp 64 (mat64 (sB2 ()))
      (comp 64 (mat64 (sB3 ())) (mat64 (sB3 ())))) := rfl
  rw [e, mat64_cw_B2, mat64_cw_B3, comp3_words, ← Nat.eq_of_beq_eq_true (hwK_spec kHW).2.1]

theorem inv_facts : ∀ k < 51840, invTest HLt (linTab (col (key (slot TB k)))) = true := by
  intro k hk
  have hk' : k < N := by rw [n_eq]; exact hk
  have ki := kInv
  unfold invK at ki
  have e := CFSG.KS.allN_spec ki k hk'
  beta_reduce at e
  rw [strictB_eq'] at e
  have e0 : Nat.add 0 k = k := Nat.zero_add k
  rw [e0] at e
  exact invW_sound (key_lt _) (by simp [HLt]) hl0 hl1 e

theorem hl_cube : allBelow HLt.size (fun k => comp 64 HLt[k]! (comp 64 HLt[k]! HLt[k]!) == idTab 64) =
    true := by
  have hs : HLt.size = 2 := rfl
  refine allBelow_true fun k hk => ?_
  rw [hs] at hk
  have hY : HLt[k]! = linTab (col (nthN HW k)) := by
    interval_cases k
    · exact hl0
    · exact hl1
  have e := CFSG.KS.allN_spec (hwK_spec kHW).2.2 k hk
  beta_reduce at e
  rw [strictB_eq'] at e
  have hc : ∀ i < 6, col (mulW (nthN HW k) (mulW (nthN HW k) (nthN HW k))) i = 2 ^ i := by
    rw [Nat.eq_of_beq_eq_true e]
    exact col_idW
  rw [hY, comp_linTab _ (fun i _ => col_lt _ i), comp_linTab _ (fun i _ => ev_lt (fun i _ => col_lt _ i) _),
    linTab_eq_id (fun i hi => by rw [← hc i hi, col_mulW _ _ hi, col_mulW _ _ hi])]
  simp

end CertificateChecks.KernelSpor.SuzI301K

end
