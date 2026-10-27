
module

public import Certificates.Kernel.SporSch.J4S.Rank
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.J4S.NoCP

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.J4Rank

open CFSG.KC.Enum CFSG.KS CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KS.SporSch.J4B
open CFSG.Sporadic.J4Schreier CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.J4Eta

theorem rows3_of {X : Array Nat} (hX : WfN X) : rows3OK X = rowsK (encN X) := by
  simp only [rows3OK, rowsK]
  rw [get_enc J4Real.hK hX (r := 0) (by omega), get_enc J4Real.hK hX (r := 1) (by omega),
    get_enc J4Real.hK hX (r := 2) (by omega)]
  rfl

theorem suf_ok {w : List Int} {T : List Nat} (hseg : ∀ k < 8, segK w T k = true)
    (hb : getN one T 8 = one ∧ getN one T 17 = one) (hlen : w.length ≤ 800)
    (hlet : ∀ l ∈ w, l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2) :
    ∀ m ≤ 8, PairOK (wordP Xn Yn (w.drop (100 * (8 - m)))) (getN one T (8 - m))
      (getN one T (9 + (8 - m)))
  | 0, _ => by
    rw [show 8 - 0 = 8 from rfl, List.drop_eq_nil_of_le (by omega), hb.1, hb.2]
    exact oneP_ok J4Real.hK
  | m + 1, hm => by
    have ih := suf_ok hseg hb hlen hlet m (by omega)
    have hk : 8 - (m + 1) < 8 := by omega
    have h := hseg _ hk
    unfold segK at h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    rw [dropI_eq, takeI_eq] at h1 h2
    have e1 : Nat.succ (8 - (m + 1)) = 8 - m := by omega
    have e2 : Nat.add 10 (8 - (m + 1)) = 9 + (8 - m) := by
      change 10 + (8 - (m + 1)) = 9 + (8 - m)
      omega
    have e3 : Nat.add 9 (8 - (m + 1)) = 9 + (8 - (m + 1)) := rfl
    have e4 : Nat.mul 100 (8 - (m + 1)) = 100 * (8 - (m + 1)) := rfl
    rw [e1, e4] at h1
    rw [e2, e3, e4] at h2
    have split : w.drop (100 * (8 - (m + 1))) =
        (w.drop (100 * (8 - (m + 1)))).take 100 ++ w.drop (100 * (8 - m)) := by
      conv_lhs => rw [← List.take_append_drop 100 (w.drop (100 * (8 - (m + 1))))]
      rw [List.drop_drop, show 100 * (8 - (m + 1)) + 100 = 100 * (8 - m) by omega]
    have := wordP_ok J4Real.hK pX pY ih ((w.drop (100 * (8 - (m + 1)))).take 100)
      (fun l hl => hlet l (List.mem_of_mem_drop (List.mem_of_mem_take hl)))
    rw [← split, Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2] at this
    exact this

theorem word0 : PairOK (wordP Xn Yn J4Q3T.w0) (getN one J4S0 0) (getN one J4S0 9) := by
  have := suf_ok (fun k hk => J4Seg0.all k hk |> fun h => by
      have := allBlk_spec h 0 Nat.zero_lt_one
      rwa [show Nat.add (Nat.mul 1 k) 0 = k by simp] at this)
    ⟨Nat.eq_of_beq_eq_true b0a, Nat.eq_of_beq_eq_true b0b⟩ len0 letters0 8 (by omega)
  simpa using this

theorem word1 : PairOK (wordP Xn Yn J4Q3T.w1) (getN one J4S1 0) (getN one J4S1 9) := by
  have := suf_ok (fun k hk => J4Seg1.all k hk |> fun h => by
      have := allBlk_spec h 0 Nat.zero_lt_one
      rwa [show Nat.add (Nat.mul 1 k) 0 = k by simp] at this)
    ⟨Nat.eq_of_beq_eq_true b1a, Nat.eq_of_beq_eq_true b1b⟩ len1 letters1 8 (by omega)
  simpa using this

theorem gen_ok {g : Nat} (hg : g < 2) :
    PairOK Q3GenPairs[g]! (getN one J4KP g) (getN one J4KP (2 + g)) := by
  have h1 := g0a
  have h2 := g0b
  have h3 := g1a
  have h4 := g1b
  obtain rfl | rfl : g = 0 ∨ g = 1 := by omega
  · have e : Q3GenPairs[0]! = powP (wordP Xn Yn J4Q3T.w0) 4 := by
      rw [← J4Three.w_get0]
      rfl
    rw [e]
    exact ofEq (powP_ok J4Real.hK word0 4) (Nat.eq_of_beq_eq_true h1) (Nat.eq_of_beq_eq_true h2)
  · have e : Q3GenPairs[1]! = powP (wordP Xn Yn J4Q3T.w1) 2 := by
      rw [← J4Three.w_get1]
      rfl
    rw [e]
    exact ofEq (powP_ok J4Real.hK word1 2) (Nat.eq_of_beq_eq_true h3) (Nat.eq_of_beq_eq_true h4)

theorem elt_ok : ∀ k < 27, PairOK (q3PairK Q3GenPairs k) (QF k) (QS k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have h := allN_spec elt k hk
    unfold eltK at h
    rw [q3PairK]
    by_cases k0 : k = 0
    · subst k0
      have h' : bAnd(Nat.beq (QF 0) one, Nat.beq (QS 0) one) = true := h
      obtain ⟨h1, h2⟩ := (bAnd_iff (Nat.beq (QF 0) one) (Nat.beq (QS 0) one)).1 h'
      rw [dite_eq_right (by omega), Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2]
      exact oneP_ok J4Real.hK
    · rw [show Nat.beq k 0 = false from Bool.eq_false_iff.2 fun e => k0 (Nat.eq_of_beq_eq_true e)]
        at h
      obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
      obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
      obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h
      have l1 : p0 k < k := Nat.le_of_ble_eq_true h1
      have l2 : p1 k < 2 := Nat.le_of_ble_eq_true h2
      have g0 : (q3Par[k]!)[0]! = p0 k := J4Three.P_get hk (by omega)
      have g1 : (q3Par[k]!)[1]! = p1 k := J4Three.P_get hk (by omega)
      rw [dite_eq_left ⟨by omega, by rw [g0]; exact l1⟩, g0, g1]
      exact ofEq (mulP_ok J4Real.hK (ih (p0 k) l1 (by omega)) (gen_ok l2))
        (Nat.eq_of_beq_eq_true h3) (Nat.eq_of_beq_eq_true h4)

theorem facts : (rows3OK (etaP 1).1 = true ∧ rows3OK (etaP 14).1 = true)
    ∧ (q3RowsOK Q3GenPairs = true) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have h := etaP_ok 1
    rw [rows3_of h.1.1, h.1.2, Nat.eq_of_beq_eq_true e1]
    exact r1
  · have h := etaP_ok 14
    rw [rows3_of h.1.1, h.1.2, Nat.eq_of_beq_eq_true e14]
    exact r14
  · rw [q3RowsOK, List.all_eq_true]
    intro k hk
    have hk' : k < 26 := List.mem_range.1 hk
    have h := elt_ok (k + 1) (by omega)
    rw [rows3_of h.1.1, h.1.2]
    exact allN_spec rowsQ k hk'

end CertificateChecks.KernelSporSch.J4Rank

end
