module

public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.FendelDataInputs
public import Certificates.Data.Kernel.Fendel

public section

namespace CFSG.KC.Fendel

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3 CFSG.EvenSmallLie.SympSix

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem lget_eq (L : List Nat) (j : Nat) : lget L j = L.getD j 0 := by
  induction L generalizing j with
  | nil => rfl
  | cons x xs ih =>
    cases j with
    | zero => rfl
    | succ j => exact ih j

theorem bIf_true {c e : Bool} (h : Bool.rec (motive := fun _ => Bool) e true c = true) :
    c = true ∨ e = true := by
  cases c
  · exact Or.inr h
  · exact Or.inl rfl

@[expose] def TrBind (lv : Array Level) (LR TR : Nat → Nat) (nl : Nat) : Prop :=
  ∀ i < nl, ∀ k < rcnt (LR i), (lv[i]!).tr[k]! = unpack 276 9 (trAt LR TR i k)

theorem prodOK_eq {p q r : Nat} (h : prodOK p q r = true) :
    compA 276 (unpack 276 9 p) (unpack 276 9 q) = unpack 276 9 r :=
  compEqK_sound h

theorem prod3_eq {lv : Array Level} {LR TR : Nat → Nat} {nl : Nat} (hnl : 3 ≤ nl)
    (hb : TrBind lv LR TR nl) {a b c : Nat} (h : prod3OK LR TR a b c = true) :
    compA 276 (compA 276 (lv[0]!).tr[a]! (lv[1]!).tr[b]!) (lv[2]!).tr[c]! =
      unpack 276 9 (prod3 LR TR a b c) := by
  obtain ⟨ha, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hb', h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hc, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  rw [hb 0 (by omega) a (Nat.le_of_ble_eq_true ha), hb 1 (by omega) b (Nat.le_of_ble_eq_true hb'),
    hb 2 (by omega) c (Nat.le_of_ble_eq_true hc), prodOK_eq h1, prodOK_eq h2]

theorem prod4_eq {lv : Array Level} {LR TR : Nat → Nat} (hb : TrBind lv LR TR 4)
    {i0 i1 i2 i3 : Nat} (h : prod4OK LR TR i0 i1 i2 i3 = true) :
    compA 276 (compA 276 (compA 276 (lv[0]!).tr[i0]! (lv[1]!).tr[i1]!) (lv[2]!).tr[i2]!)
      (lv[3]!).tr[i3]! = unpack 276 9 (prod4 LR TR i0 i1 i2 i3) := by
  obtain ⟨h3, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hd, h⟩ := (bAnd_iff _ _).1 h
  rw [prod3_eq (by omega) hb h3, hb 3 (by omega) i3 (Nat.le_of_ble_eq_true hd), prodOK_eq h]

structure Data (LRt TRt LRm TRm TRIm : Nat → Nat) (BPm A Z T : Nat) (W : List Nat) : Prop where
  trT : TrBind co3TLevels LRt TRt 3
  trM : TrBind co3MLevels LRm TRm 4
  sift : ∀ G, Nat.shiftRight G (276 * 9) = 0 →
    allN 276 (fun i => Nat.blt (pg 9 (mask 9) G i) 276) = true →
    siftK 276 9 (mask 9) (276 * 9) (pidn 276 9) LRm TRIm BPm 4 0 G = true →
    siftA 276 co3MLevels co3MBaseArr 0 (unpack 276 9 G) = true
  a : fendelAArr = unpack 276 9 A
  z : co3ZArr = unpack 276 9 Z
  t : co3TtArr = unpack 276 9 T
  w : ∀ j, fendelWit[j]! = lget W j
  id : unpack 276 9 (pidn 276 9) = idA 276

theorem hOK_sound {LRt TRt LRm TRm TRIm : Nat → Nat} {BPm A Z T : Nat} {W : List Nat}
    (D : Data LRt TRt LRm TRm TRIm BPm A Z T W) {wv X Y : Nat}
    (h : hOK LRm TRm TRIm BPm wv X Y = true) :
    isInvA 276 (fendelWitConj wv) (invCand 276 (fendelWitConj wv)) = true ∧
      siftA 276 co3MLevels co3MBaseArr 0 (fendelWitConj wv) = true ∧
      eqA 276 (compA 276 (fendelWitConj wv) (unpack 276 9 X))
        (compA 276 (unpack 276 9 Y) (fendelWitConj wv)) = true := by
  unfold hOK at h
  rw [strictB_eq] at h
  obtain ⟨h4, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hinv, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hhi, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hs, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨p1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨p2, he⟩ := (bAnd_iff _ _).1 h
  have hH : fendelWitConj wv = unpack 276 9 (hOf LRm TRm wv) := by
    unfold fendelWitConj fendelMArr hOf
    exact prod4_eq D.trM h4
  obtain ⟨e1, e2⟩ := invEqK_sound hinv
  refine ⟨?_, ?_, ?_⟩
  · rw [hH, e1]
    exact e2
  · rw [hH]
    exact D.sift _ (Nat.eq_of_beq_eq_true hhi) (range_of_permOK hinv) hs
  · rw [hH, prodOK_eq p1, prodOK_eq p2, Nat.eq_of_beq_eq_true he]
    exact eqK_sound (n := 276) (w := 9) (Nat.beq_refl _)

theorem witOK_of_witK {LRt TRt LRm TRm TRIm : Nat → Nat} {BPm A Z T : Nat} {W : List Nat}
    (D : Data LRt TRt LRm TRm TRIm BPm A Z T W) {a b c : Nat}
    (h : witK LRt TRt LRm TRm TRIm BPm A Z T (lget W ((a * 4 + b) * 2 + c)) a b c = true) :
    fendelWitOK a b c = true := by
  unfold witK at h
  rw [strictB_eq] at h
  obtain ⟨h3, h⟩ := (bAnd_iff _ _).1 h
  have hx : fendelTArr a b c = unpack 276 9 (prod3 LRt TRt a b c) := prod3_eq le_rfl D.trT h3
  have hw : fendelWit[(a * 4 + b) * 2 + c]! = lget W ((a * 4 + b) * 2 + c) := D.w _
  unfold fendelWitOK
  dsimp only
  rw [hx, hw]
  rcases bIf_true h with h | h
  · rw [← D.id, eqK_sound (n := 276) (w := 9) h]
    rfl
  rcases bIf_true h with h | h
  · obtain ⟨hp, hn⟩ := (bAnd_iff _ _).1 h
    rw [prodOK_eq hp, neIdK_sound hn]
    simp
  rcases bIf_true h with h | h
  · obtain ⟨hk, hz⟩ := (bAnd_iff _ _).1 h
    have hk' : lget W ((a * 4 + b) * 2 + c) / 16 ^ 7 = 0 := Nat.eq_of_beq_eq_true hk
    rw [D.z, eqK_sound (n := 276) (w := 9) hz, hk']
    simp
  rcases bIf_true h with h | h
  · obtain ⟨hk, hh⟩ := (bAnd_iff _ _).1 h
    have hk' : lget W ((a * 4 + b) * 2 + c) / 16 ^ 7 = 1 := Nat.eq_of_beq_eq_true hk
    obtain ⟨e1, e2, e3⟩ := hOK_sound D hh
    rw [← D.a] at e3
    rw [e1, e2, e3, hk']
    simp
  · obtain ⟨hk, hh⟩ := (bAnd_iff _ _).1 h
    have hk' : lget W ((a * 4 + b) * 2 + c) / 16 ^ 7 = 2 := Nat.eq_of_beq_eq_true hk
    obtain ⟨e1, e2, e3⟩ := hOK_sound D hh
    rw [← D.t] at e3
    rw [e1, e2, e3, hk']
    simp

end CFSG.KC.Fendel

end
