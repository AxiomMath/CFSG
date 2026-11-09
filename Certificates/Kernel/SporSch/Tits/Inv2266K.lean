module

public import Certificates.Kernel.SporSch.Tits.Inv2266M
public import Certificates.Kernel.SporSch.Tits.Central2263
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.PK.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.TitsInv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.BfsPin
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Monster.B.Co2
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2264
open CertificateChecks.KernelSpor.Tits2268 CertificateChecks.KernelMisc
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.TitsCommon
open CertificateChecks.KernelSporSch.TitsHelp CertificateChecks.KernelSporSch.TitsAbel

theorem tW : wordEqK 1755 11 (mask 11) (pidn 1755 11) TitsD.S TitsD.SI 13 titsTWord (wK titsTWord) =
    true := by
  unfold wordEqK
  quickRfl
theorem tB : Nat.beq (wK titsTWord) TitsT = true := by quickRfl
theorem cT : C TitsT := by quickRfl
theorem cG1 : C (TitsText.F 1) := by quickRfl
theorem cG1i : C (pinv (TitsText.F 1)) := by quickRfl

theorem kTK : siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsK.LR TitsK.TRI TitsK.BP 5 0 TitsT =
    true := by quickRfl
theorem kTne : neIdK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsT = true := by quickRfl
theorem kTsq : sqIdK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsT = true := by quickRfl
theorem k5 : allN 3 (fun j => sS (pc (pc (TitsText.F 1) (TitsS.S j)) (pinv (TitsText.F 1)))) = true := by
  quickRfl
theorem k6 : sS (pc (TitsText.F 1) (TitsText.F 1)) = true := by quickRfl
theorem k7 : bIf(sS (TitsText.F 1), false, true) = true := by quickRfl

@[expose] noncomputable def lIC (bw : Bool × List Int) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun _ wd => lettersK 13 wd) bw

@[expose] noncomputable def gIC (bw : Bool × List Int) (y : Nat) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun b wd =>
    conjW TitsD.S TitsD.SI wd (Bool.rec (motive := fun _ => Nat) TitsT TitsZ b) y) bw

theorem zipA_append {α : Type} {g : α → Nat → Bool} :
    ∀ {A1 A2 : List α} {L1 L2 : List Nat}, zipA g A1 L1 = true → zipA g A2 L2 = true →
      zipA g (A1 ++ A2) (L1 ++ L2) = true
  | [], _, [], _, _, h => h
  | [], _, _ :: _, _, h, _ => (Bool.false_ne_true h).elim
  | _ :: _, _, [], _, h, _ => (Bool.false_ne_true h).elim
  | a :: A1, A2, l :: L1, L2, h, h2 => by
    have h' : Bool.rec (motive := fun _ => Bool) false (zipA g A1 L1) (g a l) = true := h
    obtain ⟨h1, h3⟩ := (bAnd_iff _ _).1 h'
    change Bool.rec (motive := fun _ => Bool) false (zipA g (A1 ++ A2) (L1 ++ L2)) (g a l) = true
    rw [h1, zipA_append h3 h2]

theorem zipA_chunks {α : Type} {g : α → Nat → Bool} (c : Nat) :
    ∀ (m : Nat) (A : List α) (L : List Nat), A.length ≤ c * m → L.length ≤ c * m →
      (∀ i < m, zipA g ((A.drop (c * i)).take c) ((L.drop (c * i)).take c) = true) →
      zipA g A L = true
  | 0, A, L, hA, hL, _ => by
    rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hA),
      List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hL)]
    rfl
  | m + 1, A, L, hA, hL, h => by
    rw [← List.take_append_drop c A, ← List.take_append_drop c L]
    refine zipA_append (by simpa using h 0 (by omega)) (zipA_chunks c m _ _ ?_ ?_ fun i hi => ?_)
    · rw [List.length_drop, Nat.mul_succ] at *
      omega
    · rw [List.length_drop, Nat.mul_succ] at *
      omega
    · simpa only [List.drop_drop, Nat.mul_succ, Nat.add_comm] using h (i + 1) (by omega)

theorem zipA_imp {α : Type} {f g : α → Nat → Bool} (hfg : ∀ a l, f a l = true → g a l = true) :
    ∀ {A : List α} {L : List Nat}, zipA f A L = true → zipA g A L = true
  | [], [], _ => rfl
  | [], _ :: _, h => (Bool.false_ne_true h).elim
  | _ :: _, [], h => (Bool.false_ne_true h).elim
  | a :: A, l :: L, h => by
    have h' : Bool.rec (motive := fun _ => Bool) false (zipA f A L) (f a l) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    change Bool.rec (motive := fun _ => Bool) false (zipA g A L) (g a l) = true
    rw [hfg a l h1, zipA_imp hfg h2]

@[expose] noncomputable def invRT (A : Nat) : Bool :=
  allN 1755 (fun i => strictB (pgR A i) (fun a => bAnd(Nat.blt a 1755, Nat.beq (pgR A a) i)))

@[expose] noncomputable def conjWH (S SI : Nat → Nat) (wd : List Int) (A y : Nat) : Bool :=
  bAnd(lettersK (nat_lit 13) wd,
    allN 1755 (fun i => strictB (pgR A i) (fun a => bIf(Nat.ble i a,
      strictB (wPt S SI wd i) (fun u => strictB (pgR y u) (fun v =>
        bAnd(Nat.beq (wPt S SI wd a) v, Nat.beq (pgR y v) u))), true))))

theorem conjWH_half {W A y : Nat → Nat} (hA : ∀ i < 1755, A i < 1755 ∧ A (A i) = i)
    (h : ∀ i < 1755, i ≤ A i → W (A i) = y (W i) ∧ y (y (W i)) = W i) :
    ∀ i < 1755, W (A i) = y (W i) := by
  intro i hi
  by_cases hle : i ≤ A i
  · exact (h i hi hle).1
  · obtain ⟨hk, hkk⟩ := hA i hi
    obtain ⟨e1, e2⟩ := h (A i) hk (by rw [hkk]; omega)
    rw [hkk] at e1
    rw [e1, e2]

theorem conjW_of_conjWH {S SI : Nat → Nat} {wd : List Int} {A y : Nat} (hA : invRT A = true)
    (h : conjWH S SI wd A y = true) : conjW S SI wd A y = true := by
  have sB : ∀ (x : Nat) (k : Nat → Bool), strictB x k = k x := fun x k => by cases x <;> rfl
  obtain ⟨hl, hc⟩ := (bAnd_iff _ _).1 h
  have hA' : ∀ i < 1755, pgR A i < 1755 ∧ pgR A (pgR A i) = i := fun i hi => by
    have e := PK.allN_iff.1 hA i hi
    rw [sB] at e
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 e
    exact ⟨by simpa using h1, Nat.eq_of_beq_eq_true h2⟩
  have hc' : ∀ i < 1755, i ≤ pgR A i → wPt S SI wd (pgR A i) = pgR y (wPt S SI wd i) ∧
      pgR y (pgR y (wPt S SI wd i)) = wPt S SI wd i := fun i hi hle => by
    have e := PK.allN_iff.1 hc i hi
    have hb : Nat.ble i (pgR A i) = true := by simpa using hle
    rw [sB, hb] at e
    have e' : strictB (wPt S SI wd i) (fun u => strictB (pgR y u) (fun v =>
        bAnd(Nat.beq (wPt S SI wd (pgR A i)) v, Nat.beq (pgR y v) u))) = true := e
    rw [sB, sB] at e'
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 e'
    exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2⟩
  refine (bAnd_iff _ _).2 ⟨hl, PK.allN_iff.2 fun i hi => ?_⟩
  rw [conjWH_half hA' hc' i hi]
  exact Nat.beq_refl _

@[expose] noncomputable def gICh (bw : Bool × List Int) (y : Nat) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun b wd =>
    conjWH TitsD.S TitsD.SI wd (Bool.rec (motive := fun _ => Nat) TitsT TitsZ b) y) bw

theorem kInvT : invRT TitsT = true := by quickRfl
theorem kInvZ : invRT TitsZ = true := by quickRfl

theorem gIC_of_gICh : ∀ (bw : Bool × List Int) (y : Nat), gICh bw y = true → gIC bw y = true
  | (true, wd), y, h => @conjW_of_conjWH TitsD.S TitsD.SI wd TitsZ y kInvZ h
  | (false, wd), y, h => @conjW_of_conjWH TitsD.S TitsD.SI wd TitsT y kInvT h

theorem kIC : allA lIC titsInvCert = true := by quickRfl
theorem kICz0 : zipA gICh ((titsInvCert.drop (16 * 0)).take 16) ((TitsIC.drop (16 * 0)).take 16) =
    true := by quickRfl
theorem kICz1 : zipA gICh ((titsInvCert.drop (16 * 1)).take 16) ((TitsIC.drop (16 * 1)).take 16) =
    true := by quickRfl
theorem kICz2 : zipA gICh ((titsInvCert.drop (16 * 2)).take 16) ((TitsIC.drop (16 * 2)).take 16) =
    true := by quickRfl
theorem kICz3 : zipA gICh ((titsInvCert.drop (16 * 3)).take 16) ((TitsIC.drop (16 * 3)).take 16) =
    true := by quickRfl
theorem kICz4 : zipA gICh ((titsInvCert.drop (16 * 4)).take 16) ((TitsIC.drop (16 * 4)).take 16) =
    true := by quickRfl
theorem kICz5 : zipA gICh ((titsInvCert.drop (16 * 5)).take 16) ((TitsIC.drop (16 * 5)).take 16) =
    true := by quickRfl
theorem kICz6 : zipA gICh ((titsInvCert.drop (16 * 6)).take 16) ((TitsIC.drop (16 * 6)).take 16) =
    true := by quickRfl
theorem kICz7 : zipA gICh ((titsInvCert.drop (16 * 7)).take 16) ((TitsIC.drop (16 * 7)).take 16) =
    true := by quickRfl
theorem kICz8 : zipA gICh ((titsInvCert.drop (16 * 8)).take 16) ((TitsIC.drop (16 * 8)).take 16) =
    true := by quickRfl
theorem kICl : Nat.ble titsInvCert.length (16 * 9) = true := by quickRfl
theorem kICll : Nat.ble TitsIC.length (16 * 9) = true := by quickRfl

theorem kICz : zipA gIC titsInvCert TitsIC = true :=
  zipA_imp gIC_of_gICh <|
  zipA_chunks 16 9 _ _ (Nat.le_of_ble_eq_true kICl) (Nat.le_of_ble_eq_true kICll) fun i hi => by
    match i, hi with
    | 0, _ => exact kICz0
    | 1, _ => exact kICz1
    | 2, _ => exact kICz2
    | 3, _ => exact kICz3
    | 4, _ => exact kICz4
    | 5, _ => exact kICz5
    | 6, _ => exact kICz6
    | 7, _ => exact kICz7
    | 8, _ => exact kICz8

theorem allLT_append {f : Nat → Bool} :
    ∀ {L1 L2 : List Nat}, CFSG.KS.SporSch.allL f L1 = true → CFSG.KS.SporSch.allL f L2 = true →
      CFSG.KS.SporSch.allL f (L1 ++ L2) = true
  | [], _, _, h => h
  | y :: L1, L2, h, h2 => by
    have h' : Bool.rec (motive := fun _ => Bool) false (CFSG.KS.SporSch.allL f L1) (f y) = true := h
    obtain ⟨h1, h3⟩ := (bAnd_iff _ _).1 h'
    change Bool.rec (motive := fun _ => Bool) false (CFSG.KS.SporSch.allL f (L1 ++ L2)) (f y) = true
    rw [h1, allLT_append h3 h2]

theorem allLT_chunks {f : Nat → Bool} (c : Nat) :
    ∀ (m : Nat) (L : List Nat), L.length ≤ c * m →
      (∀ i < m, CFSG.KS.SporSch.allL f ((L.drop (c * i)).take c) = true) →
      CFSG.KS.SporSch.allL f L = true
  | 0, L, hL, _ => by
    rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hL)]
    rfl
  | m + 1, L, hL, h => by
    rw [← List.take_append_drop c L]
    refine allLT_append (by simpa using h 0 (by omega)) (allLT_chunks c m _ ?_ fun i hi => ?_)
    · rw [List.length_drop, Nat.mul_succ] at *
      omega
    · simpa only [List.drop_drop, Nat.mul_succ, Nat.add_comm] using h (i + 1) (by omega)

@[expose] noncomputable def cIC (i : Nat) : Bool :=
  CFSG.KS.SporSch.allL (fun y => canonK 1755 11 (mask 11) (1755 * 11) y)
    ((TitsIC.drop (8 * i)).take 8)

theorem kICc0 : cIC 0 = true := by quickRfl
theorem kICc1 : cIC 1 = true := by quickRfl
theorem kICc2 : cIC 2 = true := by quickRfl
theorem kICc3 : cIC 3 = true := by quickRfl
theorem kICc4 : cIC 4 = true := by quickRfl
theorem kICc5 : cIC 5 = true := by quickRfl
theorem kICc6 : cIC 6 = true := by quickRfl
theorem kICc7 : cIC 7 = true := by quickRfl
theorem kICc8 : cIC 8 = true := by quickRfl
theorem kICc9 : cIC 9 = true := by quickRfl
theorem kICc10 : cIC 10 = true := by quickRfl
theorem kICc11 : cIC 11 = true := by quickRfl
theorem kICc12 : cIC 12 = true := by quickRfl
theorem kICc13 : cIC 13 = true := by quickRfl
theorem kICc14 : cIC 14 = true := by quickRfl
theorem kICc15 : cIC 15 = true := by quickRfl
theorem kICc16 : cIC 16 = true := by quickRfl
theorem kICc17 : cIC 17 = true := by quickRfl

theorem kICc : allL (fun y => canonK 1755 11 (mask 11) (1755 * 11) y) TitsIC = true :=
  allLT_chunks 8 18 _ (Nat.le_of_ble_eq_true kICll) fun i hi => by
    match i, hi with
    | 0, _ => exact kICc0
    | 1, _ => exact kICc1
    | 2, _ => exact kICc2
    | 3, _ => exact kICc3
    | 4, _ => exact kICc4
    | 5, _ => exact kICc5
    | 6, _ => exact kICc6
    | 7, _ => exact kICc7
    | 8, _ => exact kICc8
    | 9, _ => exact kICc9
    | 10, _ => exact kICc10
    | 11, _ => exact kICc11
    | 12, _ => exact kICc12
    | 13, _ => exact kICc13
    | 14, _ => exact kICc14
    | 15, _ => exact kICc15
    | 16, _ => exact kICc16
    | 17, _ => exact kICc17
    | _ + 18, h => omega

@[expose] def fixPts : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 17, 18, 19, 21, 25, 26, 31, 32, 37, 46, 57, 68]

theorem kFix : allN 1755 (fun p => bIf(Nat.beq (pg 11 (mask 11) TitsT p) p, memN p fixPts, true)) =
    true := by quickRfl

@[expose] noncomputable def okFW (pw : Nat × List Int) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun p wd => bAnd(lettersK 13 wd,
    Nat.beq (wPt TitsD.S TitsD.SI wd 0) p)) pw

theorem kFW : allA okFW titsFixWords = true := by quickRfl

@[expose] noncomputable def qEx (pw : Nat × List Int) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun p _ => Nat.blt 2 p) pw

@[expose] noncomputable def gEx (pw : Nat × List Int) (y : Nat) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun _ wd => exclW TitsD.S TitsD.SI wd TitsT y) pw

@[expose] noncomputable def zipAF {α : Type} (q : α → Bool) (g : α → Nat → Bool) (A : List α) :
    List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun L => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) L)
    (fun a _ ih L => bIf(q a,
      List.rec (motive := fun _ => Bool) false (fun l L' _ => bAnd(g a l, ih L')) L, ih L)) A

theorem zipAF_imp {α : Type} {q : α → Bool} {f g : α → Nat → Bool}
    (hfg : ∀ a l, f a l = true → g a l = true) :
    ∀ {A : List α} {L : List Nat}, zipAF q f A L = true → zipAF q g A L = true
  | [], _, h => h
  | a :: A, L, h => by
    have h' : Bool.rec (motive := fun _ => Bool) (zipAF q f A L)
        (List.rec (motive := fun _ => Bool) false (fun l L' _ =>
          Bool.rec (motive := fun _ => Bool) false (zipAF q f A L') (f a l)) L) (q a) = true := h
    change Bool.rec (motive := fun _ => Bool) (zipAF q g A L)
        (List.rec (motive := fun _ => Bool) false (fun l L' _ =>
          Bool.rec (motive := fun _ => Bool) false (zipAF q g A L') (g a l)) L) (q a) = true
    cases hq : q a
    · rw [hq] at h'
      exact zipAF_imp hfg h'
    · rw [hq] at h'
      cases L with
      | nil => exact h'
      | cons l L' =>
        have h'' : Bool.rec (motive := fun _ => Bool) false (zipAF q f A L') (f a l) = true := h'
        obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h''
        change Bool.rec (motive := fun _ => Bool) false (zipAF q g A L') (g a l) = true
        rw [hfg a l h1, zipAF_imp hfg h2]

@[expose] noncomputable def gExH (pw : Nat × List Int) (y : Nat) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun _ wd =>
    bAnd(conjWH TitsD.S TitsD.SI wd y TitsT, invRT y)) pw

theorem exclW_of_conjWH {S SI : Nat → Nat} {wd : List Int} {T y : Nat}
    (h : bAnd(conjWH S SI wd y T, invRT y) = true) : exclW S SI wd T y = true :=
  conjW_of_conjWH ((bAnd_iff _ _).1 h).2 ((bAnd_iff _ _).1 h).1

theorem gEx_of_gExH : ∀ (pw : Nat × List Int) (y : Nat), gExH pw y = true → gEx pw y = true
  | (_, wd), y, h => @exclW_of_conjWH TitsD.S TitsD.SI wd TitsT y h

theorem kEXzH : zipAF qEx gExH titsFixWords TitsEX = true := by quickRfl
theorem kEXz : zipAF qEx gEx titsFixWords TitsEX = true := zipAF_imp gEx_of_gExH kEXzH
theorem kEXc : allL (fun y => canonK 1755 11 (mask 11) (1755 * 11) y) TitsEX = true := by quickRfl

end CertificateChecks.KernelSporSch.TitsInv

end
