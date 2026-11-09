module

public import Certificates.Data.Kernel.Griess13.Glue
public import Certificates.Data.Kernel.M1F2
public import CFSG.Monster.GMS.Griess13.GlueCertData
public import Certificates.Kernel.Griess13.Data
public meta import Certificates.Kernel.Griess13.GlueGen
public meta import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

#kc_eval CertificateChecks.KernelG13 GD CertificateChecks.KernelG13.stepGlue

#ks_chars CertificateChecks.KernelG13.Slp2 CFSG.Monster.GMS.Griess13.Co1Data.slpMax2

#ks_chars CertificateChecks.KernelG13.SlpAB CFSG.Monster.GMS.Griess13.Co1Data.slpWordsAB

#ks_chars CertificateChecks.KernelG13.TB CFSG.Monster.GMS.Griess13.Co1Data.tmatBits

namespace CertificateChecks.KernelG13

open CFSG.KC.G13 CFSG.KC.Co1B CFSG.KC.M1F2 CertificateChecks.KernelCo1Cover
  CFSG.Monster.GMS.Griess13.Co1Data

@[expose] noncomputable def slp2 : SLP := decSLP GD.s2L GD.s2O

@[expose] noncomputable def slpAB : SLP := decSLP GD.sabL GD.sabO

@[expose] noncomputable def tmatC (i : Nat) : List Char := 'T' :: '\n' :: (TB.chars.drop (576 * i)).take 576

theorem slp2_text : charsEq Slp2.chars (slpC slp2) = true := by quickRfl

theorem slpAB_text : charsEq SlpAB.chars (slpC slpAB) = true := by quickRfl

theorem h_ok : evalP slp2 [pk R0 R0, pk R1 G.B2] = GD.H := by decide +kernel

theorem g_ok : wordP GD.H (parseWord gStr) = GD.G := by decide +kernel

theorem x_ok : ∀ k : Fin 3, wordP [G.N1, G.N2] (parseWord (xStr k)) = GD.X.getD k.val 0 := by
  decide +kernel

theorem y_ok : ∀ k : Fin 3, wordP [G.N1, G.N2] (parseWord (yStr k)) = GD.Y.getD k.val 0 := by
  decide +kernel

theorem ab_ok : evalP slpAB [G.N1, G.N2, GD.G] = GD.AB := by decide +kernel

theorem tm_ok : ∀ i < 8, m1Bind (tmatC i) 24 (GD.T.getD i 0) = true := by decide +kernel

theorem el_len : GD.E.length = 1728 := by decide +kernel

@[expose] noncomputable def extP (P s : Nat) : Nat :=
  Nat.land (Nat.shiftRight P (Nat.mul 576 s)) (Nat.sub (Nat.shiftLeft 1 576) 1)

@[expose] noncomputable def foldP (Ps : List Nat) : Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun P _ ih μ acc => ih (Nat.shiftRight μ 4) (Nat.xor acc (extP P (Nat.land μ 15)))) Ps

@[expose] noncomputable def selB (b : Bool) (e : Nat) : Nat := Bool.rec (motive := fun _ => Nat) 0 e b

@[expose] noncomputable def comb4 (e0 e1 e2 e3 s : Nat) : Nat :=
  Nat.xor (Nat.xor (Nat.xor (selB (Nat.beq (Nat.land (Nat.shiftRight s 0) 1) 1) e0)
    (selB (Nat.beq (Nat.land (Nat.shiftRight s 1) 1) 1) e1))
    (selB (Nat.beq (Nat.land (Nat.shiftRight s 2) 1) 1) e2))
    (selB (Nat.beq (Nat.land (Nat.shiftRight s 3) 1) 1) e3)

@[expose] noncomputable def blkCheck (P e0 e1 e2 e3 : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun s ih => Bool.rec (motive := fun _ => Bool) false ih (Nat.beq (extP P s) (comb4 e0 e1 e2 e3 s))) 16

@[expose] noncomputable def packCheck (Ps : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun E => Nat.beq E.length 0)
    (fun P _ ih E => Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false (ih (E.drop 4))
        (blkCheck P (E.getD 0 0) (E.getD 1 0) (E.getD 2 0) (E.getD 3 0)))
      (Nat.ble 4 E.length)) Ps

@[expose] noncomputable def spanCheckP (Ps : List Nat) (fmask : Nat) (cert : Nat → Nat × Nat) : Bool :=
  (List.range 576).all fun a => fmask.testBit a ||
    (foldP Ps (cert a).1 0 == ((1 <<< a) ^^^ (cert a).2) && ((cert a).2 ||| fmask) == fmask)

theorem testBit_eq_shiftBeq (μ k : Nat) :
    Nat.testBit μ k = Nat.beq (Nat.land (Nat.shiftRight μ k) 1) 1 := by
  change _ = Nat.beq ((μ >>> k) &&& 1) 1
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (μ / 2 ^ k) with h | h <;> rw [h] <;> rfl

theorem natRec_all (c : Nat → Bool) (n : Nat)
    (h : Nat.rec (motive := fun _ => Bool) true
      (fun s ih => Bool.rec (motive := fun _ => Bool) false ih (c s)) n = true) :
    ∀ s < n, c s = true := by
  induction n with
  | zero => intro s hs; omega
  | succ n ih =>
    change Bool.rec (motive := fun _ => Bool) false (Nat.rec (motive := fun _ => Bool) true
      (fun s ih => Bool.rec (motive := fun _ => Bool) false ih (c s)) n) (c n) = true at h
    cases hc : c n
    · rw [hc] at h
      exact absurd h Bool.false_ne_true
    · rw [hc] at h
      intro s hs
      rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
      · exact ih h s hs
      · exact hc

theorem blkCheck_sound {P e0 e1 e2 e3 : Nat} (h : blkCheck P e0 e1 e2 e3 = true) :
    ∀ s < 16, extP P s = comb4 e0 e1 e2 e3 s := fun s hs =>
  Nat.eq_of_beq_eq_true (natRec_all (fun s => Nat.beq (extP P s) (comb4 e0 e1 e2 e3 s)) 16 h s hs)

theorem rec_xor (acc e : Nat) (b : Bool) :
    Bool.rec (motive := fun _ => Nat) acc (acc ^^^ e) b = acc ^^^ selB b e := by
  cases b
  · exact (Nat.xor_zero acc).symm
  · rfl

theorem testBit_low4 (μ k t : Nat) (ht : t < 4) :
    Nat.beq (Nat.land (Nat.shiftRight ((μ >>> k) &&& 15) t) 1) 1 = μ.testBit (k + t) := by
  rw [← testBit_eq_shiftBeq, Nat.testBit_and, Nat.testBit_shiftRight]
  have : (15 : Nat).testBit t = true := by
    rcases t with _ | _ | _ | _ | t
    all_goals first | rfl | omega
  rw [this, Bool.and_true]

theorem foldXorL_eq_foldP (Ps : List Nat) :
    ∀ E, packCheck Ps E = true → ∀ μ k acc, foldXorL μ E k acc = foldP Ps (μ >>> k) acc := by
  induction Ps with
  | nil =>
    intro E h μ k acc
    have hE : E = [] := List.eq_nil_of_length_eq_zero (Nat.eq_of_beq_eq_true h)
    subst hE
    rfl
  | cons P Ps ih =>
    intro E h μ k acc
    change Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false (packCheck Ps (E.drop 4))
        (blkCheck P (E.getD 0 0) (E.getD 1 0) (E.getD 2 0) (E.getD 3 0)))
      (Nat.ble 4 E.length) = true at h
    cases hl : Nat.ble 4 E.length
    · rw [hl] at h
      exact absurd h Bool.false_ne_true
    rw [hl] at h
    cases hb : blkCheck P (E.getD 0 0) (E.getD 1 0) (E.getD 2 0) (E.getD 3 0)
    · rw [hb] at h
      exact absurd h Bool.false_ne_true
    rw [hb] at h
    have hl' := Nat.le_of_ble_eq_true hl
    match E, hl', hb, h with
    | [], hl', _, _ => simp at hl'
    | [_], hl', _, _ => simp at hl'
    | [_, _], hl', _, _ => simp at hl'
    | [_, _, _], hl', _, _ => simp at hl'
    | e0 :: e1 :: e2 :: e3 :: E', _, hb, h =>
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hb
      have hs : (μ >>> k) &&& 15 < 16 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
      have hfx : ∀ e t k acc, foldXorL μ (e :: t) k acc =
          foldXorL μ t (k + 1) (Bool.rec (motive := fun _ => Nat) acc (Nat.xor acc e) (Nat.testBit μ k)) :=
        fun _ _ _ _ => rfl
      have hfp : foldP (P :: Ps) (μ >>> k) acc =
          foldP Ps ((μ >>> k) >>> 4) (Nat.xor acc (extP P ((μ >>> k) &&& 15))) := rfl
      have hx : ∀ a b : Nat, Nat.xor a b = a ^^^ b := fun _ _ => rfl
      have hk : k + 1 + 1 + 1 + 1 = k + 4 := by omega
      have hk2 : k + 1 + 1 = k + 2 := by omega
      have hk3 : k + 1 + 1 + 1 = k + 3 := by omega
      rw [hfx, hfx, hfx, hfx, hfp, ih E' h, ← Nat.shiftRight_add, blkCheck_sound hb _ hs, hk, hk3, hk2]
      simp only [hx, rec_xor]
      simp only [comb4, hx, testBit_low4 μ k 0 (by omega), testBit_low4 μ k 1 (by omega),
        testBit_low4 μ k 2 (by omega), testBit_low4 μ k 3 (by omega), Nat.xor_assoc, Nat.add_zero]

theorem spanCheckP_eq {Ps E : List Nat} (h : packCheck Ps E = true) (fmask : Nat)
    (cert : Nat → Nat × Nat) : spanCheckP Ps fmask cert = spanCheckL E fmask cert := by
  simp only [spanCheckP, spanCheckL, foldXorL_eq_foldP Ps E h, Nat.shiftRight_zero]

theorem pack_ok : packCheck GD.P GD.E = true := by decide +kernel

theorem testBit_ofBitsR (d : Nat) (f : Nat → Bool) (a : Nat) :
    (ofBitsR d f).testBit a = (decide (a < d) && f a) := by
  induction d with
  | zero => exact Nat.zero_testBit a
  | succ d ih =>
    change (Bool.rec (motive := fun _ => Nat) (ofBitsR d f)
      (ofBitsR d f ||| 1 <<< d) (f d)).testBit a = _
    cases hf : f d
    · change (ofBitsR d f).testBit a = _
      rw [ih]
      by_cases h : a = d
      · subst h
        simp [hf]
      · have : a < d + 1 ↔ a < d := by omega
        simp [this]
    · change (ofBitsR d f ||| 1 <<< d).testBit a = _
      rw [Nat.testBit_or, ih, Nat.one_shiftLeft, Nat.testBit_two_pow]
      by_cases h : a = d
      · subst h
        simp [hf]
      · have : a < d + 1 ↔ a < d := by omega
        have h' : ¬ d = a := fun e => h e.symm
        simp [this, h']

@[expose] noncomputable def spr24 (d : Nat) (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun p acc => Bool.rec (motive := fun _ => Nat) acc (Nat.lor acc (Nat.shiftLeft 1 (24 * p))) (f p)) d

theorem testBit_spr24 (d : Nat) (f : Nat → Bool) (b : Nat) :
    (spr24 d f).testBit b = (decide (b % 24 = 0) && decide (b / 24 < d) && f (b / 24)) := by
  induction d with
  | zero =>
    change Nat.testBit 0 b = _
    simp
  | succ d ih =>
    change (Bool.rec (motive := fun _ => Nat) (spr24 d f)
      (spr24 d f ||| 1 <<< (24 * d)) (f d)).testBit b = _
    cases hf : f d
    · change (spr24 d f).testBit b = _
      rw [ih]
      by_cases h : b = 24 * d
      · subst h
        simp [hf]
      · by_cases hb : b % 24 = 0
        · have : b / 24 < d + 1 ↔ b / 24 < d := by omega
          simp [this]
        · simp [hb]
    · change (spr24 d f ||| 1 <<< (24 * d)).testBit b = _
      rw [Nat.testBit_or, ih, Nat.one_shiftLeft, Nat.testBit_two_pow]
      by_cases h : b = 24 * d
      · subst h
        simp [hf]
      · have h' : ¬ 24 * d = b := fun e => h e.symm
        by_cases hb : b % 24 = 0
        · have : b / 24 < d + 1 ↔ b / 24 < d := by omega
          simp [this, h']
        · simp [hb, h']

@[expose] noncomputable def colB (X j : Nat) : Nat :=
  ofBitsR 24 fun q => Nat.beq (Nat.land (Nat.shiftRight X (24 * q + j)) 1) 1

@[expose] noncomputable def rowS (X i : Nat) : Nat :=
  spr24 24 fun p => Nat.beq (Nat.land (Nat.shiftRight X (24 * i + p)) 1) 1

@[expose] noncomputable def eqMaskF (X i j : Nat) : Nat :=
  Nat.xor (Nat.shiftLeft (colB X j) (24 * i)) (Nat.shiftLeft (rowS X i) j)

theorem eqMaskK_eq (X i j : Nat) (hi : i < 24) (hj : j < 24) : eqMaskK X i j = eqMaskF X i j := by
  apply Nat.eq_of_testBit_eq
  intro a
  change _ = ((colB X j <<< (24 * i)) ^^^ (rowS X i <<< j)).testBit a
  simp only [eqMaskK, colB, rowS, ← testBit_eq_shiftBeq, testBit_ofBitsR, testBit_spr24,
    Nat.testBit_xor, Nat.testBit_shiftLeft]
  obtain ⟨q, s, hs, rfl⟩ : ∃ q s, s < 24 ∧ a = 24 * q + s :=
    ⟨a / 24, a % 24, Nat.mod_lt _ (by omega), (Nat.div_add_mod a 24).symm⟩
  have hq : (24 * q + s) / 24 = q := by omega
  have hs' : (24 * q + s) % 24 = s := by omega
  rw [hq, hs']
  by_cases h1 : q = i
  · subst h1
    have e1 : 24 * q + s - 24 * q = s := by omega
    have c1 : 24 * q + s < 576 ↔ q < 24 := by omega
    by_cases h2 : s = j
    · subst h2
      have e2 : 24 * q + s - s = 24 * q := by omega
      have e3 : 24 * q / 24 = q := by omega
      have e4 : 24 * q % 24 = 0 := by omega
      simp [e1, e2, e3, e4, c1, hi, hs]
    · have e3 : ¬ (j ≤ 24 * q + s ∧ (24 * q + s - j) % 24 = 0) := by omega
      simp only [not_and] at e3
      have b1 : (s == j) = false := by simpa using h2
      by_cases h4 : j ≤ 24 * q + s
      · simp [e1, c1, hi, hs, b1, h4, e3 h4]
      · simp [e1, c1, hi, hs, b1, h4]
  · have e1 : ¬ (24 * i ≤ 24 * q + s ∧ 24 * q + s - 24 * i < 24) := by omega
    simp only [not_and] at e1
    have b0 : (q == i) = false := by simpa using h1
    by_cases h2 : s = j
    · subst h2
      have e2 : 24 * q + s - s = 24 * q := by omega
      have e3 : 24 * q / 24 = q := by omega
      have e4 : 24 * q % 24 = 0 := by omega
      have c1 : 24 * q + s < 576 ↔ q < 24 := by omega
      by_cases h5 : 24 * i ≤ 24 * q + s
      · simp [e2, e3, e4, c1, b0, h5, e1 h5]
      · simp [e2, e3, e4, c1, b0, h5]
    · have e3 : ¬ (j ≤ 24 * q + s ∧ (24 * q + s - j) % 24 = 0) := by omega
      simp only [not_and] at e3
      have b1 : (s == j) = false := by simpa using h2
      by_cases h5 : 24 * i ≤ 24 * q + s <;> by_cases h4 : j ≤ 24 * q + s
      · simp [b0, b1, h5, e1 h5, h4, e3 h4]
      · simp [b0, b1, h5, e1 h5, h4]
      · simp [b0, b1, h5, h4, e3 h4]
      · simp [b0, b1, h5, h4]

@[expose] noncomputable def elF (r : Nat) : Nat := eqMaskF (GD.X.getD (r / 576) 0) (r % 576 / 24) (r % 24)

@[expose] noncomputable def elWalk (E : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun e _ ih r => Bool.rec (motive := fun _ => Bool) false (ih (Nat.succ r)) (Nat.beq (elF r) e)) E

theorem elWalk_sound (E : List Nat) :
    ∀ o, elWalk E o = true → ∀ r < E.length, elF (o + r) = E.getD r 0 := by
  induction E with
  | nil =>
    intro o _ r hr
    simp at hr
  | cons e t ih =>
    intro o h r hr
    change Bool.rec (motive := fun _ => Bool) false (elWalk t (o + 1)) (Nat.beq (elF o) e) = true at h
    cases hb : Nat.beq (elF o) e
    · rw [hb] at h
      exact absurd h Bool.false_ne_true
    · rw [hb] at h
      cases r with
      | zero => simpa using Nat.eq_of_beq_eq_true hb
      | succ r =>
        have := ih (o + 1) h r (by simpa using hr)
        rwa [Nat.add_assoc, Nat.add_comm 1 r] at this

theorem elW_ok : elWalk GD.E 0 = true := by decide +kernel

theorem elW_all :
    ∀ r < 1728, eqMaskK (GD.X.getD (r / 576) 0) (r % 576 / 24) (r % 24) = GD.E.getD r 0 := by
  intro r hr
  rw [eqMaskK_eq _ _ _ (by omega) (Nat.mod_lt _ (by omega))]
  have := elWalk_sound GD.E 0 elW_ok r (by rw [el_len]; exact hr)
  rwa [Nat.zero_add] at this

theorem spanP_ok : spanCheckP GD.P (fmaskOf freePos) certTab = true := by decide +kernel

theorem span_ok : spanCheckL GD.E (fmaskOf freePos) certTab = true := by
  rw [← spanCheckP_eq pack_ok]
  exact spanP_ok

theorem seventh_ok : ∀ c : Fin 8 → ZMod 2,
    eqK (powW (mulWK GD.G (comboK GD.T c)) 7) oneK = true → eqK (comboK GD.T c) oneK = true := by
  decide +kernel

end CertificateChecks.KernelG13

end
