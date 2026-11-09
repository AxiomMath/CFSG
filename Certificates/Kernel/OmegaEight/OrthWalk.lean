module

public import Certificates.Kernel.OmegaEight.Forms
public import Certificates.Data.Kernel.O8.Orth
public import CFSG.Certificates.Kernel.O8OrthSound

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.KC.Loop CFSG.KLie.CT

@[expose] def LP : List ℕ := [0, 1152, 1152, 1152, 1152, 1152, 1152, 1152, 1152, 1152, 1152,
  1152, 0, 0, 0, 0, 1152, 1152, 0, 0, 1152, 1152, 0, 0, 1152, 1152, 0, 0, 0, 0, 1152, 1152, 1152,
  0, 1152, 0, 1152, 0, 1152, 0, 1152, 0, 1152, 0, 0, 1152, 0, 1152, 1152, 0, 0, 1152, 1152, 0, 0,
  1152, 1152, 0, 0, 1152, 0, 1152, 1152, 0]

@[expose] def LM : List ℕ := [0, 1920, 1920, 1920, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1920, 1920,
  0, 0, 0, 0, 1920, 1920, 0, 0, 1920, 1920, 0, 0, 1920, 1920, 1920, 0, 1920, 0, 0, 1920, 0, 1920,
  0, 1920, 0, 1920, 0, 1920, 0, 1920, 1920, 0, 0, 1920, 0, 1920, 1920, 0, 0, 1920, 1920, 0, 0,
  1920, 1920, 0]

theorem strictN_eq_o8 (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

@[expose] noncomputable def wordFoldR (f : Nat → Nat → Nat) (base n : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ s => s)
    (fun _ ih w s => nIf(Nat.beq w (nat_lit 0), s,
      (fun low => strictN (f (Nat.add base (CFSG.KC.Local.pop64 (Nat.sub low (nat_lit 1)))) s)
        (fun s2 => ih (Nat.xor w low) s2))
      (Nat.land w (Nat.xor w (Nat.sub w (nat_lit 1))))))
    n

theorem wordFoldR_succ (f : Nat → Nat → Nat) (base n w s : Nat) :
    wordFoldR f base (n + 1) w s = nIf(Nat.beq w (nat_lit 0), s,
      strictN (f (Nat.add base (CFSG.KC.Local.pop64
          (Nat.sub (Nat.land w (Nat.xor w (Nat.sub w (nat_lit 1)))) (nat_lit 1)))) s)
        (fun s2 => wordFoldR f base n (Nat.xor w (Nat.land w (Nat.xor w (Nat.sub w (nat_lit 1)))))
          s2)) := rfl

theorem walkK_succ_o8 (e BT QM : Nat) (f : Nat → Nat) (d C : Nat) :
    walkK e BT QM f (d + 1) C = wordFoldR (fun c s => Nat.add s (walkK e BT QM f d
        (Nat.lor C (Nat.shiftLeft c (Nat.mul (nat_lit 6) (Nat.sub (nat_lit 5) d))))))
      (nat_lit 0) (nat_lit 64) (candK e BT QM C (Nat.sub (nat_lit 5) d)) (nat_lit 0) := by
  delta walkK wordFoldR CFSG.KC.Local.wordFold
  rfl

@[expose] noncomputable def bfTabO6 : Nat := nat_lit 430762406827734748662097811766771107977033282745220841703422310847748598096692472380264199205532017311449409550781656572911185497246054847964403037292455513738681455980830059468759632118930327807010749815510383531579254288968369151020983700754311915719788893065663464283274973477639051437246749828627380670519217685231255539438691126636744049855730463316750224998065544975128110389836025576750222888700994348971800700159761935081295781572543192701005574877258453009269639357174113051412605215392641339095604006034610515872578467107134353278801902420135294650227588210949445300681962567024425606435822352698726507867396389368868459933964118203129151935317006280480865710102892183773077594363423650850412797386808817710752542907702906070812834371010010022171461523772354009913135547796076394553690268856521930574886700218203189370176240268095200328598137638355593064482278236049311073963238458452678813924631041289443953885540868682972603338409665181902869348788334900354505382284506243676668237488397426142671631670841792576676726074768399701939102061836077624624071419864283199916632482837043829532378961724265859045578809459674070049816415737283330821453444860671466211976733380338414850143468719084882461977198082308217919030427648

class OrthTab (e : Nat) : Prop where
  tab : bfTab e = bfTabO6
  mask : qMask e = e
  b05 : bfK e (pw2 0) (pw2 5) = 1

instance tab_QP : OrthTab QP := ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

instance tab_QM : OrthTab QM := ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem walkFrom_tab {e BT QMk : Nat} (f : Nat → Nat) (c : Nat) (h1 : bfTab e = BT)
    (h2 : qMask e = QMk) : walkFrom e f c = nIf(Nat.beq (bitN (candK e BT QMk (nat_lit 0)
      (nat_lit 0)) c) (nat_lit 1), walkK e BT QMk f (nat_lit 5) c, nat_lit 0) := by
  subst h1 h2
  unfold walkFrom
  rw [strictN_eq_o8, strictN_eq_o8]

theorem orthTab_walk {e c n : Nat} {f : Nat → Nat} [h : OrthTab e]
    (hw : nIf(Nat.beq (bitN (candK e bfTabO6 e (nat_lit 0) (nat_lit 0)) c) (nat_lit 1),
      walkK e bfTabO6 e f (nat_lit 5) c, nat_lit 0) = n) : walkFrom e f c = n :=
  (walkFrom_tab f c h.tab h.mask).trans hw

theorem candK_dead_rec (b : Nat) (g : Nat → Nat) (hg : g 0 = 0) : ∀ j,
    Nat.rec (motive := fun _ => Nat) b (fun i ih => strictN ih fun m => Nat.land m (g i)) (j + 1)
      = 0 := by
  intro j
  induction j with
  | zero =>
    change strictN b (fun m => Nat.land m (g 0)) = 0
    rw [strictN_eq_o8, hg]
    exact Nat.and_zero b
  | succ j ih =>
    change strictN (Nat.rec (motive := fun _ => Nat) b
      (fun i ih => strictN ih fun m => Nat.land m (g i)) (j + 1))
      (fun m => Nat.land m (g (j + 1))) = 0
    rw [ih, strictN_eq_o8]
    exact Nat.zero_and _

theorem candK_dead (e BT QMk C k : Nat) (hrow : fget BT 0 64 = 0) (hc : colAt C 0 = 0)
    (hb : bfK e (pw2 0) (pw2 (k + 1)) = 1) : candK e BT QMk C (k + 1) = 0 := by
  have h0 : Bool.rec (motive := fun _ => Nat) (Nat.xor (fget BT (colAt C 0) 64) (maskN 64))
      (fget BT (colAt C 0) 64) (Nat.beq (bfK e (pw2 0) (pw2 (k + 1))) 1) = 0 := by
    rw [hb, hc]
    exact hrow
  exact candK_dead_rec _ (fun i => Bool.rec (motive := fun _ => Nat)
    (Nat.xor (fget BT (colAt C i) 64) (maskN 64)) (fget BT (colAt C i) 64)
    (Nat.beq (bfK e (pw2 i) (pw2 (k + 1))) 1)) h0 k

theorem colAt0_lor (C c k : Nat) (hk : 1 ≤ k) :
    colAt (Nat.lor C (Nat.shiftLeft c (Nat.mul 6 k))) 0 = colAt C 0 := by
  change (C ||| c <<< (6 * k)) >>> (0 * 6) &&& (2 ^ 6 - 1) = C >>> (0 * 6) &&& (2 ^ 6 - 1)
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.zero_mul, Nat.shiftRight_zero, Nat.testBit_and, Nat.testBit_or,
    Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 6
  · have : ¬ 6 * k ≤ i := by omega
    simp [hi, this]
  · simp [hi]

theorem wordFoldR_zeroes (g : Nat → Nat) (base : Nat) (h : ∀ c, g c = 0) :
    ∀ n w, wordFoldR (fun c s => Nat.add s (g c)) base n w 0 = 0 := by
  intro n
  induction n with
  | zero => intro w; rfl
  | succ n ih =>
    intro w
    rw [wordFoldR_succ]
    cases Nat.beq w (nat_lit 0)
    · rw [strictN_eq_o8, h]
      exact ih _
    · rfl

theorem walk_dead (e BT QMk : Nat) (f : Nat → Nat) (hrow : fget BT 0 64 = 0)
    (hb : bfK e (pw2 0) (pw2 5) = 1) :
    ∀ d, d < 5 → ∀ C, colAt C 0 = 0 → walkK e BT QMk f (d + 1) C = 0 := by
  intro d
  induction d with
  | zero =>
    intro _ C hc
    rw [walkK_succ_o8, (candK_dead e BT QMk C 4 hrow hc hb :
      candK e BT QMk C (Nat.sub (nat_lit 5) 0) = 0)]
    rfl
  | succ d ih =>
    intro hd C hc
    rw [walkK_succ_o8]
    exact wordFoldR_zeroes _ 0 (fun c => ih (by omega) _
      ((colAt0_lor C c (Nat.sub 5 (d + 1)) (by change 1 ≤ 5 - (d + 1); omega)).trans hc)) 64 _

theorem fget_bfTabO6 : fget bfTabO6 0 64 = 0 := by decide +kernel

theorem walkFrom_zero_o8 {e : Nat} {f : Nat → Nat} [h : OrthTab e] : walkFrom e f 0 = 0 := by
  rw [walkFrom_tab f 0 h.tab h.mask]
  cases Nat.beq (bitN (candK e bfTabO6 e (nat_lit 0) (nat_lit 0)) 0) (nat_lit 1)
  · rfl
  · exact walk_dead e bfTabO6 e f fget_bfTabO6 h.b05 4 (by omega) 0 rfl

theorem kCntP_0 : walkFrom QP (fun _ => 1) 0 = 0 := walkFrom_zero_o8
theorem kCntP_1 : walkFrom QP (fun _ => 1) 1 = 1152 := orthTab_walk (by decide +kernel)
theorem kCntP_2 : walkFrom QP (fun _ => 1) 2 = 1152 := orthTab_walk (by decide +kernel)
theorem kCntP_3 : walkFrom QP (fun _ => 1) 3 = 1152 := orthTab_walk (by decide +kernel)
theorem kCntP_4 : walkFrom QP (fun _ => 1) 4 = 1152 := orthTab_walk (by decide +kernel)
theorem kCntP_5 : walkFrom QP (fun _ => 1) 5 = 1152 := orthTab_walk (by decide +kernel)
theorem kCntP_6 : walkFrom QP (fun _ => 1) 6 = 1152 := orthTab_walk (by decide +kernel)
theorem kCntP_7 : walkFrom QP (fun _ => 1) 7 = 1152 := orthTab_walk (by decide +kernel)
theorem kCntP_8 : walkFrom QP (fun _ => 1) 8 = 1152 := orthTab_walk (by decide +kernel)
theorem kCntP_9 : walkFrom QP (fun _ => 1) 9 = 1152 := orthTab_walk (by decide +kernel)
theorem kCntP_10 : walkFrom QP (fun _ => 1) 10 = 1152 := orthTab_walk (by decide +kernel)
theorem kCntP_11 : walkFrom QP (fun _ => 1) 11 = 1152 := orthTab_walk (by decide +kernel)
theorem kCntP_12 : walkFrom QP (fun _ => 1) 12 = 0 := orthTab_walk (by decide +kernel)
theorem kCntP_13 : walkFrom QP (fun _ => 1) 13 = 0 := orthTab_walk (by decide +kernel)
theorem kCntP_14 : walkFrom QP (fun _ => 1) 14 = 0 := orthTab_walk (by decide +kernel)
theorem kCntP_15 : walkFrom QP (fun _ => 1) 15 = 0 := orthTab_walk (by decide +kernel)
theorem kCntP_16 : walkFrom QP (fun _ => 1) 16 = 1152 := orthTab_walk (by decide +kernel)
theorem kCntP_17 : walkFrom QP (fun _ => 1) 17 = 1152 := orthTab_walk (by decide +kernel)
theorem kCntP_18 : walkFrom QP (fun _ => 1) 18 = 0 := orthTab_walk (by decide +kernel)
theorem kCntP_19 : walkFrom QP (fun _ => 1) 19 = 0 := orthTab_walk (by decide +kernel)
theorem kCntP_20 : walkFrom QP (fun _ => 1) 20 = 1152 := orthTab_walk (by decide +kernel)
theorem kCntP_21 : walkFrom QP (fun _ => 1) 21 = 1152 := orthTab_walk (by decide +kernel)
theorem kCntP_22 : walkFrom QP (fun _ => 1) 22 = 0 := orthTab_walk (by decide +kernel)
theorem kCntP_23 : walkFrom QP (fun _ => 1) 23 = 0 := orthTab_walk (by decide +kernel)
theorem kCntP_24 : walkFrom QP (fun _ => 1) 24 = 1152 := orthTab_walk (by decide +kernel)
theorem kCntP_25 : walkFrom QP (fun _ => 1) 25 = 1152 := orthTab_walk (by decide +kernel)
theorem kCntP_26 : walkFrom QP (fun _ => 1) 26 = 0 := orthTab_walk (by decide +kernel)
theorem kCntP_27 : walkFrom QP (fun _ => 1) 27 = 0 := orthTab_walk (by decide +kernel)
theorem kCntP_28 : walkFrom QP (fun _ => 1) 28 = 0 := orthTab_walk (by decide +kernel)
theorem kCntP_29 : walkFrom QP (fun _ => 1) 29 = 0 := orthTab_walk (by decide +kernel)
theorem kCntP_30 : walkFrom QP (fun _ => 1) 30 = 1152 := orthTab_walk (by decide +kernel)
theorem kCntP_31 : walkFrom QP (fun _ => 1) 31 = 1152 := orthTab_walk (by decide +kernel)
theorem kCntP_32 : walkFrom QP (fun _ => 1) 32 = 1152 := orthTab_walk (by decide +kernel)
theorem kCntP_33 : walkFrom QP (fun _ => 1) 33 = 0 := orthTab_walk (by decide +kernel)
theorem kCntP_34 : walkFrom QP (fun _ => 1) 34 = 1152 := orthTab_walk (by decide +kernel)
theorem kCntP_35 : walkFrom QP (fun _ => 1) 35 = 0 := orthTab_walk (by decide +kernel)
theorem kCntP_36 : walkFrom QP (fun _ => 1) 36 = 1152 := orthTab_walk (by decide +kernel)
theorem kCntP_37 : walkFrom QP (fun _ => 1) 37 = 0 := orthTab_walk (by decide +kernel)
theorem kCntP_38 : walkFrom QP (fun _ => 1) 38 = 1152 := orthTab_walk (by decide +kernel)
theorem kCntP_39 : walkFrom QP (fun _ => 1) 39 = 0 := orthTab_walk (by decide +kernel)
theorem kCntP_40 : walkFrom QP (fun _ => 1) 40 = 1152 := orthTab_walk (by decide +kernel)
theorem kCntP_41 : walkFrom QP (fun _ => 1) 41 = 0 := orthTab_walk (by decide +kernel)
theorem kCntP_42 : walkFrom QP (fun _ => 1) 42 = 1152 := orthTab_walk (by decide +kernel)
theorem kCntP_43 : walkFrom QP (fun _ => 1) 43 = 0 := orthTab_walk (by decide +kernel)
theorem kCntP_44 : walkFrom QP (fun _ => 1) 44 = 0 := orthTab_walk (by decide +kernel)
theorem kCntP_45 : walkFrom QP (fun _ => 1) 45 = 1152 := orthTab_walk (by decide +kernel)
theorem kCntP_46 : walkFrom QP (fun _ => 1) 46 = 0 := orthTab_walk (by decide +kernel)
theorem kCntP_47 : walkFrom QP (fun _ => 1) 47 = 1152 := orthTab_walk (by decide +kernel)
theorem kCntP_48 : walkFrom QP (fun _ => 1) 48 = 1152 := orthTab_walk (by decide +kernel)
theorem kCntP_49 : walkFrom QP (fun _ => 1) 49 = 0 := orthTab_walk (by decide +kernel)
theorem kCntP_50 : walkFrom QP (fun _ => 1) 50 = 0 := orthTab_walk (by decide +kernel)
theorem kCntP_51 : walkFrom QP (fun _ => 1) 51 = 1152 := orthTab_walk (by decide +kernel)
theorem kCntP_52 : walkFrom QP (fun _ => 1) 52 = 1152 := orthTab_walk (by decide +kernel)
theorem kCntP_53 : walkFrom QP (fun _ => 1) 53 = 0 := orthTab_walk (by decide +kernel)
theorem kCntP_54 : walkFrom QP (fun _ => 1) 54 = 0 := orthTab_walk (by decide +kernel)
theorem kCntP_55 : walkFrom QP (fun _ => 1) 55 = 1152 := orthTab_walk (by decide +kernel)
theorem kCntP_56 : walkFrom QP (fun _ => 1) 56 = 1152 := orthTab_walk (by decide +kernel)
theorem kCntP_57 : walkFrom QP (fun _ => 1) 57 = 0 := orthTab_walk (by decide +kernel)
theorem kCntP_58 : walkFrom QP (fun _ => 1) 58 = 0 := orthTab_walk (by decide +kernel)
theorem kCntP_59 : walkFrom QP (fun _ => 1) 59 = 1152 := orthTab_walk (by decide +kernel)
theorem kCntP_60 : walkFrom QP (fun _ => 1) 60 = 0 := orthTab_walk (by decide +kernel)
theorem kCntP_61 : walkFrom QP (fun _ => 1) 61 = 1152 := orthTab_walk (by decide +kernel)
theorem kCntP_62 : walkFrom QP (fun _ => 1) 62 = 1152 := orthTab_walk (by decide +kernel)
theorem kCntP_63 : walkFrom QP (fun _ => 1) 63 = 0 := orthTab_walk (by decide +kernel)

theorem kCntP : ∀ c < 64, walkFrom QP (fun _ => 1) c = LP.getD c 0 := by
  intro c hc
  interval_cases c
  exacts [kCntP_0, kCntP_1, kCntP_2, kCntP_3, kCntP_4, kCntP_5, kCntP_6, kCntP_7, kCntP_8, kCntP_9, kCntP_10, kCntP_11,
    kCntP_12, kCntP_13, kCntP_14, kCntP_15, kCntP_16, kCntP_17, kCntP_18, kCntP_19, kCntP_20, kCntP_21, kCntP_22, kCntP_23,
    kCntP_24, kCntP_25, kCntP_26, kCntP_27, kCntP_28, kCntP_29, kCntP_30, kCntP_31, kCntP_32, kCntP_33, kCntP_34, kCntP_35,
    kCntP_36, kCntP_37, kCntP_38, kCntP_39, kCntP_40, kCntP_41, kCntP_42, kCntP_43, kCntP_44, kCntP_45, kCntP_46, kCntP_47,
    kCntP_48, kCntP_49, kCntP_50, kCntP_51, kCntP_52, kCntP_53, kCntP_54, kCntP_55, kCntP_56, kCntP_57, kCntP_58, kCntP_59,
    kCntP_60, kCntP_61, kCntP_62, kCntP_63]

theorem kInvP : ∀ c < 64, walkFrom QP invBadK c = 0 := walkFrom_invBadK qBind_plus

theorem kCntM_0 : walkFrom QM (fun _ => 1) 0 = 0 := walkFrom_zero_o8
theorem kCntM_1 : walkFrom QM (fun _ => 1) 1 = 1920 := orthTab_walk (by decide +kernel)
theorem kCntM_2 : walkFrom QM (fun _ => 1) 2 = 1920 := orthTab_walk (by decide +kernel)
theorem kCntM_3 : walkFrom QM (fun _ => 1) 3 = 1920 := orthTab_walk (by decide +kernel)
theorem kCntM_4 : walkFrom QM (fun _ => 1) 4 = 0 := orthTab_walk (by decide +kernel)
theorem kCntM_5 : walkFrom QM (fun _ => 1) 5 = 0 := orthTab_walk (by decide +kernel)
theorem kCntM_6 : walkFrom QM (fun _ => 1) 6 = 0 := orthTab_walk (by decide +kernel)
theorem kCntM_7 : walkFrom QM (fun _ => 1) 7 = 0 := orthTab_walk (by decide +kernel)
theorem kCntM_8 : walkFrom QM (fun _ => 1) 8 = 0 := orthTab_walk (by decide +kernel)
theorem kCntM_9 : walkFrom QM (fun _ => 1) 9 = 0 := orthTab_walk (by decide +kernel)
theorem kCntM_10 : walkFrom QM (fun _ => 1) 10 = 0 := orthTab_walk (by decide +kernel)
theorem kCntM_11 : walkFrom QM (fun _ => 1) 11 = 0 := orthTab_walk (by decide +kernel)
theorem kCntM_12 : walkFrom QM (fun _ => 1) 12 = 0 := orthTab_walk (by decide +kernel)
theorem kCntM_13 : walkFrom QM (fun _ => 1) 13 = 0 := orthTab_walk (by decide +kernel)
theorem kCntM_14 : walkFrom QM (fun _ => 1) 14 = 0 := orthTab_walk (by decide +kernel)
theorem kCntM_15 : walkFrom QM (fun _ => 1) 15 = 0 := orthTab_walk (by decide +kernel)
theorem kCntM_16 : walkFrom QM (fun _ => 1) 16 = 1920 := orthTab_walk (by decide +kernel)
theorem kCntM_17 : walkFrom QM (fun _ => 1) 17 = 1920 := orthTab_walk (by decide +kernel)
theorem kCntM_18 : walkFrom QM (fun _ => 1) 18 = 0 := orthTab_walk (by decide +kernel)
theorem kCntM_19 : walkFrom QM (fun _ => 1) 19 = 0 := orthTab_walk (by decide +kernel)
theorem kCntM_20 : walkFrom QM (fun _ => 1) 20 = 0 := orthTab_walk (by decide +kernel)
theorem kCntM_21 : walkFrom QM (fun _ => 1) 21 = 0 := orthTab_walk (by decide +kernel)
theorem kCntM_22 : walkFrom QM (fun _ => 1) 22 = 1920 := orthTab_walk (by decide +kernel)
theorem kCntM_23 : walkFrom QM (fun _ => 1) 23 = 1920 := orthTab_walk (by decide +kernel)
theorem kCntM_24 : walkFrom QM (fun _ => 1) 24 = 0 := orthTab_walk (by decide +kernel)
theorem kCntM_25 : walkFrom QM (fun _ => 1) 25 = 0 := orthTab_walk (by decide +kernel)
theorem kCntM_26 : walkFrom QM (fun _ => 1) 26 = 1920 := orthTab_walk (by decide +kernel)
theorem kCntM_27 : walkFrom QM (fun _ => 1) 27 = 1920 := orthTab_walk (by decide +kernel)
theorem kCntM_28 : walkFrom QM (fun _ => 1) 28 = 0 := orthTab_walk (by decide +kernel)
theorem kCntM_29 : walkFrom QM (fun _ => 1) 29 = 0 := orthTab_walk (by decide +kernel)
theorem kCntM_30 : walkFrom QM (fun _ => 1) 30 = 1920 := orthTab_walk (by decide +kernel)
theorem kCntM_31 : walkFrom QM (fun _ => 1) 31 = 1920 := orthTab_walk (by decide +kernel)
theorem kCntM_32 : walkFrom QM (fun _ => 1) 32 = 1920 := orthTab_walk (by decide +kernel)
theorem kCntM_33 : walkFrom QM (fun _ => 1) 33 = 0 := orthTab_walk (by decide +kernel)
theorem kCntM_34 : walkFrom QM (fun _ => 1) 34 = 1920 := orthTab_walk (by decide +kernel)
theorem kCntM_35 : walkFrom QM (fun _ => 1) 35 = 0 := orthTab_walk (by decide +kernel)
theorem kCntM_36 : walkFrom QM (fun _ => 1) 36 = 0 := orthTab_walk (by decide +kernel)
theorem kCntM_37 : walkFrom QM (fun _ => 1) 37 = 1920 := orthTab_walk (by decide +kernel)
theorem kCntM_38 : walkFrom QM (fun _ => 1) 38 = 0 := orthTab_walk (by decide +kernel)
theorem kCntM_39 : walkFrom QM (fun _ => 1) 39 = 1920 := orthTab_walk (by decide +kernel)
theorem kCntM_40 : walkFrom QM (fun _ => 1) 40 = 0 := orthTab_walk (by decide +kernel)
theorem kCntM_41 : walkFrom QM (fun _ => 1) 41 = 1920 := orthTab_walk (by decide +kernel)
theorem kCntM_42 : walkFrom QM (fun _ => 1) 42 = 0 := orthTab_walk (by decide +kernel)
theorem kCntM_43 : walkFrom QM (fun _ => 1) 43 = 1920 := orthTab_walk (by decide +kernel)
theorem kCntM_44 : walkFrom QM (fun _ => 1) 44 = 0 := orthTab_walk (by decide +kernel)
theorem kCntM_45 : walkFrom QM (fun _ => 1) 45 = 1920 := orthTab_walk (by decide +kernel)
theorem kCntM_46 : walkFrom QM (fun _ => 1) 46 = 0 := orthTab_walk (by decide +kernel)
theorem kCntM_47 : walkFrom QM (fun _ => 1) 47 = 1920 := orthTab_walk (by decide +kernel)
theorem kCntM_48 : walkFrom QM (fun _ => 1) 48 = 1920 := orthTab_walk (by decide +kernel)
theorem kCntM_49 : walkFrom QM (fun _ => 1) 49 = 0 := orthTab_walk (by decide +kernel)
theorem kCntM_50 : walkFrom QM (fun _ => 1) 50 = 0 := orthTab_walk (by decide +kernel)
theorem kCntM_51 : walkFrom QM (fun _ => 1) 51 = 1920 := orthTab_walk (by decide +kernel)
theorem kCntM_52 : walkFrom QM (fun _ => 1) 52 = 0 := orthTab_walk (by decide +kernel)
theorem kCntM_53 : walkFrom QM (fun _ => 1) 53 = 1920 := orthTab_walk (by decide +kernel)
theorem kCntM_54 : walkFrom QM (fun _ => 1) 54 = 1920 := orthTab_walk (by decide +kernel)
theorem kCntM_55 : walkFrom QM (fun _ => 1) 55 = 0 := orthTab_walk (by decide +kernel)
theorem kCntM_56 : walkFrom QM (fun _ => 1) 56 = 0 := orthTab_walk (by decide +kernel)
theorem kCntM_57 : walkFrom QM (fun _ => 1) 57 = 1920 := orthTab_walk (by decide +kernel)
theorem kCntM_58 : walkFrom QM (fun _ => 1) 58 = 1920 := orthTab_walk (by decide +kernel)
theorem kCntM_59 : walkFrom QM (fun _ => 1) 59 = 0 := orthTab_walk (by decide +kernel)
theorem kCntM_60 : walkFrom QM (fun _ => 1) 60 = 0 := orthTab_walk (by decide +kernel)
theorem kCntM_61 : walkFrom QM (fun _ => 1) 61 = 1920 := orthTab_walk (by decide +kernel)
theorem kCntM_62 : walkFrom QM (fun _ => 1) 62 = 1920 := orthTab_walk (by decide +kernel)
theorem kCntM_63 : walkFrom QM (fun _ => 1) 63 = 0 := orthTab_walk (by decide +kernel)

theorem kCntM : ∀ c < 64, walkFrom QM (fun _ => 1) c = LM.getD c 0 := by
  intro c hc
  interval_cases c
  exacts [kCntM_0, kCntM_1, kCntM_2, kCntM_3, kCntM_4, kCntM_5, kCntM_6, kCntM_7, kCntM_8, kCntM_9, kCntM_10, kCntM_11,
    kCntM_12, kCntM_13, kCntM_14, kCntM_15, kCntM_16, kCntM_17, kCntM_18, kCntM_19, kCntM_20, kCntM_21, kCntM_22, kCntM_23,
    kCntM_24, kCntM_25, kCntM_26, kCntM_27, kCntM_28, kCntM_29, kCntM_30, kCntM_31, kCntM_32, kCntM_33, kCntM_34, kCntM_35,
    kCntM_36, kCntM_37, kCntM_38, kCntM_39, kCntM_40, kCntM_41, kCntM_42, kCntM_43, kCntM_44, kCntM_45, kCntM_46, kCntM_47,
    kCntM_48, kCntM_49, kCntM_50, kCntM_51, kCntM_52, kCntM_53, kCntM_54, kCntM_55, kCntM_56, kCntM_57, kCntM_58, kCntM_59,
    kCntM_60, kCntM_61, kCntM_62, kCntM_63]

theorem kInvM : ∀ c < 64, walkFrom QM invBadK c = 0 := walkFrom_invBadK qBind_minus

end CertificateChecks.KernelO8

end
