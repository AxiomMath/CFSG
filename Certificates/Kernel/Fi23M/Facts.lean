
module

public import Certificates.Kernel.VecCert.HomBound3
public import Certificates.Kernel.VecCert.WordProg
public import Certificates.Kernel.Fi23M.Data
public import CFSG.Sporadic.Fi23.SetupBase
import Certificates.Kernel.Fi23M.Checks
import Certificates.Kernel.Fi23M.Light
import Certificates.Kernel.Sporadic.Fi23Br.Seed
import CFSG.Certificates.Kernel.Spor.Dec3Sound
import CFSG.Certificates.Kernel.Spor.BytesFSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
import Certificates.Kernel.Sporadic.BrChain
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Certificates.SchreierStabilizerGenerators
public import CFSG.F3.SepSpec
public import CFSG.Sporadic.Fi23.CertificateBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23M

open CFSG.KC.Ord CFSG.KC.WP CFSG.KD.Fi23M CFSG.KS.Mat3 CertificateChecks.KernelHomG
  CertificateChecks.KernelHom3 CertificateChecks.KernelWP CFSG.Sporadic.Fi23

open CFSG.Sporadic.Fi23.Native (dWord eWord)

theorem hs : LayoutSound (Canon3 64009) (mat3 253 64009) MUL VLD ONE := layout3 consts

theorem hroot : rootsOK RB VLD 1 (2 + 1) = true := hroots

theorem recAnd {f : Nat → Bool} : ∀ n, (∀ g < n, f g = true) →
    Nat.rec (motive := fun _ => Bool) true (fun g ih => andB ih (f g)) n = true
  | 0, _ => rfl
  | n + 1, h => by
    change andB (Nat.rec (motive := fun _ => Bool) true (fun g ih => andB ih (f g)) n) (f n) = true
    rw [recAnd n (fun g hg => h g (by omega)), h n (by omega)]
    rfl

theorem all2 {p : Nat → Prop} (h0 : p (nat_lit 0)) (h1 : p (nat_lit 1)) : ∀ g < 2, p g := by
  intro g hg
  interval_cases g
  · exact h0
  · exact h1

theorem invsOK_of {RB' : Nat → Nat} {mul : Nat → Nat → Nat} {vld : Nat → Bool} {L ONE' : Nat}
    (h : ∀ g < L, andB (vld (RB' (Nat.add (Nat.succ L) g)))
      (Nat.beq (mul (RB' (Nat.succ g)) (RB' (Nat.add (Nat.succ L) g))) ONE') = true) :
    invsOK RB' mul vld L ONE' = true :=
  recAnd L h

theorem hinv : invsOK RB MUL VLD (nat_lit 2) ONE = true :=
  invsOK_of (all2 (p := fun g => andB (VLD (RB (Nat.add (Nat.succ (nat_lit 2)) g)))
    (Nat.beq (MUL (RB (Nat.succ g)) (RB (Nat.add (Nat.succ (nat_lit 2)) g))) ONE) = true) iv0 iv1)

theorem seed3_sound1 {d f N LO RM CI ONE UP lb len M St : Nat} {F : Nat → Nat}
    {cs : List Char} {Cs : List Nat}
    (hr : Nat.beq (decRun3 F lb len d N RM M Cs (nat_lit 1)) St = true)
    (hd : seedDone d (valid3 N LO) M St = true)
    (hc : consts3OK d f N LO RM CI ONE UP = true)
    (hb : CFSG.KS.Bytes.bytesEqK cs F lb len = true)
    (hCs : Cs = List.range ((len + lb - 1) / lb)) :
    CFSG.Blueprint.NativeSporadic.decode 3 d 1 (String.ofList cs) = mat3 d N M :=
  CFSG.KS.Dec3.seed3_sound hc hb hCs hr hd

theorem vld1 : VLD (RB 1) = true := by quickRfl

theorem vld2 : VLD (RB 2) = true := by quickRfl

theorem canon_RB1 : Canon3 64009 (RB 1) := hs.vld_q _ vld1

theorem canon_RB2 : Canon3 64009 (RB 2) := hs.vld_q _ vld2

theorem mA_eq : mA = mat3 253 64009 (RB 1) := by
  have hr := CertificateChecks.KernelSpor.BrChain.run_chain_to
      (run := decRun3 CFSG.KD.BrFi23.P1 256 65042 253 64009 RM (RB 1)) (fun _ => rfl)
      (fun l₁ l₂ s => CFSG.KS.Dec3.decRun3_append _ _ _ _ _ _ _ l₁ l₂ s) dL (fun k => DA1.getD k 0) 8
      (nat_lit 1) (nat_lit 256039) rfl rfl D1.all
  have h := seed3_sound1 hr d1_end consts
    (CFSG.KS.Bytes.bytesEqK_of_runF (by decide) CFSG.KD.BrFi23.seed1_run) (by decide +kernel)
  change CFSG.Blueprint.NativeSporadic.decode 3 253 1 CFSG.Blueprint.NativeSporadic.Fi23Seed1 = _
  rw [← CFSG.Sporadic.Fi23.seedA_eq, CFSG.KD.BrFi23.Fi23SeedA.eq, h]

theorem mB_eq : mB = mat3 253 64009 (RB 2) := by
  have hr := CertificateChecks.KernelSpor.BrChain.run_chain_to
      (run := decRun3 CFSG.KD.BrFi23.P2 256 65042 253 64009 RM (RB 2)) (fun _ => rfl)
      (fun l₁ l₂ s => CFSG.KS.Dec3.decRun3_append _ _ _ _ _ _ _ l₁ l₂ s) dL (fun k => DA2.getD k 0) 8
      (nat_lit 1) (nat_lit 256039) rfl rfl D2.all
  have h := seed3_sound1 hr d2_end consts
    (CFSG.KS.Bytes.bytesEqK_of_runF (by decide) CFSG.KD.BrFi23.seed2_run) (by decide +kernel)
  change CFSG.Blueprint.NativeSporadic.decode 3 253 1 CFSG.Blueprint.NativeSporadic.Fi23Seed2 = _
  rw [← CFSG.Sporadic.Fi23.seedB_eq, CFSG.KD.BrFi23.Fi23SeedB.eq, h]

theorem RB4_eq : mat3 253 64009 (RB 4) = mB * mB := by
  have e : MUL (RB 2) (RB 2) = RB 4 := Nat.eq_of_beq_eq_true b2
  rw [← e, (hs.mul_sound _ _ canon_RB2 canon_RB2).2, ← mB_eq]

theorem let1 : mat3 253 64009 (letM RB 2 (letC 1)) = mA := mA_eq.symm
theorem let0 : mat3 253 64009 (letM RB 2 (letC 0)) = mA := mA_eq.symm
theorem let3 : mat3 253 64009 (letM RB 2 (letC 3)) = mB := mB_eq.symm
theorem let2 : mat3 253 64009 (letM RB 2 (letC 2)) = mB * mB := RB4_eq

@[expose] def cd (x : Nat) : Nat := if x = 0 then 1 else 3

theorem wordMat_cons (c : Nat) (w : List Nat) : wordMat (mat3 253 64009) RB 2 (c :: w) =
    mat3 253 64009 (letM RB 2 (letC c)) * wordMat (mat3 253 64009) RB 2 w := by
  unfold wordMat
  rw [List.map_cons, List.prod_cons]

theorem wordMat_one (c : Nat) :
    wordMat (mat3 253 64009) RB 2 [c] = mat3 253 64009 (letM RB 2 (letC c)) := by
  rw [wordMat_cons, wordMat_nil, mul_one]

theorem wordMat_cd (w : List Nat) (hw : ∀ x ∈ w, x < 2) :
    wordMat (mat3 253 64009) RB 2 (w.map cd) = (w.map genMat).prod := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    rw [List.map_cons, List.map_cons, List.prod_cons, wordMat_cons,
      ih (fun y hy => hw y (List.mem_cons_of_mem _ hy))]
    have hx := hw x List.mem_cons_self
    obtain rfl | rfl : x = 0 ∨ x = 1 := by omega
    · have e : cd 0 = 1 := rfl
      rw [e, let1]
      rfl
    · have e : cd 1 = 3 := rfl
      rw [e, let3]
      rfl

theorem good : ∀ k < 10, Good (Canon3 64009) (mat3 253 64009) RB 2 (RS k) (WC k) := by
  exact states_good hs hroot hinv statesL S.all

theorem rel_one : ∀ j < 5, wordMat (mat3 253 64009) RB 2 (progWord WC (PR j)) = 1 := by
  exact relProgs_one hs hroot hinv good relsL R.all

theorem mat_good (k : Nat) (hk : k < 10) :
    mat3 253 64009 (RS k) = wordMat (mat3 253 64009) RB 2 (WC k) :=
  (good k hk).2

theorem wc1 : WC 1 = (List.replicate 7 (dWord.map cd)).flatten := by decide +kernel
theorem wc2 : WC 2 = eWord.map cd := by decide +kernel
theorem wc3 : WC 3 = [1] ++ WC 1 ++ [0] := by decide +kernel
theorem wc4 : WC 4 = [3] ++ WC 1 ++ [2] := by decide +kernel
theorem wc5 : WC 5 = [3] ++ WC 3 ++ [2] := by decide +kernel
theorem wc6 : WC 6 = [1] ++ WC 4 ++ [0] := by decide +kernel
theorem wc7 : WC 7 = [3] ++ WC 4 ++ [2] := by decide +kernel
theorem wc8 : WC 8 = WC 1 ++ WC 3 := by decide +kernel
theorem wc9 : WC 9 = WC 1 ++ WC 4 := by decide +kernel

theorem mat_D : mat3 253 64009 (RS 1) = mW ^ 7 := by
  rw [mat_good 1 (by norm_num), wc1, wordMat_rep, wordMat_cd _ dWord_lt]

theorem mat_E : mat3 253 64009 (RS 2) = mE := by
  rw [mat_good 2 (by norm_num), wc2, wordMat_cd _ eWord_lt]

theorem mat_conj {k j g g' : Nat} (hk : k < 10) (hj : j < 10) (h : WC k = [g] ++ WC j ++ [g']) :
    mat3 253 64009 (RS k) = mat3 253 64009 (letM RB 2 (letC g)) * mat3 253 64009 (RS j) *
      mat3 253 64009 (letM RB 2 (letC g')) := by
  rw [mat_good k hk, h, wordMat_append, wordMat_append, wordMat_one g, wordMat_one g',
    ← mat_good j hj]

theorem mat_K1 : mat3 253 64009 (RS 3) = mA * mW ^ 7 * mA := by
  rw [mat_conj (by norm_num) (by norm_num) wc3, let1, let0, mat_D]

theorem mat_K2 : mat3 253 64009 (RS 4) = mB * mW ^ 7 * (mB * mB) := by
  rw [mat_conj (by norm_num) (by norm_num) wc4, let3, let2, mat_D]

theorem mat_K3 : mat3 253 64009 (RS 5) = mB * mat3 253 64009 (RS 3) * (mB * mB) := by
  rw [mat_conj (by norm_num) (by norm_num) wc5, let3, let2]

theorem mat_K4 : mat3 253 64009 (RS 6) = mA * mat3 253 64009 (RS 4) * mA := by
  rw [mat_conj (by norm_num) (by norm_num) wc6, let1, let0]

theorem mat_K5 : mat3 253 64009 (RS 7) = mB * mat3 253 64009 (RS 4) * (mB * mB) := by
  rw [mat_conj (by norm_num) (by norm_num) wc7, let3, let2]

theorem mat_P1 : mat3 253 64009 (RS 8) = mW ^ 7 * mat3 253 64009 (RS 3) := by
  rw [mat_good 8 (by norm_num), wc8, wordMat_append, ← mat_good 1 (by norm_num),
    ← mat_good 3 (by norm_num), mat_D]

theorem mat_P2 : mat3 253 64009 (RS 9) = mW ^ 7 * mat3 253 64009 (RS 4) := by
  rw [mat_good 9 (by norm_num), wc9, wordMat_append, ← mat_good 1 (by norm_num),
    ← mat_good 4 (by norm_num), mat_D]

theorem pr0 : progWord WC (PR 0) = [3, 3, 3] := by decide +kernel
theorem pr1 : progWord WC (PR 1) = (List.replicate 5 (WC 2)).flatten := by decide +kernel
theorem pr2 : progWord WC (PR 2) = WC 1 ++ WC 1 := by decide +kernel
theorem pr3 : progWord WC (PR 3) = WC 8 ++ WC 8 := by decide +kernel
theorem pr4 : progWord WC (PR 4) = (List.replicate 3 (WC 9)).flatten := by decide +kernel

theorem canon_one : Canon3 64009 ONE := (one3_sound consts).1

theorem ne_one {X : Nat} (hX : Canon3 64009 X)
    (h : Bool.rec (motive := fun _ => Bool) true false (Nat.beq X ONE) = true) :
    mat3 253 64009 X ≠ 1 := by
  intro e
  rw [← (one3_sound consts).2] at e
  have hXO := mat3_inj (by norm_num) hX canon_one e
  rw [hXO, Nat.beq_refl] at h
  exact absurd h (by decide)

theorem A_sq : mA * mA = 1 := by
  obtain ⟨hv, hb⟩ := andB_true3 iv0
  have e : MUL (RB 1) (RB 3) = ONE := Nat.eq_of_beq_eq_true hb
  have c3 : Canon3 64009 (RB 3) := hs.vld_q _ hv
  have h := (hs.mul_sound _ _ canon_RB1 c3).2
  rw [e, (one3_sound consts).2] at h
  have e3 : RB 3 = RB 1 := rfl
  rw [e3] at h
  rw [mA_eq]
  exact h.symm

theorem matrixFacts : MatrixFacts := by
  refine ⟨A_sq, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := rel_one 0 (by norm_num)
    rw [pr0, wordMat_cons, wordMat_cons, wordMat_one, let3] at h
    exact h
  · have h := rel_one 1 (by norm_num)
    rw [pr1, wordMat_rep, ← mat_good 2 (by norm_num), mat_E] at h
    exact h
  · have h := rel_one 2 (by norm_num)
    rw [pr2, wordMat_append, ← mat_good 1 (by norm_num), mat_D] at h
    exact h
  · rw [mA_eq]
    exact ne_one canon_RB1 nA
  · rw [mB_eq]
    exact ne_one canon_RB2 nB
  · rw [← mat_D]
    exact ne_one (good 1 (by norm_num)).1 nD

theorem prodFacts : mat3 253 64009 (RS 8) * mat3 253 64009 (RS 8) = 1 ∧
    mat3 253 64009 (RS 8) ≠ 1 ∧
    mat3 253 64009 (RS 9) * mat3 253 64009 (RS 9) * mat3 253 64009 (RS 9) = 1 ∧
    mat3 253 64009 (RS 9) ≠ 1 := by
  refine ⟨?_, ne_one (good 8 (by norm_num)).1 nP1, ?_, ne_one (good 9 (by norm_num)).1 nP2⟩
  · have h := rel_one 3 (by norm_num)
    rw [pr3, wordMat_append, ← mat_good 8 (by norm_num)] at h
    exact h
  · have h := rel_one 4 (by norm_num)
    rw [pr4, wordMat_rep, ← mat_good 9 (by norm_num), pow_three, ← mul_assoc] at h
    exact h

end CertificateChecks.KernelFi23M

end
