module

public import Certificates.Kernel.Sporadic.ON.Final
public import CFSG.Certificates.Kernel.Spor.ONVecSound
public import CFSG.Certificates.Kernel.Spor.PWord
public import CFSG.Certificates.Kernel.Spor.ChainKGen
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.ONMvSound
public import CFSG.Certificates.Kernel.Spor.ONSplitSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONVec

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.Sporadic.ON.Native CFSG.ONSchreier.Native
open CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.ON (TT UU)

@[expose] noncomputable def TTA : Array (Array Nat) :=
  Array.ofFn (n := 7) fun j => Array.ofFn (n := 245520) fun i => TT j.val i.val

theorem TTA_size : TTA.size = 7 := by
  unfold TTA
  exact Array.size_ofFn

theorem TTA_get {j : Nat} (hj : j < 7) : TTA[j]! = Array.ofFn (n := 245520) fun i => TT j i.val := by
  unfold TTA
  rw [getElem!_ofFn' hj]

theorem ofFn_get2 {j x : Nat} (hj : j < 7) (hx : x < 245520) : (TTA[j]!)[x]! = TT j x := by
  rw [TTA_get hj, getElem!_ofFn' hx]

theorem allBelowN_of {n : Nat} {p : Nat → Bool} (h : ∀ i < n, p i = true) : allBelowN n p = true := by
  unfold allBelowN
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  intro ⟨i, hi⟩ _
  exact h i hi

theorem pinvs_TTA : ∀ j < 7, ∀ x < 245520, ((pinvs 245520 TTA)[j]!)[x]! = UU j x :=
  CFSG.KS.CH.pinvs_get (n := 245520) (s := 7) TTA_size fun j hj x hx =>
    ⟨ofFn_get2 hj hx, (ON.perm_facts' x hx j hj).1, (ON.perm_facts' x hx j hj).2.1,
      (ON.perm_facts' x hx j hj).2.2⟩

theorem letters_TTA : CFSG.KS.PW.LettersOK 245520 7 TTA (pinvs 245520 TTA) TT UU :=
  fun j hj x hx => ⟨ofFn_get2 hj hx, pinvs_TTA j hj x hx, (ON.perm_facts' x hx j hj).1,
    (ON.perm_facts' x hx j hj).2.1⟩

theorem tr_word {x : Nat} (hx : x < 245520) {j : Nat} (hj : j < 7) (h2 : 2 ≤ j) :
    TT j x = trace TT UU (ONV.WC j) (ONV.WL j) x := by
  have htr := ON.pt_of ON.trAll (fun _ => rfl) x hx
  unfold trAt at htr
  have hB : allBlk 2 (fun j => Nat.beq (TT j x) (trace TT UU (ONV.WC j) (ONV.WL j) x)) 5 = true :=
    ((bAnd_iff _ _).1 htr).2
  have h3 := allBlk_spec hB (j - 2) (by omega)
  have e2 : Nat.add 2 (j - 2) = j := by
    change 2 + (j - 2) = j
    omega
  rw [e2] at h3
  exact Nat.eq_of_beq_eq_true h3

theorem letterOfCode_encL' {l : Int} (h0 : l ≠ 0) (h8 : l.natAbs ≤ 8) :
    encL l < 16 ∧ CFSG.KS.Words.letterOfCode (encL l) = l := by
  unfold encL CFSG.KS.Words.letterOfCode
  by_cases hp : 0 < l
  · rw [ite_eq_left hp]
    refine ⟨by omega, ?_⟩
    rw [ite_eq_left (by omega)]
    omega
  · rw [ite_eq_right hp]
    refine ⟨by omega, ?_⟩
    rw [ite_eq_right (by omega)]
    omega

theorem encW_lt' : ∀ w : List Int, (∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 8) →
    encW w < 16 ^ w.length
  | [], _ => by simp [encW]
  | l :: w, h => by
    have ih := encW_lt' w fun z hz => h z (List.mem_cons_of_mem l hz)
    have hl := (letterOfCode_encL' (h l List.mem_cons_self).1 (h l List.mem_cons_self).2).1
    simp only [encW, List.length_cons, Nat.pow_succ]
    have : encL l * 16 ^ w.length ≤ 15 * 16 ^ w.length := Nat.mul_le_mul_right _ (by omega)
    omega

theorem shr4' (W k : Nat) : W >>> (4 * k) = W / 16 ^ k := by
  rw [Nat.shiftRight_eq_div_pow, Nat.pow_mul]

theorem decW_congr' {W W' : Nat} : ∀ L, (∀ k < L, (W >>> (4 * k)) % 16 = (W' >>> (4 * k)) % 16) →
    CFSG.KS.Words.decW W L = CFSG.KS.Words.decW W' L
  | 0, _ => rfl
  | L + 1, h => by
    rw [CFSG.KS.Words.decW, CFSG.KS.Words.decW, h L (by omega),
      decW_congr' L fun k hk => h k (by omega)]

theorem decW_encW' : ∀ w : List Int, (∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 8) →
    CFSG.KS.Words.decW (encW w) w.length = w
  | [], _ => rfl
  | l :: w, h => by
    have hw : ∀ z ∈ w, z ≠ 0 ∧ z.natAbs ≤ 8 := fun z hz => h z (List.mem_cons_of_mem l hz)
    obtain ⟨hl, hc⟩ := letterOfCode_encL' (h l List.mem_cons_self).1 (h l List.mem_cons_self).2
    have hlt := encW_lt' w hw
    have hpos : 0 < 16 ^ w.length := Nat.pow_pos (by omega)
    simp only [encW, List.length_cons]
    rw [CFSG.KS.Words.decW]
    congr 1
    · rw [shr4', Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlt, Nat.zero_add,
        Nat.mod_eq_of_lt hl, hc]
    · rw [decW_congr' (W' := encW w) w.length fun k hk => ?_]
      · exact decW_encW' w hw
      · rw [shr4', shr4']
        have e : 16 ^ w.length = 16 ^ k * (16 * 16 ^ (w.length - k - 1)) := by
          rw [← Nat.pow_succ', ← Nat.pow_add]
          congr 1
          omega
        have hk' : 0 < 16 ^ k := Nat.pow_pos (by omega)
        have e2 : encL l * 16 ^ w.length = 16 * (encL l * 16 ^ (w.length - k - 1)) * 16 ^ k := by
          rw [e]
          ac_rfl
        rw [e2, Nat.add_mul_div_right _ _ hk', Nat.add_mul_mod_self_left]

theorem peq_ofFn2 {n : Nat} {f g : Nat → Nat} (h : ∀ i < n, f i = g i) :
    peq n (Array.ofFn (n := n) fun i => f i.val) (Array.ofFn (n := n) fun i => g i.val) = true := by
  unfold peq
  refine allBelowN_of fun i hi => ?_
  rw [getElem!_ofFn' hi, getElem!_ofFn' hi]
  dsimp only
  rw [h i hi]
  exact beq_self_eq_true _

end CertificateChecks.KernelSpor.ONVec

end
