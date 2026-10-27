module

public import Certificates.Kernel.GH74.J2CentEAK
public import Certificates.Kernel.GH74.J2CentI
public import Certificates.Kernel.GH74.J2EvG
public import Certificates.Data.J2CentEACheck

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGH74.J2CentEA

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.GH74
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native
open CFSG.GH74.Generic.S45.EvSpor CertificateChecks.KernelGH74
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.J2Cn
open CertificateChecks.KernelGH74.J2CentE CertificateChecks.KernelGH74.J2Ev CFSG.Sporadic.J2

@[simp] theorem fB_eq (y : Nat) (k : Nat → Bool) : fB y k = k y := by cases y <;> rfl

@[simp] theorem orB_eq (x y : Bool) : orB x y = (x || y) := by cases x <;> rfl

@[simp] theorem andB_eq (x y : Bool) : andB x y = (x && y) := by cases x <;> rfl

@[simp] theorem notB_eq (x : Bool) : notB x = !x := by cases x <;> rfl

theorem allR_spec {n : Nat} {g : Nat → Bool} (h : allR n g = true) : ∀ k < n, g k = true := by
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    intro k hk
    change Bool.rec false (allR n g) (g n) = true at h
    cases hg : g n
    · rw [hg] at h
      exact absurd h Bool.false_ne_true
    · rw [hg] at h
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact ih h k hk
      · exact hg

theorem anyR_spec {n : Nat} {g : Nat → Bool} (h : anyR n g = true) : ∃ k < n, g k = true := by
  induction n with
  | zero => exact absurd h Bool.false_ne_true
  | succ n ih =>
    change Bool.rec (anyR n g) true (g n) = true at h
    cases hg : g n
    · rw [hg] at h
      obtain ⟨k, hk, h⟩ := ih h
      exact ⟨k, by omega, h⟩
    · exact ⟨n, by omega, hg⟩

theorem any_hRec_of {n w cnt : Nat} {T PL : Nat → Nat} {p : Table → Bool}
    (h : ∃ i < cnt, p (tabT (unpack n w (T i))) = true) : (hRec n w cnt T PL).1.any p = true := by
  obtain ⟨i, hi, h⟩ := h
  rw [Array.any_eq_true]
  exact ⟨i, by simpa [hRec] using hi, by simpa [hRec] using h⟩

theorem mem_hRec {n w cnt : Nat} {T PL : Nat → Nat} {x : Table} (h : x ∈ (hRec n w cnt T PL).1) :
    ∃ i < cnt, x = tabT (unpack n w (T i)) := by
  simp only [hRec, Array.mem_ofFn] at h
  obtain ⟨i, rfl⟩ := h
  exact ⟨i, i.2, rfl⟩

theorem comm_at {k : Nat} (hk : k < J2C2.cnt) : commSqAt (J2C2.T k) = true := by
  have hc : J2C2.cnt = 1920 := rfl
  rcases (by omega : k < 640 ∨ (640 ≤ k ∧ k < 1280) ∨ (1280 ≤ k ∧ k < 1920)) with h | h | h
  · have h1 := allR_spec comm_0 k h
    rw [fB_eq, Nat.add_eq, Nat.zero_add] at h1
    exact h1
  · have h1 := allR_spec comm_1 (k - 640) (by omega)
    have e : Nat.add 640 (k - 640) = k := by
      rw [Nat.add_eq]
      omega
    rw [fB_eq, e] at h1
    exact h1
  · have h1 := allR_spec comm_2 (k - 1280) (by omega)
    have e : Nat.add 1280 (k - 1280) = k := by
      rw [Nat.add_eq]
      omega
    rw [fB_eq, e] at h1
    exact h1

theorem commSq_ok : j2CommSqOK = true := by
  unfold j2CommSqOK
  rw [c2_arr, all_hRec_iff]
  intro k hk
  have hG := c2c hk
  have hs := comm_at hk
  rw [involF hG]
  unfold commSqAt at hs
  simp only [orB_eq, andB_eq, notB_eq, Bool.or_eq_true, Bool.and_eq_true,
    Bool.not_eq_true'] at hs
  rcases hs with h1 | h2 | ⟨hinv, hsq⟩
  · simp [h1]
  · obtain ⟨i, hi, he⟩ := anyR_spec h2
    have hm : memT 315 j2E (tabT (unpack 315 9 (J2C2.T k))) = true := by
      unfold memT
      rw [J2CentE.e_arr]
      refine any_hRec_of ⟨i, by rw [e_cnt]; exact hi, ?_⟩
      rw [tblEq_unpack hG (eT32 hi)]
      exact he
    simp [hm]
  · obtain ⟨i, hi, hc⟩ := anyR_spec hsq
    simp only [notB_eq, fB_eq, Bool.not_eq_true'] at hc
    have hEi := eT32 hi
    have hAi : canonK 315 9 (mask 9) (315 * 9) (J2EAI i) = true := (efacts.2.2 i hi).1
    have hC := CFSG.KC.BfsPin.canonK_pcomp (CFSG.KC.BfsPin.canonK_pcomp hEi hG) (CFSG.KC.BfsPin.canonK_pcomp hAi hG)
    have hany : (j2E.any fun e => !tblEq 315 (commSqT e (tabT (unpack 315 9 (J2C2.T k))))
        (idT 315)) = true := by
      rw [J2CentE.e_arr]
      refine any_hRec_of ⟨i, by rw [e_cnt]; exact hi, ?_⟩
      unfold commSqT commutatorT
      rw [eAI_tab hi, invT_unpack (by norm_num) hinv, compT_unpack hEi hG, compT_unpack hAi hG,
        compT_unpack (CFSG.KC.BfsPin.canonK_pcomp hEi hG) (CFSG.KC.BfsPin.canonK_pcomp hAi hG), compT_unpack hC hC, hid,
        tblEq_unpack (CFSG.KC.BfsPin.canonK_pcomp hC hC) hidc, Bool.not_eq_true']
      exact hc
    simp [hany]

theorem rankK_ok' : j2ERankOK = true := by
  have hM := rank_ok
  rw [fB_eq, andB_eq, Bool.and_eq_true] at hM
  obtain ⟨hm, hr⟩ := hM
  generalize invMask J2E.T 32 = M at hm hr
  have hmask : ∀ i < 32, involK (J2E.T i) = true → bitB M i = true := fun i hi h => by
    have := allR_spec hm i hi
    simp only [orB_eq, notB_eq, Bool.or_eq_true, Bool.not_eq_true'] at this
    rcases this with h' | h'
    · rw [h] at h'
      exact Bool.noConfusion h'
    · exact h'
  have hR3 : ∀ a < 32, ∀ b < 32, ∀ c < 32, involK (J2E.T a) = true → involK (J2E.T b) = true →
      involK (J2E.T c) = true → J2Cn.commK (J2E.T a) (J2E.T b) = true →
      rankZ (J2E.T a) (J2E.T b) (J2E.T c) = true := by
    intro a ha b hb c hc hia hib hic hab
    have h1 := allR_spec hr a ha
    simp only [orB_eq, notB_eq, fB_eq, hmask a ha hia, Bool.not_true, Bool.false_or] at h1
    have h2 := allR_spec h1 b hb
    simp only [orB_eq, notB_eq, fB_eq, hmask b hb hib, hab, Bool.not_true, Bool.false_or] at h2
    have h3 := allR_spec h2 c hc
    simp only [orB_eq, notB_eq, fB_eq, hmask c hc hic, Bool.not_true, Bool.false_or] at h3
    exact h3
  unfold j2ERankOK j2EInvs
  rw [J2CentE.e_arr, Array.all_eq_true']
  intro x hx
  rw [Array.mem_filter] at hx
  rw [Array.all_eq_true']
  intro y hy
  rw [Array.mem_filter] at hy
  rw [Array.all_eq_true']
  intro z hz
  rw [Array.mem_filter] at hz
  obtain ⟨a, ha, rfl⟩ := mem_hRec hx.1
  obtain ⟨b, hb, rfl⟩ := mem_hRec hy.1
  obtain ⟨c, hc, rfl⟩ := mem_hRec hz.1
  rw [e_cnt] at ha hb hc
  have ca := eT32 ha
  have cb := eT32 hb
  have cc := eT32 hc
  have hia := hx.2
  have hib := hy.2
  have hic := hz.2
  rw [involF ca] at hia
  rw [involF cb] at hib
  rw [involF cc] at hic
  rw [commF ca cb, commF ca cc, commF cb cc, tblEq_unpack cb ca, tblEq_unpack cc ca,
    tblEq_unpack cc cb, compT_unpack ca cb, tblEq_unpack cc (CFSG.KC.BfsPin.canonK_pcomp ca cb)]
  cases hab : J2Cn.commK (J2E.T a) (J2E.T b)
  · simp
  · have h := hR3 a ha b hb c hc hia hib hic hab
    unfold rankZ at h
    simp only [orB_eq, andB_eq, notB_eq, pc] at h
    revert h
    generalize J2Cn.commK (J2E.T a) (J2E.T c) = p1
    generalize J2Cn.commK (J2E.T b) (J2E.T c) = p2
    generalize Nat.beq (J2E.T b) (J2E.T a) = p3
    generalize Nat.beq (J2E.T c) (J2E.T a) = p4
    generalize Nat.beq (J2E.T c) (J2E.T b) = p5
    generalize Nat.beq (J2E.T c) (pcomp 315 9 (mask 9) (J2E.T a) (J2E.T b)) = p6
    revert p1 p2 p3 p4 p5 p6
    decide

theorem sqB_ok' : j2C2BSqOK = true := by
  unfold j2C2BSqOK
  rw [cb_arr, all_hRec_iff]
  intro k hk
  have hX := penumPt_canon (cb_pe k hk)
  have hk' : k < 240 := by
    have : J2CB.cnt = 240 := rfl
    omega
  have h := allR_spec sqB_ok k hk'
  rw [fB_eq] at h
  rw [powT_unpack (pows _) hid hidc hX 4, powT_unpack (pows _) hid hidc hX 2, hid,
    tblEq_unpack (canonP hX 4) hidc, tblEq_unpack (canonP hX 2) hidc]
  unfold sqBAt isId at h
  simp only [orB_eq, notB_eq] at h
  exact h

theorem check_ok : j2CentEACheck = true := by
  unfold j2CentEACheck
  rw [commSq_ok, rankK_ok', sqB_ok']
  rfl

end CertificateChecks.KernelGH74.J2CentEA
