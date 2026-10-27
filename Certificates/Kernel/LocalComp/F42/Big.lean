module

public import CFSG.Certificates.Kernel.F42SqSound
public import Certificates.Kernel.LocalComp.F42.Misc
public import Certificates.Kernel.LocalComp.F42.Lev0
public import Certificates.Kernel.LocalComp.F42.Lev1
public import Certificates.Kernel.LocalComp.F42.Lev2
public import Certificates.Kernel.LocalComp.F42.Lev3
public import Certificates.Kernel.LocalComp.F42.Lev4
public import Certificates.Kernel.LocalComp.F42.Lev5
public import Certificates.Kernel.LocalComp.F42.Lev6
public import Certificates.Kernel.LocalComp.F42.Lev7
public import Certificates.Kernel.LocalComp.F42.Lev8
public import Certificates.Kernel.LocalComp.F42.Lev9
public import Certificates.Kernel.LocalComp.F42.Lev10
public import Certificates.Kernel.LocalComp.F42.Lev11
public import Certificates.Kernel.LocalComp.F42.Lev12
public import Certificates.Kernel.LocalComp.F42.Lev13
public import Certificates.Kernel.LocalComp.F42.Lev14
public import Certificates.Kernel.LocalComp.F42.Lev15
public import Certificates.Kernel.LocalComp.F42.Lev16
public import Certificates.Kernel.LocalComp.F42.Lev17
public import Certificates.Kernel.LocalComp.F42.Lev18
public import Certificates.Kernel.LocalComp.F42.Lev19
public import Certificates.Kernel.LocalComp.F42.Lev20
public import Certificates.Kernel.LocalComp.F42.Lev21
public import Certificates.Kernel.LocalComp.F42.BfsAll
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.F42

open CFSG.KC.F42 CFSG.EvenSmallLie.FFourTwo

theorem preSq_step {k A nA B nB : ℕ} (h : Pc.preSq cmF 25 k = arrOf A nA)
    (hl : (Pc.extend k (arrOf A nA)).filter (fun q => mulR q q % 2 ^ (k + 1) == 0) = arrOf B nB) :
    Pc.preSq cmF 25 (k + 1) = arrOf B nB := by
  have e : ∀ q, Pc.mul cmF 25 q q = mulR q q := fun q => (mulR_eq q q).symm
  rw [Pc.preSq, h, ← hl]
  simp only [e]

theorem preSq_zero : Pc.preSq cmF 25 0 = arrOf L0 nL0 := by decide +kernel

theorem preSq_eq : Pc.preSq cmF 25 22 = arrOf L22 nL22 := by
  have e0 := preSq_zero
  have e1 := preSq_step e0
    (level_sound (nA := nL0) (nC := 2) rfl q0_0 qn_0 Lev0).1
  have e2 := preSq_step e1
    (level_sound (nA := nL1) (nC := 4) rfl q0_1 qn_1 Lev1).1
  have e3 := preSq_step e2
    (level_sound (nA := nL2) (nC := 8) rfl q0_2 qn_2 Lev2).1
  have e4 := preSq_step e3
    (level_sound (nA := nL3) (nC := 16) rfl q0_3 qn_3 Lev3).1
  have e5 := preSq_step e4
    (level_sound (nA := nL4) (nC := 32) rfl q0_4 qn_4 Lev4).1
  have e6 := preSq_step e5
    (level_sound (nA := nL5) (nC := 48) rfl q0_5 qn_5 Lev5).1
  have e7 := preSq_step e6
    (level_sound (nA := nL6) (nC := 80) rfl q0_6 qn_6 Lev6).1
  have e8 := preSq_step e7
    (level_sound (nA := nL7) (nC := 128) rfl q0_7 qn_7 Lev7).1
  have e9 := preSq_step e8
    (level_sound (nA := nL8) (nC := 192) rfl q0_8 qn_8 Lev8).1
  have e10 := preSq_step e9
    (level_sound (nA := nL9) (nC := 384) rfl q0_9 qn_9 Lev9).1
  have e11 := preSq_step e10
    (level_sound (nA := nL10) (nC := 576) rfl q0_10 qn_10 Lev10).1
  have e12 := preSq_step e11
    (level_sound (nA := nL11) (nC := 768) rfl q0_11 qn_11 Lev11).1
  have e13 := preSq_step e12
    (level_sound (nA := nL12) (nC := 1152) rfl q0_12 qn_12 Lev12).1
  have e14 := preSq_step e13
    (level_sound (nA := nL13) (nC := 2048) rfl q0_13 qn_13 Lev13).1
  have e15 := preSq_step e14
    (level_sound (nA := nL14) (nC := 4096) rfl q0_14 qn_14 Lev14).1
  have e16 := preSq_step e15
    (level_sound (nA := nL15) (nC := 6144) rfl q0_15 qn_15 Lev15).1
  have e17 := preSq_step e16
    (level_sound (nA := nL16) (nC := 9216) rfl q0_16 qn_16 Lev16).1
  have e18 := preSq_step e17
    (level_sound (nA := nL17) (nC := 16896) rfl q0_17 qn_17 Lev17).1
  have e19 := preSq_step e18
    (level_sound (nA := nL18) (nC := 22016) rfl q0_18 qn_18 Lev18).1
  have e20 := preSq_step e19
    (level_sound (nA := nL19) (nC := 36352) rfl q0_19 qn_19 Lev19).1
  have e21 := preSq_step e20
    (level_sound (nA := nL20) (nC := 43520) rfl q0_20 qn_20 Lev20).1
  have e22 := preSq_step e21
    (level_sound (nA := nL21) (nC := 66048) rfl q0_21 qn_21 Lev21).1
  exact e22

theorem sq_last (a : ℕ) (ha : a < nL22) :
    mulR (fldW L22 22 a) (fldW L22 22 a) = fldW S 3 a * 2 ^ 22 := by
  obtain ⟨h1, h2⟩ :=
    (level_sound (nA := nL21) (nC := 66048) rfl q0_21 qn_21 Lev21).2 a ha
  have h3 := h2 rfl
  rw [Nat.shiftRight_eq_div_pow] at h3
  have := Nat.div_add_mod (mulR (fldW L22 22 a) (fldW L22 22 a)) (2 ^ 22)
  rw [h3, h1] at this
  omega

theorem cnt0 : Nat.beq (cntL S nL22 0) (sqCounts.getD 0 0) = true := by
  quickRfl

theorem cnt1 : Nat.beq (cntL S nL22 1) (sqCounts.getD 1 0) = true := by
  quickRfl

theorem cnt2 : Nat.beq (cntL S nL22 2) (sqCounts.getD 2 0) = true := by
  quickRfl

theorem cnt3 : Nat.beq (cntL S nL22 3) (sqCounts.getD 3 0) = true := by
  quickRfl

theorem cnt4 : Nat.beq (cntL S nL22 4) (sqCounts.getD 4 0) = true := by
  quickRfl

theorem cnt5 : Nat.beq (cntL S nL22 5) (sqCounts.getD 5 0) = true := by
  quickRfl

theorem cnt6 : Nat.beq (cntL S nL22 6) (sqCounts.getD 6 0) = true := by
  quickRfl

theorem cnt7 : Nat.beq (cntL S nL22 7) (sqCounts.getD 7 0) = true := by
  quickRfl

theorem cnt_ok : ∀ c < 8, cntL S nL22 c = sqCounts.getD c 0 := by
  intro c hc
  interval_cases c
  exacts [Nat.eq_of_beq_eq_true cnt0, Nat.eq_of_beq_eq_true cnt1,
    Nat.eq_of_beq_eq_true cnt2, Nat.eq_of_beq_eq_true cnt3, Nat.eq_of_beq_eq_true cnt4,
    Nat.eq_of_beq_eq_true cnt5, Nat.eq_of_beq_eq_true cnt6, Nat.eq_of_beq_eq_true cnt7]

theorem sq_ok : ∀ c < 8, (Pc.preSq cmF 25 22).toList.countP (fun p => mulU p p == c * 2 ^ 22) =
    sqCounts.getD c 0 := by
  intro c hc
  have e : ∀ p, mulU p p = mulR p p := fun p => (mulR_eq p p).symm
  simp only [preSq_eq, e]
  rw [countP_eq_cntL sq_last c]
  exact cnt_ok c hc

theorem isRep_mem {p : ℕ} (h : isRep p = true) : p ∈ compReps := by
  have key : ∀ l : List ℕ, List.rec (motive := fun _ => Bool) false
      (fun a _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq a p)) l = true →
      p ∈ l := by
    intro l
    induction l with
    | nil => intro h; exact (Bool.false_ne_true h).elim
    | cons a l ih =>
      intro h
      change Bool.rec (motive := fun _ => Bool) (List.rec (motive := fun _ => Bool) false
        (fun a _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq a p)) l) true
        (Nat.beq a p) = true at h
      cases hb : Nat.beq a p
      · rw [hb] at h
        exact List.mem_cons_of_mem a (ih h)
      · exact (Nat.eq_of_beq_eq_true hb) ▸ List.mem_cons_self
  have hl : compReps.toList = crL := by decide +kernel
  rw [← Array.mem_toList_iff, hl]
  exact key crL h

theorem rmOK_mem {m : ℕ} (h : rmOK m = true) : m ∈ rMoves := by
  unfold rmOK at h
  cases h4 : Nat.blt m 4
  · rw [h4] at h
    cases h5 : Nat.beq m 5
    · rw [h5] at h
      rw [Nat.beq_eq] at h
      subst h
      decide
    · rw [Nat.beq_eq] at h5
      subst h5
      decide
  · have : m < 4 := Nat.blt_eq ▸ h4
    interval_cases m <;> decide

theorem bfs_ok : ∃ d : ℕ → ℕ, ∀ p ∈ invCosets (Pc.preSq cmF 25 22), p ∈ compReps ∨
    ∃ m ∈ rMoves, mvOK m p = true ∧ mv m p % 2 ^ 22 ≠ 0 ∧
      d (mv m p % 2 ^ 22) + 1 = d p := by
  refine ⟨dOf L22 D nL22, fun p hp => ?_⟩
  have hnd : (arrOf L22 nL22).toList.Nodup := preSq_eq ▸ (Pc.preSq_spec cmF 25 22).2
  rw [preSq_eq, invCosets, Array.mem_filter] at hp
  obtain ⟨hm, hq⟩ := hp
  rw [arrOf, Array.mem_ofFn] at hm
  obtain ⟨⟨i, hi⟩, rfl⟩ := hm
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hq
  obtain ⟨hp0, hsq⟩ := hq
  have hS : fldW S 3 i = 0 := by
    have := sq_last i hi
    rw [← mulR_eq] at hsq
    rw [hsq] at this
    omega
  rcases bfs_sound hnd bfsAll i hi hS hp0 with h | ⟨m, h1, h2, h3, h4⟩
  · exact Or.inl (isRep_mem h)
  · refine Or.inr ⟨m, rmOK_mem h1, h2, ?_, ?_⟩
    · rwa [← mvR_eq]
    · rwa [← mvR_eq]

end CertificateChecks.KernelLC.F42

end
