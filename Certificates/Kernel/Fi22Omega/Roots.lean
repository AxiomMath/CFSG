module

public import Certificates.Kernel.Fi22Omega.Orbit
public import CFSG.Monster.B.Fischer.Fi22Faithful
public import CFSG.Certificates.Kernel.Spor.RawTreeDefs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Omega

open Equiv CFSG.KC.Fi22Omega CFSG.KC.Benes CFSG.KC.Enum CFSG.KC.I242 CFSG.KS CFSG.KS.Raw
  CFSG.KC.BfsPin CertificateChecks.KernelI242 CertificateChecks.KernelSpor
  CFSG.Monster.B.Fischer CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Certificates.SetOrbit
open scoped Pointwise

@[expose] noncomputable def letP (s0 s1 : Perm (Fin 3510)) (l : Nat) : Perm (Fin 3510) :=
  Bool.rec (motive := fun _ => Perm (Fin 3510))
    (Bool.rec (motive := fun _ => Perm (Fin 3510))
      (Bool.rec (motive := fun _ => Perm (Fin 3510)) s1⁻¹ s0⁻¹ (Nat.beq l (nat_lit 4)))
      s1 (Nat.beq l (nat_lit 3)))
    s0 (Nat.beq l (nat_lit 2))

@[expose] noncomputable def wordP (s0 s1 : Perm (Fin 3510)) (fuel : Nat) : Nat → Perm (Fin 3510) :=
  Nat.rec (motive := fun _ => Nat → Perm (Fin 3510)) (fun _ => 1)
    (fun _ ih w => Bool.rec (motive := fun _ => Perm (Fin 3510))
      (ih (w / 8) * letP s0 s1 (w % 8 - 1)) 1 (Nat.beq w 0)) fuel

theorem wordPt_succ (A : Nat → Nat) (n w p : Nat) :
    wordPt A (n + 1) w p = Bool.rec (motive := fun _ => Nat)
      (wordPt A n (w / 8) (pg 12 4095 (A (w % 8 - 1)) p)) p (Nat.beq w 0) := rfl

theorem wordP_succ (s0 s1 : Perm (Fin 3510)) (n w : Nat) :
    wordP s0 s1 (n + 1) w = Bool.rec (motive := fun _ => Perm (Fin 3510))
      (wordP s0 s1 n (w / 8) * letP s0 s1 (w % 8 - 1)) 1 (Nat.beq w 0) := rfl

theorem letA_pg {x0 x1 i0 i1 : Nat} {s0 s1 : Perm (Fin 3510)}
    (h0 : ∀ q : Fin 3510, pg 12 4095 x0 q = (s0 q : Nat))
    (h1 : ∀ q : Fin 3510, pg 12 4095 x1 q = (s1 q : Nat))
    (h2 : ∀ q : Fin 3510, pg 12 4095 i0 q = (s0⁻¹ q : Nat))
    (h3 : ∀ q : Fin 3510, pg 12 4095 i1 q = (s1⁻¹ q : Nat)) (l : Nat) (q : Fin 3510) :
    pg 12 4095 (letA x0 x1 i0 i1 l) q = (letP s0 s1 l q : Nat) := by
  unfold letA letP
  cases Nat.beq l (nat_lit 2)
  · cases Nat.beq l (nat_lit 3)
    · cases Nat.beq l (nat_lit 4)
      · exact h3 q
      · exact h2 q
    · exact h1 q
  · exact h0 q

theorem wordPt_eq {A : Nat → Nat} {s0 s1 : Perm (Fin 3510)}
    (hA : ∀ (l : Nat) (q : Fin 3510), pg 12 4095 (A l) q = (letP s0 s1 l q : Nat)) :
    ∀ (n w : Nat) (q : Fin 3510), wordPt A n w q = (wordP s0 s1 n w q : Nat)
  | 0, _, _ => rfl
  | n + 1, w, q => by
    rw [wordPt_succ, wordP_succ]
    cases Nat.beq w 0
    · change wordPt A n (w / 8) (pg 12 4095 (A (w % 8 - 1)) q) =
        ((wordP s0 s1 n (w / 8) * letP s0 s1 (w % 8 - 1)) q : Nat)
      rw [hA, wordPt_eq hA n, Perm.mul_apply]
    · rfl

theorem letP_mem {H : Subgroup (Perm (Fin 3510))} {s0 s1 : Perm (Fin 3510)} (h0 : s0 ∈ H)
    (h1 : s1 ∈ H) (l : Nat) : letP s0 s1 l ∈ H := by
  unfold letP
  cases Nat.beq l (nat_lit 2)
  · cases Nat.beq l (nat_lit 3)
    · cases Nat.beq l (nat_lit 4)
      · exact H.inv_mem h1
      · exact H.inv_mem h0
    · exact h1
  · exact h0

theorem wordP_mem' {H : Subgroup (Perm (Fin 3510))} {s0 s1 : Perm (Fin 3510)} (h0 : s0 ∈ H)
    (h1 : s1 ∈ H) : ∀ (n w : Nat), wordP s0 s1 n w ∈ H
  | 0, _ => H.one_mem
  | n + 1, w => by
    rw [wordP_succ]
    cases Nat.beq w 0
    · exact H.mul_mem (wordP_mem' h0 h1 n _) (letP_mem h0 h1 _)
    · exact H.one_mem

theorem withA_eq (k : (Nat → Nat) → Bool) :
    withA k = k (letA (Fi22CGT.F 0) (Fi22CGT.F 1) (pinv (Fi22CGT.F 0)) (pinv (Fi22CGT.F 1))) := by
  unfold withA
  rw [CFSG.KC.Fi22Omega.strictB_eq, CFSG.KC.Fi22Omega.strictB_eq]

theorem rep_a {k : Nat} (hk : k < 2) :
    Rep 3510 (unpack 3510 12 (Fi22CGT.F k)) (fi22GenPerm k) := by
  rw [← Fi22G.gen_eq hk]
  exact rep_fi22Gen hk

theorem a_pg {k : Nat} (hk : k < 2) (q : Fin 3510) :
    pg 12 4095 (Fi22CGT.F k) q = (fi22GenPerm k q : Nat) :=
  pg_of_rep (rep_a hk) q

theorem ai_pg {k : Nat} (hk : k < 2) (q : Fin 3510) :
    pg 12 4095 (pinv (Fi22CGT.F k)) q = ((fi22GenPerm k)⁻¹ q : Nat) := by
  have hpm := (cpK_iff (band_true (allN_spec lets k hk)).1).2.1
  have h := CFSG.KS.Raw.rep_invCand (rep_a hk)
  rw [invCand_pinv hpm] at h
  exact pg_of_rep h q

theorem aL_pg (l : Nat) (q : Fin 3510) :
    pg 12 4095 (letA (Fi22CGT.F 0) (Fi22CGT.F 1) (pinv (Fi22CGT.F 0)) (pinv (Fi22CGT.F 1)) l) q =
      (letP (fi22GenPerm 0) (fi22GenPerm 1) l q : Nat) :=
  letA_pg (a_pg (by decide)) (a_pg (by decide)) (ai_pg (by decide)) (ai_pg (by decide)) l q

theorem wordPt_aL (n w : Nat) (q : Fin 3510) :
    wordPt (letA (Fi22CGT.F 0) (Fi22CGT.F 1) (pinv (Fi22CGT.F 0)) (pinv (Fi22CGT.F 1))) n w q =
      (wordP (fi22GenPerm 0) (fi22GenPerm 1) n w q : Nat) :=
  wordPt_eq aL_pg n w q

theorem gen_mem (k : Nat) (hk : k < 2) : fi22GenPerm k ∈ fi22P := by
  rw [fi22P_eq]
  exact Subgroup.subset_closure ⟨⟨k, hk⟩, rfl⟩

theorem wordP_mem (n w : Nat) : wordP (fi22GenPerm 0) (fi22GenPerm 1) n w ∈ fi22P :=
  wordP_mem' (gen_mem 0 (by decide)) (gen_mem 1 (by decide)) n w

theorem u0All : u0L.all (fun p => Nat.blt p (nat_lit 3510)) = true := by quickRfl

theorem oNZ : allN 3 (fun k => Bool.not (Nat.beq (MS (Nat.add 7 k)) 0)) = true := by quickRfl

theorem u0L_lt {p : Nat} (hp : p ∈ u0L) : p < 3510 :=
  Nat.blt_eq.mp (List.all_eq_true.mp u0All p hp)

theorem rootM0_bit {q : Nat} (h : (rootM 0).testBit q = true) : q < 3510 := by
  rw [Nat.eq_of_beq_eq_true u0, testBit_wordMask] at h
  obtain ⟨p, hp, e⟩ := h
  rw [wordPt_zero] at e
  subst e
  exact u0L_lt hp

theorem orb_nonempty {k : Nat} (hk : k < 3) : ∃ x : Fin 3510, x ∈ maskSet (MS (Nat.add 7 k)) := by
  have hne : MS (Nat.add 7 k) ≠ 0 := by
    have h : Bool.not (Nat.beq (MS (Nat.add 7 k)) 0) = true := allN_spec oNZ k hk
    intro e
    rw [e] at h
    exact absurd h (by decide)
  obtain ⟨q, hq⟩ := Nat.exists_testBit_of_ne_zero hne
  exact ⟨⟨q, rootM0_bit (orb_sub hk hq)⟩, hq⟩

theorem orbs_disj {a b : Nat} (ha : a < 3) (hb : b < 3) {q : Nat}
    (h1 : (MS (Nat.add 7 a)).testBit q = true) (h2 : (MS (Nat.add 7 b)).testBit q = true) :
    a = b := by
  obtain ⟨-, h3⟩ := band_true orbs
  obtain ⟨e78, h4⟩ := band_true h3
  obtain ⟨e79, e89⟩ := band_true h4
  have z78 := Nat.eq_of_beq_eq_true e78
  have z79 := Nat.eq_of_beq_eq_true e79
  have z89 := Nat.eq_of_beq_eq_true e89
  have hz : ∀ {M N : Nat}, Nat.land M N = 0 → M.testBit q = true → N.testBit q = true → False := by
    intro M N e hM hN
    have h : (Nat.land M N).testBit q = (0 : Nat).testBit q := by rw [e]
    rw [nland, Nat.testBit_and, hM, hN, Nat.zero_testBit] at h
    exact absurd h (by decide)
  interval_cases a <;> interval_cases b
  all_goals first
    | rfl
    | exact (hz z78 h1 h2).elim
    | exact (hz z78 h2 h1).elim
    | exact (hz z79 h1 h2).elim
    | exact (hz z79 h2 h1).elim
    | exact (hz z89 h1 h2).elim
    | exact (hz z89 h2 h1).elim

theorem root_mem {c : Nat} (hc : c < 3) :
    maskSet (rootM (c + 1)) =
      wordP (fi22GenPerm 0) (fi22GenPerm 1) 128 (MS (Nat.add 4 c)) • maskSet (rootM 0) := by
  have e : rootM (c + 1) = wordMask (letA (Fi22CGT.F 0) (Fi22CGT.F 1) (pinv (Fi22CGT.F 0))
      (pinv (Fi22CGT.F 1))) (MS (Nat.add 4 c)) u0L := by
    have h := roots
    rw [withA_eq] at h
    exact Nat.eq_of_beq_eq_true (allN_spec h c hc)
  ext x
  rw [Set.mem_smul_set]
  change (rootM (c + 1)).testBit x = true ↔ _
  rw [e, testBit_wordMask]
  constructor
  · rintro ⟨p, hp, hx⟩
    refine ⟨⟨p, u0L_lt hp⟩, ?_, ?_⟩
    · rw [← u0_eq]
      exact hp
    · apply Fin.ext
      rw [Perm.smul_def, ← wordPt_aL]
      exact hx
  · rintro ⟨y, hy, hx⟩
    refine ⟨y, mem_u0L hy, ?_⟩
    rw [wordPt_aL, ← hx]
    rfl

theorem coset_maps {j k : Nat} (hj : j < 6) (hk : k < 3)
    {x : Fin 3510} (hx : x ∈ maskSet (MS (Nat.add 7 k))) :
    wordP (fi22GenPerm 0) (fi22GenPerm 1) 128 (MS (Nat.add 10 j)) x ∈
      maskSet (MS (Nat.add 7 (piOf j k))) := by
  have h := cosets
  rw [withA_eq] at h
  have hm := mapsOK_sound (allN_spec (allN_spec h j hj) k hk) x
    (mem_u0L (orb_sub hk hx)) hx
  rw [wordPt_aL] at hm
  exact hm

end CertificateChecks.KernelFi22Omega

end
