module

public import Certificates.Kernel.Sporadic.OddCore.SuzDBind
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzDBridgeCheck
public import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzD

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34KSnd
open CFSG.Sporadic.SuzOddCore CFSG.PSL3Four.Native CFSG.EvenSporadicStandard.Induction
open CFSG.LieType.Multipliers.L34 CFSG.KS.PEnum

@[expose] noncomputable def A : Nat := wordTabK 42 6 (mask 6) (pidn 42 6) D suzDWordA

@[expose] noncomputable def B : Nat := wordTabK 42 6 (mask 6) (pidn 42 6) D suzDWordB

@[expose] noncomputable def AI : Nat := pinvS 42 6 (mask 6) A

@[expose] noncomputable def BI : Nat := pinvS 42 6 (mask 6) B

@[expose] noncomputable def letK (l : Fin 2 × Bool) : Nat :=
  if l.1.val = 0 then (if l.2 then A else AI) else (if l.2 then B else BI)

@[expose] noncomputable def wfK (w : List (Fin 2 × Bool)) : Nat :=
  List.rec (motive := fun _ => Nat) (pidn 42 6)
    (fun l _ ih => strictN ih (fun acc => pc (letK l) acc)) w

theorem k27140 : (canonK 42 6 (mask 6) (42 * 6) AI && Nat.beq (pc A AI) (pidn 42 6) &&
    canonK 42 6 (mask 6) (42 * 6) BI && Nat.beq (pc B BI) (pidn 42 6) &&
    rels.all (fun r => Nat.beq (wfK r) (pidn 42 6)) &&
    (List.range 5).all fun j => Nat.beq (wfK (suzDGenWords.getD j [])) (D j)) = true := by
  quickRfl

theorem hsz : szOK 42 6 = true := by decide

theorem hid : idTab 42 = unpack 42 6 (pidn 42 6) := idTab_unpack' hsz

theorem dWord {wd : List Nat} (h : ∀ j ∈ wd, j < 5) :
    wordTab 42 dGens wd = unpack 42 6 (wordTabK 42 6 (mask 6) (pidn 42 6) D wd) ∧
      canonK 42 6 (mask 6) (42 * 6) (wordTabK 42 6 (mask 6) (pidn 42 6) D wd) = true :=
  wordTabK_eq hid (canon_pidn hsz) wd fun j hj => ⟨dGens_get (h j hj), D_canon (h j hj)⟩

theorem parts : canonK 42 6 (mask 6) (42 * 6) A = true ∧ canonK 42 6 (mask 6) (42 * 6) B = true ∧
    canonK 42 6 (mask 6) (42 * 6) AI = true ∧ pc A AI = pidn 42 6 ∧
    canonK 42 6 (mask 6) (42 * 6) BI = true ∧ pc B BI = pidn 42 6 := by
  have h := k27140
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩, -⟩ := h
  exact ⟨(dWord (by decide)).2, (dWord (by decide)).2, h1, Nat.eq_of_beq_eq_true h2, h3,
    Nat.eq_of_beq_eq_true h4⟩

theorem letK_canon (l : Fin 2 × Bool) : canonK 42 6 (mask 6) (42 * 6) (letK l) = true := by
  obtain ⟨cA, cB, cAI, -, cBI, -⟩ := parts
  unfold letK
  split_ifs <;> assumption

theorem letter_eq (l : Fin 2 × Bool) :
    suzDLetterTab (unpack 42 6 A) (unpack 42 6 AI) (unpack 42 6 B) (unpack 42 6 BI) l =
      unpack 42 6 (letK l) := by
  obtain ⟨i, b⟩ := l
  fin_cases i <;> cases b <;> rfl

theorem dWordTab_eq : ∀ w : List (Fin 2 × Bool),
    suzDWordTab (unpack 42 6 A) (unpack 42 6 AI) (unpack 42 6 B) (unpack 42 6 BI) w =
      unpack 42 6 (wfK w) ∧ canonK 42 6 (mask 6) (42 * 6) (wfK w) = true
  | [] => ⟨hid, canon_pidn hsz⟩
  | l :: w => by
    obtain ⟨ih1, ih2⟩ := dWordTab_eq w
    have e : wfK (l :: w) = pc (letK l) (wfK w) := by
      change strictN (wfK w) (fun acc => pc (letK l) acc) = _
      rw [strictN_app']
    have e2 : suzDWordTab (unpack 42 6 A) (unpack 42 6 AI) (unpack 42 6 B) (unpack 42 6 BI)
        (l :: w) = comp 42 (suzDLetterTab (unpack 42 6 A) (unpack 42 6 AI) (unpack 42 6 B)
          (unpack 42 6 BI) l) (suzDWordTab (unpack 42 6 A) (unpack 42 6 AI) (unpack 42 6 B)
          (unpack 42 6 BI) w) := rfl
    rw [e2, ih1, letter_eq, e, comp_unpack' (letK_canon l) ih2]
    exact ⟨rfl, canonK_pcomp (letK_canon l) ih2⟩

theorem check27140 : suzDBridgeCheck = true := by
  obtain ⟨cA, cB, cAI, eA, cBI, eB⟩ := parts
  have hk := k27140
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨-, hrel⟩, hgen⟩ := hk
  have hA : wordTab 42 dGens suzDWordA = unpack 42 6 A := (dWord (by decide)).1
  have hB : wordTab 42 dGens suzDWordB = unpack 42 6 B := (dWord (by decide)).1
  have hAI : invTab 42 (unpack 42 6 A) = unpack 42 6 AI := invTab_eq_of_pcomp cA cAI eA
  have hBI : invTab 42 (unpack 42 6 B) = unpack 42 6 BI := invTab_eq_of_pcomp cB cBI eB
  have hw : ∀ r, (suzDWordTab (unpack 42 6 A) (unpack 42 6 AI) (unpack 42 6 B) (unpack 42 6 BI) r
      == idTab 42) = Nat.beq (wfK r) (pidn 42 6) := fun r => by
    rw [(dWordTab_eq r).1, hid, beq_unpack (dWordTab_eq r).2 (canon_pidn hsz)]
  unfold suzDBridgeCheck
  simp only [hA, hB, hAI, hBI, hw, size_unpack, comp_inv_of_pcomp cA cAI eA,
    comp_inv_of_pcomp cB cBI eB, beq_self_eq_true, Bool.true_and, hrel, Bool.and_eq_true,
    true_and]
  rw [List.all_eq_true] at hgen ⊢
  intro j hj
  have hj5 := List.mem_range.1 hj
  have h := hgen j hj
  rw [(dWordTab_eq _).1, dGens_get hj5, beq_unpack (dWordTab_eq _).2 (D_canon hj5)]
  exact h

end CertificateChecks.KernelSpor.SuzD

end
