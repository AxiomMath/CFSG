module

public import Certificates.Kernel.J2Cover.C4725P
public import Certificates.Kernel.J2Cover.M22Fold
public import Certificates.Kernel.Misc.Perm.J2C3A
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover.C4725K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3 CFSG.KC.DecText
open CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.J2Cover.Models
open CFSG.RankThree.PartTwo.J2Residue.C4725
open CertificateChecks.KernelJ2Cover CertificateChecks.KernelJ2Cover.C4725P
open CertificateChecks.KernelMisc.J2C3 (Z hz)

theorem kPS0 : Nat.beq (Nat.shiftRight PSI (4725 * 12)) 0 = true := by quickRfl
theorem kKC0 : Nat.beq (Nat.shiftRight KC (4713 * 14)) 0 = true := by quickRfl
theorem kTM0 : Nat.beq (Nat.shiftRight TM (12679 * 13)) 0 = true := by quickRfl
theorem kKT0 : Nat.beq (Nat.shiftRight KT (14139 * 13)) 0 = true := by quickRfl

theorem psi_eq : psiData = unpack 4725 12 PSI := natsOf_bind NPSI.eq (by quickRfl) (by quickRfl)
theorem kc_eq : keptCodes = unpack 4713 14 KC := natsOf_bind NKC.eq (by quickRfl) (by quickRfl)
theorem tm_eq : tMaskAll = unpack 12679 13 TM := natsOf_bind NTM.eq (by quickRfl) (by quickRfl)

theorem psi_pt (x : Nat) : psiData[x]! = pg 12 (mask 12) PSI x := by
  rw [psi_eq, getElem!_unpack_all kPS0]

theorem kc_pt (x : Nat) : keptCodes[x]! = pg 14 (mask 14) KC x := by
  rw [kc_eq, getElem!_unpack_all kKC0]

theorem tm_pt (x : Nat) : tMaskAll[x]! = pg 13 (mask 13) TM x := by
  rw [tm_eq, getElem!_unpack_all kTM0]

@[expose] noncomputable def xK (i : Nat) : Nat := x0Word.foldl (fun k j => actK j k) i

theorem xAct_eq (i : Nat) : xAct i = xK i := by
  unfold xAct wordAct xK
  simp only [act_pt]

@[expose] noncomputable def D (T n : Nat) : Nat × Nat × Nat :=
  (pg 13 (mask 13) T (3 * n), pg 13 (mask 13) T (3 * n + 1), pg 13 (mask 13) T (3 * n + 2))

@[expose] noncomputable def condK (T n : Nat) : Bool :=
  if pg 14 (mask 14) KC n % 3 = 0 then
    (D T n).1 == pg 14 (mask 14) KC n / 3 && (D T n).2.1 == xK (D T n).1 &&
      (D T n).2.2 == xK (D T n).2.1
  else
    decide (pg 14 (mask 14) KC n / 3 < n) &&
      (D T n).1 == actK (pg 14 (mask 14) KC n % 3 - 1) (D T (pg 14 (mask 14) KC n / 3)).1 &&
      (D T n).2.1 == actK (pg 14 (mask 14) KC n % 3 - 1) (D T (pg 14 (mask 14) KC n / 3)).2.1 &&
      (D T n).2.2 == actK (pg 14 (mask 14) KC n % 3 - 1) (D T (pg 14 (mask 14) KC n / 3)).2.2

theorem kKept : allN 4713 (condK KT) = true := by quickRfl

theorem negKept : (!allN 4713 (condK (KT + 1))) = true := by quickRfl

@[expose] def stepT (t : Array (Nat × Nat × Nat)) (n : Nat) : Array (Nat × Nat × Nat) :=
  if keptCodes[n]! % 3 = 0 then
    t.push (keptCodes[n]! / 3, xAct (keptCodes[n]! / 3), xAct (xAct (keptCodes[n]! / 3)))
  else
    t.push (actT (keptCodes[n]! % 3 - 1) (t[keptCodes[n]! / 3]!).1,
      actT (keptCodes[n]! % 3 - 1) (t[keptCodes[n]! / 3]!).2.1,
      actT (keptCodes[n]! % 3 - 1) (t[keptCodes[n]! / 3]!).2.2)

theorem ite_yield {β : Type} (p : Prop) [Decidable p] (a b : β) :
    (if p then (pure (ForInStep.yield a) : Id (ForInStep β)) else pure (ForInStep.yield b)) =
      pure (ForInStep.yield (if p then a else b)) := by
  split <;> rfl

theorem keptTri_foldl : keptTri () = (List.range' 0 4713).foldl stepT #[] := by
  simp [keptTri, ite_yield]
  rfl

@[expose] noncomputable def pre (k : Nat) : Array (Nat × Nat × Nat) :=
  Array.ofFn (n := k) fun i => D KT i.val

theorem pre_succ (k : Nat) : pre (k + 1) = (pre k).push (D KT k) := by
  unfold pre
  rw [Array.ofFn_succ]
  rfl

theorem step_ok {k : Nat} (h : condK KT k = true) : stepT (pre k) k = pre (k + 1) := by
  rw [pre_succ]
  unfold stepT
  unfold condK at h
  simp only [kc_pt, xAct_eq, act_pt]
  by_cases hr : pg 14 (mask 14) KC k % 3 = 0
  · rw [if_pos hr] at h ⊢
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    congr 1
    rw [← h1, ← h2, ← h3]
  · rw [if_neg hr] at h ⊢
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hlt, h1⟩, h2⟩, h3⟩ := h
    have hp : (pre k)[pg 14 (mask 14) KC k / 3]! = D KT (pg 14 (mask 14) KC k / 3) := by
      unfold pre
      exact getElem!_ofFn' hlt
    rw [hp]
    congr 1
    rw [← h1, ← h2, ← h3]

theorem fold_pre : ∀ N, N ≤ 4713 → (List.range' 0 N).foldl stepT #[] = pre N
  | 0, _ => by
    unfold pre
    simp
  | N + 1, hN => by
    rw [List.range'_concat, List.foldl_append, fold_pre N (by omega)]
    simp only [Nat.zero_add, Nat.one_mul, List.foldl_cons, List.foldl_nil]
    exact step_ok (allN_spec kKept N (by omega))

theorem kt_eq : keptTri () = pre 4713 := keptTri_foldl.trans (fold_pre 4713 le_rfl)

theorem kt_size : (keptTri ()).size = 4713 := by
  rw [kt_eq]
  unfold pre
  exact Array.size_ofFn

theorem kt_get (i : Nat) : (keptTri ())[i]! = D KT i := by
  rw [kt_eq]
  by_cases hi : i < 4713
  · unfold pre
    exact getElem!_ofFn' hi
  · rw [getElem!_neg _ i (by unfold pre; rw [Array.size_ofFn]; exact hi)]
    unfold D
    rw [pg_beyond kKT0 (by omega), pg_beyond kKT0 (by omega), pg_beyond kKT0 (by omega)]
    rfl

theorem psiC : psiCheck () = true := by
  unfold psiCheck
  simp only [psi_pt, act_pt, allLt_eq_allN]
  quickRfl

theorem negPsi : (!allN 4725 fun i => allN 2 fun j =>
    mulCols (colsJ (1 - j)) (pg 12 (mask 12) PSI (actK j i)) == pg 12 (mask 12) PSI i) = true := by
  quickRfl

theorem orbitC : orbitCheck () = true := by
  unfold orbitCheck
  simp only [psi_pt, xAct_eq, allLt_eq_allN]
  quickRfl

theorem basisC : basisCheck () = true := by
  unfold basisCheck basisCols
  simp only [psi_pt, allLt_eq_allN]
  quickRfl

theorem keptC : keptCheck () = true := by
  unfold keptCheck
  simp only [kt_get, kt_size, kc_pt, xAct_eq, act_pt, allLt_eq_allN]
  quickRfl

theorem targetC : targetCheck () = true := by
  unfold targetCheck maskList xorTri coeffXor
  simp only [kt_get, tm_pt, act_pt, allLt_eq_allN]
  quickRfl

theorem cZ : CnN 315 9 Z := by quickRfl

theorem conjC : conjCheck () = true := by
  unfold conjCheck
  simp only [wordArr_eq, hz]
  rw [← hId,
    compA_unpackN (wordP_canon gWord) cZ, compA_unpackN (wordP_canon x0Word) (wordP_canon gWord),
    compA_unpackN (wordP_canon x0Word) (wordP_canon x0Word),
    compA_unpackN (wordP_canon x0Word) (canon_pcN (wordP_canon x0Word) (wordP_canon x0Word)),
    eqA_unpackN (canon_pcN (wordP_canon gWord) cZ) (canon_pcN (wordP_canon x0Word) (wordP_canon gWord)),
    eqA_unpackN (canon_pcN (wordP_canon x0Word) (canon_pcN (wordP_canon x0Word)
      (wordP_canon x0Word))) cId]
  quickRfl

theorem negConj : (!Nat.beq (pcomp 315 9 (mask 9) (wordP gWord) (wordP x0Word))
    (pcomp 315 9 (mask 9) (wordP x0Word) (wordP gWord))) = true := by quickRfl

end CertificateChecks.KernelJ2Cover.C4725K

end
