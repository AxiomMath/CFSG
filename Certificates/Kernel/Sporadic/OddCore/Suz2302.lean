
module

public import Certificates.Kernel.Sporadic.OddCore.Suz2289
public import Certificates.Kernel.Sporadic.Suz.Order2306
public import Certificates.Kernel.Sporadic.SuzInv.Text0
public import Certificates.Kernel.Sporadic.SuzInv.Text1
public import Certificates.Kernel.Sporadic.SuzInv.Text2
public import Certificates.Kernel.Sporadic.SuzInv.Text3
public import Certificates.Kernel.Sporadic.OddCore.Glue
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Sporadic.SuzOddCore.InvTCheckInputs
public import CFSG.Sporadic.SuzOddCore.InvGraphCheckInputs
meta import CFSG.Sporadic.SuzOddCore.InvGraphCheckInputs
meta import CFSG.Sporadic.SuzOddCore.InvTCheckInputs
import CFSG.Sporadic.SuzOddCore.Arrays
import CFSG.Sporadic.SuzOddCore.InvArrays
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native

meta def repWordsM : Array (Array Nat) :=
  (List.range 4).toArray.map fun i => wordA 1782 bTriple bTripleInv (invRepWords.getD i [])

meta def tM : Array (Array Nat) := (List.range 4).toArray.map tArr

meta def witM : Array (Array Nat) :=
  (List.range 4).toArray.map fun i =>
    #[((List.range (invFullGenCounts.getD i 0)).find? fun k =>
      !inM (invFullGenArrs i)[k]!).getD 0]

end CertificateChecks.KernelSpor.OddCore

#kmisc_packarrs CertificateChecks.KernelSpor.SuzTW CertificateChecks.KernelSpor.OddCore.repWordsM 11

#kmisc_packarrs CertificateChecks.KernelSpor.SuzTP CertificateChecks.KernelSpor.OddCore.tM 11

#kmisc_packarrs CertificateChecks.KernelSpor.SuzTWit CertificateChecks.KernelSpor.OddCore.witM 11

namespace CertificateChecks.KernelSpor.OddCore

open CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.KC.Enum
open CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Mathieu CFSG.KC.BfsPin CertificateChecks.KernelSpor.Suz2306

@[expose] noncomputable def triS (h : Nat) : Nat := nIf(Nat.beq h 0, B0, nIf(Nat.beq h 1, B1, V))

@[expose] noncomputable def triSI (h : Nat) : Nat := SuzMtxI h

@[expose] noncomputable def msift (G : Nat) : Bool := Suz2306.sift G

@[expose] noncomputable def fixCntK (n w m p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i s => nIf(Nat.beq (pg w m p i) i, Nat.succ s, s)) n

@[expose] noncomputable def repK (i : Nat) : Bool :=
  strictB (SuzTP i) (fun T =>
  bAnd(wordEqK 1782 11 (mask 11) (pidn 1782 11) triS triSI 3 (dword invRepWords 0 i) (SuzTW i),
  bAnd(powEqK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) (SuzTW i) (nget invRepPowers i) T,
  bAnd(sqIdK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) T,
  bAnd(neIdK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) T,
    Nat.beq (fixCntK 1782 11 (mask 11) T) (nget invFixedCounts i))))))

@[expose] noncomputable def fullK (T G : Nat) : Bool :=
  bAnd(commK 1782 11 (mask 11) (1782 * 11) G T, bIf(msift G, true, msift (pcomp 1782 11 (mask 11) V G)))

@[expose] noncomputable def innerK (T G : Nat) : Bool :=
  bAnd(commK 1782 11 (mask 11) (1782 * 11) G T, msift G)

@[expose] noncomputable def entryK (F : Nat → Nat) (i fc is ic : Nat) : Bool :=
  strictB (SuzTP i) (fun T =>
  bAnd(allN fc (fun k => fullK T (F (Nat.add 1 k))),
  bAnd(allN ic (fun k => innerK T (F (Nat.add is k))),
  strictB (SuzTWit i) (fun x => bAnd(Nat.blt x fc, bIf(msift (F (Nat.add 1 x)), false, true))))))

theorem tri_perms : allN 3 (fun j =>
    permOK 1782 11 (mask 11) (1782 * 11) (triS j) (triSI j)) = true := by
  quickRfl

theorem reps : allN 4 repK = true := by
  quickRfl

theorem reps_in : bAnd(msift (SuzTP 0), bAnd(msift (SuzTP 1),
    bAnd(bIf(msift (SuzTP 2), false, true), bIf(msift (SuzTP 3), false, true)))) = true := by
  quickRfl

theorem entry0 : entryK SuzInvT0.F 0 12 32 22 = true := by
  quickRfl

theorem entry1 : entryK SuzInvT1.F 1 6 18 10 = true := by
  quickRfl

theorem entry2 : entryK SuzInvT2.F 2 3 12 2 = true := by
  quickRfl

theorem entry3 : entryK SuzInvT3.F 3 6 20 5 = true := by
  quickRfl

theorem strictB_app (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem canon_shift {G : Nat} (h : canonK 1782 11 (mask 11) (1782 * 11) G = true) :
    Nat.shiftRight G (1782 * 11) = 0 := by
  have h' : bAnd(szOK 1782 11, bAnd(Nat.beq (Nat.shiftRight G (1782 * 11)) (nat_lit 0),
      allN 1782 (fun i => Nat.blt (pg 11 (mask 11) G i) 1782))) = true := h
  simp only [bAnd_iff] at h'
  exact Nat.eq_of_beq_eq_true h'.2.1

theorem inM_eq {g : Array Nat} {G : Nat} (hg : g = unpack 1782 11 G)
    (hc : canonK 1782 11 (mask 11) (1782 * 11) G = true) : inM g = msift G := by
  unfold inM
  rw [smallLevels, siftK_eq binds perm SuzC.hl hg (canon_shift hc) (range_of_canonK hc)]
  rfl

theorem dword_eq (D : List (List Int)) (i : Nat) : dword D 0 i = D.getD i [] := by
  change List.rec (motive := fun _ => Nat → List Int) (fun _ => [])
    (fun x _ ih i => Nat.rec (motive := fun _ => List Int) x (fun i' _ => ih i') i) D i = _
  induction D generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem nget_eq (l : List Nat) (i : Nat) : nget l i = l.getD i 0 := by
  induction l generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem powA_eq (n : Nat) (t : Array Nat) :
    ∀ k, powA n t k = CFSG.Sporadic.Schreier.Co3.co3PowA n t k
  | 0 => rfl
  | k + 1 => by
    rw [powA, CFSG.Sporadic.Schreier.Co3.co3PowA, powA_eq n t k]

theorem fixCntK_eq (w m p : Nat) : ∀ n, fixCntK n w m p =
    (List.range n).countP (fun i => Nat.beq (pg w m p i) i)
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.countP_append, ← fixCntK_eq w m p n]
    change nIf(Nat.beq (pg w m p n) n, Nat.succ (fixCntK n w m p), fixCntK n w m p) = _
    cases h : Nat.beq (pg w m p n) n <;> simp [h]

theorem fixedCount_eq (t : Array Nat) : fixedCount t = (fixedList 1782 t).length := by
  unfold fixedCount fixedList
  rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
  apply Finset.card_bij (fun (x : Fin 1782) _ => (x : ℕ))
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range, beq_iff_eq]
    exact ⟨x.2, hx⟩
  · intro x _ y _ h
    exact Fin.ext h
  · intro y hy
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range, beq_iff_eq] at hy
    exact ⟨⟨y, hy.1⟩, by simpa using hy.2, rfl⟩

theorem fixedCount_unpack {T : Nat} : fixedCount (unpack 1782 11 T) =
    fixCntK 1782 11 (mask 11) T := by
  rw [fixedCount_eq, fixCntK_eq, fixedList, List.countP_eq_length_filter]
  apply congrArg List.length
  apply List.filter_congr
  intro i hi
  have hi' : i < 1782 := List.mem_range.1 hi
  rw [CFSG.KC.Misc.PairCount.unpack_get hi']
  cases h : Nat.beq (pg 11 (mask 11) T i) i
  · have : pg 11 (mask 11) T i ≠ i := fun e => by simp [e] at h
    simp [this]
  · simp [Nat.eq_of_beq_eq_true h]

theorem rep_facts {i : Nat} (hi : i < 4) :
    tArr i = unpack 1782 11 (SuzTP i) ∧ canonK 1782 11 (mask 11) (1782 * 11) (SuzTP i) = true ∧
      eqA 1782 (compA 1782 (tArr i) (tArr i)) (idA 1782) = true ∧
      eqA 1782 (tArr i) (idA 1782) = false ∧ fixedCount (tArr i) = invFixedCounts.getD i 0 := by
  have h := allN_spec reps i hi
  unfold repK at h
  rw [strictB_app] at h
  obtain ⟨hw, hp, hs, hn, hf⟩ := (by simpa only [bAnd_iff] using h :
    wordEqK 1782 11 (mask 11) (pidn 1782 11) triS triSI 3 (dword invRepWords 0 i) (SuzTW i) = true ∧
    powEqK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) (SuzTW i) (nget invRepPowers i)
      (SuzTP i) = true ∧
    sqIdK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) (SuzTP i) = true ∧
    neIdK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) (SuzTP i) = true ∧
    Nat.beq (fixCntK 1782 11 (mask 11) (SuzTP i)) (nget invFixedCounts i) = true)
  have hS : bTriple.size = 3 ∧ ∀ j < 3, bTriple[j]! = unpack 1782 11 (triS j) := by
    refine ⟨rfl, fun j hj => ?_⟩
    interval_cases j
    · change bTriple[0]! = unpack 1782 11 B0
      simpa [bTriple] using b0Arr_eq
    · change bTriple[1]! = unpack 1782 11 B1
      simpa [bTriple] using b1Arr_eq
    · change bTriple[2]! = unpack 1782 11 V
      simpa [bTriple] using vArr_eq
  have hword := (wordEqK_sound hS tri_perms hw).1
  have hpow := powEqK_sound hp
  have hcan : canonK 1782 11 (mask 11) (1782 * 11) (SuzTP i) = true := by
    have h' : bAnd(canonK 1782 11 (mask 11) (1782 * 11) (SuzTP i),
        Nat.beq (pcomp 1782 11 (mask 11) (SuzTP i) (SuzTP i)) (pidn 1782 11)) = true := hs
    exact ((bAnd_iff _ _).1 h').1
  have ht : tArr i = unpack 1782 11 (SuzTP i) := by
    unfold tArr
    rw [powA_eq, ← nget_eq, ← dword_eq]
    change CFSG.Sporadic.Schreier.Co3.co3PowA 1782
      (wordA 1782 bTriple (rawInvs 1782 bTriple) (dword invRepWords 0 i)) (nget invRepPowers i) = _
    rw [hword]
    exact hpow
  refine ⟨ht, hcan, ?_, ?_, ?_⟩
  · rw [ht]
    exact sqIdK_sound hs
  · rw [ht]
    exact neIdK_sound hn
  · rw [ht, fixedCount_unpack, Nat.eq_of_beq_eq_true hf, nget_eq]

theorem commutes_eq {G T : Nat} (h : commK 1782 11 (mask 11) (1782 * 11) G T = true) :
    commutesA (unpack 1782 11 G) (unpack 1782 11 T) = true :=
  commK_sound h

theorem commK_canon {G T : Nat} (h : commK 1782 11 (mask 11) (1782 * 11) G T = true) :
    canonK 1782 11 (mask 11) (1782 * 11) G = true := by
  have h' : bAnd(canonK 1782 11 (mask 11) (1782 * 11) G, bAnd(canonK 1782 11 (mask 11) (1782 * 11) T,
      Nat.beq (pcomp 1782 11 (mask 11) G T) (pcomp 1782 11 (mask 11) T G))) = true := h
  exact ((bAnd_iff _ _).1 h').1

theorem canonV : canonK 1782 11 (mask 11) (1782 * 11) V = true := by
  quickRfl

theorem entry_facts {i fc is ic : Nat} {F : Nat → Nat} (hi : i < 4)
    (hfc : invFullGenCounts.getD i 0 = fc) (hic : invInnerGenCounts.getD i 0 = ic)
    (his : invInnerStart i = is)
    (hrun : ∀ k, k < is + ic → invRun i k = unpack 1782 11 (F k)) (hfis : 1 + fc ≤ is)
    (h : entryK F i fc is ic = true) :
    (∀ k < invFullGenCounts.getD i 0,
      (inM (invFullGenArrs i)[k]! = true ∨ inM (compA 1782 vArr (invFullGenArrs i)[k]!) = true) ∧
        commutesA (invFullGenArrs i)[k]! (tArr i) = true) ∧
    (∃ k < invFullGenCounts.getD i 0, inM (invFullGenArrs i)[k]! = false) ∧
    (∀ k < invInnerGenCounts.getD i 0,
      inM (invInnerGenArrs i)[k]! = true ∧ commutesA (invInnerGenArrs i)[k]! (tArr i) = true) := by
  obtain ⟨ht, _, -⟩ := rep_facts hi
  unfold entryK at h
  rw [strictB_app] at h
  obtain ⟨hf, hin, hw⟩ := (by simpa only [bAnd_iff] using h :
    allN fc (fun k => fullK (SuzTP i) (F (Nat.add 1 k))) = true ∧
    allN ic (fun k => innerK (SuzTP i) (F (Nat.add is k))) = true ∧
    strictB (SuzTWit i) (fun x => bAnd(Nat.blt x fc, bIf(msift (F (Nat.add 1 x)), false, true))) = true)
  have fg : ∀ k < fc, (invFullGenArrs i)[k]! = unpack 1782 11 (F (Nat.add 1 k)) := fun k hk => by
    rw [getElem!_pos (invFullGenArrs i) k (by rw [invFullGenArrs, Array.size_ofFn, hfc]; exact hk)]
    simp only [invFullGenArrs, Array.getElem_ofFn]
    exact hrun (1 + k) (by omega)
  have ig : ∀ k < ic, (invInnerGenArrs i)[k]! = unpack 1782 11 (F (Nat.add is k)) := fun k hk => by
    rw [getElem!_pos (invInnerGenArrs i) k (by rw [invInnerGenArrs, Array.size_ofFn, hic]; exact hk)]
    simp only [invInnerGenArrs, Array.getElem_ofFn, his]
    exact hrun (is + k) (by omega)
  refine ⟨fun k hk => ?_, ?_, fun k hk => ?_⟩
  · rw [hfc] at hk
    have hk' := allN_spec hf k hk
    unfold fullK at hk'
    obtain ⟨hc, hs⟩ := (bAnd_iff _ _).1 hk'
    have hcan := commK_canon hc
    rw [fg k hk, ht]
    refine ⟨?_, commutes_eq hc⟩
    rw [inM_eq rfl hcan]
    cases hsg : msift (F (Nat.add 1 k))
    · rw [hsg] at hs
      right
      rw [vArr_eq, compA_unpack canonV hcan, inM_eq rfl (canonK_pcomp canonV hcan)]
      exact hs
    · left
      rfl
  · rw [strictB_app] at hw
    obtain ⟨hx, hs⟩ := (bAnd_iff _ _).1 hw
    refine ⟨SuzTWit i, by rw [hfc]; exact Eq.mp Nat.blt_eq hx, ?_⟩
    have hxf : SuzTWit i < fc := Eq.mp Nat.blt_eq hx
    rw [fg _ hxf]
    have hcan : canonK 1782 11 (mask 11) (1782 * 11) (F (Nat.add 1 (SuzTWit i))) = true :=
      commK_canon ((bAnd_iff _ _).1 (allN_spec hf _ hxf)).1
    rw [inM_eq rfl hcan]
    cases hsg : msift (F (Nat.add 1 (SuzTWit i)))
    · rfl
    · rw [hsg] at hs
      exact absurd hs (by decide)
  · rw [hic] at hk
    have hk' := allN_spec hin k hk
    unfold innerK at hk'
    obtain ⟨hc, hs⟩ := (bAnd_iff _ _).1 hk'
    rw [ig k hk, ht, inM_eq rfl (commK_canon hc)]
    exact ⟨hs, commutes_eq hc⟩

theorem facts2302 :
    (∀ i < 4, eqA 1782 (compA 1782 (tArr i) (tArr i)) (idA 1782) = true ∧
      eqA 1782 (tArr i) (idA 1782) = false ∧ fixedCount (tArr i) = invFixedCounts.getD i 0) ∧
    inM (tArr 0) = true ∧ inM (tArr 1) = true ∧ inM (tArr 2) = false ∧ inM (tArr 3) = false ∧
    (∀ i < 4, ∀ k < invFullGenCounts.getD i 0,
      (inM (invFullGenArrs i)[k]! = true ∨ inM (compA 1782 vArr (invFullGenArrs i)[k]!) = true) ∧
      commutesA (invFullGenArrs i)[k]! (tArr i) = true) ∧
    (∀ i < 4, ∃ k < invFullGenCounts.getD i 0, inM (invFullGenArrs i)[k]! = false) ∧
    (∀ i < 4, ∀ k < invInnerGenCounts.getD i 0,
      inM (invInnerGenArrs i)[k]! = true ∧ commutesA (invInnerGenArrs i)[k]! (tArr i) = true) := by
  have e0 := entry_facts (i := 0) (fc := 12) (is := 32) (ic := 22) (by omega) rfl rfl rfl
    (fun _ hk => SuzInv.run_eq0 (by omega)) (by omega) entry0
  have e1 := entry_facts (i := 1) (fc := 6) (is := 18) (ic := 10) (by omega) rfl rfl rfl
    (fun _ hk => SuzInv.run_eq1 (by omega)) (by omega) entry1
  have e2 := entry_facts (i := 2) (fc := 3) (is := 12) (ic := 2) (by omega) rfl rfl rfl
    (fun _ hk => SuzInv.run_eq2 (by omega)) (by omega) entry2
  have e3 := entry_facts (i := 3) (fc := 6) (is := 20) (ic := 5) (by omega) rfl rfl rfl
    (fun _ hk => SuzInv.run_eq3 (by omega)) (by omega) entry3
  obtain ⟨s0, s1, s2, s3⟩ := (by simpa only [bAnd_iff] using reps_in :
    msift (SuzTP 0) = true ∧ msift (SuzTP 1) = true ∧ bIf(msift (SuzTP 2), false, true) = true ∧
      bIf(msift (SuzTP 3), false, true) = true)
  have m : ∀ i < 4, inM (tArr i) = msift (SuzTP i) := fun i hi => by
    obtain ⟨ht, hc, -⟩ := rep_facts hi
    exact inM_eq ht hc
  refine ⟨fun i hi => (rep_facts hi).2.2, by rw [m 0 (by omega)]; exact s0,
    by rw [m 1 (by omega)]; exact s1, ?_, ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [m 2 (by omega)]
    cases h : msift (SuzTP 2)
    · rfl
    · rw [h] at s2
      exact absurd s2 (by decide)
  · rw [m 3 (by omega)]
    cases h : msift (SuzTP 3)
    · rfl
    · rw [h] at s3
      exact absurd s3 (by decide)
  · interval_cases i
    exacts [e0.1, e1.1, e2.1, e3.1]
  · interval_cases i
    exacts [e0.2.1, e1.2.1, e2.2.1, e3.2.1]
  · interval_cases i
    exacts [e0.2.2, e1.2.2, e2.2.2, e3.2.2]

end CertificateChecks.KernelSpor.OddCore

end
