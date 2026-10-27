module

public import Certificates.Kernel.SuzThree13637.Bind
public import Certificates.Kernel.SuzThree13637.CEnum
public import Certificates.Kernel.SuzPump.PairFacts
public import CFSG.Certificates.Kernel.PGrpSound
public import CFSG.Certificates.Kernel.B3S3KSound
public import CFSG.Certificates.Kernel.BfsPinSliceSound
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporE81Local
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CFSG.KD.SuzThree13637

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PSearch CFSG.KS.HypK CFSG.KC.PGrp
  CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K CertificateChecks.KernelSpor
open CertificateChecks.KernelSuzPump (hw rebuild_eq)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT CFSG.RankThree.Native
open CFSG.RankThree.PartTwo.Sec4.Item434SporE81 (suzE81 posWord qGens getElem!_map')

theorem nthN_get13637 : ∀ (l : List ℕ) (i : ℕ) (h : i < l.length), nthN l i = l[i]
  | _ :: _, 0, _ => rfl
  | _ :: l, i + 1, h => nthN_get13637 l i (by simp at h; omega)

theorem map_nthN13637 {W : Array (List ℕ)} {f : List ℕ → ℕ} {L : List ℕ}
    (h : W.toList.map f = L) {k : ℕ} (hk : k < W.size) : f W[k]! = nthN L k := by
  subst h
  rw [getElem!_pos W k hk, nthN_get13637 _ _ (by simpa using hk)]
  simp

theorem letters13637 {W : Array (List ℕ)} {m : ℕ}
    (h : (W.toList.all fun w => w.all fun l => decide (l < m)) = true) :
    ∀ k < W.size, ∀ l ∈ W[k]!, l < m := by
  intro k hk l hl
  rw [List.all_eq_true] at h
  have h1 := h W[k]! (by rw [getElem!_pos W k hk]; exact Array.getElem_mem_toList hk)
  simpa using List.all_eq_true.1 h1 l hl

theorem perm_bq : (∀ l < 2, permB 1782 11 (bG l) = true) ∧ ∀ l < 3, permB 1782 11 (qG l) = true := by
  have h := bind_perm
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := h
  refine ⟨fun l hl => ?_, fun l hl => ?_⟩
  · interval_cases l
    · exact h0
    · exact h1
  · interval_cases l
    · exact h2
    · exact h3
    · exact h4

theorem pg_bind : ∀ l < 2, suzE81.pg[l]! = unpack 1782 11 (bG l) := by
  intro l hl
  interval_cases l
  · exact Suz2306.b0Arr_eq
  · exact Suz2306.b1Arr_eq

theorem q_size : (qGensS ()).size = 3 := by
  rw [qGensS, qGens, Array.size_map, bind_letters.2.2.1]

theorem q_gen {k : ℕ} (hk : k < 3) :
    (qGensS ())[k]! = unpack 1782 11 (qG k) ∧ permB 1782 11 (qG k) = true := by
  have hk' : k < suzE81.qW.size := by rw [bind_letters.2.2.1]; exact hk
  obtain ⟨e, -⟩ := posWord_unpack hw pg_bind perm_bq.1
    (letters13637 bind_letters.1 k hk')
  rw [map_nthN13637 bind_q hk'] at e
  refine ⟨?_, perm_bq.2 k hk⟩
  rw [qGensS, qGens, getElem!_map' _ _ hk']
  exact e

theorem d_gen {i : ℕ} (hi : i < 5) :
    (dGens ())[i]! = unpack 1782 11 (nthN F.D i) ∧ permB 1782 11 (nthN F.D i) = true := by
  have hi' : i < (suzE81.dW[0]!).size := by rw [bind_letters.2.2.2]; exact hi
  obtain ⟨e, p⟩ := posWord_unpack hw (fun l hl => (q_gen hl).1) (fun l hl => (q_gen hl).2)
    (letters13637 bind_letters.2.1 i hi')
  rw [map_nthN13637 bind_d hi'] at e p
  refine ⟨?_, p⟩
  rw [dGens, getElem!_map' _ _ hi']
  exact e

theorem nb_reb {i : ℕ} (hi : i < 2) :
    (rebK 1782 11 SuzC.LR SuzC.TR SuzC.TRI (fun l => nthN (nthL F.nb i) l) 6).1 = qG (i + 1) ∧
      (rebK 1782 11 SuzC.LR SuzC.TR SuzC.TRI (fun l => nthN (nthL F.nb i) l) 6).2.2 = true := by
  have h := allN_spec bind_nb i hi
  unfold withReb at h
  rcases e : rebK 1782 11 SuzC.LR SuzC.TR SuzC.TRI (fun l => nthN (nthL F.nb i) l) 6 with
    ⟨g, gi, ok⟩
  rw [e] at h
  change strictB g (fun g => bAnd(ok, Nat.beq g (qG (Nat.succ i)))) = true at h
  have hs : strictB g (fun g => bAnd(ok, Nat.beq g (qG (Nat.succ i)))) =
      bAnd(ok, Nat.beq g (qG (Nat.succ i))) := by cases g <;> rfl
  rw [hs] at h
  cases ok
  · exact absurd h Bool.false_ne_true
  · exact ⟨Nat.eq_of_beq_eq_true h, rfl⟩

theorem ce_n' : CE.N = 3240 ∧ CE.ng = 3 :=
  ⟨Nat.eq_of_beq_eq_true ce_n.1, Nat.eq_of_beq_eq_true ce_n.2⟩

theorem ce_reb' {k : ℕ} (hk : k < 3) :
    (cReb k).2.2 = true ∧ (cReb k).1 = CE.G k ∧ permB 1782 11 (CE.G k) = true := by
  have h := ce_reb k hk
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, Nat.eq_of_beq_eq_true h.1.2, h.2⟩

theorem c_gen : BindA 1782 11 (cGens (levels ())) CE.ng CE.G := by
  rw [ce_n'.2]
  refine ⟨rfl, fun k hk => ?_⟩
  obtain ⟨h1, h2, -⟩ := ce_reb' hk
  have e : (cGens (levels ()))[k]! = rebuild (levels ()) (cBeta k) := by
    interval_cases k <;> rfl
  rw [e, ← h2]
  exact rebuild_eq h1

theorem c_enum : enumOK 1782 (cGens (levels ())) cKeys (cCert (levels ())) = true ∧
    (cCert (levels ())).pts.size = 3240 ∧
    ∀ i < 3240, (cCert (levels ())).pts[i]! = unpack 1782 11 (CE.T i) := by
  have hK : cKeysA.toList = cKeys := rfl
  have hok : CFSG.KC.BfsPin.bfsK 1782 11 CE.ng CE.G CE.N CE.T CE.E CE.S = true :=
    CFSG.KC.BfsPin.bfsK_of_slices (L := 120) (K := 27) (C := CE.C) (ce_n'.1.trans (by norm_num))
      (by norm_num) hw CE.g CE.csAll CE.t0 CE.dist (Nat.eq_of_beq_eq_true CE.c0)
      (Nat.eq_of_beq_eq_true CE.cK) CE.rsAll
  have h := enum_of (fuel := 3300) (ps := cKeys) c_gen
    (fun k hk => (ce_reb' (by rw [ce_n'.2] at hk; exact hk)).2.2)
    hok (by decide) (by rw [← hK]; exact CE.keys) (by rw [ce_n'.1]; omega)
  rw [ce_n'.1] at h
  exact h

end CFSG.KD.SuzThree13637

end
