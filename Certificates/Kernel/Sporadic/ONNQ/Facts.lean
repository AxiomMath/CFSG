module

public import Certificates.Kernel.Sporadic.ONNQ.TRAll
public import Certificates.Kernel.Sporadic.ONNQ.FCWAll
public import Certificates.Kernel.Sporadic.ONLine.Final
public import CFSG.Certificates.Kernel.Spor.ONNQSound
public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.FixCheck
import CFSG.Certificates.Kernel.Spor.Loops

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONNQ

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.ONNQ CFSG.KS.Words
open CFSG.LocalAnalysis.RankThreeTheoremC.ONPair CFSG.Sporadic.ONOddCore

@[expose] def hsh (w : List Int) : List Int := w.map fun l => if 0 < l then l + 2 else l - 2

theorem nq_trAt : ∀ x < 122760, trAt TT UU ONQ.WC ONQ.WL 122760 8 2 x = true :=
  fun x hx => slice_pt (F := trAt TT UU ONQ.WC ONQ.WL 122760 8 2) (SL := 120) (NS := 1023)
    nqTrAll x (by omega)

theorem nq_perm : ∀ x < 122760, ∀ h < 8,
    TT h x < 122760 ∧ UU h x < 122760 ∧ UU h (TT h x) = x := by
  intro x hx h hh
  have hA := ((bAnd_iff _ _).1 (nq_trAt x hx)).1
  have h3 := allBlk_spec hA h hh
  rw [show Nat.add 0 h = h from Nat.zero_add h] at h3
  change strictB (TT h x) _ = true at h3
  rw [show ∀ (y : Nat) (k : Nat → Bool), strictB y k = k y from fun y k => by cases y <;> rfl] at h3
  obtain ⟨a1, h4⟩ := (bAnd_iff _ _).1 h3
  obtain ⟨a2, a3⟩ := (bAnd_iff _ _).1 h4
  exact ⟨Nat.blt_eq.mp a1, Nat.blt_eq.mp a2, Nat.eq_of_beq_eq_true a3⟩

theorem nq_trace : ∀ x < 122760, ∀ j < 8, 2 ≤ j →
    TT j x = (decW (ONQ.WC j) (ONQ.WL j)).foldr (fun z y => CFSG.KS.TW.GZ TT UU z y) x := by
  intro x hx j hj h2
  have hB := ((bAnd_iff _ _).1 (nq_trAt x hx)).2
  have h3 := allBlk_spec hB (j - 2) (by change j - 2 < 8 - 2; omega)
  rw [show Nat.add 2 (j - 2) = j by change 2 + (j - 2) = j; omega] at h3
  rw [← CFSG.KS.TW.trace_eq]
  exact Nat.eq_of_beq_eq_true h3

theorem nq_tabWords :
    decW (ONQ.WC 2) (ONQ.WL 2) = h1Word ∧ decW (ONQ.WC 3) (ONQ.WL 3) = h2Word ∧
      decW (ONQ.WC 4) (ONQ.WL 4) = [-2, 1, 2, -1, 1, 2, -2, 1, -1, -2, 2, -1, 2, 1, 2, 1] ∧
      decW (ONQ.WC 5) (ONQ.WL 5) = [5, 5, 5, 5, 5] ∧
      decW (ONQ.WC 6) (ONQ.WL 6) = h1Word.map (fun l => if l = 1 then 6 else if l = -1 then -6 else l) ∧
      decW (ONQ.WC 7) (ONQ.WL 7) = h2Word.map (fun l => if l = 1 then 6 else if l = -1 then -6 else l) := by
  decide +kernel

theorem nq_tab01 : ∀ x < 122760, dArr0[x]! = TT 0 x ∧ dArr1[x]! = TT 1 x := by
  intro x hx
  obtain ⟨-, hA, hB⟩ := CertificateChecks.KernelSpor.ONLine.line_eq
  have eA : dArr0 = Array.ofFn (n := 122760) fun i => tab ONL.A i.val := hA
  have eB : dArr1 = Array.ofFn (n := 122760) fun i => tab ONL.B i.val := hB
  rw [eA, eB, getElem!_pos _ x (by simpa using hx), getElem!_pos _ x (by simpa using hx),
    Array.getElem_ofFn, Array.getElem_ofFn]
  exact ⟨rfl, rfl⟩

theorem nq_items :
    wd (ONQ.D 18736) = hsh qWords[0]! ∧ wd (ONQ.D 18737) = hsh qWords[1]! ∧
      wd (ONQ.D 18738) = hsh qWords[2]! ∧ wd (ONQ.D 18739) = hsh tWord ∧
      wd (ONQ.D 18740) = u2Word := by
  decide +kernel

theorem nq_letters :
    (∀ a < 36, (wd (ONQ.D a)).all (fun l => decide (l ≠ 0 ∧ l.natAbs ≤ 2))) ∧
      (∀ k < 460, (wd (ONQ.D (36 + k))).all (fun l => decide (l.natAbs = 3 ∨ l.natAbs = 4))) := by
  decide +kernel

theorem nq_head : ev TT UU 0 (wd (ONQ.D 18740)) 0 = 58818 ∧ ev TT UU 0 (wd (ONQ.D 0)) 0 = 0 ∧
    (∀ k < 4, ev TT UU 1 (wd (ONQ.D (36 + k))) 58818 = 58818) ∧
    ev TT UU 1 (wd (ONQ.D 40)) 58818 = 58818 ∧ ev TT UU 1 (wd (ONQ.D 41)) 58818 ≠ 58818 :=
  headOK_sound nqHead_ok

theorem nq_forest : ∀ y < 122760, ∃ ks : List Nat, (∀ k ∈ ks, k < 4) ∧ ∃ a < 36,
    y = ks.foldr (fun k z => ev TT UU 0 (wd (ONQ.D (36 + k))) z) (ev TT UU 0 (wd (ONQ.D a)) 0) :=
  fstAt_sound fun y hy => slice_pt (F := fstAt TT UU ONQ.D ONQ.FR 122760) (SL := 1240) (NS := 99)
    nqFoAll y (by omega)

theorem nq_coset : ∀ i < 456, ∀ q < 4, ∃ j < 456,
    ev TT UU 1 (wd (ONQ.D (18736 + q))) (ev TT UU 1 (wd (ONQ.D (40 + i))) 58818) =
      ev TT UU 1 (wd (ONQ.D (40 + j))) 58818 :=
  cosAt_sound fun i hi => slice_pt (F := cosAt TT UU ONQ.D 58818) (SL := 57) (NS := 8)
    nqCoAll i (by omega)

theorem nq_wit : ∀ a < 35, ∀ i < 456,
    (ev TT UU 0 (wit ONQ.D a i) 0 = 0 ∧ ev TT UU 1 (wit ONQ.D a i) 58818 ≠ 58818) ∨
      (ev TT UU 1 (wit ONQ.D a i) 58818 = 58818 ∧ ev TT UU 0 (wit ONQ.D a i) 0 ≠ 0) :=
  witAt_sound fun j hj => slice_pt (F := witAt TT UU ONQ.D 58818) (SL := 120) (NS := 133)
    nqWiAll j (by omega)

end CertificateChecks.KernelSpor.ONNQ

end
