
module

public import Certificates.Kernel.Misc.E6StdSlp

public section

namespace CFSG.KC.Misc.E6Std

open CFSG.KC.Misc CFSG.KC.Ord CFSG.KC.LQT.P CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.Monster.B.Classical.E6Adjoint CFSG.LieType.Chevalley.C2E6Std.MatrixModel

attribute [local irreducible] mulB powB oneB rowStarts fullRow rootB

theorem nthV_eq_getD (l : List ℕ) (i : ℕ) : nthV l i = l.getD i 0 := by
  induction l generalizing i with
  | nil => rfl
  | cons x l ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem lenN_eq_length (l : List ℕ) : lenN l = l.length := by
  induction l with
  | nil => rfl
  | cons x l ih => exact congrArg Nat.succ ih

theorem rep_run {V : List ℕ} {prog : List (List ℕ)} {gens : Array Native.Mat}
    (hV : ∀ i < gens.size, Rep (nthV V i) (toMat (gens.getD i Native.one)))
    (hp : ∀ t < lenLL prog, slpLine V prog gens.size t = true) :
    ∀ i < gens.size + lenLL prog,
      Rep (nthV V i) (toMat ((Native.slpRun gens prog).getD i Native.one)) := by
  intro i hi
  rw [toMat_getD, toMat_slpRun]
  refine rep_slp V prog gens.size (gens.map toMat) (Array.size_map ..) (fun j hj => ?_) hp i hi
  rw [← toMat_getD]
  exact hV j hj

theorem e6_sound {codes bits iA iB : ℕ} {fwd bwd : List (List ℕ)} {tgt Fv Wv : List ℕ}
    (hc : codesOK codes = true)
    (hl : ∀ j < 12, Nat.beq (letterB codes bits j) (nthV Fv j) = true)
    (hf : ∀ t < lenLL fwd, slpLine Fv fwd 12 t = true)
    (hnF : Nat.beq (lenN Fv) (12 + lenLL fwd) = true)
    (hb : ∀ t < lenLL bwd, slpLine Wv bwd 2 t = true)
    (hnW : Nat.beq (lenN Wv) (2 + lenLL bwd) = true)
    (hiA : Nat.blt iA (lenN Fv) = true) (hiB : Nat.blt iB (lenN Fv) = true)
    (hA : Nat.beq (nthV Wv 0) (nthV Fv iA) = true) (hB : Nat.beq (nthV Wv 1) (nthV Fv iB) = true)
    (ht : tgtOK Fv Wv tgt = true)
    (h2 : ordB (nthV Fv iA) 2 = true) (h3 : ordB (nthV Fv iB) 3 = true)
    (h19 : ordB (mulB (nthV Fv iA) (nthV Fv iB)) 19 = true)
    (h5 : ordB (wordB (nthV Fv iA) (nthV Fv iB)
      [(0, true), (1, true), (0, true), (1, true), (1, true)]) 5 = true) :
    (Native.check codes bits fwd iA iB bwd tgt = true) ∧
      (Native.ordP (Native.wordMat (Native.genAB codes bits fwd iA iB).1
        (Native.genAB codes bits fwd iA iB).2
        [(0, true), (1, true), (0, true), (1, true), (1, true)]) 5 = true) := by
  rw [Nat.beq_eq] at hnF hnW
  rw [Nat.blt_eq] at hiA hiB
  have hsL : (Native.letters codes bits).size = 12 := by simp [Native.letters]
  have hL : ∀ j < (Native.letters codes bits).size,
      Rep (nthV Fv j) (toMat ((Native.letters codes bits).getD j Native.one)) := by
    intro j hj
    rw [hsL] at hj
    have h := hl j hj
    rw [Nat.beq_eq] at h
    exact rep_of_eq (rep_letterB hc bits hj) (by rw [Nat.beq_eq]; exact h.symm)
  have hF := rep_run hL (by rw [hsL]; exact hf)
  rw [hsL] at hF
  have RA : Rep (nthV Fv iA) (toMat (Native.genAB codes bits fwd iA iB).1) :=
    hF iA (by omega)
  have RB : Rep (nthV Fv iB) (toMat (Native.genAB codes bits fwd iA iB).2) :=
    hF iB (by omega)
  have hG : ∀ i < (#[(Native.genAB codes bits fwd iA iB).1,
      (Native.genAB codes bits fwd iA iB).2] : Array Native.Mat).size,
      Rep (nthV Wv i) (toMat ((#[(Native.genAB codes bits fwd iA iB).1,
        (Native.genAB codes bits fwd iA iB).2] : Array Native.Mat).getD i Native.one)) := by
    intro i hi
    change i < 2 at hi
    rcases i with _ | _ | i
    · exact rep_of_eq RA hA
    · exact rep_of_eq RB hB
    · omega
  have hW := rep_run hG hb
  change ∀ i < 2 + lenLL bwd, _ at hW
  refine ⟨?_, ordP_of_ordB (rep_wordB RA RB _) h5⟩
  unfold Native.check
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨fun j hj => ?_, ordP_of_ordB RA h2⟩, ordP_of_ordB RB h3⟩,
    ordP_of_ordB (by rw [toMat_mul]; exact rep_mulB RA RB) h19⟩
  have htj := allN_true ht j hj
  rw [andB_eq', Bool.and_eq_true, Nat.blt_eq, nthV_eq_getD tgt] at htj
  rw [eqM_iff_of_rep (hW _ (by omega)) (hL j (by rw [hsL]; exact hj))]
  exact htj.2

end CFSG.KC.Misc.E6Std

namespace CFSG.KD.Misc.E6Std

open CFSG.KC.Misc.E6Std CFSG.Monster.B.Classical.E6Adjoint CFSG.LieType.Chevalley.C2E6Std.MatrixModel

theorem facts :
    (Native.check bracketCodes formBits fwdProg idxA idxB bwdProg letterIdx = true) ∧
      (Native.ordP (Native.wordMat nativeAB.1 nativeAB.2
        [(0, true), (1, true), (0, true), (1, true), (1, true)]) 5 = true) :=
  e6_sound codes lets fwds lenF bwds lenW iA iB genA genB tgts ordA ordB3 ordAB ordW

end CFSG.KD.Misc.E6Std

end
