
module

public import Certificates.Kernel.Misc.E6StdRoot
public import Certificates.Kernel.Misc.E6Std
public import CFSG.LieType.Chevalley.C2E6StdMatrixModelBase

public section

namespace CFSG.KC.Misc.E6Std

open CFSG.KC.Misc CFSG.KC.Ord CFSG.KC.LQT.P CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Chevalley.C2E6Std.MatrixModel CFSG.Monster.B.Classical.E6Adjoint
open CFSG.LieType.Chevalley.C2E6Std.MatrixModel.Native (code)

attribute [local irreducible] mulB powB oneB rowStarts fullRow rootB

abbrev MK : Type := Matrix (Fin 78) (Fin 78) K

theorem allN_true {m : ℕ} {f : ℕ → Bool} (h : allN m f = true) : ∀ i < m, f i = true := by
  induction m with
  | zero => intro i hi; omega
  | succ m ih =>
    change andB (f m) (allN m f) = true at h
    rw [andB_eq', Bool.and_eq_true] at h
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact ih h.2 i hi
    · exact h.1

theorem allL_true {l : List ℕ} {f : ℕ → Bool} (h : allL l f = true) : ∀ x ∈ l, f x = true := by
  induction l with
  | nil => intro x hx; simp at hx
  | cons y l ih =>
    change andB (f y) (allL l f) = true at h
    rw [andB_eq', Bool.and_eq_true] at h
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact ih h.2 x hx

theorem code_lt_of_codesOK {codes : ℕ} (h : codesOK codes = true) {r l : ℕ} (hr : r < 78)
    (hl : l < 78) : code codes r l < 136 := by
  have := allN_true (allN_true h r hr) l hl
  rw [Nat.blt_eq, codeK_eq] at this
  exact this

theorem getD_push_of_lt {α : Type*} (G : Array α) (x d : α) {i : ℕ} (hi : i < G.size) :
    (G.push x).getD i d = G.getD i d := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, hi, Nat.ne_of_lt hi]

theorem getD_push_size {α : Type*} (G : Array α) (x d : α) : (G.push x).getD G.size d = x := by
  simp [Array.getD_eq_getD_getElem?]

theorem toMat_getD (A : Array Native.Mat) (i : ℕ) :
    toMat (A.getD i Native.one) = (A.map toMat).getD i 1 := by
  rw [← toMat_one, getD_map]

theorem rep_xB {codes : ℕ} (hc : codesOK codes = true) (bits : ℕ) {j : ℕ} (hj : j < 72)
    (b₀ b₁ : Bool) :
    Rep (xB codes bits j b₀.toNat b₁.toNat) (toMat (Native.xMat codes bits j b₀ b₁)) :=
  rep_rootB codes bits (6 + j) b₀ b₁ (by omega) fun _ hl => code_lt_of_codesOK hc (by omega) hl

theorem rep_nB {codes : ℕ} (hc : codesOK codes = true) (bits : ℕ) {j : ℕ} (hj : j < 6) :
    Rep (nB codes bits j) (toMat (Native.nMat codes bits j)) := by
  have hx := rep_xB hc bits (j := j) (by omega) true false
  have hy : Rep (rootB codes bits (Nat.add 12 (Nat.mul 2 j)) 1 0)
      (toMat (Native.yMat codes bits j)) :=
    rep_rootB codes bits (12 + 2 * j) true false (by omega)
      fun _ hl => code_lt_of_codesOK hc (by omega) hl
  unfold nB Native.nMat
  rw [letN_eq, toMat_mul, toMat_mul]
  exact rep_mulB (rep_mulB hx hy) hx

theorem rep_letterB {codes : ℕ} (hc : codesOK codes = true) (bits : ℕ) {j : ℕ} (hj : j < 12) :
    Rep (letterB codes bits j) (toMat ((Native.letters codes bits).getD j Native.one)) := by
  have x := fun (i : ℕ) (hi : i < 72) (b₀ b₁ : Bool) => rep_xB hc bits (j := i) hi b₀ b₁
  have n := fun (i : ℕ) (hi : i < 6) => rep_nB hc bits (j := i) hi
  have xx : ∀ i i' (hi : i < 72) (hi' : i' < 72) (b₀ b₁ b₀' b₁' : Bool),
      Rep (mulB (xB codes bits i b₀.toNat b₁.toNat) (xB codes bits i' b₀'.toNat b₁'.toNat))
        (toMat (Native.mul (Native.xMat codes bits i b₀ b₁) (Native.xMat codes bits i' b₀' b₁'))) :=
    fun i i' hi hi' b₀ b₁ b₀' b₁' => by
      rw [toMat_mul]
      exact rep_mulB (x i hi b₀ b₁) (x i' hi' b₀' b₁')
  have nn : ∀ i i' (hi : i < 6) (hi' : i' < 6),
      Rep (mulB (nB codes bits i) (nB codes bits i'))
        (toMat (Native.mul (Native.nMat codes bits i) (Native.nMat codes bits i'))) :=
    fun i i' hi hi' => by
      rw [toMat_mul]
      exact rep_mulB (n i hi) (n i' hi')
  interval_cases j
  · exact xx 0 5 (by omega) (by omega) true false true false
  · exact xx 0 5 (by omega) (by omega) false true true true
  · exact xx 0 5 (by omega) (by omega) true true false true
  · exact xx 2 4 (by omega) (by omega) true false true false
  · exact xx 2 4 (by omega) (by omega) false true true true
  · exact xx 2 4 (by omega) (by omega) true true false true
  · exact x 3 (by omega) true false
  · exact x 1 (by omega) true false
  · exact nn 0 5 (by omega) (by omega)
  · exact nn 2 4 (by omega) (by omega)
  · exact n 3 (by omega)
  · exact n 1 (by omega)

theorem rep_lineRec (V : List ℕ) (G : Array MK) {g : ℕ}
    (hV : ∀ i < g, Rep (nthV V i) (G.getD i 1)) (line : List ℕ) (hl : ∀ i ∈ line, i < g) :
    ∀ (acc : ℕ) (A : MK), Rep acc A →
      Rep (List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
        (fun i _ ih acc => ih (mulB acc (nthV V i))) line acc)
        (line.foldl (fun acc i => acc * G.getD i 1) A) := by
  induction line with
  | nil => intro acc A h; exact h
  | cons i line ih =>
    intro acc A h
    exact ih (fun j hj => hl j (List.mem_cons_of_mem _ hj)) _ _
      (rep_mulB h (hV i (hl i List.mem_cons_self)))

theorem rep_lineB (V : List ℕ) (G : Array MK) {g : ℕ}
    (hV : ∀ i < g, Rep (nthV V i) (G.getD i 1)) (line : List ℕ) (hl : ∀ i ∈ line, i < g) :
    Rep (lineB V line) (lineProdG G line) :=
  rep_lineRec V G hV line hl oneB 1 rep_oneB

theorem nthLL_cons_succ (line : List ℕ) (prog : List (List ℕ)) (t : ℕ) :
    nthLL (line :: prog) (t + 1) = nthLL prog t := rfl

theorem nthLL_cons_zero (line : List ℕ) (prog : List (List ℕ)) : nthLL (line :: prog) 0 = line :=
  rfl

theorem rep_slp (V : List ℕ) (prog : List (List ℕ)) :
    ∀ (g : ℕ) (G : Array MK), G.size = g → (∀ i < g, Rep (nthV V i) (G.getD i 1)) →
      (∀ t < lenLL prog, slpLine V prog g t = true) →
      ∀ i < g + lenLL prog, Rep (nthV V i) ((slpRunG G prog).getD i 1) := by
  induction prog with
  | nil =>
    intro g G _ hV _ i hi
    exact hV i hi
  | cons line prog ih =>
    intro g G hG hV hlines
    have h0 := hlines 0 (Nat.succ_pos _)
    unfold slpLine at h0
    rw [andB_eq', Bool.and_eq_true, nthLL_cons_zero] at h0
    have hl : ∀ i ∈ line, i < g := by
      intro i hi
      have := allL_true h0.1 i hi
      rw [Nat.blt_eq] at this
      exact this
    have hx : Rep (nthV V g) (lineProdG G line) :=
      rep_of_eq (rep_lineB V G hV line hl) (by rw [Nat.beq_eq] at h0 ⊢; exact h0.2.symm)
    have hV' : ∀ i < g + 1, Rep (nthV V i) ((G.push (lineProdG G line)).getD i 1) := by
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · rw [getD_push_of_lt _ _ _ (by omega)]
        exact hV i hi
      · rw [← hG, getD_push_size, hG]
        exact hx
    have hlines' : ∀ t < lenLL prog, slpLine V prog (g + 1) t = true := by
      intro t ht
      have := hlines (t + 1) (Nat.succ_lt_succ ht)
      unfold slpLine at this ⊢
      rw [nthLL_cons_succ] at this
      have e : Nat.add g (t + 1) = Nat.add (g + 1) t := by
        change g + (t + 1) = g + 1 + t
        omega
      rw [e] at this
      exact this
    intro i hi
    have := ih (g + 1) _ (by rw [Array.size_push, hG]) hV' hlines' i (by
      change i < g + (lenLL prog + 1) at hi
      omega)
    exact this

open CFSG.KD.Misc.E6Std in
theorem rep_Fvals : ∀ i < 12 + lenLL fwdProg, Rep (nthV Fvals i)
    ((slpRunG ((Native.letters bracketCodes formBits).map toMat) fwdProg).getD i 1) := by
  refine rep_slp Fvals fwdProg 12 _ (by simp [Native.letters]) (fun i hi => ?_) fwds
  rw [← toMat_getD]
  have h := lets i hi
  rw [Nat.beq_eq] at h
  exact rep_of_eq (rep_letterB codes formBits hi) (by rw [Nat.beq_eq]; exact h.symm)

open CFSG.KD.Misc.E6Std in
theorem rep_genAB {i : ℕ} (hi : Nat.blt i (lenN Fvals) = true) :
    Rep (nthV Fvals i) (toMat ((Native.slpRun (Native.letters bracketCodes formBits) fwdProg).getD
      i Native.one)) := by
  rw [toMat_getD, toMat_slpRun]
  refine rep_Fvals i ?_
  have h := lenF
  rw [Nat.blt_eq] at hi
  rw [Nat.beq_eq] at h
  omega

open CFSG.KD.Misc.E6Std in
theorem rep_A : Rep (nthV Fvals idxA) (toMat nativeAB.1) := rep_genAB iA

open CFSG.KD.Misc.E6Std in
theorem rep_B : Rep (nthV Fvals idxB) (toMat nativeAB.2) := rep_genAB iB

end CFSG.KC.Misc.E6Std

end
