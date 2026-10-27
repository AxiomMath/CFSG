module

public import Certificates.Kernel.Misc.E6StdBridge
public import Certificates.Data.Kernel.Misc.E6StdThree
public import Certificates.Data.CFSGNative.Chevalley.C2E6CertSylowThree

public section

namespace CFSG.KC.Misc.E6Std

open CFSG.KC.Misc CFSG.KC.Ord CFSG.KC.LQT.P CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Chevalley.C2E6Std.MatrixModel CFSG.Monster.Existence.StdOdd

attribute [local irreducible] mulB powB oneB rowStarts fullRow rootB

theorem colB_eq (col : ℕ → ℕ) : colB col = rootRec col 78 := by
  have h : (fun l acc => letN acc fun acc => blowCol l (col l) acc) =
      (fun l acc => orRec (blk4 l (col l)) acc 78) :=
    funext fun l => funext fun acc => (letN_eq _ _).trans (blowCol_eq _ _ _)
  unfold colB rootRec
  rw [h]
  rfl

theorem rep_colB {P : Native.Mat} (col : ℕ → ℕ)
    (hP : ∀ l < 78, ∀ k < 78, (col l).testBit k = (P.getD l (0, 0)).1.testBit k ∧
      (col l).testBit (k + 78) = (P.getD l (0, 0)).2.testBit k) :
    Rep (colB col) (toMat P) := by
  rw [colB_eq]
  refine rep_of_testBit (rootRec_lt _) fun k l a b => ?_
  obtain ⟨h0, h1⟩ := hP l l.2 k k.2
  rw [← h0, ← h1, Bool.eq_iff_iff, testBit_rootRec]
  have hk := k.2
  have hl := l.2
  set v := col l
  fin_cases a <;> fin_cases b <;> simp only [bb] <;> constructor
  all_goals first
    | (rintro ⟨l', hl', k', hk', h⟩
       rw [testBit_blk4] at h
       rcases h with ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ | ⟨e, h⟩ <;>
         simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero] at e <;>
         first
         | (have : l' = l := by omega
            have : k' = k := by omega
            subst_vars
            simpa using h)
         | omega)
    | (intro h
       refine ⟨l, hl, k, hk, ?_⟩
       rw [testBit_blk4]
       simp_all)

theorem testBit_shiftLeft_one (l k : ℕ) : (1 <<< l).testBit k = decide (k = l) := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : k = l
  · simp [h]
  · simp [h, Ne.symm h]

theorem diag_getD (es : List ℕ) {l : ℕ} (hl : l < 78) {e : ℕ} (he : es.getD l 0 % 3 = e) :
    (CertNative.diagMat es).getD l (0, 0) =
      if e = 0 then ((1 <<< l : ℕ), (0 : ℕ)) else if e = 1 then (0, 1 <<< l)
        else (1 <<< l, 1 <<< l) := by
  have hm : e < 3 := he ▸ Nat.mod_lt _ (by norm_num)
  simp only [CertNative.diagMat, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD] at he ⊢
  simp only [Array.getElem?_map, List.getElem?_toArray, List.getElem?_range hl, Option.map_some,
    Option.getD_some]
  rw [he]
  interval_cases e <;> rfl

theorem diagColK_eq (es : List ℕ) (l : ℕ) {e : ℕ} (he : es.getD l 0 % 3 = e) :
    diagColK es l = (Bool.rec (motive := fun _ => ℕ) 1 0 (Nat.beq e 1) * (1 <<< l)) |||
      ((Bool.rec (motive := fun _ => ℕ) 1 0 (Nat.beq e 0) * (1 <<< l)) <<< 78) := by
  unfold diagColK
  rw [letN_eq, nthV_eq_getD]
  change (Bool.rec (motive := fun _ => ℕ) 1 0 (Nat.beq (es.getD l 0 % 3) 1) * (1 <<< l)) |||
      ((Bool.rec (motive := fun _ => ℕ) 1 0 (Nat.beq (es.getD l 0 % 3) 0) * (1 <<< l)) <<< 78) = _
  rw [he]

theorem rep_diagB (es : List ℕ) : Rep (diagB es) (toMat (CertNative.diagMat es)) := by
  refine rep_colB _ fun l hl k hk => ?_
  have hm : es.getD l 0 % 3 < 3 := Nat.mod_lt _ (by norm_num)
  rw [diag_getD es hl rfl, diagColK_eq es l rfl]
  generalize es.getD l 0 % 3 = e at hm ⊢
  have h1 : (k + 78 = l) ↔ False := ⟨fun h => by omega, False.elim⟩
  have h2 : (k = l + 78) ↔ False := ⟨fun h => by omega, False.elim⟩
  have h3 : (k + 78 = l + 78) ↔ (k = l) := by omega
  interval_cases e
  · change ((1 * (1 <<< l)) ||| ((0 * (1 <<< l)) <<< 78)).testBit k = _ ∧
      ((1 * (1 <<< l)) ||| ((0 * (1 <<< l)) <<< 78)).testBit (k + 78) = _
    simp only [Nat.one_mul, Nat.zero_mul, Nat.zero_shiftLeft, Nat.testBit_or,
      testBit_shiftLeft_one, Nat.zero_testBit, h1]
    simp [testBit_shiftLeft_one, -Nat.testBit_shiftLeft]
  · change ((0 * (1 <<< l)) ||| ((1 * (1 <<< l)) <<< 78)).testBit k = _ ∧
      ((0 * (1 <<< l)) ||| ((1 * (1 <<< l)) <<< 78)).testBit (k + 78) = _
    simp only [Nat.one_mul, Nat.zero_mul, ← Nat.shiftLeft_add, Nat.testBit_or,
      testBit_shiftLeft_one, Nat.zero_testBit, h2, h3]
    simp [testBit_shiftLeft_one, -Nat.testBit_shiftLeft]
  · change ((1 * (1 <<< l)) ||| ((1 * (1 <<< l)) <<< 78)).testBit k = _ ∧
      ((1 * (1 <<< l)) ||| ((1 * (1 <<< l)) <<< 78)).testBit (k + 78) = _
    simp only [Nat.one_mul, ← Nat.shiftLeft_add, Nat.testBit_or, testBit_shiftLeft_one, h1, h2, h3]
    simp [testBit_shiftLeft_one, -Nat.testBit_shiftLeft]

theorem bN_eq (b : Bool) : bN b = b.toNat := by
  cases b <;> rfl

theorem rep_letLB {codes : ℕ} (hc : codesOK codes = true) (bits : ℕ) (l : ℕ × Bool × Bool)
    (hl : l.1 < 72) : Rep (letLB codes bits l) (toMat (CertNative.letterMat codes bits l)) := by
  obtain ⟨j, c₀, c₁⟩ := l
  change Rep (rootB codes bits (6 + j) (bN c₀) (bN c₁))
    (toMat (Native.rootMat codes bits (6 + j) c₀ c₁))
  rw [bN_eq, bN_eq]
  exact rep_rootB codes bits (6 + j) c₀ c₁ (by change j < 72 at hl; omega)
    fun _ hl' => code_lt_of_codesOK hc (by change j < 72 at hl; omega) hl'

theorem twLB_eq (codes bits : ℕ) (gam : List ℕ) (l : ℕ × Bool × Bool) :
    twLB codes bits gam l = letLB codes bits (CertNative.twistLetter gam l) := by
  obtain ⟨j, c₀, c₁⟩ := l
  change rootB codes bits (Nat.add 6 (nthV gam j)) _ _ = rootB codes bits (Nat.add 6 (gam.getD j 0)) _ _
  rw [nthV_eq_getD]
  cases c₀ <;> cases c₁ <;> rfl

theorem wordLB_foldl {codes : ℕ} (hc : codesOK codes = true) (bits : ℕ) :
    ∀ (w : List (ℕ × Bool × Bool)), (∀ l ∈ w, l.1 < 72) → ∀ (acc : ℕ) (A : Native.Mat),
      Rep acc (toMat A) →
      Rep (List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
        (fun l _ ih acc => ih (mulB acc (letLB codes bits l))) w acc)
        (toMat (w.foldl (fun acc l => Native.mul acc (CertNative.letterMat codes bits l)) A)) := by
  intro w
  induction w with
  | nil => intro _ acc A h; exact h
  | cons l w ih =>
    intro hw acc A h
    refine ih (fun x hx => hw x (List.mem_cons_of_mem _ hx)) _ _ ?_
    rw [toMat_mul]
    exact rep_mulB h (rep_letLB hc bits l (hw l List.mem_cons_self))

theorem rep_wordLB {codes : ℕ} (hc : codesOK codes = true) (bits : ℕ) (w : List (ℕ × Bool × Bool))
    (hw : ∀ l ∈ w, l.1 < 72) :
    Rep (wordLB codes bits w) (toMat (CertNative.wordMat codes bits w)) :=
  wordLB_foldl hc bits w hw oneB Native.one (toMat_one ▸ rep_oneB)

theorem wordTB_eq (codes bits : ℕ) (gam : List ℕ) (w : List (ℕ × Bool × Bool)) :
    wordTB codes bits gam w = wordLB codes bits (w.map (CertNative.twistLetter gam)) := by
  have key : ∀ acc, List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
      (fun l _ ih acc => ih (mulB acc (twLB codes bits gam l))) w acc =
      List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
      (fun l _ ih acc => ih (mulB acc (letLB codes bits l))) (w.map (CertNative.twistLetter gam))
        acc := by
    induction w with
    | nil => intro acc; rfl
    | cons l w ih =>
      intro acc
      rw [List.map_cons]
      change _ = List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
        (fun l _ ih acc => ih (mulB acc (letLB codes bits l))) (w.map (CertNative.twistLetter gam))
          (mulB acc (letLB codes bits (CertNative.twistLetter gam l)))
      rw [← twLB_eq]
      exact ih _
  exact key oneB

theorem ltW_true {w : List (ℕ × Bool × Bool)} (h : ltW w = true) : ∀ l ∈ w, l.1 < 72 := by
  induction w with
  | nil => intro l hl; simp at hl
  | cons x w ih =>
    change andB (Nat.blt x.1 72) (ltW w) = true at h
    rw [andB_eq', Bool.and_eq_true, Nat.blt_eq] at h
    intro l hl
    rcases List.mem_cons.1 hl with rfl | hl
    · exact h.1
    · exact ih h.2 l hl

theorem twist_lt {gam : List ℕ} (hg : allN 72 (fun j => Nat.blt (nthV gam j) 72) = true)
    {w : List (ℕ × Bool × Bool)} (hw : ∀ l ∈ w, l.1 < 72) :
    ∀ l ∈ w.map (CertNative.twistLetter gam), l.1 < 72 := by
  intro l hl
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hl
  have h := allN_true hg x.1 (hw x hx)
  rw [Nat.blt_eq, nthV_eq_getD] at h
  exact h

theorem rep_getD_map {codes : ℕ} (hc : codesOK codes = true) (bits : ℕ)
    {ws : List (List (ℕ × Bool × Bool))} (hw : ∀ w ∈ ws, ∀ l ∈ w, l.1 < 72) {V : List ℕ}
    (hV : ∀ i < ws.length, Nat.beq (wordLB codes bits (ws.getD i [])) (nthV V i) = true)
    {i : ℕ} (hi : i < ws.length) :
    Rep (nthV V i) (toMat ((ws.map (CertNative.wordMat codes bits)).getD i Native.one)) := by
  have e : (ws.map (CertNative.wordMat codes bits)).getD i Native.one =
      CertNative.wordMat codes bits (ws.getD i []) := by
    simp [List.getD_eq_getElem?_getD, hi]
  rw [e]
  have h := hV i hi
  rw [Nat.beq_eq] at h
  rw [← h]
  exact rep_wordLB hc bits _ (hw _ (by simp [List.getD_eq_getElem?_getD, hi]))

theorem fixedOK_of {codes : ℕ} (hc : codesOK codes = true) (bits : ℕ) {gam : List ℕ}
    (hg : allN 72 (fun j => Nat.blt (nthV gam j) 72) = true)
    {ws : List (List (ℕ × Bool × Bool))} (hw : ∀ w ∈ ws, ∀ l ∈ w, l.1 < 72)
    (h : ∀ w ∈ ws, Nat.beq (wordTB codes bits gam w) (wordLB codes bits w) = true) :
    CertNative.fixedOK codes bits gam ws = true := by
  unfold CertNative.fixedOK
  rw [List.all_eq_true]
  intro w hw'
  have h1 := h w hw'
  rw [wordTB_eq] at h1
  rw [eqM_iff_of_rep (rep_wordLB hc bits _ (twist_lt hg (hw w hw'))) (rep_wordLB hc bits w (hw w hw'))]
  exact h1

theorem torusOK_of {codes : ℕ} (hc : codesOK codes = true) (bits : ℕ)
    {hs : List (List (ℕ × Bool × Bool))} {es : List (List ℕ)} (hw : ∀ w ∈ hs, ∀ l ∈ w, l.1 < 72)
    (h : ∀ j < hs.length, Nat.beq (wordLB codes bits (hs.getD j [])) (diagB (es.getD j [])) = true) :
    CertNative.torusOK codes bits hs es = true := by
  unfold CertNative.torusOK
  rw [List.all_eq_true]
  intro j hj
  rw [List.mem_range] at hj
  have hm : hs.getD j [] ∈ hs := by simp [List.getD_eq_getElem?_getD, hj]
  rw [eqM_iff_of_rep (rep_wordLB hc bits _ (hw _ hm)) (rep_diagB _)]
  exact h j hj

theorem rep_mulM {a b : ℕ} {P Q : Native.Mat} (ha : Rep a (toMat P)) (hb : Rep b (toMat Q)) :
    Rep (mulB a b) (toMat (Native.mul P Q)) := by
  rw [toMat_mul]
  exact rep_mulB ha hb

theorem rep_powM {a : ℕ} {P : Native.Mat} (n : ℕ) (ha : Rep a (toMat P)) :
    Rep (powB a n) (toMat (Native.pow P n)) := by
  rw [toMat_pow]
  exact rep_powB ha n

theorem rep_psiB {E : List ℕ} {M : List Native.Mat}
    (hE : ∀ i < 5, Rep (nthV E i) (toMat (M.getD i Native.one))) (ns : List ℕ) :
    Rep (psiB E ns) (toMat (CertNative.psiMat M ns)) := by
  have rp : ∀ i < 5, Rep (powB (nthV E i) (nthV ns i))
      (toMat (Native.pow (M.getD i Native.one) (ns.getD i 0))) := fun i hi => by
    rw [← nthV_eq_getD]
    exact rep_powM _ (hE i hi)
  exact rep_mulM (rep_mulM (rep_mulM (rep_mulM (rp 0 (by omega)) (rp 1 (by omega)))
    (rp 2 (by omega))) (rp 3 (by omega))) (rp 4 (by omega))

theorem nthLL_eq_getD (L : List (List ℕ)) (i : ℕ) : nthLL L i = L.getD i [] := by
  induction L generalizing i with
  | nil => rfl
  | cons x L ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem conjOK_of {codes : ℕ} (hc : codesOK codes = true) (bits : ℕ)
    {rs es : List (List (ℕ × Bool × Bool))} {cols : List (List ℕ)} {R E : List ℕ}
    (hrw : ∀ w ∈ rs, ∀ l ∈ w, l.1 < 72) (hew : ∀ w ∈ es, ∀ l ∈ w, l.1 < 72)
    (hrl : rs.length = 6) (hel : es.length = 5)
    (hR : ∀ i < rs.length, Nat.beq (wordLB codes bits (rs.getD i [])) (nthV R i) = true)
    (hE : ∀ i < es.length, Nat.beq (wordLB codes bits (es.getD i [])) (nthV E i) = true)
    (h : ∀ i < 6, allN 5 (fun j => Nat.beq (mulB (nthV R i) (nthV E j))
      (mulB (psiB E (nthLL cols (Nat.add (Nat.mul 5 i) j))) (nthV R i))) = true) :
    CertNative.conjOK codes bits rs es cols = true := by
  unfold CertNative.conjOK
  simp only [List.all_eq_true, List.mem_range]
  intro i hi j hj
  have hRi := rep_getD_map hc bits hrw hR (i := i) (by omega)
  have hEall : ∀ j < 5, Rep (nthV E j) (toMat ((es.map (CertNative.wordMat codes bits)).getD j
      Native.one)) := fun j hj => rep_getD_map hc bits hew hE (by omega)
  have hpsi := rep_psiB hEall (cols.getD (5 * i + j) [])
  rw [eqM_iff_of_rep (rep_mulM hRi (hEall j hj)) (rep_mulM hpsi hRi)]
  have h1 := allN_true (h i hi) j hj
  have e : nthLL cols (Nat.add (Nat.mul 5 i) j) = cols.getD (5 * i + j) [] := by
    rw [nthLL_eq_getD]
    rfl
  rw [e] at h1
  exact h1

theorem rep_line2 {X Y : Native.Mat} {a b : ℕ} (hX : Rep a (toMat X)) (hY : Rep b (toMat Y))
    (line : List ℕ) (hl : ∀ x ∈ line, x < 2) :
    Rep (lineB [a, b] line) (toMat (Native.lineProd #[X, Y] line)) := by
  rw [toMat_lineProd]
  refine rep_lineB [a, b] (#[X, Y].map toMat) (g := 2) (fun i hi => ?_) line hl
  rw [← toMat_getD]
  rcases i with _ | _ | i
  · exact hX
  · exact hY
  · omega

theorem getD_map_lineProd (G : Array Native.Mat) (pw : List (List ℕ)) (j : ℕ) :
    (pw.map (Native.lineProd G)).getD j Native.one = Native.lineProd G (pw.getD j []) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases pw[j]? <;> rfl

theorem toArray_getD {α : Type*} (l : List α) (i : ℕ) (d : α) : l.toArray.getD i d = l.getD i d := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem splitOK_of {codes : ℕ} (hc : codesOK codes = true) (bits : ℕ)
    {rs : List (List (ℕ × Bool × Bool))} {tAi tBi ra rb R W : List ℕ} {pw : List (List ℕ)}
    (hrw : ∀ w ∈ rs, ∀ l ∈ w, l.1 < 72)
    (hR : ∀ i < rs.length, Nat.beq (wordLB codes bits (rs.getD i [])) (nthV R i) = true)
    (htA : ∀ i ∈ tAi, i < rs.length) (htB : ∀ i ∈ tBi, i < rs.length)
    (hpw : ∀ j < 81, ∀ x ∈ pw.getD j [], x < 2)
    (hW : ∀ j < 81, Nat.beq (lineB [lineB R tAi, lineB R tBi] (pw.getD j [])) (nthV W j) = true)
    (hra : ∀ j < 81, ra.getD j 0 < 81) (hrb : ∀ j < 81, rb.getD j 0 < 81)
    (h3A : Nat.beq (powB (lineB R tAi) 3) oneB = true)
    (h3B : Nat.beq (powB (lineB R tBi) 3) oneB = true)
    (hsA : ∀ j < 81, Nat.beq (mulB (nthV W j) (lineB R tAi)) (nthV W (ra.getD j 0)) = true)
    (hsB : ∀ j < 81, Nat.beq (mulB (nthV W j) (lineB R tBi)) (nthV W (rb.getD j 0)) = true) :
    CertNative.splitOK codes bits rs tAi tBi pw ra rb = true := by
  have hRV : ∀ i < rs.length, Rep (nthV R i)
      ((((rs.map (CertNative.wordMat codes bits)).toArray).map toMat).getD i 1) := by
    intro i hi
    rw [← toMat_getD, toArray_getD]
    exact rep_getD_map hc bits hrw hR hi
  have rline : ∀ line : List ℕ, (∀ i ∈ line, i < rs.length) →
      Rep (lineB R line) (toMat (Native.lineProd (rs.map (CertNative.wordMat codes bits)).toArray
        line)) := fun line hl => by
    rw [toMat_lineProd]
    exact rep_lineB R _ hRV line hl
  have hA := rline tAi htA
  have hB := rline tBi htB
  have hWj : ∀ j < 81, Rep (nthV W j) (toMat ((pw.map (Native.lineProd
      #[Native.lineProd (rs.map (CertNative.wordMat codes bits)).toArray tAi,
        Native.lineProd (rs.map (CertNative.wordMat codes bits)).toArray tBi])).getD j
        Native.one)) := by
    intro j hj
    rw [getD_map_lineProd]
    have h := hW j hj
    rw [Nat.beq_eq] at h
    rw [← h]
    exact rep_line2 hA hB _ (hpw j hj)
  unfold CertNative.splitOK
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨⟨?_, ?_⟩, fun j hj => ⟨?_, ?_⟩⟩
  · rw [eqM_iff_of_rep (rep_powM 3 hA) (toMat_one ▸ rep_oneB)]
    exact h3A
  · rw [eqM_iff_of_rep (rep_powM 3 hB) (toMat_one ▸ rep_oneB)]
    exact h3B
  · rw [eqM_iff_of_rep (rep_mulM (hWj j hj) hA) (hWj _ (hra j hj))]
    exact hsA j hj
  · rw [eqM_iff_of_rep (rep_mulM (hWj j hj) hB) (hWj _ (hrb j hj))]
    exact hsB j hj

end CFSG.KC.Misc.E6Std

end
