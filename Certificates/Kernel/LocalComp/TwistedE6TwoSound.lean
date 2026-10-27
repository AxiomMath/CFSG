module

public import Certificates.Kernel.Misc.E6StdBridge
public import Certificates.Data.Kernel.TwistedE6Two
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExcHypIITwistedE6TwoTests

public section

namespace CFSG.KC.TwistedE6Two

open CFSG.KC.Misc CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.E6Std
open CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std.MatrixModel
open CFSG.Monster.B.Classical.E6Adjoint CFSG.ComponentClassification.RankTwoExcHypII.TwistedE6Two

attribute [local irreducible] mulB powB oneB rowStarts fullRow rootB

@[expose] def RepAll (V : List ℕ) (vals : Array Native.Mat) (n : ℕ) : Prop :=
  ∀ i < n, Rep (nthV V i) (toMat (vals.getD i Native.one))

theorem rep_one : Rep oneB (toMat Native.one) := by
  rw [toMat_one]
  exact rep_oneB

theorem rep_root {codes : ℕ} (hc : codesOK codes = true) (bits : ℕ) {r : ℕ} (hr : r < 78)
    (b₀ b₁ : Bool) :
    Rep (rootB codes bits r b₀.toNat b₁.toNat) (toMat (Native.rootMat codes bits r b₀ b₁)) :=
  rep_rootB codes bits r b₀ b₁ hr fun _ hl => code_lt_of_codesOK hc hr hl

theorem rep_mul {A B : ℕ} {X Y : Native.Mat} (hA : Rep A (toMat X)) (hB : Rep B (toMat Y)) :
    Rep (mulB A B) (toMat (Native.mul X Y)) := by
  rw [toMat_mul]
  exact rep_mulB hA hB

theorem rep_pow {A : ℕ} {X : Native.Mat} (hA : Rep A (toMat X)) (m : ℕ) :
    Rep (powB A m) (toMat (Native.pow X m)) := by
  rw [toMat_pow]
  exact rep_powB hA m

theorem lt78 {k : ℕ} (hk : k < 72) : Nat.add k 6 < 78 := by
  rw [Nat.add_eq]
  omega

theorem rep_genK {codes : ℕ} (hc : codesOK codes = true) (bits : ℕ) {k r : ℕ} (hk : k < 72)
    (hr : r < 72) :
    Rep (genK codes bits k r) (toMat (if r = k then Native.rootMat codes bits (k + 6) true false
      else Native.mul (Native.rootMat codes bits (k + 6) true false)
        (Native.rootMat codes bits (r + 6) true false))) := by
  by_cases h : r = k
  · subst h
    simp only [genK, Nat.beq_refl, ↓reduceIte]
    exact rep_root hc bits (lt78 hk) true false
  · have hb : Nat.beq r k = false := by
      rw [Bool.eq_false_iff, ne_eq, Nat.beq_eq]
      exact h
    simp only [genK, hb, h, ↓reduceIte]
    exact rep_mul (rep_root hc bits (lt78 hk) true false) (rep_root hc bits (lt78 hr) true false)

theorem rep_genWK {codes : ℕ} (hc : codesOK codes = true) (bits : ℕ) {k r : ℕ} (hk : k < 72)
    (hr : r < 72) :
    Rep (genWK codes bits k r) (toMat (if r = k then Native.rootMat codes bits (k + 6) true false
      else Native.mul (Native.rootMat codes bits (k + 6) false true)
        (Native.rootMat codes bits (r + 6) true true))) := by
  by_cases h : r = k
  · subst h
    simp only [genWK, Nat.beq_refl, ↓reduceIte]
    exact rep_root hc bits (lt78 hk) true false
  · have hb : Nat.beq r k = false := by
      rw [Bool.eq_false_iff, ne_eq, Nat.beq_eq]
      exact h
    simp only [genWK, hb, h, ↓reduceIte]
    exact rep_mul (rep_root hc bits (lt78 hk) false true) (rep_root hc bits (lt78 hr) true true)

theorem nGens_getD {k : ℕ} (hk : k < 72) : nGens.getD k Native.one = nGen k := by
  simp [nGens, Array.getD_eq_getD_getElem?, hk]

theorem repAll_nGens {V : List ℕ} (h : gensOK bracketCodes formBits rhoIdx V 0 = true) :
    RepAll V nGens 72 := by
  intro k hk
  have hk' := allN_true h k hk
  rw [andB_eq', Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, Nat.add_eq, Nat.zero_add] at hk'
  rw [nGens_getD hk, nGen, ← nthV_eq_getD]
  refine rep_of_eq (rep_genK CFSG.KD.Misc.E6Std.codes formBits hk hk'.1) ?_
  rw [Nat.beq_eq]
  exact hk'.2.symm

theorem repAll_run {V : List ℕ} {gens : Array Native.Mat} {prog : List (List ℕ)}
    (hV : RepAll V gens gens.size) (hp : ∀ t < lenLL prog, slpLine V prog gens.size t = true) :
    RepAll V (Native.slpRun gens prog) (gens.size + lenLL prog) :=
  rep_run hV hp

theorem rep_line {V : List ℕ} {vals : Array Native.Mat} {n : ℕ} (h : RepAll V vals n)
    {line : List ℕ} (hl : allLt line n = true) :
    Rep (lineB V line) (toMat (Native.lineProd vals line)) := by
  rw [toMat_lineProd]
  refine rep_lineB V (vals.map toMat) (g := n) (fun i hi => ?_) line fun i hi => ?_
  · rw [← toMat_getD]
    exact h i hi
  · have := allL_true hl i hi
    rwa [Nat.blt_eq] at this

@[expose] def oddN (vals : Array Native.Mat) (X : Native.Mat) (i m : ℕ) : Bool :=
  m % 2 == 1 && Native.eqM (Native.pow (vals.getD i Native.one) m) Native.one &&
    Native.eqM (Native.mul (vals.getD i Native.one) X) (Native.mul X (vals.getD i Native.one))

theorem oddK_lt {V : List ℕ} {T n i m : ℕ} (hk : oddK V T n i m = true) : i < n := by
  unfold oddK at hk
  simp only [andB_eq', letB_eq', Bool.and_eq_true, Nat.blt_eq] at hk
  exact hk.2.1

theorem oddN_of_oddK {V : List ℕ} {vals : Array Native.Mat} {n T i m : ℕ} {X : Native.Mat}
    (h : RepAll V vals n) (hT : Rep T (toMat X)) (hk : oddK V T n i m = true) :
    oddN vals X i m = true := by
  have hi := oddK_lt hk
  unfold oddK at hk
  simp only [andB_eq', letB_eq', Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at hk
  obtain ⟨hm, -, hp, hc⟩ := hk
  have hv := h i hi
  unfold oddN
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨hm, ?_⟩, ?_⟩
  · rw [eqM_iff_of_rep (rep_pow hv m) rep_one, Nat.beq_eq]
    exact hp
  · rw [eqM_iff_of_rep (rep_mul hv hT) (rep_mul hT hv), Nat.beq_eq]
    exact hc

theorem factor_of_factorK {V : List ℕ} {vals gens : Array Native.Mat} {t n g : ℕ}
    {X : Native.Mat} {D : List (ℕ × List (ℕ × ℕ))} (h : RepAll V vals n) (hG : RepAll V gens g)
    (hT : Rep (nthV V t) (toMat X)) (hk : factorK V t n g D = true) :
    ∀ p ∈ D, p.1 < g ∧ (p.2.all fun q => oddN vals X q.1 q.2) = true ∧
      Native.eqM (Native.lineProd vals (p.2.map Prod.fst)) (gens.getD p.1 Native.one) = true := by
  intro p hp
  unfold factorK at hk
  rw [letB_eq', List.all_eq_true] at hk
  have hk := hk p hp
  simp only [Bool.and_eq_true, List.all_eq_true, Nat.blt_eq] at hk
  obtain ⟨⟨⟨ho, hl⟩, hg⟩, he⟩ := hk
  refine ⟨hg, ?_, ?_⟩
  · rw [List.all_eq_true]
    exact fun q hq => oddN_of_oddK h hT (ho q hq)
  · rw [eqM_iff_of_rep (rep_line h hl) (hG _ hg)]
    exact he

@[expose] def conjN (vals gens : Array Native.Mat) (a : List ℕ) (l : List (ℕ × ℕ)) : Native.Mat :=
  l.foldl (fun acc q => Native.mul acc (Native.mul (Native.mul (vals.getD q.1 Native.one)
    (Native.lineProd gens a)) (Native.pow (vals.getD q.1 Native.one) (q.2 - 1)))) Native.one

theorem rep_conjB {V : List ℕ} {vals gens : Array Native.Mat} {n g : ℕ} (h : RepAll V vals n)
    (hG : RepAll V gens g) {a : List ℕ} (ha : allLt a g = true) {l : List (ℕ × ℕ)}
    (hl : ∀ q ∈ l, q.1 < n) : Rep (conjB V a l) (toMat (conjN vals gens a l)) := by
  have hA := rep_line hG ha
  have key : ∀ (acc : ℕ) (P : Native.Mat), Rep acc (toMat P) →
      Rep (l.foldl (fun acc q => mulB acc (mulB (mulB (nthV V q.1) (lineB V a))
        (powB (nthV V q.1) (Nat.sub q.2 1)))) acc)
      (toMat (l.foldl (fun acc q => Native.mul acc (Native.mul (Native.mul
        (vals.getD q.1 Native.one) (Native.lineProd gens a))
        (Native.pow (vals.getD q.1 Native.one) (q.2 - 1)))) P)) := by
    induction l with
    | nil => intro acc P hP; exact hP
    | cons q l ih =>
      intro acc P hP
      have hq := h q.1 (hl q List.mem_cons_self)
      exact ih (fun q' hq' => hl q' (List.mem_cons_of_mem _ hq')) _ _
        (rep_mul hP (rep_mul (rep_mul hq hA) (rep_pow hq _)))
  exact key oneB Native.one rep_one

theorem conj_of_conjK {V : List ℕ} {vals gens : Array Native.Mat} {t n g : ℕ}
    {X : Native.Mat} {D : List (List ℕ × List (ℕ × ℕ))} (h : RepAll V vals n)
    (hG : RepAll V gens g) (hT : Rep (nthV V t) (toMat X)) (hk : conjK V t n g D = true) :
    ∀ p ∈ D, (p.2.all fun q => oddN vals X q.1 q.2) = true ∧
      Native.eqM X (conjN vals gens p.1 p.2) = true := by
  intro p hp
  unfold conjK at hk
  rw [letB_eq', List.all_eq_true] at hk
  have hk := hk p hp
  simp only [Bool.and_eq_true, List.all_eq_true] at hk
  obtain ⟨⟨ho, ha⟩, he⟩ := hk
  refine ⟨?_, ?_⟩
  · rw [List.all_eq_true]
    exact fun q hq => oddN_of_oddK h hT (ho q hq)
  · rw [eqM_iff_of_rep hT (rep_conjB h hG ha fun q hq => oddK_lt (ho q hq))]
    exact he

end CFSG.KC.TwistedE6Two

end
