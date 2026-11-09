module

public import Certificates.Data.Kernel.HMathieu.Tab
public import CFSG.Quasithin.Background.HMathieuMask
public import CFSG.Quasithin.Background.HMathieuCodeMask
public import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.Certificates.Kernel.Common.JsonGz
public meta import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Certificates.Kernel.Common.JsonGz
public import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43
import CFSG.Certificates.Kernel.HMathieu.BfsSound

set_option maxRecDepth 400000

public section

#kc_repo #kc_json CertificateChecks.KernelHMathieu.T24
  "Certificates/Kernel/HMathieu/data/T24.json" 164181 15314921325718240962
  (gens : List Nat) (E : List Nat) (inv : List Nat) (P : List Nat) (rows : List (Nat × Nat))
  (Mc : List (List Nat)) (Md : List (List Nat))

namespace CertificateChecks.KernelHMathieu.T24

open CFSG.KC.HMathieu CFSG.KC.Enum CFSG.Quasithin.H.Mathieu

@[expose] noncomputable def memB24 (x : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => Bool.rec ih true (Nat.beq x a)) l

@[expose] noncomputable def strictP24 (y : Nat) (k : Nat → List Nat × List Nat) :
    List Nat × List Nat :=
  Nat.rec (motive := fun _ => List Nat × List Nat) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def stepQ24 (gens : List Nat) (st : List Nat × List Nat) (x : Nat) :
    List Nat × List Nat :=
  gens.foldl (fun st' g => strictP24 (pc24 g x) fun y =>
    Bool.rec (motive := fun _ => List Nat × List Nat) (y :: st'.1, y :: st'.2) st'
      (memB24 y st'.1)) st

@[expose] noncomputable def bfsQ24 (gens : List Nat) : Nat → List Nat → List Nat → List Nat
  | 0, acc, _ => acc
  | _ + 1, acc, [] => acc
  | f + 1, acc, x :: xs =>
    Prod.rec (motive := fun _ => List Nat) (fun a n => bfsQ24 gens f a n.reverse)
      ((x :: xs).foldl (stepQ24 gens) (acc, []))

theorem memB24_eq (x : Nat) (l : List Nat) : memB24 x l = l.contains x := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have e : memB24 x (a :: l) =
        Bool.rec (motive := fun _ => Bool) (memB24 x l) true (Nat.beq x a) := rfl
    rw [e, List.contains_cons, ← ih]
    by_cases hxa : x = a
    · subst hxa
      rw [Nat.beq_refl]
      simp
    · have h1 : Nat.beq x a = false := by
        cases h : Nat.beq x a
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) hxa
      have h2 : (x == a) = false := by simp [hxa]
      rw [h1, h2, Bool.false_or]

theorem strictP24_eq (y : Nat) (k : Nat → List Nat × List Nat) : strictP24 y k = k y := by
  cases y <;> rfl

theorem stepQ24_eq (gens : List Nat) : stepQ24 gens = bfsStep gens := by
  funext st x
  unfold stepQ24 bfsStep
  congr 1
  funext st' g
  rw [strictP24_eq, memB24_eq]
  cases st'.1.contains (pc24 g x) <;> rfl

theorem bfsQ24_eq (gens : List Nat) : ∀ (f : Nat) (acc fr : List Nat),
    bfsQ24 gens f acc fr = bfsP gens f acc fr
  | 0, _, _ => by simp only [bfsQ24, bfsP]
  | _ + 1, _, [] => by simp only [bfsQ24, bfsP]
  | f + 1, acc, x :: xs => by
    simp only [bfsQ24, bfsP, stepQ24_eq, bfsQ24_eq gens f]

@[expose] noncomputable def strictB24 (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def sqR24 (t : Nat) (c : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih x => Bool.rec (motive := fun _ => Bool) false (ih (Nat.succ x))
      (Nat.beq (pg 5 (CFSG.KS.mask 5) t (pg 5 (CFSG.KS.mask 5) t x)) x)) c

@[expose] noncomputable def pairK24 (m : Nat) (P : List Nat) (p q c r j : Nat) : Bool :=
  strictB24 (pc24 p q) fun t => sqR24 t 24 0 == c.testBit j &&
    (!c.testBit j || (decide (Nat.land (Nat.shiftRight r (8 * j)) 255 ≤ m) &&
      t == P.getD (Nat.land (Nat.shiftRight r (8 * j)) 255) 0))

@[expose] noncomputable def symK24 (D : List (Nat × Nat)) (i j : Nat) : Bool :=
  (cmD D i).testBit j == (cmD D j).testBit i &&
    (!(cmD D i).testBit j || Nat.beq (Nat.land (Nat.shiftRight (mkD D i) (8 * j)) 255)
      (Nat.land (Nat.shiftRight (mkD D j) (8 * i)) 255))

@[expose] noncomputable def tabsK24 (m : Nat) (P : List Nat) (D : List (Nat × Nat)) : Bool :=
  (List.range m).all fun i => (List.range m).all fun j =>
    Bool.rec (motive := fun _ => Bool)
      (pairK24 m P (P.getD i 0) (P.getD j 0) (cmD D i) (mkD D i) j) (symK24 D i j) (Nat.blt j i)

theorem strictB24_eq (y : Nat) (k : Nat → Bool) : strictB24 y k = k y := by
  cases y <;> rfl

theorem sqR24_iff (t : Nat) : ∀ (c lo : Nat), sqR24 t c lo = true ↔
    ∀ x, lo ≤ x → x < lo + c → pg 5 (CFSG.KS.mask 5) t (pg 5 (CFSG.KS.mask 5) t x) = x
  | 0, lo => ⟨fun _ x _ h2 => absurd h2 (by omega), fun _ => rfl⟩
  | c + 1, lo => by
    have e : sqR24 t (c + 1) lo = Bool.rec (motive := fun _ => Bool) false (sqR24 t c (lo + 1))
        (Nat.beq (pg 5 (CFSG.KS.mask 5) t (pg 5 (CFSG.KS.mask 5) t lo)) lo) := rfl
    rw [e]
    cases hb : Nat.beq (pg 5 (CFSG.KS.mask 5) t (pg 5 (CFSG.KS.mask 5) t lo)) lo
    · refine ⟨fun h => (nomatch h), fun h => ?_⟩
      rw [h lo (Nat.le_refl _) (by omega), Nat.beq_refl] at hb
      exact nomatch hb
    · change sqR24 t c (lo + 1) = true ↔ _
      rw [sqR24_iff t c (lo + 1)]
      refine ⟨fun h x h1 h2 => ?_, fun h x h1 h2 => h x (by omega) (by omega)⟩
      rcases Nat.eq_or_lt_of_le h1 with h3 | h3
      · subst h3
        exact Nat.eq_of_beq_eq_true hb
      · exact h x h3 (by omega)

theorem sqR24_eq {p q : Nat} (hp : vpK p = true) (hq : vpK q = true)
    (hp2 : pc24 p p = pidn 24 5) (hq2 : pc24 q q = pidn 24 5) :
    sqR24 (pc24 p q) 24 0 = (pc24 p q == pc24 q p) := by
  have bp := (vpK_spec hp).2
  have bq := (vpK_spec hq).2
  have hf : ∀ x < 24, pg 5 (CFSG.KS.mask 5) p (pg 5 (CFSG.KS.mask 5) p x) = x := fun x hx => by
    rw [← pg_pc24 p p hx, hp2, pg_id hx]
  have hg : ∀ x < 24, pg 5 (CFSG.KS.mask 5) q (pg 5 (CFSG.KS.mask 5) q x) = x := fun x hx => by
    rw [← pg_pc24 q q hx, hq2, pg_id hx]
  rw [Bool.eq_iff_iff, sqR24_iff, beq_iff_eq]
  refine ⟨fun h => eq_of_pg (vpK_pc24 hp hq) (vpK_pc24 hq hp) fun i hi => ?_, fun h x _ hx => ?_⟩
  · have e := h _ (Nat.zero_le _) (bq _ (bp i hi))
    rw [pg_pc24 p q (bq _ (bp i hi)), hg _ (bp i hi), hf i hi, pg_pc24 p q hi] at e
    rw [pg_pc24 _ _ hi, pg_pc24 _ _ hi]
    exact e
  · have e1 : pg 5 (CFSG.KS.mask 5) (pc24 p q) x =
        pg 5 (CFSG.KS.mask 5) q (pg 5 (CFSG.KS.mask 5) p x) := by
      rw [h, pg_pc24 q p hx]
    rw [e1, pg_pc24 p q (bq _ (bp x hx)), hg _ (bp x hx), hf x hx]

theorem pairK_swap {m : Nat} {P : List Nat} {p q c r c' r' i j : Nat}
    (h1 : pairK m P q p c' r' i = true) (hs : c.testBit j = c'.testBit i)
    (hidx : c.testBit j = true → Nat.land (Nat.shiftRight r (8 * j)) 255 =
      Nat.land (Nat.shiftRight r' (8 * i)) 255) :
    pairK m P p q c r j = true := by
  unfold pairK at h1 ⊢
  cases hb : c'.testBit i
  · rw [hs, hb]
    rw [hb, Bool.and_eq_true] at h1
    have e : (pc24 q p == pc24 p q) = (pc24 p q == pc24 q p) := by
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
      exact eq_comm
    rw [← e, h1.1]
    rfl
  · rw [hs, hb] at hidx ⊢
    rw [hb, Bool.and_eq_true] at h1
    obtain ⟨h1a, h1b⟩ := h1
    have hc : pc24 q p = pc24 p q := by
      have := h1a
      simp only [beq_iff_eq] at this
      exact this
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      at h1b ⊢
    rw [hidx rfl, ← hc]
    exact ⟨rfl, h1b⟩

theorem tabsK_of_24 {m : Nat} {P : List Nat} (D : List (Nat × Nat)) (hm : m ≤ P.length)
    (hP : P.all (fun p => vpK p && Nat.beq (pc24 p p) (pidn 24 5)) = true)
    (h : tabsK24 m P D = true) : tabsK m P D = true := by
  have hv : ∀ i < m, vpK (P.getD i 0) = true ∧ pc24 (P.getD i 0) (P.getD i 0) = pidn 24 5 := by
    intro i hi
    rw [List.getD_eq_getElem _ _ (by omega)]
    have h := List.all_eq_true.1 hP _ (List.getElem_mem (l := P) (by omega : i < P.length))
    rw [Bool.and_eq_true, Nat.beq_eq] at h
    exact h
  unfold tabsK24 at h
  simp only [List.all_eq_true, List.mem_range] at h
  have hpair : ∀ i < m, ∀ j < m, i ≤ j →
      pairK m P (P.getD i 0) (P.getD j 0) (cmD D i) (mkD D i) j = true := by
    intro i hi j hj hij
    have e := h i hi j hj
    have hb : Nat.blt j i = false := by
      rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]
      omega
    rw [hb] at e
    change pairK24 m P (P.getD i 0) (P.getD j 0) (cmD D i) (mkD D i) j = true at e
    unfold pairK24 at e
    unfold pairK
    rwa [strictB24_eq, sqR24_eq (hv i hi).1 (hv j hj).1 (hv i hi).2 (hv j hj).2] at e
  unfold tabsK
  simp only [List.all_eq_true, List.mem_range]
  intro i hi j hj
  by_cases hij : i ≤ j
  · exact hpair i hi j hj hij
  · have e := h i hi j hj
    have hb : Nat.blt j i = true := by
      rw [Nat.blt_eq]
      omega
    rw [hb] at e
    change symK24 D i j = true at e
    unfold symK24 at e
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true',
      Nat.beq_eq] at e
    refine pairK_swap (hpair j hj i hi (by omega)) e.1 fun hb => ?_
    rcases e.2 with h2 | h2
    · rw [hb] at h2
      exact absurd h2 (by decide)
    · exact h2

theorem bfsQE : (bfsQ24 gens 64 [pidn 24 5] [pidn 24 5]).reverse = E := by decide +kernel

theorem bfs : (bfsP gens 64 [pidn 24 5] [pidn 24 5]).reverse = E := by
  rw [← bfsQ24_eq]
  exact bfsQE

theorem vpE : E.all vpK = true := by decide +kernel

theorem vpG : gens.all vpK = true := by decide +kernel

theorem invOK : invFrom (E.getD 0 0) E 0 = inv := by decide +kernel

theorem pOK : P = inv.map (fun i => E.getD i 0) ++ [E.getD 0 0] := by decide +kernel

theorem lenOK : inv.length = 191 ∧ rows.length = 191 := by decide +kernel

theorem p2OK : P.all (fun p => vpK p && Nat.beq (pc24 p p) (pidn 24 5)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem tabs24 : tabsK24 191 P rows = true := by decide +kernel

theorem tabs : tabsK 191 P rows = true :=
  tabsK_of_24 rows (by rw [pOK, List.length_append, List.length_map, lenOK.1]; decide) p2OK tabs24

set_option maxHeartbeats 0 in
theorem mcOK : Mc = P.map (matP ccECols liftECols 11) := by decide +kernel

set_option maxHeartbeats 0 in
theorem mdOK : Md = P.map (matP κCCols liftCCols 11) := by decide +kernel

end CertificateChecks.KernelHMathieu.T24

end
