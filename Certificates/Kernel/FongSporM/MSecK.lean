module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalMSecDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal.MSecK

open CFSG.RankThree.Asc83Table.Native CFSG.SectionRank.Native
  CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

@[expose] noncomputable def getL {α : Type} (l : List α) (k : ℕ) (d : α) : α :=
  List.rec (motive := fun _ => ℕ → α) (fun _ => d)
    (fun a _ ih k => Nat.rec (motive := fun _ => α) a (fun k' _ => ih k') k) l k

theorem getL_eq {α : Type} : ∀ (l : List α) (k : ℕ) (d : α), getL l k d = l.getD k d
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | a :: l, k + 1, d => by
    show getL l k d = (a :: l).getD (k + 1) d
    rw [getL_eq l k d]
    rfl

@[expose] noncomputable def srK (c : MSec) (k : ℕ) : ℕ := getL c.sreg k 0

@[expose] noncomputable def kFactsK (c : MSec) (k : ℕ) : List MFact :=
  [.ord (srK c k) (getL c.sord k 1)] ++
  (if k = 0 then [.eq [(srK c k, 1)] []]
   else [.eq [(srK c k, 1)]
      [(srK c (getL c.simple.par k 0), 1), (c.gReg (getL c.simple.gen k false), 1)]]) ++
  [.eq [(srK c k, 1), (c.rg1, 1)] [(srK c (getL c.simple.suc1 k 0), 1)],
   .eq [(srK c k, 1), (c.rg2, 1)] [(srK c (getL c.simple.suc2 k 0), 1)]] ++
  (match getL c.simple.cls k none with
    | none => [.eq [(srK c k, 1)] []]
    | some (u, i) =>
      [.eq [(srK c k, 1), (srK c u, 1)] [(srK c u, 1), (srK c (getL c.simple.reps i 0), 1)]])

@[expose] noncomputable def repFactsK (c : MSec) (i : ℕ) : List MFact :=
  [.eq [(c.rg1, 1)] ((getL c.simple.nc i ([], [])).1.map fun l => (srK c l, 1)),
   .eq [(c.rg2, 1)] ((getL c.simple.nc i ([], [])).2.map fun l => (srK c l, 1))]

@[expose] noncomputable def simpleFactsK (c : MSec) : List MFact :=
  [.ord c.rg1 c.simple.o1, .ord c.rg2 c.simple.o2,
    .eq [(c.rg1, 1)] (c.base.g.idxWord c.h1), .eq [(c.rg2, 1)] (c.base.g.idxWord c.h2)] ++
  (List.range c.simple.par.length).flatMap (kFactsK c) ++
  (List.range c.simple.reps.length).flatMap (repFactsK c) ++
  [.ne [(c.rg1, 1), (c.rg2, 1)] [(c.rg2, 1), (c.rg1, 1)] c.tg,
   .eq [(srK c c.simple.k3, 3)] [], .ne [(srK c c.simple.k3, 1)] [] c.t3,
   .eq [(srK c c.simple.kz, 1)] (pwToWord c.base.g.z)]

@[expose] noncomputable def factsK (c : MSec) : List MFact := c.base.baseFacts ++ simpleFactsK c

theorem kFactsK_eq (c : MSec) : kFactsK c = c.kFacts := by
  funext k
  simp only [kFactsK, MSec.kFacts, srK, MSec.sr, getL_eq]
  rcases c.simple.cls.getD k none with _ | ⟨u, i⟩ <;> rfl

theorem repFactsK_eq (c : MSec) : repFactsK c = c.repFacts := by
  funext i
  simp only [repFactsK, MSec.repFacts, srK, MSec.sr, getL_eq]

theorem facts_eqK (c : MSec) : c.facts = factsK c := by
  unfold factsK simpleFactsK MSec.facts MSec.simpleFacts
  rw [kFactsK_eq, repFactsK_eq]
  simp only [srK, MSec.sr, getL_eq]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal.MSecK

end
