module

public import Certificates.Data.Kernel.PermCent.Sp6BTwin
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum

public section

set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.Sp6B

open CFSG.EvenSmallLie.Sp6

@[expose] def layNs : List Nat :=
  [57853586670385055155569485357288036537813811968685422750156465949,
    57914546073096184467680471383749831819329428783591985594304933978,
    36754492629474977194842362787755095451847755308102672997954625618]

noncomputable instance instDecCanon36 (p : Nat) : Decidable (Canon 36 p) :=
  inferInstanceAs (Decidable (_ ∧ _))

@[expose] noncomputable def cvOfNat (p : Nat) : CV 36 := if h : Canon 36 p then ⟨p, h⟩ else 1

theorem cvOfNat_val (s : CV 36) : cvOfNat s.1 = s := by
  unfold cvOfNat
  rw [dif_pos s.2]

@[expose] noncomputable def layR : List (CV 36) := layNs.map cvOfNat

@[expose] noncomputable def lay0 : CV 36 := cvOfNat (layNs.getD 0 0)

@[expose] noncomputable def lay1 : CV 36 := cvOfNat (layNs.getD 1 0)

@[expose] noncomputable def lay2 : CV 36 := cvOfNat (layNs.getD 2 0)

theorem layR_eq : layR = [lay0, lay1, lay2] := rfl

@[expose] noncomputable def layF (c : CV 36) : Bool :=
  (commAllC c L0C && commAllC c L1C) &&
    (!decide (c = 1) && !((List.range wsC.length).all fun k =>
      k == 0 || k == 11 || !commAllC c (memberElemsC L0C (wsC.getD k 1))))

@[expose] noncomputable def subP (c : CV 36) : Bool := !layF c || decide (c ∈ layR)

theorem laySlen : (elemsC sp6CentQ2).length ≤ 8 * 576 := by decide +kernel

theorem layS0 : (((elemsC sp6CentQ2).drop (0 * 576)).take 576).all subP = true := by
  decide +kernel

theorem layS1 : (((elemsC sp6CentQ2).drop (1 * 576)).take 576).all subP = true := by
  decide +kernel

theorem layS2 : (((elemsC sp6CentQ2).drop (2 * 576)).take 576).all subP = true := by
  decide +kernel

theorem layS3 : (((elemsC sp6CentQ2).drop (3 * 576)).take 576).all subP = true := by
  decide +kernel

theorem layS4 : (((elemsC sp6CentQ2).drop (4 * 576)).take 576).all subP = true := by
  decide +kernel

theorem layS5 : (((elemsC sp6CentQ2).drop (5 * 576)).take 576).all subP = true := by
  decide +kernel

theorem layS6 : (((elemsC sp6CentQ2).drop (6 * 576)).take 576).all subP = true := by
  decide +kernel

theorem layS7 : (((elemsC sp6CentQ2).drop (7 * 576)).take 576).all subP = true := by
  decide +kernel

theorem layC_sub : ∀ x ∈ layC, x ∈ layR := by
  have hall := CFSG.Certificates.Kernel.PkEnum.all_of_chunks (elemsC sp6CentQ2) subP 576 8 laySlen
    fun j hj =>
      match j, hj with
    | 0, _ => layS0
    | 1, _ => layS1
    | 2, _ => layS2
    | 3, _ => layS3
    | 4, _ => layS4
    | 5, _ => layS5
    | 6, _ => layS6
    | 7, _ => layS7
      | k + 8, h => absurd h (by omega)
  intro x hx
  unfold layC at hx
  simp only [List.mem_filter] at hx
  have h := List.all_eq_true.1 hall x hx.1.1
  unfold subP layF at h
  rw [hx.1.2, hx.2] at h
  simpa using h

theorem all2_layC {f : CV 36 → CV 36 → Bool}
    (h : (layR.all fun a => layR.all fun b => f a b) = true) :
    (layC.all fun a => layC.all fun b => f a b) = true := by
  rw [List.all_eq_true] at h ⊢
  intro a ha
  have h1 := List.all_eq_true.1 (h a (layC_sub a ha))
  rw [List.all_eq_true]
  exact fun b hb => h1 b (layC_sub b hb)

theorem all_layC {f : CV 36 → Bool} (h0 : f lay0 = true) (h1 : f lay1 = true)
    (h2 : f lay2 = true) : layC.all f = true := by
  rw [List.all_eq_true]
  intro x hx
  have hr := layC_sub x hx
  rw [layR_eq] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2

end CFSG.Certificates.Kernel.PkCV.Sp6B

end
