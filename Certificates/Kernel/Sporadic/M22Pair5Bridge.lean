module

public import Certificates.Certificate2202
public import CFSG.Sporadic.Schreier.M22Check
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Schreier.ImagePairs

public section

namespace CertificateChecks.KernelSpor.M22Pair5

open CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

private theorem wordsRel_iff (x y : Equiv.Perm (Fin 22)) :
    WordsRel m22AutWords x y ↔
      orderOf (x * y) = 11 ∧ orderOf (x * y * x⁻¹ * y⁻¹) = 6 ∧ orderOf (x * y * y) = 5 := by
  simp [m22AutWords, WordsRel, evalW, letterW, mul_assoc]

private theorem pair_iff {x y : Table} {xg yg : Equiv.Perm (Fin 22)} (hx : Rep 22 x xg)
    (hy : Rep 22 y yg) (hxo : orderOf xg = 2) (hyo : orderOf yg = 4) :
    (pairTest 22 11 6 2 4 x y && ordW 22 [x, y, y] 5) = true ↔ WordsRel m22AutWords xg yg := by
  rw [Bool.and_eq_true, pairTest_iff perm_faithful hx hy (by norm_num) (by norm_num) hxo hyo
    (by norm_num) (by norm_num),
    ordW_iff perm_faithful (.cons hx (.cons hy (.cons hy .nil))) (by norm_num)]
  simp only [wordsRel_iff, List.prod_cons, List.prod_nil, mul_one, mul_assoc, and_assoc]

private theorem ordW_gens {a b : Equiv.Perm (Fin 22)} (h : orderOf (a * b * b) = 5) :
    ordW 22 [toTable a, toTable b, toTable b] 5 = true := by
  rw [ordW_iff perm_faithful (.cons (rep_toTable (by norm_num) a)
    (.cons (rep_toTable (by norm_num) b) (.cons (rep_toTable (by norm_num) b) .nil)))
    (by norm_num)]
  simpa [mul_assoc] using h

theorem counts : (ordW 22 [toTable m22gA, toTable m22gB, toTable m22gB] 5 = true)
    ∧ (pairCount (orderTables m22Certificate 2) (orderTables m22Certificate 4)
       (fun x y => pairTest 22 11 6 2 4 x y && ordW 22 [x, y, y] 5) = 887040) := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m22Certificate := m22Certificate_check
  obtain ⟨hok, -, hord⟩ := Certificates.certificate2202.1
  obtain ⟨hoa, hob, hws, htot⟩ := Certificates.certificate2202.2.2
  have hH : m22Certificate.originalSubgroup = Subgroup.closure {g | g ∈ [m22gA, m22gB]} := by
    rw [m22Certificate]
    exact certificate_originalSubgroup _ _ _ _ _
  set H := m22Certificate.originalSubgroup
  have hAB : ∀ g ∈ [m22gA, m22gB], g ∈ H := fun g hg => by
    rw [hH]
    exact Subgroup.subset_closure hg
  have hA : m22gA ∈ H := hAB _ (List.mem_cons_self ..)
  have hB : m22gB ∈ H := hAB _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have ha' : orderOf m22gA = 2 :=
    (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 hoa
  have hb' : orderOf m22gB = 4 :=
    (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 hob
  have hpos : ∀ p ∈ m22AutWords, 0 < p.2 := by decide
  have hwr : WordsRel m22AutWords m22gA m22gB :=
    (wordsTest_iff perm_faithful (rep_toTable hn _) (rep_toTable hn _) ha' hb' (by norm_num)
      (by norm_num) hpos).1 hws
  have hreps : ∀ r ∈ m22InvReps, r ∈ H ∧ orderOf r = 2 := fun r hr => by
    refine ⟨?_, (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1
      (List.all_eq_true.1 hord _ (List.mem_map_of_mem hr))⟩
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hr
    exact evalCodes_mem H hAB w
  have hcount := card_pairs_eq_repsTotal hn m22Certificate hQ (mx := 2) (my := 4) (by norm_num)
    (by norm_num) hpos (pairTables_spec hn hA hB) m22InvReps hreps 2000 hok
  rw [htot] at hcount
  refine ⟨ordW_gens ((wordsRel_iff _ _).1 hwr).2.2, Eq.trans ?_ hcount⟩
  have hcoe : ∀ p : H × H,
      (orderOf p.1 = 2 ∧ orderOf p.2 = 4 ∧ WordsRel m22AutWords p.1 p.2) ↔
      (orderOf (p.1 : Equiv.Perm (Fin 22)) = 2 ∧ orderOf (p.2 : Equiv.Perm (Fin 22)) = 4 ∧
        WordsRel m22AutWords (p.1 : Equiv.Perm (Fin 22)) p.2) := fun p => by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, wordsRel_coe]
  rw [Nat.card_congr (Equiv.subtypeEquivRight hcoe),
    card_pairs_eq_sum H (enumeration m22Certificate) (enumeration_nodup _ hQ)
      (mem_enumeration_iff _ hQ) (fun h => orderOf h = 2) (fun h => orderOf h = 4)
      (WordsRel m22AutWords),
    pairCount_spec (forall₂_orderTables hn m22Certificate (by norm_num : 0 < 2))
      (forall₂_orderTables hn m22Certificate (by norm_num : 0 < 4))
      (R := fun x y => WordsRel m22AutWords x y) ?_, List.map_reverse, List.sum_reverse]
  · refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
    rw [List.countP_reverse]
  · intro x xg y yg hx hy hxg hyg
    rw [List.mem_reverse, List.mem_filter, decide_eq_true_eq] at hxg hyg
    exact pair_iff hx hy hxg.2 hyg.2

end CertificateChecks.KernelSpor.M22Pair5

end
