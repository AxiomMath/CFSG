
module

public import Certificates.Kernel.Misc.Tits.JTab8073
public import Certificates.Kernel.EvenBN.Table4
public import Certificates.Kernel.Sporadic.Tits.Final2268
public import CFSG.Sporadic.Schreier.TitsCertCheckInputs
public import CFSG.Sporadic.Schreier.TitsLocalCheckInputs
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public import CFSG.Sporadic.Schreier.TitsCentral
public import CFSG.Sporadic.Schreier.TitsChain
public import CFSG.Quasithin.Recognition.CertTitsJCheckInputs
public import CFSG.Certificates.Kernel.Spor.SiftRSound
public import Certificates.Kernel.EvenBN.Bind

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.TitsJT

open CFSG CFSG.Quasithin CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.Sporadic.Schreier.Tits
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.Tits2264 CertificateChecks.KernelSpor.Tits2268
open CertificateChecks.KernelEvenBN

theorem invCand_foldl (n : ℕ) (t : Array ℕ) :
    invCand n t = (List.range n).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0) := by
  unfold invCand
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure, List.range_eq_range']
  rfl

theorem rep_invCandJ {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) :
    Rep n (invCand n t) g⁻¹ := by
  have key : ∀ k ≤ n, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0)).size = n ∧ ∀ i < k, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0))[t[i]!]! = i := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      obtain ⟨hs, hi⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set r := (List.range k).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0)
      have htk : t[k]! < n := ht.lt (by omega)
      refine ⟨by rw [Array.size_set!, hs], fun i hik => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hik with hlt | rfl
      · have hne : t[i]! ≠ t[k]! := by
          intro e
          rw [ht.apply (by omega : i < n), ht.apply (by omega : k < n)] at e
          have := g.injective (Fin.ext e)
          simp at this
          omega
        rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hne)]
        exact hi i hlt
      · rw [Array.getElem!_set!_self _ _ _ (by rw [hs]; exact htk)]
  intro x
  obtain ⟨hs, hi⟩ := key n le_rfl
  rw [invCand_foldl]
  have e : t[(g⁻¹ x : Fin n).val]! = x.val := by
    rw [ht.apply (g⁻¹ x).2]
    simp
  rw [← e, hi _ (g⁻¹ x).2]

theorem isInvA_of_rep {n : ℕ} {t r : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g)
    (hr : Rep n r g⁻¹) : isInvA n t r = true := by
  unfold isInvA
  refine allLt_iff.2 fun i hi => ?_
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨ht.lt hi, ?_⟩
  rw [ht.apply hi, hr ⟨_, (g ⟨i, hi⟩).2⟩]
  simp

theorem isInvA_invCand {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) :
    isInvA n t (invCand n t) = true := isInvA_of_rep ht (rep_invCandJ ht)

theorem permOfArr_of_rep {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (h : Rep n t g) :
    permOfArr n t = g := by
  have hc : (∀ i < n, t[i]! < n) ∧ ∀ i < n, ∀ j < n, t[i]! = t[j]! → i = j :=
    ⟨fun i hi => h.lt hi, fun i hi j hj hij => by
      rw [h.apply hi, h.apply hj] at hij
      have := g.injective (Fin.ext hij)
      simpa using this⟩
  ext x
  rw [permOfArr, dite_eq_left hc]
  change t[(x : ℕ)]! = _
  exact h x

theorem rep_unpack {p r : Nat} (h : permOK 1755 11 (mask 11) (1755 * 11) p r = true) :
    Rep 1755 (unpack 1755 11 p) (permOfArr 1755 (unpack 1755 11 p)) ∧
      Rep 1755 (unpack 1755 11 r) (permOfArr 1755 (unpack 1755 11 p))⁻¹ := by
  have h2 := (invEqK_sound (n := 1755) (w := 11) h).2
  exact rep_permOfArr h2

theorem jPel_size : jPel.size = 512 := by
  unfold jPel jLevels
  rw [table4_size bindsJ permJ TitsJ.hl]
  exact Nat.eq_of_beq_eq_true sizeK

theorem jPel_spec :
    (∀ i < jPel.size, ∃ g ∈ titsJ, Rep 1755 jPel[i]! g) ∧
    (∀ g ∈ titsJ, ∃ i < jPel.size, Rep 1755 jPel[i]! g) := by
  have hA : ChainArrays titsQJ (titsJArrs.extract 0 4) titsJArrs (baseArr 1755 titsJBase)
      (wordsArr 4 9 titsJDerivations) :=
    chainArrays_ofArrays' titsLocalData_check.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h := table4_spec hA (by norm_num : 0 < 4) titsLocalChains_check.2.2.2.1 rfl
  rw [titsQJ_facts.2.2.1] at h
  exact h

@[expose] noncomputable def el (i : ℕ) : Equiv.Perm (Fin 1755) := permOfArr 1755 jPel[i]!

theorem el_rep {i : ℕ} (hi : i < 512) : Rep 1755 jPel[i]! (el i) := by
  obtain ⟨g, -, hg⟩ := jPel_spec.1 i (by rw [jPel_size]; exact hi)
  rw [el, permOfArr_of_rep hg]
  exact hg

theorem el_mem {i : ℕ} (hi : i < 512) : el i ∈ titsJ := by
  obtain ⟨g, hgJ, hg⟩ := jPel_spec.1 i (by rw [jPel_size]; exact hi)
  rw [el, permOfArr_of_rep hg]
  exact hgJ

theorem el_surj {g : Equiv.Perm (Fin 1755)} (hg : g ∈ titsJ) : ∃ i < 512, el i = g := by
  obtain ⟨i, hi, hrep⟩ := jPel_spec.2 g hg
  rw [jPel_size] at hi
  exact ⟨i, hi, permOfArr_of_rep hrep⟩

theorem el_inj {i j : ℕ} (hi : i < 512) (hj : j < 512) (h : el i = el j) : i = j := by
  let f : Fin 512 → titsJ := fun k => ⟨el k, el_mem k.2⟩
  have hs : Function.Surjective f := fun ⟨g, hg⟩ => by
    obtain ⟨k, hk, e⟩ := el_surj hg
    exact ⟨⟨k, hk⟩, Subtype.ext e⟩
  have hc : Nat.card titsJ = 512 := titsQJ_facts.2.2.2
  have hinj := (Finite.injective_iff_surjective_of_equiv (Finite.equivFinOfCardEq hc).symm).2 hs
  have := hinj (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) (Subtype.ext h)
  exact congrArg Fin.val this

theorem agree {g h : Equiv.Perm (Fin 1755)} (hg : g ∈ titsJ) (hh : h ∈ titsJ)
    (hb : ∀ p ∈ titsJBase, (g (finPt 1755 p) : ℕ) = h (finPt 1755 p)) : g = h := by
  refine eq_of_agree_base (Q := titsQJ) titsQJ_facts.1 ?_ ?_ fun b hb' => ?_
  · rw [titsQJ_facts.2.2.1]; exact hg
  · rw [titsQJ_facts.2.2.1]; exact hh
  · rw [titsQJ, RawSchreierDatum.ofArrays_base_toList, finList] at hb'
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hb'
    exact Fin.ext (hb p hp)

theorem key_inj {x0 x1 x2 x3 y0 y1 y2 y3 : ℕ} (_h0 : x0 < 1755) (h1 : x1 < 1755) (h2 : x2 < 1755)
    (h3 : x3 < 1755) (_k0 : y0 < 1755) (k1 : y1 < 1755) (k2 : y2 < 1755) (k3 : y3 < 1755)
    (h : jKey4 x0 x1 x2 x3 = jKey4 y0 y1 y2 y3) : x0 = y0 ∧ x1 = y1 ∧ x2 = y2 ∧ x3 = y3 := by
  unfold jKey4 at h
  omega

theorem foldl_insert (f : ℕ → ℕ) : ∀ s, (∀ i < s, ∀ j < s, f i = f j → i = j) → ∀ j < s,
    ((List.range s).foldl (fun m i => m.insert (f i) i) (∅ : Std.HashMap ℕ ℕ))[f j]? = some j
  | 0, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | s + 1, hinj, j, hj => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Std.HashMap.getElem?_insert]
    split
    · next e =>
      rw [beq_iff_eq] at e
      rw [hinj s (by omega) j hj e]
    · next e =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | rfl
      · exact foldl_insert f s (fun i hi j hj h => hinj i (by omega) j (by omega) h) j hj'
      · exact absurd (beq_self_eq_true _) e

@[expose] noncomputable def keyOf (i : ℕ) : ℕ :=
  jKey4 (jPel[i]!)[5]! (jPel[i]!)[1]! (jPel[i]!)[24]! (jPel[i]!)[12]!

theorem rep_base {t : Array ℕ} {g : Equiv.Perm (Fin 1755)} (ht : Rep 1755 t g) (p : ℕ)
    (hp : p < 1755) : t[p]! = (g (finPt 1755 p) : ℕ) := by
  rw [ht.apply hp, finPt_eq hp]

theorem keyOf_inj {i j : ℕ} (hi : i < 512) (hj : j < 512) (h : keyOf i = keyOf j) : i = j := by
  have ri := el_rep hi
  have rj := el_rep hj
  obtain ⟨e0, e1, e2, e3⟩ := key_inj (ri.lt (by norm_num)) (ri.lt (by norm_num))
    (ri.lt (by norm_num)) (ri.lt (by norm_num)) (rj.lt (by norm_num)) (rj.lt (by norm_num))
    (rj.lt (by norm_num)) (rj.lt (by norm_num)) h
  refine el_inj hi hj (agree (el_mem hi) (el_mem hj) fun p hp => ?_)
  simp only [titsJBase, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · rw [← rep_base ri _ (by norm_num), ← rep_base rj _ (by norm_num)]; exact e0
  · rw [← rep_base ri _ (by norm_num), ← rep_base rj _ (by norm_num)]; exact e1
  · rw [← rep_base ri _ (by norm_num), ← rep_base rj _ (by norm_num)]; exact e2
  · rw [← rep_base ri _ (by norm_num), ← rep_base rj _ (by norm_num)]; exact e3

theorem idx_key {i : ℕ} (hi : i < 512) : jIdxMap.getD (keyOf i) 0 = i := by
  have e := foldl_insert keyOf 512 (fun i hi j hj h => keyOf_inj hi hj h) i hi
  rw [jIdxMap, jPel_size]
  change ((List.range 512).foldl (fun m i => m.insert (keyOf i) i) (∅ : Std.HashMap ℕ ℕ)).getD
    (keyOf i) 0 = i
  rw [Std.HashMap.getD_eq_getD_getElem?, e]
  rfl

theorem jIdx_of {a : Array ℕ} {g : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a g) (hg : g ∈ titsJ) :
    ∃ i < 512, el i = g ∧ jIdx a = i := by
  obtain ⟨i, hi, rfl⟩ := el_surj hg
  refine ⟨i, hi, rfl, ?_⟩
  have ri := el_rep hi
  have e : ∀ p < 1755, a[p]! = (jPel[i]!)[p]! := fun p hp => by
    rw [rep_base ha p hp, rep_base ri p hp]
  rw [jIdx, jIdx4, e 5 (by norm_num), e 1 (by norm_num), e 24 (by norm_num), e 12 (by norm_num)]
  exact idx_key hi

theorem jIdx4_of {g : Equiv.Perm (Fin 1755)} (hg : g ∈ titsJ) :
    ∃ i < 512, el i = g ∧ jIdx4 (g (finPt 1755 5)) (g (finPt 1755 1)) (g (finPt 1755 24))
      (g (finPt 1755 12)) = i := by
  obtain ⟨i, hi, rfl⟩ := el_surj hg
  refine ⟨i, hi, rfl, ?_⟩
  have ri := el_rep hi
  rw [jIdx4, ← rep_base ri 5 (by norm_num), ← rep_base ri 1 (by norm_num),
    ← rep_base ri 24 (by norm_num), ← rep_base ri 12 (by norm_num)]
  exact idx_key hi

end CertificateChecks.KernelMisc.TitsJT

end
