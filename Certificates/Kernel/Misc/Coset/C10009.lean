module

public import CFSG.LieType.Multipliers.TitsCheckInputs
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import CFSG.Certificates.Kernel.Misc.Coset.PGChain
public import CFSG.Certificates.Kernel.Misc.Coset.ActPermRep
public import Certificates.Kernel.Misc.Tits.Text
public import Certificates.Kernel.Misc.Coset.XTitsR
public import Certificates.Kernel.Misc.Coset.XTitsRBC
public import Certificates.Kernel.Misc.Coset.XTitsC
public import Certificates.Kernel.Misc.Coset.XTitsCBC
public import Certificates.Kernel.Misc.Coset.XTitsPA.All
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.LieType.Multipliers.CoverWords
import CFSG.Certificates.CosetTablePresented
import CFSG.Monster.B.Co2.PermArr
import CFSG.Certificates.PresentationLetters
public import CFSG.Certificates.NativeSchreierCard

public section

namespace CertificateChecks.KernelMiscCoset.C10009

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.LieType.Multipliers CFSG.LieType.Multipliers.Tits
  CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2 CFSG.Certificates CFSG.KC.Enum CFSG.KS
  CFSG.KS.Raw

set_option maxRecDepth 100000

theorem tR : titsRels.map encW = CFSG.KBRoute.XTitsR.rels := by decide +kernel
theorem wR : CFSG.KBRoute.XTitsR.T1.words = (subsetOf 3 [1, 2]).map fun x => [(x.val, true)] := by
  decide +kernel
theorem tRBC : titsRelsBC.map encW = CFSG.KBRoute.XTitsRBC.rels := by decide +kernel
theorem tC : titsCoverWords.map encW = CFSG.KBRoute.XTitsC.rels := by decide +kernel
theorem wC : CFSG.KBRoute.XTitsC.T1.words = (subsetOf 3 [1, 2]).map fun x => [(x.val, true)] := by
  decide +kernel
theorem tCBC : titsCoverWordsBC.map encW = CFSG.KBRoute.XTitsCBC.rels := by decide +kernel

theorem card_rels : Finite (PG 3 titsRels) ∧ Nat.card (PG 3 titsRels) ≤ 17971200 := by
  have h := XTitsR.t1
  unfold CFSG.KBRoute.XTitsR.T1.ok at h
  have h' := XTitsRBC.t1
  unfold CFSG.KBRoute.XTitsRBC.T1.ok at h'
  have c1 := card_le_of_tableOk titsRelsBC tRBC h' (by decide) CFSG.KBRoute.XTitsRBC.top rfl
  have c0 := card_le_of_index_restrict titsRels _ (genSub_index_le_of_tableOk titsRels tR h
    (by norm_num) CFSG.KBRoute.XTitsR.top _ wR) c1
  exact ⟨c0.1, c0.2.trans (by norm_num)⟩

theorem card_cover : Finite (PG 3 titsCoverWords) ∧ Nat.card (PG 3 titsCoverWords) ≤ 17971200 := by
  have h := XTitsC.t1
  unfold CFSG.KBRoute.XTitsC.T1.ok at h
  have h' := XTitsCBC.t1
  unfold CFSG.KBRoute.XTitsCBC.T1.ok at h'
  have c1 := card_le_of_tableOk titsCoverWordsBC tCBC h' (by decide) CFSG.KBRoute.XTitsCBC.top rfl
  have c0 := card_le_of_index_restrict titsCoverWords _ (genSub_index_le_of_tableOk titsCoverWords
    tC h (by norm_num) CFSG.KBRoute.XTitsC.top _ wC) c1
  exact ⟨c0.1, c0.2.trans (by norm_num)⟩

@[expose] def e2 (h : Fin 2) : Fin 5 := ⟨h.val, Nat.lt_of_lt_of_le h.isLt (by decide)⟩

@[expose] def sh (h : Fin 3) : Fin 5 := ⟨h.val + 2, Nat.add_lt_add_right h.isLt 2⟩

@[expose] def permWords : List (List (Fin 5 × Bool)) :=
  ((List.finRange 3).map fun i => (sh i, false) ::
      (toLetters 2 (abcWords.getD i.val [])).map fun l => (e2 l.1, l.2)) ++
    (titsOneWords.map fun w => w.map fun l => (sh l.1, l.2)) ++
    ((List.finRange 2).map fun j => (e2 j, false) ::
      (toLetters 3 (titsDWords.getD j.val [])).map fun l => (sh l.1, l.2))

theorem hrels : permWords.map Act.revCodes = CFSG.KAct.XTitsP.rels := by decide +kernel

theorem bind : Act.allR 0 1755 (fun x => Act.andB
    (Nat.beq (CFSG.KAct.XTitsP.A (x * (5 + 5) + 2 * 0))
      (pg 11 (mask 11) (CertificateChecks.KernelMisc.TitsText.F (18 + 0)) x))
    (Nat.beq (CFSG.KAct.XTitsP.A (x * (5 + 5) + 2 * 1))
      (pg 11 (mask 11) (CertificateChecks.KernelMisc.TitsText.F (18 + 1)) x))) = true := by
  quickRfl

theorem signedProd_map {G : Type*} [Group G] {m k : ℕ} (σ : Fin m → G) (f : Fin k → Fin m)
    (w : List (Fin k × Bool)) :
    signedProd σ (w.map fun l => (f l.1, l.2)) = signedProd (fun h => σ (f h)) w := by
  induction w with
  | nil => rfl
  | cons l w ih => rw [List.map_cons, signedProd_cons, signedProd_cons, ih]

theorem wordIn_eq {G : Type*} [Group G] (k : ℕ) (gs : ℕ → G) (w : List ℤ) :
    wordIn k gs w = signedProd (fun h : Fin k => gs h) (toLetters k w) := by
  rw [wordIn, Quiver.SchreierGraph.evalWord, lift_mk_eq_signedProd]

theorem permOfArr_eq {n : ℕ} {t : Array ℕ} {σ : Equiv.Perm (Fin n)}
    (h : ∀ x : Fin n, t[x.val]! = σ x) : permOfArr n t = σ := by
  have hc : (∀ i < n, t[i]! < n) ∧ ∀ i < n, ∀ j < n, t[i]! = t[j]! → i = j := by
    refine ⟨fun i hi => by rw [h ⟨i, hi⟩]; exact (σ _).2, fun i hi j hj hij => ?_⟩
    rw [h ⟨i, hi⟩, h ⟨j, hj⟩] at hij
    exact congrArg Fin.val (σ.injective (Fin.ext hij))
  refine Equiv.ext fun x => Fin.ext ?_
  rw [permOfArr, dite_eq_left hc]
  exact h x

theorem perms :
    (∀ w ∈ titsOneWords, FreeGroup.lift (fun i : Fin 3 => wordIn 2
      (fun j => permOfArr 1755 titsDerivedArrs[j]!) (abcWords.getD i.val [])) (FreeGroup.mk w) = 1)
    ∧ ∀ j < 2, permOfArr 1755 titsDerivedArrs[j]! = wordIn 3
      (fun i => wordIn 2 (fun j => permOfArr 1755 titsDerivedArrs[j]!) (abcWords.getD i []))
      (titsDWords.getD j []) := by
  have hpt := Act.pointOK_of_allR CFSG.KAct.XTitsP.all
  obtain ⟨σ, hσ⟩ := Act.exists_rep hpt
  have hw := Act.relsAt_sound hσ permWords hrels (fun x hx => Act.relsAt_of_pointOK (hpt x hx))
  have hb := Act.allR_spec bind
  have hδ : ∀ j (hj : j < 2), permOfArr 1755 titsDerivedArrs[j]! = σ (e2 ⟨j, hj⟩) := by
    intro j hj
    rw [CertificateChecks.KernelMisc.TitsText.titsDerivedArrs_get (by omega)]
    apply permOfArr_eq
    intro x
    have hx := hb x.val (Nat.zero_le _) (by simpa using x.2)
    simp only [Act.andB_eq, Bool.and_eq_true] at hx
    rw [unpack, getElem!_ofFn_nat _ x.2]
    have hr := (hσ (e2 ⟨j, hj⟩) x).1
    interval_cases j
    · exact (Nat.eq_of_beq_eq_true hx.1).symm.trans hr
    · exact (Nat.eq_of_beq_eq_true hx.2).symm.trans hr
  have habc : ∀ i : Fin 3, wordIn 2 (fun j => permOfArr 1755 titsDerivedArrs[j]!)
      (abcWords.getD i.val []) = σ (sh i) := by
    intro i
    have h1 := hw _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩)))
    rw [signedProd_cons, signedProd_map] at h1
    simp only [Bool.false_eq_true, ↓reduceIte] at h1
    rw [wordIn_eq, inv_mul_eq_one.1 h1]
    congr 1
    funext h
    exact hδ h.val h.2
  refine ⟨fun w hw' => ?_, fun j hj => ?_⟩
  · have h1 := hw _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.2 ⟨w, hw', rfl⟩)))
    rw [signedProd_map] at h1
    rw [lift_mk_eq_signedProd, ← h1]
    congr 1
    funext h
    exact habc h
  · have h1 := hw _ (List.mem_append_right _ (List.mem_map.2 ⟨⟨j, hj⟩, List.mem_finRange _, rfl⟩))
    rw [signedProd_cons, signedProd_map] at h1
    simp only [Bool.false_eq_true, ↓reduceIte] at h1
    rw [hδ j hj, wordIn_eq, inv_mul_eq_one.1 h1]
    congr 1
    funext h
    exact (habc h).symm

end CertificateChecks.KernelMiscCoset.C10009

end
