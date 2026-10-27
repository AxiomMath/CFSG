module

public import Certificates.Kernel.Multipliers.U43BChain
public import Certificates.Kernel.Multipliers.BindListSound
public import CFSG.Certificates.Kernel.Misc.Coset.ActPermRep
public import CFSG.LieType.Multipliers.U43Data
public import CFSG.Sporadic.Bridge.TwoGen
public import CFSG.Monster.B.Co2.PermArr
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.PresentationLetters
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

namespace CertificateChecks.KernelU43B

open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.U43 CFSG.KC.Enum CFSG.KC.MiscCoset.Act CFSG.KS
  CFSG.KS.Raw CFSG.KC.BindList
  CFSG.Monster.B.Co2 CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen

set_option maxRecDepth 100000

@[expose] noncomputable def selP (c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (C.S 0)
    (fun k _ => Nat.rec (motive := fun _ => Nat) (C.SI 0)
      (fun k _ => Nat.rec (motive := fun _ => Nat) (C.S 1) (fun _ _ => C.SI 1) k) k) c

@[expose] noncomputable def actA (n : Nat) : Nat := pg 10 (mask 10) (selP (n % 4)) (n / 4)

@[expose] def ws : List (List (Fin 2 × Bool)) :=
  rels ++ kernelT.map Prod.fst ++
    [commWords (coverPairs 0) ++ [(0, false)], commWords (coverPairs 1) ++ [(1, false)]]

@[expose] def wsCodes : List (List Nat) :=
  [[0, 0], [2, 2, 2, 2, 2, 2], [3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0, 3, 0],
    [2, 2, 0, 2, 2, 0, 3, 3, 0, 3, 3, 0, 3, 3, 0, 2, 2, 0],
    [2, 2, 0, 3, 3, 3, 0, 3, 3, 3, 0, 3, 3, 3, 0, 2, 2, 2, 0, 2],
    [3, 0, 2, 2, 0, 2, 0, 3, 3, 0, 3, 0, 3, 3, 0, 2, 0, 2, 2, 0, 3, 0, 3, 3, 0, 2, 0, 3, 3, 0],
    [3, 3, 0, 3, 3, 0, 3, 0, 2, 2, 0, 3, 3, 3, 0, 2, 2, 0, 3, 0, 2, 2, 0, 2, 0, 3, 0, 3, 0, 3, 3,
      0, 3, 0, 3, 3, 0, 3, 0, 2, 2, 2, 0, 2, 0, 2, 0],
    [2, 2, 0, 3, 3, 3, 0, 3, 3, 3, 0, 3, 3, 3, 0, 2, 2, 2, 0, 2],
    [3, 0, 2, 2, 0, 2, 0, 3, 3, 0, 3, 0, 3, 3, 0, 2, 0, 2, 2, 0, 3, 0, 3, 3, 0, 2, 0, 3, 3, 0],
    [3, 3, 0, 3, 3, 0, 3, 0, 2, 2, 0, 3, 3, 3, 0, 2, 2, 0, 3, 0, 2, 2, 0, 2, 0, 3, 0, 3, 0, 3, 3,
      0, 3, 0, 3, 3, 0, 3, 0, 2, 2, 2, 0, 2, 0, 2, 0, 3, 3, 0, 3, 3, 0, 3, 0, 2, 2, 0, 3, 3, 3, 0,
      2, 2, 0, 3, 0, 2, 2, 0, 2, 0, 3, 0, 3, 0, 3, 3, 0, 3, 0, 3, 3, 0, 3, 0, 2, 2, 2, 0, 2, 0, 2,
      0, 3, 3, 0, 3, 3, 0, 3, 0, 2, 2, 0, 3, 3, 3, 0, 2, 2, 0, 3, 0, 2, 2, 0, 2, 0, 3, 0, 3, 0, 3,
      3, 0, 3, 0, 3, 3, 0, 3, 0, 2, 2, 2, 0, 2, 0, 2, 0, 3, 3, 0, 3, 3, 0, 3, 0, 2, 2, 0, 3, 3, 3,
      0, 2, 2, 0, 3, 0, 2, 2, 0, 2, 0, 3, 0, 3, 0, 3, 3, 0, 3, 0, 3, 3, 0, 3, 0, 2, 2, 2, 0, 2, 0,
      2, 0],
    [1, 2, 2, 2, 1, 3, 1, 2, 1, 3, 0, 3, 3, 3, 2, 0, 3, 0, 2, 1, 2, 2, 1, 3, 3, 3, 1, 2, 2, 2, 0, 3,
      3, 0, 3, 0, 2],
    [3, 3, 3, 1, 3, 1, 2, 1, 2, 2, 1, 3, 3, 3, 0, 2, 0, 2, 2, 2, 2, 0, 3, 3, 0, 2, 1, 3, 1, 3, 1, 3,
      1, 2, 0, 2, 0, 3, 0, 2, 0]]

theorem hcodes : ws.map revCodes = wsCodes := by decide +kernel

theorem checkWords_eq : checkWords = ws.map (List.map fun l : Fin 2 × Bool => (l.1.val, l.2)) :=
  rfl

theorem pt0 : allR 0 205 (pointOK actA 2 820 wsCodes) = true := by quickRfl
theorem pt1 : allR 205 205 (pointOK actA 2 820 wsCodes) = true := by quickRfl
theorem pt2 : allR 410 205 (pointOK actA 2 820 wsCodes) = true := by quickRfl
theorem pt3 : allR 615 205 (pointOK actA 2 820 wsCodes) = true := by quickRfl

theorem ptAll : allR 0 820 (pointOK actA 2 820 wsCodes) = true :=
  allR_join' (allR_join' (d := 410) pt0 pt1 (by quickRfl) (by quickRfl))
    (allR_join' (d := 410) pt2 pt3 (by quickRfl) (by quickRfl)) (by quickRfl) (by quickRfl)

theorem bindA : bindListK 10 (mask 10) (C.S 0) tabA.toList 0 = true := by quickRfl
theorem bindB : bindListK 10 (mask 10) (C.S 1) tabB.toList 0 = true := by quickRfl

theorem permOfArr_eq_of_rep {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)}
    (h : CFSG.Monster.B.Co2.Rep n t g) :
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

theorem actA_eq (x c : ℕ) (hc : c < 4) : actA (x * (2 + 2) + c) = pg 10 (mask 10) (selP c) x := by
  have h1 : (x * (2 + 2) + c) % 4 = c := by omega
  have h2 : (x * (2 + 2) + c) / 4 = x := by omega
  rw [actA, h1, h2]

theorem rep_of_bind {P : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin 820)} (ht : t.toList.length = 820)
    (hb : bindListK 10 (mask 10) P t.toList 0 = true)
    (hg : ∀ x : Fin 820, pg 10 (mask 10) P x.val = (g x).val) :
    CFSG.Monster.B.Co2.Rep 820 t g := by
  intro x
  have := toArray_eq_unpack ht hb
  rw [Array.toArray_toList] at this
  rw [this, unpack, getElem!_ofFn_nat _ x.2]
  exact hg x

theorem signedProd_eq {G : Type*} [Group G] (x y : G) (w : List (Fin 2 × Bool)) :
    wordProd (img2 x y) (w.map fun l => (l.1.val, l.2)) =
      CFSG.Certificates.signedProd (fun i : Fin 2 => img2 x y i.val) w := by
  rw [wordProd, CFSG.Certificates.signedProd, List.map_map]
  rfl

theorem checkWords_eval : ∀ v ∈ checkWords,
    wordProd (img2 (permOfArr 820 tabA) (permOfArr 820 tabB)) v = 1 := by
  have hpt := pointOK_of_allR ptAll
  obtain ⟨σ, hσ⟩ := exists_rep hpt
  have hw := relsAt_sound hσ ws hcodes (fun x hx => relsAt_of_pointOK (hpt x hx))
  have hr : ∀ g : Fin 2, ∀ x : Fin 820, pg 10 (mask 10) (selP (2 * g.val)) x.val = (σ g x).val :=
    fun g x => by
      have := (hσ g x).1
      rwa [actA_eq x.val (2 * g.val) (by have := g.isLt; omega)] at this
  have e0 : permOfArr 820 tabA = σ 0 :=
    permOfArr_eq_of_rep (rep_of_bind (by decide) bindA (hr 0))
  have e1 : permOfArr 820 tabB = σ 1 :=
    permOfArr_eq_of_rep (rep_of_bind (by decide) bindB (hr 1))
  intro v hv
  rw [checkWords_eq] at hv
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
  rw [signedProd_eq, e0, e1, ← hw u hu]
  congr 1
  funext i
  fin_cases i <;> rfl

end CertificateChecks.KernelU43B

end
