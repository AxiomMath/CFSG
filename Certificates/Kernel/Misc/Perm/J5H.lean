module

public import Certificates.Kernel.Misc.Perm.J5E
public import CFSG.Certificates.Kernel.Misc.ArrEnumOps
public import CFSG.Certificates.Kernel.Misc.ChainTailSound
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2F

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum
open CFSG.RankThree.PartOne CFSG.RankThree.Native CFSG.Monster.B.Co2.Native
open CertificateChecks.KernelMisc.CertBind (Bound)

theorem comm_of {p q : ℕ} (hp : permB 315 9 p = true) (hq : permB 315 9 q = true)
    (h : Nat.beq (cm p q) (cm q p) = true) :
    commA 315 (unpack 315 9 p) (unpack 315 9 q) = true := by
  rw [commA, comp_unpack' hw hp hq, comp_unpack' hw hq hp,
    eqA_unpack' hw (permB_pcomp hw hp hq) (permB_pcomp hw hq hp)]
  exact h

theorem eqA_of {p q : ℕ} (hp : permB 315 9 p = true) (hq : permB 315 9 q = true)
    (h : Nat.beq p q = true) : eqA 315 (unpack 315 9 p) (unpack 315 9 q) = true := by
  rw [eqA_unpack' hw hp hq]
  exact h

theorem toList_of {a : Array (Array ℕ)} {N : ℕ} {F : ℕ → Array ℕ} (hs : a.size = N)
    (h : ∀ i < N, a[i]! = F i) : a.toList = (List.range N).map F := by
  apply List.ext_getElem
  · simp [hs]
  · intro i h1 h2
    rw [Array.getElem_toList, List.getElem_map, List.getElem_range,
      ← h i (by simpa [hs] using h1), getElem!_pos a i (by simpa using h1)]

theorem relsOKP_of {base : Array ℕ} {BP X nb : ℕ} {rels : List (ℕ × ℕ × ℕ)}
    (hb : base.size = nb) (hbp : ∀ t < nb, base[t]! = pg 9 (mask 9) BP t)
    (hbn : ∀ t < nb, pg 9 (mask 9) BP t < 315) (hX : permB 315 9 X = true)
    (h : relsK BP X nb rels = true) :
    relsOKP 5 315 base (unpack 315 9 X) rels = true := by
  rw [relsOKP, List.all_eq_true]
  rw [relsK, List.all_eq_true] at h
  intro r hr
  have hr' := h r hr
  simp only [Bool.and_eq_true, Nat.blt_eq] at hr'
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hr'
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, hb]
  refine ⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩
  rw [pow_unpack' hw hX, hbp _ h2, hbp _ h3, CFSG.KC.Misc.PairCount.unpack_get (hbn _ h2)]
  exact Nat.eq_of_beq_eq_true h4

theorem rel_lt_of {BP X nb : ℕ} {rels : List (ℕ × ℕ × ℕ)} (h : relsK BP X nb rels = true) :
    ∀ r ∈ rels, r.2.2 < 5 := by
  intro r hr
  rw [relsK, List.all_eq_true] at h
  have hr' := h r hr
  simp only [Bool.and_eq_true, Nat.blt_eq] at hr'
  exact hr'.1.1.1

theorem powPA_get {X : ℕ} (hX : permB 315 9 X = true) :
    ∀ e < (CFSG.RankThree.PartOne.powPA 5 315 (unpack 315 9 X)).size,
      (CFSG.RankThree.PartOne.powPA 5 315 (unpack 315 9 X))[e]! = unpack 315 9 (pw X e) := by
  intro e he
  rw [getElem!_pos _ e he]
  simp only [CFSG.RankThree.PartOne.powPA, Array.getElem_ofFn]
  exact pow_unpack' hw hX e

end CertificateChecks.KernelMisc.J2F

end
