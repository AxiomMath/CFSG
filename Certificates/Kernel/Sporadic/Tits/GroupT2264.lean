module

public import Certificates.Kernel.Sporadic.Tits.Sift2264
public import Certificates.Kernel.Misc.Coset.C10009
public import CFSG.Certificates.Kernel.Spor.PresCardPG
public import CFSG.Certificates.Kernel.Spor.IndexTwo
public import CFSG.Certificates.Kernel.Spor.RawCard
public import CFSG.Certificates.Kernel.Spor.RawOrbSound
public import CFSG.Certificates.Kernel.Spor.SiftRSound
public import CFSG.Certificates.Kernel.Spor.SiftAMemOf
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Tits2264

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.PresPG CFSG.KS.IndexTwo
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native CFSG.LieType.Multipliers.Tits CertificateChecks.KernelMisc

theorem get_extract {S : Array (Array Nat)} {m k : Nat} (hk : k < m) (hS : m ≤ S.size) :
    (S.extract 0 m)[k]! = S[k]! := by
  rw [getElem!_pos _ k (by simp; omega), Array.getElem_extract, getElem!_pos S k (by omega)]
  simp

theorem hiOf {G : Nat} (h : canonK 1755 11 (mask 11) (1755 * 11) G = true) :
    Nat.shiftRight G (1755 * 11) = 0 := by
  have h' : bAnd(Nat.beq (Nat.shiftRight G (1755 * 11)) (nat_lit 0),
      allN 1755 (fun i => Nat.blt (pg 11 (mask 11) G i) 1755)) = true := h
  exact Nat.eq_of_beq_eq_true ((bAnd_iff (Nat.beq (Nat.shiftRight G (1755 * 11)) (nat_lit 0))
    (allN 1755 (fun i => Nat.blt (pg 11 (mask 11) G i) 1755))).1 h').1

theorem isInv_of {P : Nat} (h : permC P = true) :
    isInvA 1755 (unpack 1755 11 P) (invCand 1755 (unpack 1755 11 P)) = true := by
  obtain ⟨p, -, -⟩ := permC_spec h
  rw [(invEqK_sound p).1]
  exact (invEqK_sound p).2

theorem rep_of {P : Nat} (h : permC P = true) :
    Rep 1755 (unpack 1755 11 P) (permOfArr 1755 (unpack 1755 11 P)) ∧
      Rep 1755 (unpack 1755 11 (pinvS 1755 11 (mask 11) P)) (permOfArr 1755 (unpack 1755 11 P))⁻¹ :=
  rep_permOfArr (invEqK_sound (permC_spec h).1).2

theorem allPerms_of {A : Array (Array Nat)} {k : Nat} {P PI : Nat → Nat} (hs : A.size = k)
    (hA : ∀ j < k, A[j]! = unpack 1755 11 (P j))
    (hp : allN k (fun j => permOK 1755 11 (mask 11) (1755 * 11) (P j) (PI j)) = true) :
    allPermsOK 1755 A = true := by
  unfold allPermsOK
  rw [allLt_iff]
  intro j hj
  rw [hs] at hj
  have h := invEqK_sound (allN_spec hp j hj)
  rw [hA j hj, h.1]
  exact h.2

@[expose] noncomputable def d (j : Nat) : Equiv.Perm (Fin 1755) := permOfArr 1755 titsDerivedArrs[j]!

@[expose] noncomputable def T : Subgroup (Equiv.Perm (Fin 1755)) :=
  Subgroup.closure (Set.range fun j : Fin 2 => d j.val)

theorem card_T : Nat.card T ≤ 17971200 := by
  obtain ⟨h1, h2⟩ := CertificateChecks.KernelMiscCoset.C10009.perms
  obtain ⟨hfin, hcard⟩ := CertificateChecks.KernelMiscCoset.C10009.card_rels
  let x : ℕ → Equiv.Perm (Fin 1755) := fun i =>
    wordIn 2 (fun j => permOfArr 1755 titsDerivedArrs[j]!) (abcWords.getD i [])
  have hle : T ≤ Subgroup.closure (Set.range fun i : Fin 3 => x i.val) := by
    unfold T
    rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    change permOfArr 1755 titsDerivedArrs[j.val]! ∈ _
    rw [h2 j.val j.2]
    exact wordIn_mem_closure 3 x _
  have hc := card_closure_le_PG (m := 3) (ws := titsRels) (fun i => x i.val)
    (fun w hw => h1 w (List.mem_append_left _ hw))
  exact (Subgroup.card_le_of_le hle).trans (hc.trans hcard)

theorem orbitsD : rawOrbitSizes 1755 titsDerivedArrs (baseArr 1755 titsDerivedBase) =
    [1755, 10, 8, 8, 8, 2] := by
  rw [rawOrbitSizesK_sound bindsD permD TitsD.hl]
  decide

theorem orbitsA : rawOrbitSizes 1755 titsAmbientArrs (baseArr 1755 titsAmbientBase) =
    [1755, 80, 8, 2, 4, 4] := by
  rw [rawOrbitSizesK_orb bindsA permA TitsA.ho (by norm_num)]
  decide

theorem orbitsP : rawOrbitSizes 1755 titsPerfectArrs (baseArr 1755 titsPerfectBase) =
    [1755, 10, 8, 2, 8, 4, 2] := by
  rw [rawOrbitSizesK_orb bindsP permP TitsP.ho (by norm_num)]
  decide

theorem chainD : rawChainOK 1755 (titsDerivedArrs.extract 0 2) titsDerivedArrs
    (baseArr 1755 titsDerivedBase) (wordsArr 2 13 titsDerivedDerivations) 4 = true :=
  rawChainK_of_card 4 bindsD TitsD.head TitsD.hl (by
    rw [orbitsD]
    exact card_T.trans (by norm_num))

theorem mem_T {P : Nat} (hs : siftD P = true) (hp : permC P = true) :
    permOfArr 1755 (unpack 1755 11 P) ∈ T := by
  have hsa := siftK_soundR bindsD permD TitsD.hl rfl (hiOf (permC_spec hp).2.1)
    (range_of_permOK (permC_spec hp).1) hs
  have hP : allPermsOK 1755 titsDerivedArrs = true :=
    allPerms_of (by simp [titsDerivedArrs, titsField1755]) (fun j hj => der_eq hj) permD
  exact siftA_mem_of (by norm_num) (k := 2) (by simp [titsDerivedArrs, titsField1755])
    (by decide) hP (by norm_num) chainD (isInv_of hp) hsa

theorem sift_spec (k : Nat) (hk : k < 8) : siftD (toSift k) = true ∧ permC (toSift k) = true :=
  (bAnd_iff _ _).1 (allN_spec siftOK k hk)

end CertificateChecks.KernelSpor.Tits2264

end
