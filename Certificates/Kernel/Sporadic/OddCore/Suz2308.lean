module

public import Certificates.Kernel.Sporadic.OddCore.Suz2308R
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import CFSG.Certificates.Kernel.Spor.RowWordSound
public import CFSG.Certificates.Kernel.Spor.MulHSound
public import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import CFSG.Monster.B.Co2.PermArr
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Sporadic.SuzOddCore.Arrays
import CFSG.Sporadic.SuzOddCore.GraphArrays
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.List.Sort
import CFSG.Certificates.Kernel.Spor.RawOrbGrp
public import CFSG.Sporadic.SuzOddCore.Perms
import CFSG.Sporadic.SuzOddCore.CertChain
import CFSG.Sporadic.Schreier.PairChain

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.OddCore.S2308

open CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.KC.Enum CFSG.KS
open CFSG.KS.Row CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.Raw CFSG.KS.Mathieu CFSG.PSL3Four.Native
open CFSG.Certificates.Native CertificateChecks.KernelSpor

theorem bAnd_eq (a b : Bool) : bAnd(a, b) = (a && b) := by cases a <;> rfl

theorem notB_eq (a : Bool) : notB a = !a := by cases a <;> rfl

theorem nIf_eq (c : Bool) (t e : Nat) : nIf(c, t, e) = if c then t else e := by cases c <;> rfl

theorem o2_eq (f g : Nat → Nat) (x : Nat) : o2 f g x = f (g x) := strictN_app _ _

theorem itr_succ (f : Nat → Nat) (k x : Nat) : itr f (k + 1) x = f (itr f k x) :=
  strictN_app _ _

theorem itr_zero (f : Nat → Nat) (x : Nat) : itr f 0 x = x := rfl

theorem itr_congr {f g : Nat → Nat} (hfg : ∀ y < 22880, f y = g y) (hf : ∀ y < 22880, f y < 22880) :
    ∀ k, ∀ x < 22880, itr f k x = itr g k x ∧ itr f k x < 22880
  | 0, x, hx => ⟨rfl, hx⟩
  | k + 1, x, hx => by
    obtain ⟨e, hl⟩ := itr_congr hfg hf k x hx
    rw [itr_succ, itr_succ, ← e, hfg _ hl]
    exact ⟨rfl, by rw [← hfg _ hl]; exact hf _ hl⟩

theorem beq_nat (a b : Nat) : (a == b) = Nat.beq a b := by
  cases h : Nat.beq a b
  · rw [beq_eq_false_iff_ne]
    intro e
    rw [e, Nat.beq_refl] at h
    exact absurd h (by decide)
  · rw [Nat.eq_of_beq_eq_true h]
    exact beq_self_eq_true _

theorem alt_iff {n : Nat} {p : Nat → Bool} : allLt n p = true ↔ ∀ i < n, p i = true :=
  CFSG.Monster.B.Co2.allLt_iff

theorem comp_eqA (n : Nat) (p q : Array Nat) : comp n p q = compA n p q := rfl

theorem eqA_true {n : Nat} {t u : Array Nat} (h : ∀ x < n, t[x]! = u[x]!) : eqA n t u = true :=
  alt_iff.2 fun i hi => beq_iff_eq.2 (h i hi)

theorem eqA_false {n x : Nat} {t u : Array Nat} (hx : x < n) (h : t[x]! ≠ u[x]!) :
    eqA n t u = false := by
  cases e : eqA n t u
  · rfl
  · exact absurd (beq_iff_eq.1 (alt_iff.1 e x hx)) h

theorem arr_eq {n : Nat} {t u : Array Nat} (ht : t.size = n) (hu : u.size = n)
    (h : ∀ x < n, t[x]! = u[x]!) : t = u := by
  apply Array.ext
  · rw [ht, hu]
  · intro i h1 h2
    rw [← getElem!_pos t i h1, ← getElem!_pos u i h2]
    exact h i (by omega)

theorem size_wordA (n : Nat) (S Sinv : Array (Array Nat)) (w : List Int) :
    (wordA n S Sinv w).size = n := by
  cases w <;> simp [wordA, compA, idA]

theorem map_get {L : Array (Array Nat)} {f : Array Nat → Array Nat} {j : Nat} (hj : j < L.size) :
    (L.map f)[j]! = f L[j]! := by
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_map, getElem!_pos L j hj]

theorem arr2_get0 {α : Type} [Inhabited α] (a b : α) : (#[a, b] : Array α)[0]! = a := rfl

theorem arr2_get1 {α : Type} [Inhabited α] (a b : α) : (#[a, b] : Array α)[1]! = b := rfl

theorem rl_get {F : Nat → Nat} {o x : Nat} (hx : x < 22880) :
    (rowArr 22880 15 F o)[x]! = rl F o x := rowArr_get hx

theorem cert_get {k x : Nat} (hk : k < 12) (hx : x < 22880) : (certArr k)[x]! = cgk k x := by
  rw [certArr_eq hk, rowArr_get hx]
  rfl

theorem cert_inv {k : Nat} (hk : k < 12) :
    invCand 22880 (certArr k) = rowArr 22880 15 SuzCertI (ofs k) := by
  rw [certArr_eq hk]
  exact (rpermK_sound (allN_spec cert_perms k hk)).1

theorem cert_rngF {k : Nat} (hk : k < 12) : ∀ i < 22880, rg 15 (mask 15) SuzCertT.F (ofs k) i < 22880 :=
  rpermK_range (allN_spec cert_perms k hk)

theorem strong_get {j : Nat} (hj : j < 10) : certStrongArrs[j]! = certArr (j + 2) := by
  interval_cases j <;> simp [certStrongArrs]

theorem strongInv_get {j : Nat} (hj : j < 10) :
    certStrongInvs[j]! = rowArr 22880 15 SuzCertI (ocs j) := by
  have e : certStrongInvs[j]! = invCand 22880 certStrongArrs[j]! := by
    interval_cases j <;> simp [certStrongInvs, certStrongArrs]
  rw [e, strong_get hj, cert_inv (k := j + 2) (by omega)]
  rfl

theorem strong_rows {j : Nat} (hj : j < 10) :
    certStrongArrs[j]! = rowArr 22880 15 SuzCertT.F (ocs j) := by
  rw [strong_get hj, certArr_eq (k := j + 2) (by omega)]
  rfl

theorem cen_get {r x : Nat} (hr : r < 9) (hx : x < 22880) : (centerFull r)[x]! = cf r x := by
  rw [centerFull_eq hr, rowArr_get hx]
  rfl

theorem cen_lt {r x : Nat} (hr : r < 9) (hx : x < 22880) : cf r x < 22880 :=
  rpermK_range (allN_spec full_perms r hr) x hx

theorem cen_perm {r : Nat} (hr : r < 9) :
    CFSG.Sporadic.SuzOddCore.permOK 22880 (centerFull r) = true := by
  have hp := rpermK_sound (n := 22880) (w := 15) (o := 715 * r) (o' := 715 * r)
    (allN_spec full_perms r hr)
  unfold CFSG.Sporadic.SuzOddCore.permOK
  rw [centerFull_eq hr, size_rowArr, hp.1]
  simp only [beq_self_eq_true, Bool.true_and]
  exact hp.2

theorem suzS_memP {j : Nat} (hj : j < 10) : suzS j ∈ suzP := by
  rw [← certChain_originalSubgroup]
  have := certChain_eqns.strong_mem ⟨j, hj⟩
  rwa [certChain_strong_get] at this

theorem suz_faith {g : Equiv.Perm (Fin 22880)} (hg : g ∈ suzP)
    (hb : ∀ p < 6, ∀ hp : p < 22880, (g ⟨p, hp⟩ : Nat) = p) : g = 1 := by
  have hF := CFSG.Sporadic.Schreier.baseFaithful_of_valid certChain_valid
  have eb : certChain.base.toList.map Fin.val = [0, 1, 2, 3, 4, 5] := by
    rw [certChain_base_toList]
    rfl
  rw [certChain_originalSubgroup, eb] at hF
  refine hF g hg fun x hx => Fin.ext (hb x.val ?_ x.2)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  omega

theorem suz_eqF {f f' : Nat → Nat} {g h : Equiv.Perm (Fin 22880)}
    (hf : ∀ x : Fin 22880, f x = g x) (hf' : ∀ x : Fin 22880, f' x = h x) (hg : g ∈ suzP)
    (hh : h ∈ suzP) (hb : ∀ p < 6, f p = f' p) : ∀ x < 22880, f x = f' x := by
  have e : h⁻¹ * g = 1 := suz_faith (suzP.mul_mem (suzP.inv_mem hh) hg) fun p hp hp' => by
    have e1 : g ⟨p, hp'⟩ = h ⟨p, hp'⟩ :=
      Fin.ext (by rw [← hf ⟨p, hp'⟩, ← hf' ⟨p, hp'⟩]; exact hb p hp)
    rw [Equiv.Perm.mul_apply, e1]
    simp
  have e' : g = h := (inv_mul_eq_one.1 e).symm
  intro x hx
  rw [hf ⟨x, hx⟩, hf' ⟨x, hx⟩, e']

theorem repF_comp {f f' : Nat → Nat} {g g' : Equiv.Perm (Fin 22880)}
    (hf : ∀ x : Fin 22880, f x = g x) (hf' : ∀ x : Fin 22880, f' x = g' x) :
    ∀ x : Fin 22880, o2 f f' x = (g * g') x := fun x => by
  rw [o2_eq, hf' x, hf (g' x)]
  rfl

@[expose] def RepSuz (t : Array Nat) : Prop := ∃ g ∈ suzP, Rep 22880 t g

theorem repP_word {kS : Nat} {L M : Array (Array Nat)} (hL : ∀ h < kS, RepSuz L[h]!)
    (hM : ∀ h < kS, isInvA 22880 L[h]! M[h]! = true) {w : List Int}
    (hw : lettersOK kS w = true) : RepSuz (wordA 22880 L M w) := by
  classical
  let gs : Nat → Equiv.Perm (Fin 22880) := fun h => if hh : h < kS then (hL h hh).choose else 1
  have hg : ∀ h < kS, gs h ∈ suzP ∧ Rep 22880 L[h]! (gs h) := fun h hh => by
    simp only [gs, hh, dite_true]
    exact (hL h hh).choose_spec
  refine ⟨_, ?_, rep_wordA (fun h hh => (hg h hh).2)
    (fun h hh => rep_inv_of_isInvA (hg h hh).2 (hM h hh)) w hw⟩
  exact (Subgroup.closure_le suzP).2 (Set.range_subset_iff.2 fun h : Fin kS => (hg h h.2).1)
    (Quiver.SchreierGraph.evalWord_mem_closure _ _)

def crtL : Array (Array Nat) :=
  #[certArr 0, certArr 1, certArr 2, certArr 3, certArr 4, certArr 5, certArr 6, certArr 7,
    certArr 8, certArr 9, certArr 10, certArr 11]

theorem crt_get {j : Nat} (hj : j < 12) : crtL[j]! = certArr j := by
  interval_cases j <;> simp [crtL]

theorem crt_repP {k : Nat} (hk : k < 12) : RepSuz (certArr k) := by
  rcases Nat.lt_or_ge k 2 with h | h
  · interval_cases k
    · exact ⟨suzA0, Subgroup.subset_closure (by simp), rep_suzA0⟩
    · exact ⟨suzA1, Subgroup.subset_closure (by simp), rep_suzA1⟩
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    exact ⟨suzS j, suzS_memP (by omega), rep_suzS (by omega)⟩

theorem cert_rngG {k : Nat} (hk : k < 12) : ∀ i < 22880, rg 15 (mask 15) SuzCertI (ofs k) i < 22880 :=
  fun i hi => by
    obtain ⟨g, -, hr⟩ := crt_repP hk
    have h := CFSG.KS.Raw.rep_invCand hr ⟨i, hi⟩
    rw [cert_inv hk, rowArr_get hi] at h
    rw [h]
    exact (g⁻¹ ⟨i, hi⟩).2

theorem wpC_repP {w : List Int} (hw : lettersOK 12 w = true) :
    (∃ g ∈ suzP, ∀ y : Fin 22880, wpC w y = g y) ∧ ∀ x < 22880, wpC w x < 22880 := by
  have hs : 12 ≤ crtL.size := by simp [crtL]
  have hi : ∀ j < 12, (crtL.map (invCand 22880))[j]! = rowArr 22880 15 SuzCertI (ofs j) :=
    fun j hj => by rw [map_get (L := crtL) (j := j) (by omega), crt_get hj, cert_inv hj]
  have h := rwordPt_eq (kS := 12) (O := ofs) (S := crtL) (Sinv := crtL.map (invCand 22880))
    (fun j hj => (crt_get hj).trans (certArr_eq hj)) hi (fun j hj => cert_rngF hj)
    (fun j hj => cert_rngG hj) w hw
  obtain ⟨g, hg, hr⟩ := repP_word (kS := 12) (L := crtL) (M := crtL.map (invCand 22880))
    (fun j hj => by rw [crt_get hj]; exact crt_repP hj)
    (fun j hj => by
      rw [hi j hj, crt_get hj, certArr_eq hj]
      exact (rpermK_sound (allN_spec cert_perms j hj)).2) hw
  exact ⟨⟨g, hg, fun y => (h y y.2).1.symm.trans (hr y)⟩, fun x hx => (h x hx).2⟩

theorem fe_size : ∀ k, (fullExtArrList k).size = 8 + k
  | 0 => by simp [fullExtArrList, localStrongIdx]
  | k + 1 => by
    simp only [fullExtArrList, Array.size_push, fe_size k]
    omega

theorem fe_lt {j k : Nat} (hj : j < 8 + k) : (fullExtArrList (k + 1))[j]! = (fullExtArrList k)[j]! := by
  have hlt : j < (fullExtArrList k).size := by rw [fe_size]; omega
  simp only [fullExtArrList]
  rw [getElem!_pos _ j (by rw [Array.size_push]; omega), Array.getElem_push_lt hlt,
    ← getElem!_pos _ j hlt]

theorem fe_top (k : Nat) : (fullExtArrList (k + 1))[8 + k]! =
    wordA 22880 (fullExtArrList k) ((fullExtArrList k).map (invCand 22880))
      (localDerivs.getD (8 + k) []) := by
  have hsz := fe_size k
  simp only [fullExtArrList]
  rw [getElem!_pos _ (8 + k) (by rw [Array.size_push, hsz]; omega), Array.getElem_push]
  simp [hsz]

theorem rwG_cons (f g : Nat → Nat → Nat) (z : Int) (wd : List Int) (x : Nat) :
    rwG f g (z :: wd) x = Int.rec (motive := fun _ => Nat) (fun k => f (Nat.sub k 1) (rwG f g wd x))
      (fun k => g k (rwG f g wd x)) z :=
  strictN_app (rwG f g wd x) fun y => Int.rec (motive := fun _ => Nat) (fun k => f (Nat.sub k 1) y)
    (fun k => g k y) z

theorem rwG_eq {n kS kI : Nat} {L M : Array (Array Nat)} {f g : Nat → Nat → Nat}
    (hL : ∀ j < kS, ∀ x < n, (L[j]!)[x]! = f j x ∧ f j x < n)
    (hM : ∀ j < kI, ∀ x < n, (M[j]!)[x]! = g j x ∧ g j x < n) :
    ∀ (wd : List Int), lettersOK kS wd = true → wd.all (fun z => decide (-(kI : Int) ≤ z)) = true →
      ∀ x < n, (wordA n L M wd)[x]! = rwG f g wd x ∧ rwG f g wd x < n
  | [], _, _, x, hx => by
    refine ⟨?_, hx⟩
    rw [wordA, idA, getElem!_pos _ x (by simp [hx])]
    simp [rwG]
  | z :: rest, hl, hn, x, hx => by
    simp only [lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hl hn
    obtain ⟨⟨hz0, hzk⟩, hrest⟩ := hl
    obtain ⟨ih1, ih2⟩ := rwG_eq hL hM rest (by simpa [lettersOK] using hrest) hn.2 x hx
    have hw : (wordA n L M (z :: rest))[x]! = (letterA L M z)[(wordA n L M rest)[x]!]! := by
      rw [wordA, compA, getElem!_pos _ x (by simp [hx])]
      simp
    rw [rwG_cons, hw, ih1]
    cases z with
    | ofNat k =>
      have hk1 : 1 ≤ k := by
        rcases k with _ | k
        · exact absurd rfl hz0
        · omega
      have hnat : (Int.ofNat k).natAbs = k := rfl
      have hkS : k - 1 < kS := by omega
      have hpos : (0 : Int) < Int.ofNat k := Int.ofNat_lt.mpr hk1
      have hlet : letterA L M (Int.ofNat k) = L[k - 1]! := by
        unfold letterA
        simp only [hpos, ↓reduceIte]
        rfl
      rw [hlet]
      exact hL _ hkS _ ih2
    | negSucc k =>
      have hkI : k < kI := by
        have h1 := hn.1
        rw [Int.negSucc_eq] at h1
        omega
      have hlet : letterA L M (Int.negSucc k) = M[k]! := by
        simp [letterA]
      rw [hlet]
      exact hM _ hkI _ ih2

theorem fe0_get {j : Nat} (hj : j < 8) : (fullExtArrList 0)[j]! = certArr (j + 4) := by
  interval_cases j <;> simp [fullExtArrList, localStrongIdx, certStrongArrs]

theorem fe_lo : ∀ k, ∀ {j : Nat}, j < 8 → (fullExtArrList k)[j]! = certArr (j + 4)
  | 0, _, hj => fe0_get hj
  | k + 1, _, hj => (fe_lt (by omega)).trans (fe_lo k hj)

theorem fy_lo {j x : Nat} (hj : j < 8) : fy j x = cgk (j + 4) x := by
  have hb : Nat.blt j 8 = true := Eq.mpr Nat.blt_eq hj
  have e : fy j x = cgk (Nat.add j 4) x := by
    unfold fy
    rw [hb]
  exact e

theorem fyi_lo {j x : Nat} (hj : j < 8) : fyi j x = ci (j + 4) x := by
  have hb : Nat.blt j 8 = true := Eq.mpr Nat.blt_eq hj
  have e : fyi j x = ci (Nat.add j 4) x := by
    unfold fyi
    rw [hb]
  exact e

theorem blt8_false {j : Nat} (hj : ¬ j < 8) : Nat.blt j 8 = false := by
  cases h : Nat.blt j 8
  · rfl
  · exact absurd (Eq.mp Nat.blt_eq h) hj

theorem fy_hi {j x : Nat} (hj : ¬ j < 8) : fy j x = wpC (suzRowW.getD (Nat.sub j 8) []) x := by
  unfold fy
  rw [blt8_false hj]

theorem fyi_hi {j x : Nat} (hj : ¬ j < 8) :
    fyi j x = wpC (suzInvW (suzRowW.getD (Nat.sub j 8) [])) x := by
  unfold fyi
  rw [blt8_false hj]

theorem wpC_rep' {w : List Int} (hw : lettersOK 12 w = true) {f : Nat → Nat}
    (hf : ∀ x, f x = wpC w x) :
    (∃ g ∈ suzP, ∀ y : Fin 22880, f y = g y) ∧ ∀ x < 22880, f x < 22880 := by
  obtain ⟨⟨g, hg, hr⟩, hl⟩ := wpC_repP hw
  refine ⟨⟨g, hg, fun y => (hf y).trans (hr y)⟩, fun x hx => ?_⟩
  rw [hf x]
  exact hl x hx

theorem fy_rep {j : Nat} (hj : j < 14) :
    (∃ g ∈ suzP, ∀ y : Fin 22880, fy j y = g y) ∧ ∀ x < 22880, fy j x < 22880 := by
  rcases Nat.lt_or_ge j 8 with h | h
  · obtain ⟨g, hg, hr⟩ := crt_repP (k := j + 4) (by omega)
    refine ⟨⟨g, hg, fun y => ?_⟩, fun x hx => ?_⟩
    · rw [fy_lo h]
      exact (cert_get (k := j + 4) (by omega) y.2).symm.trans (hr y)
    · rw [fy_lo h]
      exact cert_rngF (k := j + 4) (by omega) x hx
  · have hw : lettersOK 12 (suzRowW.getD (Nat.sub j 8) []) = true := by
      interval_cases j <;> decide
    exact wpC_rep' hw fun x => fy_hi (by omega)

theorem fyi_rep {j : Nat} (hj : j < 14) :
    (∃ g ∈ suzP, ∀ y : Fin 22880, fyi j y = g y) ∧ ∀ x < 22880, fyi j x < 22880 := by
  rcases Nat.lt_or_ge j 8 with h | h
  · obtain ⟨g, hg, hr⟩ := crt_repP (k := j + 4) (by omega)
    have hi := CFSG.KS.Raw.rep_invCand hr
    rw [cert_inv (k := j + 4) (by omega)] at hi
    refine ⟨⟨g⁻¹, suzP.inv_mem hg, fun y => ?_⟩, fun x hx => ?_⟩
    · rw [fyi_lo h]
      exact (rl_get (F := SuzCertI) (o := ofs (j + 4)) y.2).symm.trans (hi y)
    · rw [fyi_lo h]
      exact cert_rngG (k := j + 4) (by omega) x hx
  · have hw : lettersOK 12 (suzInvW (suzRowW.getD (Nat.sub j 8) [])) = true := by
      interval_cases j <;> decide
    exact wpC_rep' hw fun x => fyi_hi (by omega)

theorem suzLvl_facts {p : Nat} (hp : p < 6) :
    (∀ k < 6, fy (8 + k) p = rwG fy fyi (localDerivs.getD (8 + k) []) p ∧
      fy (8 + k) (fyi (8 + k) p) = p) ∧
    ∀ a < 5, tx a p = rwG fy fyi (sylowQuotWords.getD a []) p := by
  have h := allN_spec suzLvl p hp
  simp only [bAnd_eq, Bool.and_eq_true] at h
  refine ⟨fun k hk => ?_, fun a ha => Nat.eq_of_beq_eq_true (allN_spec h.2 a ha)⟩
  have e := allN_spec h.1 k hk
  simp only [Bool.and_eq_true, Nat.add_eq] at e
  exact ⟨Nat.eq_of_beq_eq_true e.1, Nat.eq_of_beq_eq_true e.2⟩

theorem FE_repP : ∀ k ≤ 6, ∀ j < 8 + k, RepSuz (fullExtArrList k)[j]!
  | 0, _, j, hj => by
    rw [fe0_get (by omega)]
    exact ⟨suzS (j + 2), suzS_memP (by omega), rep_suzS (j := j + 2) (by omega)⟩
  | k + 1, hk, j, hj => by
    rcases Nat.lt_or_ge j (8 + k) with h | h
    · rw [fe_lt h]
      exact FE_repP k (by omega) j h
    · obtain rfl : j = 8 + k := by omega
      rw [fe_top k]
      refine repP_word (kS := 8 + k) (fun h hh => FE_repP k (by omega) h hh) (fun h hh => ?_) ?_
      · rw [map_get (L := fullExtArrList k) (j := h) (by rw [fe_size]; omega)]
        obtain ⟨g, -, hr⟩ := FE_repP k (by omega) h hh
        exact CFSG.KS.Raw.isInvA_of_rep hr (CFSG.KS.Raw.rep_invCand hr)
      · have : k < 6 := by omega
        interval_cases k <;> decide

theorem full_size : fullExtArrs.size = 14 := fe_size 6

theorem full_get {j : Nat} (hj : j < 8) : fullExtArrs[j]! = certArr (j + 4) := fe_lo 6 hj

theorem full_repP {j : Nat} (hj : j < 14) : RepSuz fullExtArrs[j]! := FE_repP 6 le_rfl j hj

theorem fe_lvl : ∀ k ≤ 6, ∀ j < 8 + k, ∀ x < 22880, ((fullExtArrList k)[j]!)[x]! = fy j x ∧
    (((fullExtArrList k).map (invCand 22880))[j]!)[x]! = fyi j x
  | 0, _, j, hj, x, hx => by
    have h8 : j < 8 := by omega
    rw [map_get (L := fullExtArrList 0) (j := j) (by rw [fe_size]; omega), fe0_get h8,
      cert_inv (k := j + 4) (by omega), cert_get (k := j + 4) (by omega) hx, rl_get hx, fy_lo h8,
      fyi_lo h8]
    exact ⟨rfl, rfl⟩
  | k + 1, hk, j, hj, x, hx => by
    have ih := fe_lvl k (by omega)
    rcases Nat.lt_or_ge j (8 + k) with h | h
    · have e1 := fe_lt (k := k) h
      have e2 : ((fullExtArrList (k + 1)).map (invCand 22880))[j]! =
          ((fullExtArrList k).map (invCand 22880))[j]! := by
        rw [map_get (L := fullExtArrList (k + 1)) (by rw [fe_size]; omega),
          map_get (L := fullExtArrList k) (by rw [fe_size]; omega), e1]
      rw [e1, e2]
      exact ih j h x hx
    obtain rfl : j = 8 + k := by omega
    have hk6 : k < 6 := by omega
    have hl : lettersOK (8 + k) (localDerivs.getD (8 + k) []) = true := by
      interval_cases k <;> decide
    have hn : (localDerivs.getD (8 + k) []).all
        (fun z => decide (-((8 + k : Nat) : Int) ≤ z)) = true := by
      interval_cases k <;> decide
    have hw := rwG_eq (n := 22880) (kS := 8 + k) (kI := 8 + k) (L := fullExtArrList k)
      (M := (fullExtArrList k).map (invCand 22880)) (f := fy) (g := fyi)
      (fun i hi y hy => ⟨(ih i hi y hy).1, (fy_rep (j := i) (by omega)).2 y hy⟩)
      (fun i hi y hy => ⟨(ih i hi y hy).2, (fyi_rep (j := i) (by omega)).2 y hy⟩) _ hl hn
    obtain ⟨g, hg, hrep⟩ := FE_repP (k + 1) hk (8 + k) (by omega)
    obtain ⟨⟨h1, hh1, hr1⟩, -⟩ := fy_rep (j := 8 + k) (by omega)
    obtain ⟨⟨h2, hh2, hr2⟩, -⟩ := fyi_rep (j := 8 + k) (by omega)
    have htop : ∀ y < 22880, ((fullExtArrList (k + 1))[8 + k]!)[y]! = fy (8 + k) y :=
      suz_eqF (f := fun y => ((fullExtArrList (k + 1))[8 + k]!)[y]!) hrep hr1 hg hh1 fun p hp => by
        rw [fe_top k, (hw p (by omega)).1]
        exact ((suzLvl_facts hp).1 k hk6).1.symm
    have hid : ∀ y < 22880, o2 (fy (8 + k)) (fyi (8 + k)) y = y :=
      suz_eqF (f' := fun y => y) (h := 1) (repF_comp hr1 hr2) (fun y => rfl)
        (suzP.mul_mem hh1 hh2) suzP.one_mem fun p hp => by
          rw [o2_eq]
          exact ((suzLvl_facts hp).1 k hk6).2
    have einv : ∀ y : Fin 22880, g⁻¹ y = h2 y := fun y => by
      rw [Equiv.Perm.inv_eq_iff_eq]
      apply Fin.ext
      rw [← hrep (h2 y), htop _ (h2 y).2, ← hr2 y]
      have e := hid y y.2
      rw [o2_eq] at e
      exact e.symm
    refine ⟨htop x hx, ?_⟩
    rw [map_get (L := fullExtArrList (k + 1)) (by rw [fe_size]; omega)]
    exact ((CFSG.KS.Raw.rep_invCand hrep ⟨x, hx⟩).trans (congrArg Fin.val (einv ⟨x, hx⟩))).trans
      (hr2 ⟨x, hx⟩).symm

theorem full_pt {j : Nat} (hj : j < 14) {x : Nat} (hx : x < 22880) : (fullExtArrs[j]!)[x]! = fy j x :=
  (fe_lvl 6 le_rfl j hj x hx).1

theorem T_size : (tFullOf fullExtArrs).size = 5 := by simp [tFullOf]

theorem tx_rep {a : Nat} (ha : a < 5) :
    (∃ g ∈ suzP, ∀ y : Fin 22880, tx a y = g y) ∧ ∀ x < 22880, tx a x < 22880 := by
  have hw : lettersOK 12 (suzTxW.getD a []) = true := by
    interval_cases a <;> decide
  exact wpC_rep' (f := tx a) hw fun x => rfl

theorem T_get {a x : Nat} (ha : a < 5) (hx : x < 22880) :
    ((tFullOf fullExtArrs)[a]!)[x]! = tx a x ∧ tx a x < 22880 := by
  have hl : lettersOK 14 (sylowQuotWords.getD a []) = true := by
    interval_cases a <;> decide
  have hn : (sylowQuotWords.getD a []).all (fun z => decide (-((0 : Nat) : Int) ≤ z)) = true := by
    interval_cases a <;> decide
  have hw := rwG_eq (n := 22880) (kS := 14) (kI := 0) (L := fullExtArrs)
    (M := fullExtArrs.map (invCand 22880)) (f := fy) (g := fyi)
    (fun j hj y hy => ⟨full_pt hj hy, (fy_rep hj).2 y hy⟩)
    (fun j hj => absurd hj (Nat.not_lt_zero _)) _ hl hn
  have he : (tFullOf fullExtArrs)[a]! = wordA 22880 fullExtArrs (fullExtArrs.map (invCand 22880))
      (sylowQuotWords.getD a []) := by
    rw [tFullOf, getElem!_pos _ a (by simp; omega), Array.getElem_ofFn]
  have hT : RepSuz (tFullOf fullExtArrs)[a]! := by
    rw [he]
    refine repP_word (kS := 14) (fun h hh => full_repP hh) (fun h hh => ?_) hl
    rw [map_get (L := fullExtArrs) (j := h) (by rw [full_size]; exact hh)]
    obtain ⟨g, -, hr⟩ := full_repP hh
    exact CFSG.KS.Raw.isInvA_of_rep hr (CFSG.KS.Raw.rep_invCand hr)
  obtain ⟨g, hg, hrep⟩ := hT
  obtain ⟨⟨h, hh, hr⟩, hlt⟩ := tx_rep ha
  refine ⟨suz_eqF (f := fun y => ((tFullOf fullExtArrs)[a]!)[y]!) hrep hr hg hh (fun p hp => ?_) x hx,
    hlt x hx⟩
  rw [he, (hw p (by omega)).1]
  exact ((suzLvl_facts hp).2 a ha).symm

theorem T1_get {a x : Nat} (ha : a < 5) (hx : x < 22880) :
    ((tFullOf fullExtArrs)[a]!)[x]! = tx a x := (T_get ha hx).1

theorem tx_lt {a x : Nat} (ha : a < 5) (hx : x < 22880) : tx a x < 22880 := (T_get ha hx).2

theorem foldr_addV (g : Nat → Nat) (l : List Nat) (s : Nat) :
    l.foldr (fun d s => Nat.add s (g d)) s = s + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.foldr_cons, ih]
    simp only [List.map_cons, List.sum_cons, Nat.add_eq]
    omega

theorem s23cV_eq (x : Nat) : s23cV x = if cenP x = true then
    (if Nat.beq (cf 3 x) x = true then 1 else 0) + ((if Nat.beq (cf 4 x) x = true then 8192 else 0) +
      (if bAnd(notB (Nat.beq x 0), Nat.beq (zx x) x) = true then 67108864 else 0))
    else 549755813888 := by
  rw [s23cV.eq_1]
  simp only [nIf_eq, Nat.add_eq]

theorem s23cV_sum (o : Nat) : ∀ l : List Nat,
    (l.map fun d => s23cV (o + d)).sum < 549755813888 →
    (∀ d ∈ l, cenP (o + d) = true) ∧
    (l.map fun d => s23cV (o + d)).sum =
      (l.filter fun d => Nat.beq (cf 3 (o + d)) (o + d)).length +
      8192 * (l.filter fun d => Nat.beq (cf 4 (o + d)) (o + d)).length +
      67108864 *
        (l.filter fun d => bAnd(notB (Nat.beq (o + d) 0), Nat.beq (zx (o + d)) (o + d))).length
  | [], _ => by simp
  | d :: l, h => by
    simp only [List.map_cons, List.sum_cons] at h
    rw [s23cV_eq] at h
    have hc : cenP (o + d) = true := by
      by_contra hc
      simp only [hc, ↓reduceIte] at h
      omega
    simp only [hc, ↓reduceIte] at h
    have ih := s23cV_sum o l (by omega)
    refine ⟨fun e he => ?_, ?_⟩
    · rcases List.mem_cons.1 he with rfl | he
      · exact hc
      · exact ih.1 e he
    · simp only [List.map_cons, List.sum_cons]
      rw [s23cV_eq]
      simp only [hc, ↓reduceIte]
      rw [ih.2]
      simp only [List.filter_cons]
      split_ifs <;> (try simp only [List.length_cons]) <;> omega

@[expose] noncomputable def s23cQ (p : Nat → Bool) (o : Nat) : Nat :=
  ((List.range 5720).filter fun d => p (o + d)).length

theorem s23cQ_le (p : Nat → Bool) (o : Nat) : s23cQ p o ≤ 5720 :=
  (List.length_filter_le _ _).trans (List.length_range ..).le

theorem s23dig {N a b c : Nat} (h : N = a + 8192 * b + 67108864 * c) (ha : a ≤ 5720)
    (hb : b ≤ 5720) : a = N % 8192 ∧ b = N / 8192 % 8192 ∧ c = N / 67108864 := by
  omega

theorem s23cS_spec {q N : Nat} (h : s23cB q N = true) (hN : N < 549755813888) :
    (∀ d < 5720, cenP (5720 * q + d) = true) ∧
    s23cQ (fun i => Nat.beq (cf 3 i) i) (5720 * q) = N % 8192 ∧
    s23cQ (fun i => Nat.beq (cf 4 i) i) (5720 * q) = N / 8192 % 8192 ∧
    s23cQ (fun i => bAnd(notB (Nat.beq i 0), Nat.beq (zx i) i)) (5720 * q) = N / 67108864 := by
  rw [s23cB.eq_1] at h
  have e := Nat.eq_of_beq_eq_true h
  rw [s23cS.eq_1, CFSG.KS.Raw.Orb.foldN_eq, foldr_addV, Nat.zero_add] at e
  have hs := s23cV_sum (5720 * q) (List.range 5720) (by rw [← e] at hN; exact hN)
  refine ⟨fun d hd => hs.1 d (List.mem_range.2 hd), s23dig ?_ (s23cQ_le _ _) (s23cQ_le _ _)⟩
  rw [← e]
  exact hs.2

theorem filter_len_add (p : Nat → Bool) (a b : Nat) :
    ((List.range (a + b)).filter p).length =
      ((List.range a).filter p).length + ((List.range b).filter fun d => p (a + d)).length := by
  rw [List.range_add, List.filter_append, List.length_append, List.filter_map, List.length_map]
  rfl

theorem cnt_full (p : Nat → Bool) : ((List.range 22880).filter p).length =
    s23cQ p 0 + s23cQ p 5720 + s23cQ p 11440 + s23cQ p 17160 := by
  have e : (22880 : Nat) = 0 + 5720 + 5720 + 5720 + 5720 := by norm_num
  rw [e, filter_len_add, filter_len_add, filter_len_add, filter_len_add]
  simp only [List.range_zero, List.filter_nil, List.length_nil, Nat.zero_add, Nat.reduceAdd, s23cQ]

theorem cqF0 : (∀ d < 5720, cenP (5720 * 0 + d) = true) ∧
    s23cQ (fun i => Nat.beq (cf 3 i) i) 0 = 14 ∧ s23cQ (fun i => Nat.beq (cf 4 i) i) 0 = 14 ∧
    s23cQ (fun i => bAnd(notB (Nat.beq i 0), Nat.beq (zx i) i)) 0 = 73 :=
  s23cS_spec cq0 (by norm_num)

theorem cqF1 : (∀ d < 5720, cenP (5720 * 1 + d) = true) ∧
    s23cQ (fun i => Nat.beq (cf 3 i) i) 5720 = 7 ∧ s23cQ (fun i => Nat.beq (cf 4 i) i) 5720 = 7 ∧
    s23cQ (fun i => bAnd(notB (Nat.beq i 0), Nat.beq (zx i) i)) 5720 = 72 :=
  s23cS_spec cq1 (by norm_num)

theorem cqF2 : (∀ d < 5720, cenP (5720 * 2 + d) = true) ∧
    s23cQ (fun i => Nat.beq (cf 3 i) i) 11440 = 8 ∧ s23cQ (fun i => Nat.beq (cf 4 i) i) 11440 = 8 ∧
    s23cQ (fun i => bAnd(notB (Nat.beq i 0), Nat.beq (zx i) i)) 11440 = 61 :=
  s23cS_spec cq2 (by norm_num)

theorem cqF3 : (∀ d < 5720, cenP (5720 * 3 + d) = true) ∧
    s23cQ (fun i => Nat.beq (cf 3 i) i) 17160 = 9 ∧ s23cQ (fun i => Nat.beq (cf 4 i) i) 17160 = 9 ∧
    s23cQ (fun i => bAnd(notB (Nat.beq i 0), Nat.beq (zx i) i)) 17160 = 74 :=
  s23cS_spec cq3 (by norm_num)

theorem cen_all : ∀ x < 22880, cenP x = true := by
  intro x hx
  rcases Nat.lt_or_ge x 5720 with a | a
  · have := cqF0.1 x a
    rwa [Nat.mul_zero, Nat.zero_add] at this
  rcases Nat.lt_or_ge x 11440 with b | b
  · have := cqF1.1 (x - 5720) (by omega)
    rwa [Nat.mul_one, Nat.add_sub_of_le a] at this
  rcases Nat.lt_or_ge x 17160 with c | c
  · have := cqF2.1 (x - 11440) (by omega)
    simp only [Nat.reduceMul] at this
    rwa [Nat.add_sub_of_le b] at this
  · have := cqF3.1 (x - 17160) (by omega)
    simp only [Nat.reduceMul] at this
    rwa [Nat.add_sub_of_le c] at this

theorem cen_counts : ((List.range 22880).filter fun i => Nat.beq (cf 3 i) i).length = 38 ∧
    ((List.range 22880).filter fun i => Nat.beq (cf 4 i) i).length = 38 ∧
    ((List.range 22880).filter fun i => bAnd(notB (Nat.beq i 0), Nat.beq (zx i) i)).length =
      280 := by
  simp only [cnt_full, cqF0.2.1, cqF1.2.1, cqF2.2.1, cqF3.2.1, cqF0.2.2.1, cqF1.2.2.1,
    cqF2.2.2.1, cqF3.2.2.1, cqF0.2.2.2, cqF1.2.2.2, cqF2.2.2.2, cqF3.2.2.2, Nat.reduceAdd,
    and_self]

theorem sbase_facts {p : Nat} (hp : p < 6) : zx p = itr (wpS zWord) 7 p ∧ gx p = wpC fusW p ∧
    cf 3 p = tx 1 p := by
  have h := allN_spec sbase p hp
  simp only [bAnd_eq, Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2.1, Nat.eq_of_beq_eq_true h.2.2⟩

theorem cenP_eqs {y : Nat} (hy : y < 22880) : cf 0 y = y ∧ zx y = cf 5 (cf 8 y) ∧
    cf 2 y = cf 1 (zx y) ∧ cf 4 y = cf 3 (zx y) ∧ cf 5 y = cf 4 (zx y) ∧ cf 6 y = cf 3 (cf 3 y) ∧
    cf 7 y = cf 6 (zx y) ∧ cf 8 y = wpC suzC8W (cf 5 (wpC suzC8W y)) ∧ cf 5 y = wpC suzC5W y := by
  have h := cen_all y hy
  unfold cenP at h
  simp only [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h0, h1, h2, h4, h5, h6, h7, h8, h3⟩ := h
  exact ⟨Nat.eq_of_beq_eq_true h0, Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2,
    Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5, Nat.eq_of_beq_eq_true h6,
    Nat.eq_of_beq_eq_true h7, Nat.eq_of_beq_eq_true h8, Nat.eq_of_beq_eq_true h3⟩

theorem c58_rep : ∃ k ∈ suzP, ∃ w ∈ suzP, (∀ y : Fin 22880, cf 5 y = k y) ∧
    ∀ y : Fin 22880, cf 8 y = (w * (k * w)) y := by
  obtain ⟨⟨k, hk, hkr⟩, -⟩ := wpC_repP (w := suzC5W) (by decide)
  obtain ⟨⟨w, hw, hwr⟩, -⟩ := wpC_repP (w := suzC8W) (by decide)
  have h5 : ∀ y : Fin 22880, cf 5 y = k y := fun y => (cenP_eqs y.2).2.2.2.2.2.2.2.2.trans (hkr y)
  refine ⟨k, hk, w, hw, h5, fun y => ?_⟩
  have e := repF_comp hwr (repF_comp h5 hwr) y
  simp only [o2_eq] at e
  rw [(cenP_eqs y.2).2.2.2.2.2.2.2.1]
  exact e

theorem zx_rep : (∃ g ∈ suzP, ∀ y : Fin 22880, zx y = g y) ∧ ∀ x < 22880, zx x < 22880 := by
  obtain ⟨k, hk, w, hw, h5, h8⟩ := c58_rep
  have hz : ∀ y : Fin 22880, zx y = (k * (w * (k * w))) y := fun y => by
    have e := repF_comp h5 h8 y
    rw [o2_eq] at e
    rw [(cenP_eqs y.2).2.1]
    exact e
  exact ⟨⟨_, suzP.mul_mem hk (suzP.mul_mem hw (suzP.mul_mem hk hw)), hz⟩,
    fun x hx => lt_of_eq_of_lt (hz ⟨x, hx⟩) (Fin.isLt _)⟩

theorem zArr_repSuz : RepSuz zArr := by
  have hw : RepSuz (wordA 22880 certStrongArrs certStrongInvs zWord) := by
    refine ⟨_, ?_, rep_wordA (gs := suzS) (fun h hh => rep_certStrong hh)
      (fun h hh => rep_certStrongInv hh) zWord (by decide)⟩
    exact (Subgroup.closure_le suzP).2 (Set.range_subset_iff.2 fun h : Fin 10 => suzS_memP h.2)
      (Quiver.SchreierGraph.evalWord_mem_closure _ _)
  obtain ⟨g, hg, hr⟩ := hw
  have hp : ∀ k, Rep 22880 (powArr 22880 (wordA 22880 certStrongArrs certStrongInvs zWord) k)
      (g ^ k) := by
    intro k
    induction k with
    | zero =>
      rw [powArr, pow_zero]
      exact rep_idA
    | succ k ih =>
      rw [powArr, pow_succ']
      exact rep_compA hr ih
  exact ⟨g ^ 7, suzP.pow_mem hg 7, hp 7⟩

theorem z_get {x : Nat} (hx : x < 22880) : zArr[x]! = zx x ∧ zx x < 22880 := by
  have hw : ∀ y < 22880, (wordA 22880 certStrongArrs certStrongInvs zWord)[y]! = wpS zWord y ∧
      wpS zWord y < 22880 :=
    rwordPt_eq (kS := 10) (O := ocs) (F := SuzCertT.F) (G := SuzCertI)
      (fun j hj => strong_rows hj) (fun j hj => strongInv_get hj)
      (fun j hj => cert_rngF (k := j + 2) (by omega)) (fun j hj => cert_rngG (k := j + 2) (by omega))
      zWord (by decide)
  have hp : ∀ k, ∀ y < 22880, (powArr 22880 (wordA 22880 certStrongArrs certStrongInvs zWord) k)[y]! =
      itr (fun v => (wordA 22880 certStrongArrs certStrongInvs zWord)[v]!) k y := by
    intro k
    induction k with
    | zero => intro y hy; rw [powArr, idA_get hy]; rfl
    | succ k ih =>
      intro y hy
      rw [powArr, compA_get hy, ih y hy, itr_succ]
  obtain ⟨g, hg, hr⟩ := zArr_repSuz
  obtain ⟨⟨h, hh, hzr⟩, hzl⟩ := zx_rep
  refine ⟨suz_eqF (f := fun y => zArr[y]!) (fun y => hr y) hzr hg hh (fun p hp6 => ?_) x hx, hzl x hx⟩
  have hp' : p < 22880 := by omega
  have e7 : zPower = 7 := rfl
  change zArr[p]! = zx p
  unfold zArr
  rw [(sbase_facts hp6).1, e7, hp 7 p hp']
  exact (itr_congr (fun y hy => (hw y hy).1) (fun y hy => (hw y hy).1 ▸ (hw y hy).2) 7 p hp').1

theorem zP_facts {x : Nat} (hx : x < 22880) : itr zx 3 x = x ∧
    ∀ j < 8, o2 (cgk (Nat.add j 4)) (o2 zx (ci (Nat.add j 4))) x =
      nIf(Nat.beq (nget S2308W (Nat.add 82 j)) 0, zx x, o2 zx zx x) := by
  obtain ⟨g, hg, hr⟩ := zArr_repSuz
  have hz : ∀ y : Fin 22880, zx y = g y := fun y => by
    rw [← (z_get y.2).1]
    exact hr y
  have hb : ∀ p < 6, Nat.beq (itr zx 3 p) p = true ∧
      allN 8 (fun j => Nat.beq (o2 (cgk (Nat.add j 4)) (o2 zx (ci (Nat.add j 4))) p)
        (nIf(Nat.beq (nget S2308W (Nat.add 82 j)) 0, zx p, o2 zx zx p))) = true := fun p hp => by
    have h := allN_spec zbase p hp
    unfold zBP at h
    simp only [bAnd_eq, Bool.and_eq_true] at h
    exact h
  refine ⟨?_, fun j hj => ?_⟩
  · have h3 : ∀ y : Fin 22880, itr zx 3 y = (g * (g * g)) y := fun y => by
      have := repF_comp hz (repF_comp hz hz) y
      rw [o2_eq, o2_eq] at this
      rw [itr_succ, itr_succ, itr_succ, itr_zero]
      exact this
    exact suz_eqF (f' := fun y => y) (h := 1) h3 (fun y => rfl)
      (suzP.mul_mem hg (suzP.mul_mem hg hg)) suzP.one_mem
      (fun p hp => Nat.eq_of_beq_eq_true (hb p hp).1) x hx
  · have hc : ∀ y : Fin 22880, cgk (Nat.add j 4) y = suzS (j + 2) y := fun y => by
      rw [← cert_get (k := j + 4) (by omega) y.2]
      exact rep_suzS (j := j + 2) (by omega) y
    have hci : ∀ y : Fin 22880, ci (Nat.add j 4) y = (suzS (j + 2))⁻¹ y := fun y => by
      have := rep_certStrongInv (j := j + 2) (by omega) y
      rw [strongInv_get (j := j + 2) (by omega), rowArr_get y.2] at this
      exact this
    have hL := repF_comp hc (repF_comp hz hci)
    have hm : suzS (j + 2) * (g * (suzS (j + 2))⁻¹) ∈ suzP :=
      suzP.mul_mem (suzS_memP (by omega)) (suzP.mul_mem hg (suzP.inv_mem (suzS_memP (by omega))))
    have hbj : ∀ p < 6, o2 (cgk (Nat.add j 4)) (o2 zx (ci (Nat.add j 4))) p =
        nIf(Nat.beq (nget S2308W (Nat.add 82 j)) 0, zx p, o2 zx zx p) :=
      fun p hp => Nat.eq_of_beq_eq_true (allN_spec (hb p hp).2 j hj)
    simp only [nIf_eq] at hbj ⊢
    cases hcb : Nat.beq (nget S2308W (Nat.add 82 j)) 0
    · simp only [hcb, Bool.false_eq_true, ite_false] at hbj ⊢
      exact suz_eqF hL (repF_comp hz hz) hm (suzP.mul_mem hg hg) hbj x hx
    · simp only [hcb, ite_true] at hbj ⊢
      exact suz_eqF hL hz hm hg hbj x hx

theorem compA3 {t : Array Nat} {f : Nat → Nat} (ht : ∀ y < 22880, t[y]! = f y)
    (hf : ∀ y < 22880, f y < 22880) {x : Nat} (hx : x < 22880) :
    (compA 22880 t (compA 22880 t t))[x]! = itr f 3 x := by
  rw [compA_get hx, compA_get hx, ht x hx, ht _ (hf x hx), ht _ (hf _ (hf x hx)), itr_succ,
    itr_succ, itr_succ, itr_zero]

theorem ld_eq {i : Nat} (hi : i < 280) (h : i < localDomain.length) : localDomain[i] = ld i := by
  simp only [localDomain_eq, Array.getElem_toList]
  rw [← getElem!_pos _ i (by simpa [unpack] using hi), CFSG.KS.Raw.Orb.unpack_get hi]
  rfl

theorem dom_len : localDomain.length = 280 := domain.1

theorem pw_of_strictIncr : ∀ l : List Nat, strictIncr l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    simp only [strictIncr, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := pw_of_strictIncr (b :: l) h.2
    refine List.Pairwise.cons (fun x hx => ?_) ih
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact lt_trans h.1 (List.rel_of_pairwise_cons ih hx)

theorem dom_pw : localDomain.Pairwise (· < ·) := pw_of_strictIncr _ domain.2.1

theorem dom_nodup : localDomain.Nodup := dom_pw.imp (fun h => Nat.ne_of_lt h)

theorem rst_facts : (∀ j < 14, ∀ i < 280, fy j (ld i) = ld (pg 9 (mask 9) (SuzLocR (Nat.add 8 j)) i)) ∧
    (∀ a < 5, ∀ i < 280, tx a (ld i) = ld (pg 9 (mask 9) (S2308CE.G a) i)) ∧
    (∀ i < 280, cf 3 (ld i) = ld (pg 9 (mask 9) (SuzCenC 3) i)) ∧
    (∀ i < 280, ld i ≠ 0 ∧ zx (ld i) = ld i) ∧
    (∀ k < 8, SuzLocR k = SuzLocR (Nat.add 8 k)) ∧
    (∀ j < 14, S2308LC.S j = SuzLocR (Nat.add 8 j)) ∧
    (∀ t < 4, nget [0, 1, 2, 3] t = pg 9 (mask 9) S2308LC.BP t) := by
  have h := rst
  simp only [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨fun j hj i hi => Nat.eq_of_beq_eq_true (allN_spec (allN_spec h1 j hj) i hi),
    fun a ha i hi => Nat.eq_of_beq_eq_true (allN_spec (allN_spec h2 a ha) i hi),
    fun i hi => Nat.eq_of_beq_eq_true (allN_spec h3 i hi), fun i hi => ?_,
    fun k hk => Nat.eq_of_beq_eq_true (allN_spec h5 k hk),
    fun j hj => Nat.eq_of_beq_eq_true (allN_spec h6 j hj),
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec h7 t ht)⟩
  have e := allN_spec h4 i hi
  simp only [notB_eq, Bool.and_eq_true, Bool.not_eq_true'] at e
  refine ⟨fun h0 => ?_, Nat.eq_of_beq_eq_true e.2⟩
  rw [h0] at e
  exact absurd e.1 (by decide)

theorem ld_lt {i : Nat} (hi : i < 280) : ld i < 22880 := by
  have := domain.2.2 (localDomain[i]'(by rw [dom_len]; exact hi)) (List.getElem_mem _)
  rwa [ld_eq hi] at this

theorem mem_dom {x : Nat} : x ∈ localDomain ↔ ∃ i < 280, ld i = x := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by rw [dom_len] at hi; exact hi, (ld_eq (by rw [dom_len] at hi; exact hi) hi).symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by rw [dom_len]; exact hi, ld_eq hi _⟩

theorem delta_eq : deltaOf zArr = localDomain := by
  have hpw : (deltaOf zArr).Pairwise (· < ·) := List.pairwise_lt_range.filter _
  have hmem : ∀ x, x ∈ deltaOf zArr ↔ x < 22880 ∧ x ≠ 0 ∧ zx x = x := by
    intro x
    unfold deltaOf
    rw [List.mem_filter, List.mem_range]
    constructor
    · rintro ⟨hx, h⟩
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
      exact ⟨hx, h.1, by rw [← (z_get hx).1]; exact h.2⟩
    · rintro ⟨hx, h0, hz⟩
      refine ⟨hx, ?_⟩
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
      exact ⟨h0, by rw [(z_get hx).1]; exact hz⟩
  have hsub : localDomain ⊆ deltaOf zArr := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_dom.1 hx
    exact (hmem _).2 ⟨ld_lt hi, (rst_facts.2.2.2.1 i hi).1, (rst_facts.2.2.2.1 i hi).2⟩
  have hlen : (deltaOf zArr).length = 280 := by
    have hcnt := cen_counts.2.2
    have hfc : (List.range 22880).filter (fun i => i != 0 && zArr[i]! == i) =
        (List.range 22880).filter (fun i => bAnd(notB (Nat.beq i 0), Nat.beq (zx i) i)) := by
      apply List.filter_congr
      intro x hx
      rw [List.mem_range] at hx
      rw [bAnd_eq, notB_eq, (z_get hx).1]
      simp only [bne, beq_nat]
    unfold deltaOf
    rw [hfc]
    exact hcnt
  have hperm := (List.subperm_of_subset dom_nodup hsub).perm_of_length_le
    (by rw [hlen, dom_len])
  exact (List.Subset.antisymm_of_pairwise dom_pw hpw hsub (fun x hx => hperm.symm.subset hx)).symm

theorem conj_case {j : Nat} (hj : j < 8) :
    (eqA 22880 (compA 22880 certStrongArrs[j + 2]! (compA 22880 zArr certStrongInvs[j + 2]!)) zArr ||
      eqA 22880 (compA 22880 certStrongArrs[j + 2]! (compA 22880 zArr certStrongInvs[j + 2]!))
        (compA 22880 zArr zArr)) = true := by
  have hc : ∀ x < 22880, (compA 22880 certStrongArrs[j + 2]!
      (compA 22880 zArr certStrongInvs[j + 2]!))[x]! =
        o2 (cgk (Nat.add j 4)) (o2 zx (ci (Nat.add j 4))) x := by
    intro x hx
    have hy : ci (Nat.add j 4) x < 22880 := cert_rngG (k := j + 4) (by omega) x hx
    rw [compA_get hx, compA_get hx, strongInv_get (j := j + 2) (by omega), rowArr_get hx,
      strong_rows (j := j + 2) (by omega),
      o2_eq, o2_eq]
    have e1 : rg 15 (mask 15) SuzCertI (ocs (j + 2)) x = ci (Nat.add j 4) x := rfl
    rw [e1, (z_get hy).1, rowArr_get (z_get hy).2]
    rfl
  by_cases hf : nget S2308W (Nat.add 82 j) = 0
  · have : eqA 22880 (compA 22880 certStrongArrs[j + 2]! (compA 22880 zArr certStrongInvs[j + 2]!))
        zArr = true := eqA_true fun x hx => by
      rw [hc x hx, (zP_facts hx).2 j hj, hf, (z_get hx).1]
      rfl
    rw [this, Bool.true_or]
  · have : eqA 22880 (compA 22880 certStrongArrs[j + 2]! (compA 22880 zArr certStrongInvs[j + 2]!))
        (compA 22880 zArr zArr) = true := eqA_true fun x hx => by
      have hb : Nat.beq (nget S2308W (Nat.add 82 j)) 0 = false := by
        cases e : Nat.beq (nget S2308W (Nat.add 82 j)) 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true e) hf
      rw [hc x hx, (zP_facts hx).2 j hj, hb, compA_get hx, (z_get hx).1, (z_get (z_get hx).2).1]
      exact o2_eq _ _ _
    rw [this, Bool.or_true]

theorem zpt_facts : zx 0 = 0 ∧ zx (nget S2308W 0) ≠ nget S2308W 0 ∧ nget S2308W 0 < 22880 := by
  have hc := zpts
  simp only [bAnd_eq, notB_eq, Bool.and_eq_true, Bool.not_eq_true'] at hc
  refine ⟨Nat.eq_of_beq_eq_true hc.1, fun h => ?_, Eq.mp Nat.blt_eq hc.2.2⟩
  rw [h, Nat.beq_refl] at hc
  exact absurd hc.2.1 (by decide)

theorem zChecks_ok : zChecks = true := by
  unfold zChecks
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨eqA_true fun x hx => ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [compA3 (fun y hy => (z_get hy).1) (fun y hy => (z_get hy).2) hx, (zP_facts hx).1,
      idA_get hx]
  · rw [Bool.not_eq_true']
    obtain ⟨-, h1, h2⟩ := zpt_facts
    exact eqA_false h2 (by rw [(z_get h2).1, idA_get h2]; exact h1)
  · rw [(z_get (x := 0) (by norm_num)).1, zpt_facts.1]
    rfl
  · rw [List.all_eq_true]
    intro j hj
    simp only [certStabIdx, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [conj_case (j := 0) (by norm_num), conj_case (j := 1) (by norm_num),
      conj_case (j := 2) (by norm_num), conj_case (j := 3) (by norm_num),
      conj_case (j := 4) (by norm_num), conj_case (j := 5) (by norm_num),
      conj_case (j := 6) (by norm_num), conj_case (j := 7) (by norm_num)]
  · rw [delta_eq]
    exact beq_self_eq_true _

theorem restrict_eq {t : Array Nat} {P : Nat} (h : ∀ i < 280, t[ld i]! = ld (pg 9 (mask 9) P i))
    (hr : ∀ i < 280, pg 9 (mask 9) P i < 280) : restrictArr localDomain t = unpack 280 9 P := by
  refine arr_eq (n := 280) (by simp [restrictArr, dom_len]) (by simp [unpack]) fun i hi => ?_
  rw [CFSG.KS.Raw.Orb.unpack_get hi, getElem!_pos _ i (by simp [restrictArr, dom_len]; exact hi)]
  simp only [restrictArr, List.getElem_toArray, List.getElem_map]
  rw [ld_eq hi, h i hi, ← ld_eq (hr i hi) (by rw [dom_len]; exact hr i hi),
    dom_nodup.idxOf_getElem]

theorem unpack_rng {P Q : Nat} (h : invEqK 280 9 (mask 9) (280 * 9) P Q = true) :
    ∀ i < 280, pg 9 (mask 9) P i < 280 := by
  intro i hi
  have := (isInvA_spec (invEqK_sound h).2 hi).1
  rwa [CFSG.KS.Raw.Orb.unpack_get hi] at this

theorem canon_rng {P : Nat} (h : canonK 280 9 (mask 9) (280 * 9) P = true) :
    ∀ i < 280, pg 9 (mask 9) P i < 280 := fun i hi =>
  Eq.mp Nat.blt_eq (allN_spec (range_of_canonK h) i hi)

theorem loc_get {k : Nat} (hk : k < 22) : localRun k = unpack 280 9 (SuzLocR k) := localRun_eq hk

theorem restrict_F {j : Nat} (hj : j < 14) :
    restrictArr localDomain fullExtArrs[j]! = unpack 280 9 (SuzLocR (Nat.add 8 j)) :=
  restrict_eq (fun i hi => by rw [full_pt hj (ld_lt hi)]; exact rst_facts.1 j hj i hi)
    (unpack_rng (allN_spec run_perms (Nat.add 8 j) (by simp only [Nat.add_eq]; omega)))

theorem binds : Binds 280 9 S2308LC.S 14 4 S2308LC.BP localStrongArrs localBaseNat.toArray := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [localStrongArrs], fun j hj => ?_, by
    simp [localBaseNat], fun t ht => ?_⟩
  · rw [getElem!_pos _ j (by simp [localStrongArrs]; exact hj)]
    simp only [localStrongArrs, Array.getElem_ofFn]
    rw [loc_get (k := 8 + j) (by omega), rst_facts.2.2.2.2.2.1 j hj]
    rfl
  · rw [← rst_facts.2.2.2.2.2.2 t ht]
    interval_cases t <;> rfl

theorem gen_eq : localStrongArrs.extract 0 8 = localGenArrs := by
  apply Array.ext
  · simp [localStrongArrs, localGenArrs]
  · intro i h1 h2
    have hi : i < 8 := by simpa [localGenArrs] using h2
    simp only [Array.getElem_extract, localStrongArrs, localGenArrs, Array.getElem_ofFn, Nat.zero_add]
    have e := rst_facts.2.2.2.2.1 i hi
    simp only [Nat.add_eq] at e
    rw [loc_get (k := 8 + i) (by omega), loc_get (k := i) (by omega), ← e]

theorem orb_eq : rawOrbitSizes 280 localStrongArrs localBaseNat.toArray = [280, 36, 216, 3] := by
  rw [rawOrbitSizesK_sound binds lperm S2308LC.hl]
  decide

theorem chain_ok :
    rawChainOK 280 localGenArrs localStrongArrs localBaseNat.toArray localDerivs 4 = true := by
  have h := rawChainK_sound (NS := 1) (CH := 280) (chunks := 4) binds S2308LC.head S2308LC.hl
    (by norm_num) S2308LC.hs
  have hw : CFSG.Sporadic.Schreier.Co3.Native.wordsArr 8 14 S2308M.dM = localDerivs := by decide
  rwa [gen_eq, hw] at h

theorem localChecks_ok : localChecks fullExtArrs = true := by
  unfold localChecks
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨full_size, dom_len⟩, ?_⟩, ?_⟩, chain_ok⟩, by rw [orb_eq]; rfl⟩, by rw [orb_eq]; rfl⟩
  · rw [alt_iff]
    intro k hk
    rw [beq_iff_eq]
    have e : certStrongArrs[localStrongIdx.getD k 0]! = fullExtArrs[k]! := by
      rw [full_get hk]
      interval_cases k <;> simp [localStrongIdx, certStrongArrs]
    rw [e, restrict_F (j := k) (by omega),
      getElem!_pos localGenArrs k (by simp [localGenArrs]; exact hk)]
    simp only [localGenArrs, Array.getElem_ofFn]
    rw [loc_get (k := k) (by omega), ← rst_facts.2.2.2.2.1 k hk]
  · rw [alt_iff]
    intro j hj
    rw [Bool.and_eq_true, beq_iff_eq, restrict_F hj]
    obtain ⟨g, -, hr⟩ := full_repP hj
    refine ⟨CFSG.KS.Raw.isInvA_of_rep hr (CFSG.KS.Raw.rep_invCand hr), ?_⟩
    rw [getElem!_pos localStrongArrs j (by simp [localStrongArrs]; exact hj)]
    simp only [localStrongArrs, Array.getElem_ofFn]
    rw [loc_get (k := 8 + j) (by omega)]
    rfl

theorem pen_facts : szOK 280 9 = true ∧ (∀ a < 5, canonK 280 9 (mask 9) (280 * 9) (S2308CE.G a) = true) ∧
    S2308CE.k = 5 ∧ S2308CE.cnt = 729 ∧ canonK 280 9 (mask 9) (280 * 9) (SuzCenC 3) = true ∧
    SuzCenC 3 ≠ pidn 280 9 ∧ penumHdK (pidn 280 9) S2308CE.cnt 729 S2308CE.T S2308CE.PL = true := by
  have h := pen
  simp only [bAnd_eq, notB_eq, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1, fun a ha => allN_spec h2 a ha, Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4, h5,
    fun e => ?_, h7⟩
  rw [e, Nat.beq_refl] at h6
  exact absurd h6 (by decide)

theorem id_canon : canonK 280 9 (mask 9) (280 * 9) (pidn 280 9) = true := by
  have h := nw
  simp only [bAnd_eq, Bool.and_eq_true] at h
  exact h.1

theorem s23Pt_sound {n w k cnt : Nat} {G GI T PL POS SRT SRI : Nat → Nat}
    (hG : ∀ j < k, canonK n w (mask w) (n * w) (G j) = true)
    (h0 : canonK n w (mask w) (n * w) (T 0) = true)
    (h : ∀ i < cnt, s23Pt n w (mask w) false G GI k cnt T PL POS SRT SRI i = true) :
    ∀ i < cnt, penumPtK n w (mask w) (n * w) false G GI k cnt T PL POS SRT SRI i = true := by
  have hd : ∀ i < cnt, (i ≠ 0 → parOf PL i < i ∧ labOf PL i < k ∧
      r32 POS (Nat.add (Nat.mul (parOf PL i) k) (labOf PL i)) = i) ∧
      ∀ j < k, T (r32 POS (Nat.add (Nat.mul i k) j)) = stepK n w (mask w) false G GI j (T i) := by
    intro i hi
    have hq := h i hi
    unfold s23Pt at hq
    simp only [CFSG.KS.Raw.Orb.strictB_eq, bAnd_eq, Bool.and_eq_true,
      CFSG.KS.Raw.Orb.allN_iff] at hq
    obtain ⟨hA, hB, -⟩ := hq
    refine ⟨fun hi0 => ?_, fun j hj => Nat.eq_of_beq_eq_true (hB j hj).2.1⟩
    have hb : Nat.beq i (nat_lit 0) = false := by
      cases e : Nat.beq i (nat_lit 0)
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) hi0
    rw [hb] at hA
    simp only [Bool.and_eq_true] at hA
    exact ⟨Nat.le_of_ble_eq_true hA.1, Nat.le_of_ble_eq_true hA.2.1,
      Nat.eq_of_beq_eq_true hA.2.2.1⟩
  have hpar : ∀ i < cnt, i ≠ 0 →
      T i = stepK n w (mask w) false G GI (labOf PL i) (T (parOf PL i)) := fun i hi hi0 => by
    obtain ⟨hp, hl, he⟩ := (hd i hi).1 hi0
    have e := (hd (parOf PL i) (by omega)).2 _ hl
    rwa [he] at e
  have hc : ∀ i, i < cnt → canonK n w (mask w) (n * w) (T i) = true := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · exact h0
      obtain ⟨hp, hl, -⟩ := (hd i hi).1 (by omega)
      rw [hpar i hi (by omega)]
      exact CFSG.KC.BfsPin.canonK_pcomp (hG _ hl) (ih _ hp (by omega))
  intro i hi
  have hq := h i hi
  unfold s23Pt at hq
  unfold penumPtK
  simp only [CFSG.KS.Raw.Orb.strictB_eq, bAnd_eq, Bool.and_eq_true] at hq ⊢
  obtain ⟨hA, hB, hC⟩ := hq
  refine ⟨hc i hi, ?_, hB, hC⟩
  cases hb : Nat.beq i (nat_lit 0)
  swap
  · rfl
  have hi0 : i ≠ 0 := fun e => absurd hb (by rw [e]; decide)
  rw [hb] at hA
  simp only [Bool.and_eq_true] at hA ⊢
  refine ⟨hA.1, hA.2.1, ?_, hA.2.2.2⟩
  rw [← hpar i hi hi0]
  exact Nat.beq_refl _

theorem s23Sl_spec {lo len : Nat} (h : s23Sl lo len = true) {i : Nat} (h1 : lo ≤ i)
    (h2 : i < lo + len) (hi : i < S2308CE.cnt) : s23Pt 280 9 (mask 9) false S2308CE.G S2308CE.GI 5
      S2308CE.cnt S2308CE.T S2308CE.PL S2308CE.POS S2308CE.SRT S2308CE.SRI i = true := by
  unfold s23Sl at h
  have h' := CFSG.KS.Raw.Orb.allN_iff.1 h (i - lo) (by omega)
  rw [CFSG.KS.Raw.Orb.strictB_eq] at h'
  have e : Nat.add lo (i - lo) = i := by
    change lo + (i - lo) = i
    omega
  rw [e, Nat.blt_eq.mpr hi] at h'
  exact h'

theorem s23hd {root cnt cap : Nat} {T PL : Nat → Nat} (h : penumHdK root cnt cap T PL = true) :
    T 0 = root := by
  unfold penumHdK at h
  simp only [bAnd_eq, Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true h.2.2.1

theorem pts_all {i : Nat} (hi : i < S2308CE.cnt) : penumPtK 280 9 (mask 9) (280 * 9) false
    S2308CE.G S2308CE.GI 5 S2308CE.cnt S2308CE.T S2308CE.PL S2308CE.POS S2308CE.SRT S2308CE.SRI i =
      true := by
  have h0 : canonK 280 9 (mask 9) (280 * 9) (S2308CE.T 0) = true := by
    rw [s23hd pen_facts.2.2.2.2.2.2]
    exact id_canon
  refine s23Pt_sound (fun a ha => pen_facts.2.1 a ha) h0 (fun i hi => ?_) i hi
  rcases Nat.lt_or_ge i 365 with h | h
  · exact s23Sl_spec pts0 (by omega) (by omega) hi
  · exact s23Sl_spec pts1 h (by have := pen_facts.2.2.2.1; omega) hi

theorem C_get {a : Nat} (ha : a < 5) :
    (tCompOf (tFullOf fullExtArrs))[a]! = unpack 280 9 (S2308CE.G a) := by
  rw [tCompOf, map_get (by rw [T_size]; exact ha)]
  exact restrict_eq (fun i hi => by rw [T1_get ha (ld_lt hi)]; exact rst_facts.2.1 a ha i hi)
    (canon_rng (pen_facts.2.1 a ha))

theorem gensC : GensOK 280 9 5 S2308CE.G (tCompOf (tFullOf fullExtArrs)) :=
  ⟨by simp [tCompOf, T_size], fun a ha => ⟨C_get ha, pen_facts.2.1 a ha⟩⟩

theorem enumC : compactEnum (tFullOf fullExtArrs) = penumRec 280 9 S2308CE.cnt S2308CE.T S2308CE.PL ∧
    enumOK 280 (tCompOf (tFullOf fullExtArrs))
      (penumRec 280 9 S2308CE.cnt S2308CE.T S2308CE.PL) = true :=
  penumK_left_sound (cap := 729) pen_facts.1 gensC pen_facts.2.2.2.2.2.2 (fun _ hi => pts_all hi)

theorem rec_get {i : Nat} (hi : i < S2308CE.cnt) :
    (penumRec 280 9 S2308CE.cnt S2308CE.T S2308CE.PL).tabs[i]! = unpack 280 9 (S2308CE.T i) := by
  rw [getElem!_pos _ i (by simp [penumRec, hi])]
  simp [penumRec]

theorem unpack_ne {p q : Nat} (hp : canonK 280 9 (mask 9) (280 * 9) p = true)
    (hq : canonK 280 9 (mask 9) (280 * 9) q = true) (h : p ≠ q) : unpack 280 9 p ≠ unpack 280 9 q :=
  fun e => h (CFSG.KS.MulH.unpack_injH hp hq e)

theorem beq_unpack {p q : Nat} (hp : canonK 280 9 (mask 9) (280 * 9) p = true)
    (hq : canonK 280 9 (mask 9) (280 * 9) q = true) :
    (unpack 280 9 p == unpack 280 9 q) = Nat.beq p q := by
  cases e : Nat.beq p q
  · rw [beq_eq_false_iff_ne]
    exact unpack_ne hp hq (fun h => by rw [h, Nat.beq_refl] at e; exact absurd e (by decide))
  · rw [Nat.eq_of_beq_eq_true e]
    exact beq_self_eq_true _

theorem allN_false {n : Nat} {f : Nat → Bool} (h : allN n f = false) : ∃ i < n, f i = false := by
  by_contra hc
  push Not at hc
  have := CFSG.KS.PackFld.allN_of_forall (n := n) (f := f) fun i hi => by
    cases e : f i
    · exact absurd e (hc i hi)
    · rfl
  rw [this] at h
  exact absurd h (by decide)

theorem idTab280 : idTab 280 = unpack 280 9 (pidn 280 9) := CFSG.KC.BfsPin.idA_eq pen_facts.1

theorem scan_ok : allLt (penumRec 280 9 S2308CE.cnt S2308CE.T S2308CE.PL).tabs.size (fun k =>
    !(allLt 5 fun a => comp 280 (tCompOf (tFullOf fullExtArrs))[a]!
        (penumRec 280 9 S2308CE.cnt S2308CE.T S2308CE.PL).tabs[k]! ==
      comp 280 (penumRec 280 9 S2308CE.cnt S2308CE.T S2308CE.PL).tabs[k]!
        (tCompOf (tFullOf fullExtArrs))[a]!) ||
      (penumRec 280 9 S2308CE.cnt S2308CE.T S2308CE.PL).tabs[k]! == idTab 280 ||
      (penumRec 280 9 S2308CE.cnt S2308CE.T S2308CE.PL).tabs[k]! == centerCompact 3 ||
      (penumRec 280 9 S2308CE.cnt S2308CE.T S2308CE.PL).tabs[k]! ==
        comp 280 (centerCompact 3) (centerCompact 3)) = true := by
  rw [alt_iff]
  intro k hk
  have hk' : k < S2308CE.cnt := by simpa [penumRec] using hk
  have hc := penumPt_canon (pts_all hk')
  have hcc := pen_facts.2.2.2.2.1
  have he := allN_spec esc k (by rw [← pen_facts.2.2.2.1]; exact hk')
  unfold escP at he
  rw [strictB_app'] at he
  have hcomm : (allLt 5 fun a => comp 280 (tCompOf (tFullOf fullExtArrs))[a]!
      (penumRec 280 9 S2308CE.cnt S2308CE.T S2308CE.PL).tabs[k]! ==
    comp 280 (penumRec 280 9 S2308CE.cnt S2308CE.T S2308CE.PL).tabs[k]!
      (tCompOf (tFullOf fullExtArrs))[a]!) = allN 5 (fun a => Nat.beq
        (pcomp 280 9 (mask 9) (S2308CE.G a) (S2308CE.T k))
        (pcomp 280 9 (mask 9) (S2308CE.T k) (S2308CE.G a))) := by
    have hpt : ∀ a < 5, (comp 280 (tCompOf (tFullOf fullExtArrs))[a]!
        (penumRec 280 9 S2308CE.cnt S2308CE.T S2308CE.PL).tabs[k]! ==
      comp 280 (penumRec 280 9 S2308CE.cnt S2308CE.T S2308CE.PL).tabs[k]!
        (tCompOf (tFullOf fullExtArrs))[a]!) = Nat.beq
          (pcomp 280 9 (mask 9) (S2308CE.G a) (S2308CE.T k))
          (pcomp 280 9 (mask 9) (S2308CE.T k) (S2308CE.G a)) := by
      intro a ha
      have hg := pen_facts.2.1 a ha
      rw [C_get ha, rec_get hk', comp_eqA, comp_eqA,
        CFSG.KC.BfsPin.compA_unpack hg hc, CFSG.KC.BfsPin.compA_unpack hc hg]
      exact beq_unpack (CFSG.KC.BfsPin.canonK_pcomp hg hc) (CFSG.KC.BfsPin.canonK_pcomp hc hg)
    cases e : allN 5 (fun a => Nat.beq (pcomp 280 9 (mask 9) (S2308CE.G a) (S2308CE.T k))
        (pcomp 280 9 (mask 9) (S2308CE.T k) (S2308CE.G a)))
    · obtain ⟨a, ha, hf⟩ := allN_false e
      cases e2 : allLt 5 _
      · rfl
      · have := alt_iff.1 e2 a ha
        rw [hpt a ha, hf] at this
        exact absurd this (by decide)
    · exact alt_iff.2 fun a ha => by rw [hpt a ha]; exact allN_spec e a ha
  rw [hcomm]
  revert he
  cases allN 5 (fun a => Nat.beq (pcomp 280 9 (mask 9) (S2308CE.G a) (S2308CE.T k))
      (pcomp 280 9 (mask 9) (S2308CE.T k) (S2308CE.G a)))
  · intro _
    rfl
  · intro he
    rw [rec_get hk', idTab280, centerCompact_eq (r := 3) (by norm_num), comp_eqA,
      CFSG.KC.BfsPin.compA_unpack hcc hcc, beq_unpack hc id_canon, beq_unpack hc hcc,
      beq_unpack hc (CFSG.KC.BfsPin.canonK_pcomp hcc hcc)]
    simp only [Bool.not_true, Bool.false_or]
    revert he
    cases Nat.beq (S2308CE.T k) (pidn 280 9) <;> cases Nat.beq (S2308CE.T k) (SuzCenC 3) <;> simp

theorem cf_lt {r x : Nat} (hr : r < 9) (hx : x < 22880) : cf r x < 22880 := cen_lt hr hx

theorem powArr_get' {t : Array Nat} {f : Nat → Nat} (ht : ∀ y < 22880, t[y]! = f y)
    (hf : ∀ y < 22880, f y < 22880) : ∀ k, ∀ x < 22880, (powArr 22880 t k)[x]! = itr f k x
  | 0, x, hx => by rw [powArr, idA_get hx]; rfl
  | k + 1, x, hx => by
    rw [powArr, compA_get hx, powArr_get' ht hf k x hx, itr_succ,
      ht _ (itr_congr (fun y _ => rfl) hf k x hx).2]

theorem tx_repSuz {a : Nat} (ha : a < 5) : ∃ g ∈ suzP, ∀ y : Fin 22880, tx a y = g y :=
  (tx_rep ha).1

theorem s23cB8 {p : Nat} (hp : p < 6) : cf 8 p = cf 7 (zx p) := by
  have h := allN_spec cenbase p hp
  unfold cenBP at h
  simp only [bAnd_eq, Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true h.2.2.2.2.2.2.2

theorem cenP_facts12 {x : Nat} (hx : x < 22880) :
    (∀ r < 9, cf r x = o2 (itr (cf 3) (Nat.div r 3)) (itr zx (Nat.mod r 3)) x) ∧ cf 3 x = tx 1 x := by
  have zl : ∀ y < 22880, zx y < 22880 := fun y hy => (z_get hy).2
  obtain ⟨k, hk, w, hw, h5, h8⟩ := c58_rep
  obtain ⟨g, hg, hgr⟩ := zx_rep.1
  have h3 : ∀ y : Fin 22880, cf 3 y = (k * g) y := fun y => by
    have e3 : zx (zx (zx y)) = y := by
      have h := (zP_facts y.2).1
      rwa [itr_succ zx 2, itr_succ zx 1, itr_succ zx 0, itr_zero] at h
    have z1 := zl y y.2
    have z2 := zl _ z1
    rw [← repF_comp h5 hgr y, o2_eq, (cenP_eqs z1).2.2.2.2.1, (cenP_eqs z2).2.2.2.1, e3]
  have h87 : ∀ y < 22880, cf 8 y = cf 7 (zx y) := by
    have h7 : ∀ y : Fin 22880, o2 (cf 7) zx y = ((k * g) * ((k * g) * (g * g))) y := fun y => by
      have e := repF_comp h3 (repF_comp h3 (repF_comp hgr hgr)) y
      simp only [o2_eq] at e ⊢
      have z1 := zl y y.2
      rw [(cenP_eqs z1).2.2.2.2.2.2.1, (cenP_eqs (zl _ z1)).2.2.2.2.2.1]
      exact e
    have hm : k * g ∈ suzP := suzP.mul_mem hk hg
    intro y hy
    have e := suz_eqF (f := cf 8) (f' := o2 (cf 7) zx) h8 h7
      (suzP.mul_mem hw (suzP.mul_mem hk hw))
      (suzP.mul_mem hm (suzP.mul_mem hm (suzP.mul_mem hg hg)))
      (fun p hp => by rw [o2_eq]; exact s23cB8 hp) y hy
    rwa [o2_eq] at e
  have H : ∀ y < 22880, cf 0 y = y ∧ cf 1 y = zx y ∧ cf 2 y = cf 1 (zx y) ∧
      cf 4 y = cf 3 (zx y) ∧ cf 5 y = cf 4 (zx y) ∧ cf 6 y = cf 3 (cf 3 y) ∧
      cf 7 y = cf 6 (zx y) ∧ cf 8 y = cf 7 (zx y) ∧ cf 5 y = wpC suzC5W y := fun y hy => by
    obtain ⟨h0, -, h2, h4, h5', h6, h7, -, hw5⟩ := cenP_eqs hy
    exact ⟨h0, rfl, h2, h4, h5', h6, h7, h87 y hy, hw5⟩
  have hc3 : cf 3 x = tx 1 x := by
    obtain ⟨c, hcm, hc⟩ := tx_repSuz (a := 1) (by norm_num)
    exact suz_eqF (f := cf 3) h3 hc (suzP.mul_mem hk hg) hcm (fun p hp => (sbase_facts hp).2.2) x hx
  refine ⟨fun r hr => ?_, hc3⟩
  have z1 := zl x hx
  have z2 := zl _ z1
  interval_cases r <;> rw [o2_eq]
  · rw [itr_zero, itr_zero]
    exact (H x hx).1
  · rw [itr_zero, itr_succ zx 0, itr_zero]
    exact (H x hx).2.1
  · rw [itr_zero, itr_succ zx 1, itr_succ zx 0, itr_zero, (H x hx).2.2.1, (H _ z1).2.1]
  · rw [itr_succ (cf 3) 0, itr_zero, itr_zero]
  · rw [itr_succ (cf 3) 0, itr_zero, itr_succ zx 0, itr_zero, (H x hx).2.2.2.1]
  · rw [itr_succ (cf 3) 0, itr_zero, itr_succ zx 1, itr_succ zx 0, itr_zero, (H x hx).2.2.2.2.1,
      (H _ z1).2.2.2.1]
  · rw [itr_succ (cf 3) 1, itr_succ (cf 3) 0, itr_zero, itr_zero, (H x hx).2.2.2.2.2.1]
  · rw [itr_succ (cf 3) 1, itr_succ (cf 3) 0, itr_zero, itr_succ zx 0, itr_zero,
      (H x hx).2.2.2.2.2.2.1, (H _ z1).2.2.2.2.2.1]
  · rw [itr_succ (cf 3) 1, itr_succ (cf 3) 0, itr_zero, itr_succ zx 1, itr_succ zx 0, itr_zero,
      (H x hx).2.2.2.2.2.2.2.1, (H _ z1).2.2.2.2.2.2.1, (H _ z2).2.2.2.2.2.1]

theorem repF_itr {f : Nat → Nat} {g : Equiv.Perm (Fin 22880)} (hf : ∀ x : Fin 22880, f x = g x) :
    ∀ k, ∀ x : Fin 22880, itr f k x = (g ^ k) x
  | 0, x => by
    rw [itr_zero, pow_zero]
    rfl
  | k + 1, x => by
    rw [itr_succ, repF_itr hf k x, pow_succ', Equiv.Perm.mul_apply]
    exact hf _

theorem cenP_facts {x : Nat} (hx : x < 22880) :
    (∀ r < 9, cf r x = o2 (itr (cf 3) (Nat.div r 3)) (itr zx (Nat.mod r 3)) x) ∧
    o2 (cf 1) (cf 1) x = cf 2 x ∧ o2 (cf 3) (cf 3) x = cf 6 x ∧ o2 (cf 4) (cf 4) x = cf 8 x ∧
    o2 (cf 5) (cf 5) x = cf 7 x ∧ cf 3 x = tx 1 x ∧ o2 (cf 3) zx x = o2 zx (cf 3) x ∧
    (∀ a < 5, o2 (cf 3) (tx a) x = o2 (tx a) (cf 3) x ∧ o2 zx (tx a) x = o2 (tx a) zx x) ∧
    itr (cf 3) 3 x = x := by
  obtain ⟨g, hg, hr⟩ := zArr_repSuz
  have hz : ∀ y : Fin 22880, zx y = g y := fun y => by
    rw [← (z_get y.2).1]
    exact hr y
  obtain ⟨c, hcm, hc⟩ := tx_repSuz (a := 1) (by norm_num)
  have hc' : ∀ y : Fin 22880, cf 3 y = c y := fun y => by
    rw [(cenP_facts12 y.2).2]
    exact hc y
  have hrec : ∀ r < 9, ∀ y : Fin 22880, cf r y = (c ^ (r / 3) * g ^ (r % 3)) y := fun r hr y => by
    rw [(cenP_facts12 y.2).1 r hr]
    exact repF_comp (repF_itr hc' _) (repF_itr hz _) y
  have hrm : ∀ r, c ^ (r / 3) * g ^ (r % 3) ∈ suzP := fun r =>
    suzP.mul_mem (suzP.pow_mem hcm _) (suzP.pow_mem hg _)
  have hbf : ∀ p < 6, o2 (cf 1) (cf 1) p = cf 2 p ∧ o2 (cf 3) (cf 3) p = cf 6 p ∧
      o2 (cf 4) (cf 4) p = cf 8 p ∧ o2 (cf 5) (cf 5) p = cf 7 p ∧
      o2 (cf 3) zx p = o2 zx (cf 3) p ∧
      (∀ a < 5, o2 (cf 3) (tx a) p = o2 (tx a) (cf 3) p ∧ o2 zx (tx a) p = o2 (tx a) zx p) ∧
      itr (cf 3) 3 p = p := fun p hp => by
    have h := allN_spec cenbase p hp
    unfold cenBP at h
    simp only [bAnd_eq, Bool.and_eq_true] at h
    obtain ⟨h2, h3, h4, h5, h7, h8, h9, -⟩ := h
    refine ⟨Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4,
      Nat.eq_of_beq_eq_true h5, Nat.eq_of_beq_eq_true h7, fun a ha => ?_, Nat.eq_of_beq_eq_true h9⟩
    have e := allN_spec h8 a ha
    simp only [Bool.and_eq_true] at e
    exact ⟨Nat.eq_of_beq_eq_true e.1, Nat.eq_of_beq_eq_true e.2⟩
  have sq : ∀ r r', r < 9 → r' < 9 → (∀ p < 6, o2 (cf r) (cf r) p = cf r' p) →
      o2 (cf r) (cf r) x = cf r' x := fun r r' hr hr' h =>
    suz_eqF (repF_comp (hrec r hr) (hrec r hr)) (hrec r' hr') (suzP.mul_mem (hrm r) (hrm r))
      (hrm r') h x hx
  have cm : ∀ {f f' : Nat → Nat} {u v : Equiv.Perm (Fin 22880)}, (∀ y : Fin 22880, f y = u y) →
      (∀ y : Fin 22880, f' y = v y) → u ∈ suzP → v ∈ suzP → (∀ p < 6, o2 f f' p = o2 f' f p) →
      o2 f f' x = o2 f' f x := fun hf hf' hu hv h =>
    suz_eqF (repF_comp hf hf') (repF_comp hf' hf) (suzP.mul_mem hu hv) (suzP.mul_mem hv hu) h x hx
  refine ⟨(cenP_facts12 hx).1, sq 1 2 (by norm_num) (by norm_num) fun p hp => (hbf p hp).1,
    sq 3 6 (by norm_num) (by norm_num) fun p hp => (hbf p hp).2.1,
    sq 4 8 (by norm_num) (by norm_num) fun p hp => (hbf p hp).2.2.1,
    sq 5 7 (by norm_num) (by norm_num) fun p hp => (hbf p hp).2.2.2.1, (cenP_facts12 hx).2,
    cm hc' hz hcm hg fun p hp => (hbf p hp).2.2.2.2.1, fun a ha => ?_, ?_⟩
  · obtain ⟨t, htm, ht⟩ := tx_repSuz ha
    exact ⟨cm hc' ht hcm htm fun p hp => ((hbf p hp).2.2.2.2.2.1 a ha).1,
      cm hz ht hg htm fun p hp => ((hbf p hp).2.2.2.2.2.1 a ha).2⟩
  · exact suz_eqF (f' := fun y => y) (h := 1) (repF_itr hc' 3) (fun y => rfl)
      (suzP.pow_mem hcm 3) suzP.one_mem (fun p hp => (hbf p hp).2.2.2.2.2.2) x hx

theorem comm_eqA {t u : Array Nat} {f g : Nat → Nat} (ht : ∀ y < 22880, t[y]! = f y)
    (hu : ∀ y < 22880, u[y]! = g y) (hf : ∀ y < 22880, f y < 22880) (hg : ∀ y < 22880, g y < 22880)
    (h : ∀ x < 22880, o2 f g x = o2 g f x) :
    eqA 22880 (compA 22880 t u) (compA 22880 u t) = true :=
  eqA_true fun x hx => by
    have := h x hx
    rw [o2_eq, o2_eq] at this
    rw [compA_get hx, compA_get hx, hu x hx, ht x hx, ht _ (hg x hx), hu _ (hf x hx), this]

theorem sq_eqA {r r' : Nat} (hr : r < 9) (hr' : r' < 9) (h : ∀ x < 22880, o2 (cf r) (cf r) x = cf r' x) :
    eqA 22880 (compA 22880 (centerFull r) (centerFull r)) (centerFull r') = true :=
  eqA_true fun x hx => by
    rw [compA_get hx, cen_get hr hx, cen_get hr (cf_lt hr hx), cen_get hr' hx, ← h x hx, o2_eq]

theorem sylow_ok : sylowCenterChecks (tFullOf fullExtArrs) (compactEnum (tFullOf fullExtArrs)) =
    true := by
  have hz : ∀ y < 22880, zArr[y]! = zx y := fun y hy => (z_get hy).1
  have hzl : ∀ y < 22880, zx y < 22880 := fun y hy => (z_get hy).2
  have hc : ∀ y < 22880, (centerFull 3)[y]! = cf 3 y := fun y hy => cen_get (by norm_num) hy
  have hcl : ∀ y < 22880, cf 3 y < 22880 := fun y hy => cf_lt (by norm_num) hy
  unfold sylowCenterChecks
  rw [enumC.1]
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨enumC.2, by simp [penumRec, pen_facts.2.2.2.1]⟩, scan_ok⟩, ?_⟩, ?_⟩,
    sq_eqA (by norm_num) (by norm_num) fun x hx => (cenP_facts hx).2.1⟩,
    sq_eqA (by norm_num) (by norm_num) fun x hx => (cenP_facts hx).2.2.1⟩,
    sq_eqA (by norm_num) (by norm_num) fun x hx => (cenP_facts hx).2.2.2.1⟩,
    sq_eqA (by norm_num) (by norm_num) fun x hx => (cenP_facts hx).2.2.2.2.1⟩, ?_⟩, ?_⟩, ?_⟩,
    comm_eqA hc hz hcl hzl fun x hx => (cenP_facts hx).2.2.2.2.2.2.1⟩, ?_⟩, ?_⟩
  · rw [alt_iff]
    intro r hr
    rw [Bool.and_eq_true]
    refine ⟨cen_perm hr, eqA_true fun x hx => ?_⟩
    have hy := (itr_congr (fun y _ => rfl) hzl (r % 3) x hx).2
    rw [cen_get hr hx, (cenP_facts hx).1 r hr, compA_get hx,
      powArr_get' hz hzl (r % 3) x hx, powArr_get' hc hcl (r / 3) _ hy, o2_eq]
    rfl
  · rw [alt_iff]
    intro r hr
    rw [alt_iff]
    intro r' hr'
    have h := allN_spec (allN_spec cdist r hr) r' hr'
    by_cases hlt : r < r'
    · have hb : Nat.blt r r' = true := by
        rw [Nat.blt_eq]
        exact hlt
      rw [hb] at h
      simp only [bAnd_eq, notB_eq, Bool.and_eq_true, Bool.not_eq_true'] at h
      have hp := Eq.mp Nat.blt_eq h.1
      rw [decide_eq_true hlt, Bool.not_true, Bool.false_or, Bool.not_eq_true']
      refine eqA_false hp ?_
      rw [cen_get hr hp, cen_get hr' hp]
      intro e
      rw [e, Nat.beq_refl] at h
      exact absurd h.2 (by decide)
    · rw [decide_eq_false hlt]
      rfl
  · exact eqA_true fun x hx => by rw [hc x hx, T1_get (a := 1) (by norm_num) hx]; exact (cenP_facts hx).2.2.2.2.2.1
  · rw [centerCompact_eq (r := 3) (by norm_num)]
    exact restrict_eq (fun i hi => by rw [hc _ (ld_lt hi)]; exact rst_facts.2.2.1 i hi)
      (canon_rng pen_facts.2.2.2.2.1)
  · rw [Bool.not_eq_true', centerCompact_eq (r := 3) (by norm_num), idTab280,
      beq_unpack pen_facts.2.2.2.2.1 id_canon]
    cases e : Nat.beq (SuzCenC 3) (pidn 280 9)
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) pen_facts.2.2.2.2.2.1
  · rw [alt_iff]
    intro a ha
    rw [Bool.and_eq_true]
    have ht : ∀ y < 22880, ((tFullOf fullExtArrs)[a]!)[y]! = tx a y := fun y hy => T1_get ha hy
    have htl : ∀ y < 22880, tx a y < 22880 := fun y hy => tx_lt ha hy
    exact ⟨comm_eqA hc ht hcl htl fun x hx => ((cenP_facts hx).2.2.2.2.2.2.2.1 a ha).1,
      comm_eqA hz ht hzl htl fun x hx => ((cenP_facts hx).2.2.2.2.2.2.2.1 a ha).2⟩
  · exact eqA_true fun x hx => by
      rw [powArr_get' hc hcl 3 x hx, (cenP_facts hx).2.2.2.2.2.2.2.2, idA_get hx]

theorem fusT_rep : RepSuz fusionTransArr := by
  have hL : ∀ h < 2, RepSuz (#[certArr 0, certArr 1] : Array (Array Nat))[h]! := fun h hh => by
    interval_cases h
    · rw [arr2_get0]
      exact crt_repP (by norm_num)
    · rw [arr2_get1]
      exact crt_repP (by norm_num)
  have hM : ∀ h < 2, isInvA 22880 (#[certArr 0, certArr 1] : Array (Array Nat))[h]!
      (#[invCand 22880 (certArr 0), invCand 22880 (certArr 1)] : Array (Array Nat))[h]! = true :=
    fun h hh => by
      interval_cases h
      · rw [arr2_get0, arr2_get0, cert_inv (by norm_num), certArr_eq (by norm_num)]
        exact (rpermK_sound (allN_spec cert_perms 0 (by norm_num))).2
      · rw [arr2_get1, arr2_get1, cert_inv (by norm_num), certArr_eq (by norm_num)]
        exact (rpermK_sound (allN_spec cert_perms 1 (by norm_num))).2
  unfold fusionTransArr
  exact repP_word (kS := 2) hL hM (w := fusW) (by decide)

theorem gz_facts : gx 0 = 95 ∧ ∀ p < 6, o2 gx (o2 zx gxi) p = cf 5 p ∧ gx (gxi p) = p := by
  have h := gzbase
  simp only [bAnd_eq, Bool.and_eq_true] at h
  refine ⟨Nat.eq_of_beq_eq_true h.1, fun p hp => ?_⟩
  have e := allN_spec h.2 p hp
  simp only [Bool.and_eq_true] at e
  exact ⟨Nat.eq_of_beq_eq_true e.1, Nat.eq_of_beq_eq_true e.2⟩

theorem gx_rep : ∃ g ∈ suzP, (∀ y : Fin 22880, gx y = g y) ∧ ∀ y : Fin 22880, gxi y = g⁻¹ y := by
  obtain ⟨⟨g, hg, hr⟩, -⟩ := wpC_rep' (f := gx) (w := suzGW) (by decide) fun x => rfl
  obtain ⟨⟨h, hh, hr'⟩, -⟩ := wpC_rep' (f := gxi) (w := suzInvW suzGW) (by decide) fun x => rfl
  have hid : ∀ y < 22880, o2 gx gxi y = y :=
    suz_eqF (f' := fun y => y) (h := 1) (repF_comp hr hr') (fun y => rfl)
      (suzP.mul_mem hg hh) suzP.one_mem fun p hp => by
        rw [o2_eq]
        exact (gz_facts.2 p hp).2
  refine ⟨g, hg, hr, fun y => ?_⟩
  have e : g (h y) = y := Fin.ext (by
    rw [← hr (h y), ← hr' y]
    have e' := hid y y.2
    rwa [o2_eq] at e')
  exact (hr' y).trans (congrArg Fin.val (Equiv.Perm.eq_inv_iff_eq.2 e))

theorem g_get {x : Nat} (hx : x < 22880) : fusionTransArr[x]! = gx x := by
  have hS : ∀ j < 2, (#[certArr 0, certArr 1] : Array (Array Nat))[j]! = rowArr 22880 15 SuzCertT.F (ofs j) :=
    fun j hj => by
      interval_cases j
      · rw [arr2_get0]
        exact certArr_eq (by norm_num)
      · rw [arr2_get1]
        exact certArr_eq (by norm_num)
  have hSi : ∀ j < 2, (#[invCand 22880 (certArr 0), invCand 22880 (certArr 1)] : Array (Array Nat))[j]! =
      rowArr 22880 15 SuzCertI (ofs j) := fun j hj => by
    interval_cases j
    · rw [arr2_get0]
      exact cert_inv (by norm_num)
    · rw [arr2_get1]
      exact cert_inv (by norm_num)
  have h := rwordPt_eq (kS := 2) (O := ofs) hS hSi (fun j hj => cert_rngF (by omega))
    (fun j hj => cert_rngG (by omega)) fusW (by decide)
  obtain ⟨g, hgm, hr⟩ := fusT_rep
  obtain ⟨k, hk, hgx, -⟩ := gx_rep
  refine suz_eqF (f := fun y => fusionTransArr[y]!) (fun y => hr y) hgx hgm hk (fun p hp => ?_) x hx
  have hF : fusionTransArr = wordA 22880 #[certArr 0, certArr 1]
      #[invCand 22880 (certArr 0), invCand 22880 (certArr 1)] fusW := by
    rw [fusionTransArr, fusW]
  rw [(sbase_facts hp).2.1, hF]
  exact (h p (by omega)).1

theorem fusI_get {x : Nat} (hx : x < 22880) : (invCand 22880 fusionTransArr)[x]! = gxi x := by
  obtain ⟨g, -, hr⟩ := fusT_rep
  obtain ⟨k, -, hkx, hki⟩ := gx_rep
  have e : g = k := Equiv.ext fun y => Fin.ext ((hr y).symm.trans ((g_get y.2).trans (hkx y)))
  rw [CFSG.KS.Raw.rep_invCand hr ⟨x, hx⟩, e]
  exact (hki ⟨x, hx⟩).symm

theorem gz_conj5 {x : Nat} (hx : x < 22880) : o2 gx (o2 zx gxi) x = cf 5 x := by
  obtain ⟨g, hgm, hgx, hgi⟩ := gx_rep
  obtain ⟨z, hzm, hzr⟩ := zArr_repSuz
  have hz : ∀ y : Fin 22880, zx y = z y := fun y => by
    rw [← (z_get y.2).1]
    exact hzr y
  obtain ⟨c, hcm, hc⟩ := tx_repSuz (a := 1) (by norm_num)
  have hc' : ∀ y : Fin 22880, cf 3 y = c y := fun y => by
    rw [(cenP_facts12 y.2).2]
    exact hc y
  have h5 : ∀ y : Fin 22880, cf 5 y = (c ^ (5 / 3) * z ^ (5 % 3)) y := fun y => by
    rw [(cenP_facts12 y.2).1 5 (by norm_num)]
    exact repF_comp (repF_itr hc' _) (repF_itr hz _) y
  exact suz_eqF (repF_comp hgx (repF_comp hz hgi)) h5
    (suzP.mul_mem hgm (suzP.mul_mem hzm (suzP.inv_mem hgm)))
    (suzP.mul_mem (suzP.pow_mem hcm _) (suzP.pow_mem hzm _))
    (fun p hp => (gz_facts.2 p hp).1) x hx

theorem fixed_count {r : Nat} (hr : r < 9)
    (hb : ((List.range 22880).filter fun i => Nat.beq (cf r i) i).length = 38) :
    fixedCountN 22880 (centerFull r) = 38 := by
  have hfc : (List.range 22880).filter (fun x => (centerFull r)[x]! == x) =
      (List.range 22880).filter (fun i => Nat.beq (cf r i) i) := by
    apply List.filter_congr
    intro x hx
    rw [List.mem_range] at hx
    rw [cen_get hr hx, beq_nat]
  unfold CFSG.Sporadic.SuzOddCore.fixedCountN CFSG.Sporadic.SuzOddCore.fixedList
  rw [hfc]
  exact hb

theorem pos_word {S Sinv : Array (Array Nat)} {n : Nat} :
    ∀ w : List Int, (∀ l ∈ w, 0 < l) →
      wordA n S Sinv w = (w.map fun l => l.toNat - 1).foldr (fun j acc => comp n S[j]! acc) (idTab n)
  | [], _ => rfl
  | l :: w, h => by
    have hl := h l List.mem_cons_self
    rw [wordA, pos_word w (fun l' hl' => h l' (List.mem_cons_of_mem _ hl')), List.map_cons,
      List.foldr_cons, comp_eqA]
    congr 1
    unfold letterA
    simp [hl]

theorem nw_facts : (∀ k < 8, canonK 280 9 (mask 9) (280 * 9) (SuzLocR k) = true ∧
      canonK 280 9 (mask 9) (280 * 9) (SuzLocRI k) = true) ∧
    (∀ k < 39, invEqK 280 9 (mask 9) (280 * 9) (nwK k) (nwiK k) = true) ∧
    (∀ k < 39, ∀ k' < 39, k < k' → ncK k ≠ ncK k' ∧ ncK k ≠ pcomp 280 9 (mask 9) (ncK k') (ncK k')) := by
  have h := nw
  simp only [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨-, h2, h3, h4⟩ := h
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk k' hk' hlt => ?_⟩
  · have e := allN_spec h2 k hk
    simp only [Bool.and_eq_true] at e
    exact e
  · have e := allN_spec h3 k hk
    simp only [Bool.and_eq_true] at e
    exact e.2
  · have e := allN_spec h4 k hk
    rw [strictB_app'] at e
    have e2 := allN_spec e k' hk'
    have hb : Nat.blt k k' = true := by
      rw [Nat.blt_eq]
      exact hlt
    rw [hb] at e2
    change strictB (ncK k') _ = true at e2
    rw [strictB_app'] at e2
    simp only [notB_eq, Bool.and_eq_true, Bool.not_eq_true'] at e2
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [h, Nat.beq_refl] at e2
      exact absurd e2.1 (by decide)
    · rw [h, Nat.beq_refl] at e2
      exact absurd e2.2 (by decide)

theorem nwN_lt : ∀ k < 39, ∀ j ∈ nwN k, j < 8 := by decide

theorem nw_pos : ∀ k < 39, ∀ l ∈ normWords.getD k [], 0 < l := by decide

theorem lg_get {j : Nat} (hj : j < 8) : localGenArrs[j]! = unpack 280 9 (SuzLocR j) := by
  rw [getElem!_pos localGenArrs j (by simp [localGenArrs]; exact hj)]
  simp only [localGenArrs, Array.getElem_ofFn]
  exact loc_get (by omega)

theorem nwK_canon {k : Nat} (hk : k < 39) : normWordArr k = unpack 280 9 (nwK k) ∧
    canonK 280 9 (mask 9) (280 * 9) (nwK k) = true := by
  unfold normWordArr
  rw [pos_word _ (nw_pos k hk)]
  exact wordTabK_eq idTab280 id_canon (nwN k) fun j hj =>
    ⟨lg_get (nwN_lt k hk j hj), (nw_facts.1 j (nwN_lt k hk j hj)).1⟩

theorem nwiK_canon {k : Nat} (hk : k < 39) : canonK 280 9 (mask 9) (280 * 9) (nwiK k) = true := by
  have := wordTabK_eq (gs := Array.ofFn (n := 8) fun j => unpack 280 9 (SuzLocRI j.val))
    idTab280 id_canon (nwN k).reverse fun j hj => by
      have hj8 := nwN_lt k hk j (List.mem_reverse.1 hj)
      refine ⟨?_, (nw_facts.1 j hj8).2⟩
      rw [getElem!_pos _ j (by simp; exact hj8), Array.getElem_ofFn]
  exact this.2

theorem nc_eq {k : Nat} (hk : k < 39) : normConj k = unpack 280 9 (ncK k) ∧
    canonK 280 9 (mask 9) (280 * 9) (ncK k) = true := by
  have hw := nwK_canon hk
  have hi := invEqK_sound (nw_facts.2.1 k hk)
  have hwi := nwiK_canon hk
  have hcc := pen_facts.2.2.2.2.1
  unfold normConj
  rw [hw.1, hi.1, centerCompact_eq (r := 3) (by norm_num), CFSG.KC.BfsPin.compA_unpack hcc hwi,
    CFSG.KC.BfsPin.compA_unpack hw.2 (CFSG.KC.BfsPin.canonK_pcomp hcc hwi)]
  exact ⟨rfl, CFSG.KC.BfsPin.canonK_pcomp hw.2 (CFSG.KC.BfsPin.canonK_pcomp hcc hwi)⟩

theorem eqA_unpack_false {p q : Nat} (hp : canonK 280 9 (mask 9) (280 * 9) p = true)
    (hq : canonK 280 9 (mask 9) (280 * 9) q = true) (h : p ≠ q) :
    eqA 280 (unpack 280 9 p) (unpack 280 9 q) = false := by
  cases e : eqA 280 (unpack 280 9 p) (unpack 280 9 q)
  · rfl
  · refine absurd (arr_eq (n := 280) (by simp [unpack]) (by simp [unpack]) fun x hx => ?_) (unpack_ne hp hq h)
    exact beq_iff_eq.1 (alt_iff.1 e x hx)

theorem fusion_ok : fusionNormChecks = true := by
  have hz : ∀ y < 22880, zArr[y]! = zx y := fun y hy => (z_get hy).1
  obtain ⟨g, -, hgr⟩ := fusT_rep
  unfold fusionNormChecks
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, fixed_count (r := 3) (by norm_num) cen_counts.1⟩,
    fixed_count (r := 4) (by norm_num) cen_counts.2.1⟩, ?_⟩, ?_⟩, ?_⟩
  · exact CFSG.KS.Raw.isInvA_of_rep hgr (CFSG.KS.Raw.rep_invCand hgr)
  · refine eqA_true fun x hx => ?_
    have hy : gxi x < 22880 := (wpC_repP (w := suzInvW suzGW) (by decide)).2 x hx
    rw [compA_get hx, compA_get hx, fusI_get hx, hz _ hy, g_get (z_get hy).2,
      cen_get (by norm_num) hx, ← gz_conj5 hx, o2_eq, o2_eq]
  · rw [g_get (x := 0) (by norm_num)]
    exact gz_facts.1
  · rw [alt_iff]
    intro k hk
    rw [(nwK_canon hk).1, (invEqK_sound (nw_facts.2.1 k hk)).1]
    exact (invEqK_sound (nw_facts.2.1 k hk)).2
  · rw [alt_iff]
    intro k hk
    rw [lg_get hk, (invEqK_sound (allN_spec run_perms k (by omega))).1]
    exact (invEqK_sound (allN_spec run_perms k (by omega))).2
  · rw [alt_iff]
    intro k hk
    rw [alt_iff]
    intro k' hk'
    by_cases hlt : k < k'
    · rw [decide_eq_true hlt, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true',
        Bool.not_eq_true', (nc_eq hk).1, (nc_eq hk').1, CFSG.KC.BfsPin.compA_unpack (nc_eq hk').2
          (nc_eq hk').2]
      obtain ⟨n1, n2⟩ := nw_facts.2.2 k hk k' hk' hlt
      exact ⟨eqA_unpack_false (nc_eq hk).2 (nc_eq hk').2 n1,
        eqA_unpack_false (nc_eq hk).2 (CFSG.KC.BfsPin.canonK_pcomp (nc_eq hk').2 (nc_eq hk').2) n2⟩
    · rw [decide_eq_false hlt]
      rfl

theorem facts2308 :
    threeChecks fullExtArrs (tFullOf fullExtArrs) (compactEnum (tFullOf fullExtArrs)) = true := by
  unfold threeChecks
  rw [zChecks_ok, localChecks_ok, sylow_ok, fusion_ok]
  rfl

end CertificateChecks.KernelSpor.OddCore.S2308

end
