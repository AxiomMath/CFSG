module

public import Certificates.Kernel.Misc.Perm.Over148004
public import CFSG.Certificates.Kernel.Misc.OrbLoopMem
public import CFSG.Certificates.Kernel.Misc.ConjWitSound
public import CFSG.Certificates.Kernel.Misc.EnumBfsMem
public import CFSG.Certificates.Kernel.Misc.ArrEnumOps
public import CFSG.Certificates.Kernel.BfsPinSetSound
public import Certificates.Kernel.Misc.Perm.J2C3B
import Mathlib.Tactic.Group
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelMisc.Over148004

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ConjWit
open CertificateChecks.KernelMisc.J2C3
open CFSG.RankThree.PartTwo.Sec4.Ronan148V CFSG.RankThree.PartTwo.Sec4.Sporadic.J2
open CFSG.ComponentClassification.J2Cover CFSG.RankThree.Native CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer CFSG.KC.Bfs
open CFSG.Monster.B.Co2 (Rep eqA_iff eq_of_eqA rep_compA allLt_iff)
open CFSG.KC.Misc.Clos (allN_iff)
open CFSG.KC.OrbLoop (eqA_refl eq_of_eqA_size zOrbit_spec)

theorem eqA_conjInv_conj {g y : Array ℕ} (hg : validA 315 g = true) (hy : validA 315 y = true) :
    eqA 315 (conjInvA 315 g (conjA 315 g y)) y = true := by
  have h1 := rep_conjInvA hg (rep_conjA hg (rep_of_validA hy))
  refine (eqA_iff h1 (rep_of_validA hy)).2 ?_
  group

theorem conjA_inj {g y₁ y₂ : Array ℕ} (hg : validA 315 g = true) (h₁ : validA 315 y₁ = true)
    (h₂ : validA 315 y₂ = true) (hs₁ : y₁.size = 315) (hs₂ : y₂.size = 315)
    (e : conjA 315 g y₁ = conjA 315 g y₂) : y₁ = y₂ := by
  have a := eqA_conjInv_conj hg h₁
  have b := eqA_conjInv_conj hg h₂
  rw [e] at a
  have r := rep_conjInvA hg (rep_conjA hg (rep_of_validA h₂))
  have p₁ := eq_of_eqA r (rep_of_validA h₁) a
  have p₂ := eq_of_eqA r (rep_of_validA h₂) b
  exact eq_of_eqA_size ((eqA_iff (rep_of_validA h₁) (rep_of_validA h₂)).2 (p₁.symm.trans p₂))
    hs₁ hs₂

theorem conjA_surj {T : Finset (Array ℕ)} {g : Array ℕ} (hg : validA 315 g = true)
    (hv : ∀ x ∈ T, validA 315 x = true) (hs : ∀ x ∈ T, x.size = 315)
    (hcl : ∀ x ∈ T, conjA 315 g x ∈ T) : ∀ x ∈ T, ∃ y ∈ T, conjA 315 g y = x := by
  have hsub : T.image (conjA 315 g) ⊆ T := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    exact hcl y hy
  have hcard : T.card ≤ (T.image (conjA 315 g)).card := by
    rw [Finset.card_image_of_injOn]
    intro a ha b hb e
    have ha' := Finset.mem_coe.1 ha
    have hb' := Finset.mem_coe.1 hb
    exact conjA_inj hg (hv a ha') (hv b hb') (hs a ha') (hs b hb') e
  have he := Finset.eq_of_subset_of_card_le hsub hcard
  intro x hx
  rw [← he] at hx
  exact Finset.mem_image.1 hx

theorem any_of_mem {S : Array (Array ℕ)} {y t : Array ℕ} (hy : y ∈ S) (h : eqA 315 t y = true) :
    S.any (eqA 315 t) = true := by
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hy
  exact Array.any_eq_true.2 ⟨i, hi, h⟩

theorem eqA_conj_of {h s t m z : Array ℕ} (vh : validA 315 h = true) (vs : validA 315 s = true)
    (vt : validA 315 t = true) (vm : validA 315 m = true) (vz : validA 315 z = true)
    (h₁ : eqA 315 (compA 315 h s) (compA 315 t h) = true)
    (h₂ : eqA 315 (compA 315 m z) (compA 315 t m) = true) :
    eqA 315 (conjA 315 h s) (conjA 315 m z) = true := by
  have e₁ := eq_of_eqA (rep_compA (rep_of_validA vh) (rep_of_validA vs))
    (rep_compA (rep_of_validA vt) (rep_of_validA vh)) h₁
  have e₂ := eq_of_eqA (rep_compA (rep_of_validA vm) (rep_of_validA vz))
    (rep_compA (rep_of_validA vt) (rep_of_validA vm)) h₂
  refine (eqA_iff (rep_conjA vh (rep_of_validA vs)) (rep_conjA vm (rep_of_validA vz))).2 ?_
  rw [e₁, e₂]
  group

theorem map_get! {f : Array ℕ → Array ℕ} {a : Array (Array ℕ)} {h : ℕ} (hh : h < a.size) :
    (a.map f)[h]! = f a[h]! := by
  rw [getElem!_pos _ h (by simpa using hh), Array.getElem_map, getElem!_pos a h hh]

theorem unpack_size (P : ℕ) : (unpack 315 9 P).size = 315 := by
  simp [unpack]

theorem zop : ∀ i < 560, permB 315 9 (ZoP.F i) = true := fun i hi => by
  have := (allN_iff _ _).1 zo_points i hi
  simp only [pointA, Bool.and_eq_true] at this
  exact this.1.1

theorem zo_valid {i : ℕ} (hi : i < cZo.pts.size) : validA 315 cZo.pts[i]! = true := by
  have := arrCertOK_valid zo_cert hi
  simp only [okA, Bool.and_eq_true] at this
  exact this.1

noncomputable abbrev T : Finset (Array ℕ) := cZo.pts.toList.toFinset

theorem memT (x : Array ℕ) : x ∈ T ↔ x ∈ cZo.pts := by
  rw [List.mem_toFinset, Array.mem_toList_iff]

theorem idxT {x : Array ℕ} (hx : x ∈ T) : ∃ i < cZo.pts.size, cZo.pts[i]! = x := by
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 ((memT x).1 hx)
  exact ⟨i, hi, getElem!_pos _ i hi⟩

theorem validT : ∀ x ∈ T, validA 315 x = true := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := idxT hx
  exact zo_valid hi

theorem sizeT : ∀ x ∈ T, x.size = 315 := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := idxT hx
  rw [zo.2.1 i (zo.1 ▸ hi)]
  exact unpack_size _

theorem rootT : zArr ∈ T := by
  rw [memT, ← arrCertOK_root zo_cert, getElem!_pos _ 0 (arrCertOK_pos zo_cert)]
  exact Array.getElem_mem _

theorem clT : ∀ x ∈ T, ∀ k < 2, zConj k x ∈ T := by
  intro x hx k hk
  obtain ⟨i, hi, rfl⟩ := idxT hx
  obtain ⟨hj, e⟩ := arrCertOK_edge zo_cert hi hk
  rw [memT, ← e, getElem!_pos cZo.pts _ hj]
  exact Array.getElem_mem _

theorem reachT : ∀ x ∈ T, Reach zConj 2 zArr x := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := idxT hx
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [arrCertOK_root zo_cert]
      exact Reach.root
    · obtain ⟨hp, hl, e⟩ := arrCertOK_tree zo_cert hi0 hi
      rw [e]
      have hm : cZo.pts[cZo.par[i]!]! ∈ T := by
        rw [memT, getElem!_pos cZo.pts _ (hp.trans hi)]
        exact Array.getElem_mem _
      exact Reach.step _ hl (ih _ hp (hp.trans hi) hm)

theorem cardT : T.card ≤ 560 := by
  have := List.toFinset_card_le cZo.pts.toList
  rw [Array.length_toList, zo.1] at this
  exact this

theorem orbit : (∀ x, x ∈ zOrbit () ↔ x ∈ T) ∧ 0 < (zOrbit ()).size ∧ (zOrbit ())[0]! = zArr :=
  zOrbit_spec rootT clT reachT sizeT cardT

theorem closedT {g : Array ℕ} (k : ℕ) (hk : k < 2) (hgk : g = autStrong[k]!)
    (hg : validA 315 g = true) {S : Array (Array ℕ)} (hS : ∀ x, x ∈ S ↔ x ∈ T) {x : Array ℕ}
    (hx : x ∈ T) :
    (S.any (eqA 315 (conjA 315 g x)) && S.any (eqA 315 (conjInvA 315 g x))) = true := by
  have hc : ∀ y ∈ T, conjA 315 g y ∈ T := fun y hy => by
    rw [hgk]
    exact clT y hy k hk
  rw [Bool.and_eq_true]
  refine ⟨any_of_mem ((hS _).2 (hc x hx)) (eqA_refl _ _), ?_⟩
  obtain ⟨y, hy, rfl⟩ := conjA_surj hg validT sizeT hc x hx
  exact any_of_mem ((hS y).2 hy) (eqA_conjInv_conj hg (validT y hy))

theorem closedAll : allLt (zOrbit ()).size (fun i => closedAt (zOrbit ()) autStrong[0]! i &&
    closedAt (zOrbit ()) autStrong[1]! i) = true := by
  rw [allLt_iff]
  intro i hi
  have hx : (zOrbit ())[i]! ∈ T := by
    rw [← orbit.1, getElem!_pos _ i hi]
    exact Array.getElem_mem hi
  rw [Bool.and_eq_true]
  exact ⟨closedT 0 (by norm_num) rfl va orbit.1 hx, closedT 1 (by norm_num) rfl vb orbit.1 hx⟩

theorem ma (r : ℕ) (hr : r < 8) : mArrs[r]! = unpack 315 9 (MA r) :=
  arrBind_sound ((allN_iff _ _).1 maA r hr)

theorem maP (r : ℕ) (hr : r < 8) : permB 315 9 (MA r) = true := by
  have := (allN_iff _ _).1 maK r hr
  rw [Bool.and_eq_true] at this
  exact this.2

theorem maOk (r : ℕ) (hr : r < 8) : okA mArrs[r]! = true := by
  have := (allN_iff _ _).1 maK r hr
  rw [Bool.and_eq_true] at this
  rw [ma r hr]
  exact okA_of_okK this.1

theorem maV (r : ℕ) (hr : r < 8) : validA 315 mArrs[r]! = true := by
  have := maOk r hr
  simp only [okA, Bool.and_eq_true] at this
  exact this.1

theorem msize : mArrs.size = 8 := by
  have := sizes
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact this.1.1

theorem cz_valid {k : ℕ} (hk : k < 1080) : validA 315 (unpack 315 9 (CzP.F k)) = true := by
  rw [← cz.2.1 k hk]
  exact (enumOK_spec (n := 315) (by decide) enumCz).2.2 k (cz.1 ▸ hk)

theorem coverAt (i : ℕ) (hi : i < 560) :
    (inZ (unpack 315 9 (ZoP.F i)) || coveredBy cCz.pts (mArrs.map fun m => conjA 315 m zArr)
      (unpack 315 9 (ZoP.F i))) = true := by
  have hw' := witK_spec (witL_spec W 0 cov i (wlen ▸ hi))
  rw [Nat.zero_add] at hw'
  rw [inZ_unpack (zop i hi), Bool.or_eq_true]
  rcases hw' with h | ⟨hk, hr, e⟩
  · left
    rcases h with h | h | h <;> simp only [h, Nat.beq_refl, Bool.true_or, Bool.or_true]
  · right
    set k := W[i]! % 2048
    set r := W[i]! / 2048
    have htr := (allN_iff _ _).1 trK r hr
    rw [Bool.and_eq_true] at htr
    have hzv : validA 315 (unpack 315 9 (ZoP.F i)) = true := by
      rw [← zo.2.1 i hi]
      exact zo_valid (zo.1 ▸ hi)
    have htv : validA 315 (unpack 315 9 (TT r)) = true := CFSG.KC.BfsPin.validA_unpack htr.1
    have hzA : validA 315 zArr = true := by
      have := okz
      simp only [okA, Bool.and_eq_true] at this
      exact this.1
    unfold coveredBy
    refine Array.any_eq_true.2 ⟨k, cz.1 ▸ hk, Array.any_eq_true.2 ⟨r, by simpa [msize] using hr, ?_⟩⟩
    rw [Array.getElem_map, ← getElem!_pos cCz.pts k (cz.1 ▸ hk), cz.2.1 k hk,
      ← getElem!_pos mArrs r (msize ▸ hr)]
    refine eqA_conj_of (cz_valid hk) hzv htv (maV r hr) hzA ?_ ?_
    · rw [comp_unpack hw (czp k hk) (zop i hi), comp_unpack hw htr.1 (czp k hk),
        eqA_unpack hw (permB_pcomp hw (czp k hk) (zop i hi)) (permB_pcomp hw htr.1 (czp k hk)), e]
      exact Nat.beq_refl _
    · rw [ma r hr, hz, comp_unpack hw (maP r hr) pZ, comp_unpack hw htr.1 (maP r hr),
        eqA_unpack hw (permB_pcomp hw (maP r hr) pZ) (permB_pcomp hw htr.1 (maP r hr))]
      exact htr.2

theorem coverAll : allLt (zOrbit ()).size (fun i => inZ (zOrbit ())[i]! ||
    coveredBy cCz.pts (mArrs.map fun m => conjA 315 m zArr) (zOrbit ())[i]!) = true := by
  have hmem : ∀ x, x ∈ zOrbit () ↔ x ∈ cZo.pts := fun x => (orbit.1 x).trans (memT x)
  have e := CFSG.KC.EnumBfs.allLt_congr_of_mem hmem
    (fun s => inZ s || coveredBy cCz.pts (mArrs.map fun m => conjA 315 m zArr) s)
  rw [e, allLt_iff, zo.1]
  intro i hi
  rw [zo.2.1 i hi]
  exact coverAt i hi

theorem scP (r : ℕ) (hr : r < 8) : ∀ h < 3, permB 315 9 (SC r h) = true := by
  intro h hh
  interval_cases h
  · have h0 : permB 315 9 (GC 0) = true := by quickRfl
    exact h0
  · have h1 : permB 315 9 (GC 1) = true := by quickRfl
    exact h1
  · exact maP r hr

theorem scS (r : ℕ) (hr : r < 8) : ∀ h < 3, (wGens mArrs[r]!)[h]! = unpack 315 9 (SC r h) := by
  intro h hh
  interval_cases h
  · exact hgc 0 (by norm_num)
  · exact hgc 1 (by norm_num)
  · exact ma r hr

theorem wordOK (r : ℕ) (hr : r < 8) : CFSG.RankThree.PartTwo.Sec4.Ronan148V.wordsOK r = true := by
  have hS := scS r hr
  have hSp := scP r hr
  have hSIp : ∀ h < 3, permB 315 9 (SIC r h) = true := fun h hh => permB_pinvS hw (hSp h hh)
  have hSI : ∀ h < 3, ((wGens mArrs[r]!).map (invCand 315))[h]! = unpack 315 9 (SIC r h) := by
    intro h hh
    rw [map_get! (by simp [wGens]; omega), hS h hh, inv_unpack hw (hSp h hh)]
    rfl
  have hl := (allN_iff _ _).1 lK r hr
  rw [Bool.and_eq_true] at hl
  have hwk := (allN_iff _ _).1 wK r hr
  simp only [wordsK, Bool.and_eq_true] at hwk
  unfold CFSG.RankThree.PartTwo.Sec4.Ronan148V.wordsOK
  dsimp only
  rw [wordA_unpack hw hS hSI hSp hSIp hl.1, wordA_unpack hw hS hSI hSp hSIp hl.2,
    hab 0 (by norm_num), hab 1 (by norm_num),
    eqA_unpack hw (permB_wordK hw hSp hSIp hl.1) (by quickRfl),
    eqA_unpack hw (permB_wordK hw hSp hSIp hl.2) (by quickRfl), hl.1, hl.2, hwk.1, hwk.2]
  rfl

theorem over_ok : overCheck () = true := by
  have h7 : allLt 8 (fun r => okA mArrs[r]!) = true := allLt_iff.2 maOk
  have h12 : allLt 8 CFSG.RankThree.PartTwo.Sec4.Ronan148V.wordsOK = true := allLt_iff.2 wordOK
  have hs := sizes
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  have h9 : eqA 315 (zOrbit ())[0]! zArr = true := by
    rw [orbit.2.2]
    exact eqA_refl _ _
  unfold overCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨va, vb⟩, gcz_size⟩, hs.1.1⟩, hs.1.2⟩, hs.2⟩, h7⟩, orbit.2.1⟩, h9⟩,
    closedAll⟩, coverAll⟩, h12⟩

end CertificateChecks.KernelMisc.Over148004

end
