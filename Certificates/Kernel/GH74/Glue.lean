module

public import CFSG.GH74.Generic.S45.LEvSporSpec
public import Certificates.Kernel.Sporadic.OddCore.M12SylF
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue3

public section

namespace CertificateChecks.KernelGH74

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.GH74.Generic.S45.EvSpor

theorem tabsOK_of_map {n w k : Nat} {G : Nat → Nat} {gs : List Table}
    (he : gs.map natArr = (List.range k).map fun j => unpack n w (G j))
    (hc : ∀ j < k, canonK n w (mask w) (n * w) (G j) = true) : TabsOK n w k G gs.toArray := by
  have hlen : gs.length = k := by simpa using congrArg List.length he
  refine ⟨by simp [hlen], fun j hj => ⟨?_, hc j hj⟩⟩
  have hj' : j < gs.length := by omega
  have e1 : (gs.map natArr)[j]'(by simpa using hj') = unpack n w (G j) := by
    simp only [he, List.getElem_map, List.getElem_range]
  rw [List.getElem_map] at e1
  rw [getElem!_pos _ j (by simpa using hj'), List.getElem_toArray, ← tabT_natArr gs[j], e1]

theorem tab_of_list {n w X : Nat} {T : Table}
    (h : T.toList.map UInt32.toNat = (List.range n).map (pg w (mask w) X)) :
    T = tabT (unpack n w X) := by
  rw [← tabT_natArr T]
  congr 1
  apply Array.toList_inj.1
  rw [natArr, Array.toList_map, h, unpack, Array.toList_ofFn]
  exact (CFSG.KS.PEnum.ofFn_range n (pg w (mask w) X)).symm

theorem closArr_eq {n w k cnt cap : Nat} {G GI T PL POS SRT SRI HS HSI : Nat → Nat}
    {gs : List Table} (hn : szOK n w = true) (hG : ∀ j < k, G j = pidn n w)
    (hg : TabsOK n w k GI gs.toArray) (hh : penumHdK (pidn n w) cnt cap T PL = true)
    (hp : ∀ i < cnt, penumPtK n w (mask w) (n * w) true G GI k cnt T PL POS SRT SRI i = true)
    (hs : ∀ i < cnt, hsortPtK n w (mask w) cnt T HS HSI i = true) :
    closArr n cap gs = (hRec n w cnt T PL).1 := by
  unfold closArr
  rw [(mulH_sound hn hG hg hh hp hs).1]

theorem evEnum_of_rec {n w k cnt cap m : Nat} {G GI GJ T PL POS SRT SRI HS HSI CL : Nat → Nat}
    {gs : List Table} (hn : szOK n w = true) (hG : ∀ j < k, G j = pidn n w)
    (hg : TabsOK n w k GI gs.toArray)
    (hgj : ∀ j < k, invEqK n w (mask w) (n * w) (GI j) (GJ j) = true ∧
      canonK n w (mask w) (n * w) (GJ j) = true)
    (hh : penumHdK (pidn n w) cnt cap T PL = true)
    (hp : ∀ i < cnt, penumPtK n w (mask w) (n * w) true G GI k cnt T PL POS SRT SRI i = true)
    (hs : ∀ i < cnt, hsortPtK n w (mask w) cnt T HS HSI i = true)
    (hcl : ∀ c < cnt * (k + k),
      findPtK cnt T (prodQK n w (mask w) (k + k) T (bothK k GI GJ)) CL c = true)
    (hm : cnt = m) : enumOK n cap gs m = true := by
  refine KernelSpor.M12Syl.evEnum_of (enumOK_of hn hG hg hgj hh hp hs hcl hm) ?_
  rw [List.all_eq_true]
  intro g hgm
  obtain ⟨j, hj, rfl, hc⟩ := TabsOK_list hg hgm
  exact permOK_unpack hc (hgj j hj).1

theorem all_hRec_iff {n w cnt : Nat} {T PL : Nat → Nat} {p : Table → Bool} :
    (hRec n w cnt T PL).1.all p = true ↔ ∀ i < cnt, p (tabT (unpack n w (T i))) = true := by
  rw [Array.all_eq_true]
  constructor
  · intro h i hi
    have := h i (by simpa [hRec] using hi)
    simpa [hRec] using this
  · intro h i hi
    have hi' : i < cnt := by simpa [hRec] using hi
    simpa [hRec] using h i hi'

theorem invsOK_of_enumOK {n cap sz : Nat} {gs : List Table} (hn : n < 2 ^ 32)
    (h : enumOK n cap gs sz = true) : invsOK n (closArr n cap gs) = true := by
  obtain ⟨hE, -, -⟩ := enumOK_spec hn h
  rw [invsOK, Array.all_eq_true]
  intro k hk
  obtain ⟨c, -, hrep⟩ := hE.1 k hk
  rw [← getElem!_pos _ k hk]
  refine invOK_invT hn _ (fun i hi => ?_) (fun i hi i' hi' e => ?_)
  · have := hrep i hi
    unfold ap at this
    rw [this]
    exact idx_lt c hi
  · have h1 := hrep i hi
    have h2 := hrep i' hi'
    unfold ap at h1 h2
    rw [h1, h2] at e
    have := congrArg (idx n c⁻¹) e
    rwa [idx_inv_idx, idx_inv_idx] at this

open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore in
theorem card_eq_countP_of_enums {n : Nat} {E : Array Table} {H : Subgroup (Equiv.Perm (Fin n))}
    (hE : EnumsSub n E H) (hcard : Nat.card H = E.size) {p : Table → Bool}
    {P : Equiv.Perm (Fin n) → Prop} [DecidablePred P]
    (hp : ∀ T g, Rep n T g → (p T = true ↔ P g)) :
    Nat.card {x : H // P x} = E.toList.countP p := by
  classical
  have hrep : ∀ k < E.size, Rep n E[k]! (tablePerm n E[k]!) := fun k hk => by
    obtain ⟨c, -, hc⟩ := hE.1 k hk
    rw [tablePerm_eq hc]
    exact hc
  set L := E.toList.map (tablePerm n) with hLdef
  have hmem : ∀ g, g ∈ L ↔ g ∈ H := by
    intro g
    constructor
    · intro hg
      obtain ⟨k, hk, rfl⟩ := mem_map_tablePerm hrep hg
      obtain ⟨c, hc, hrc⟩ := hE.1 k hk
      rw [tablePerm_eq hrc]
      exact hc
    · intro hg
      obtain ⟨k, hk, hrk⟩ := hE.2 g hg
      rw [hLdef, List.mem_map]
      refine ⟨E[k]!, ?_, tablePerm_eq hrk⟩
      rw [getElem!_pos E k hk]
      exact Array.mem_toList_iff.mpr (Array.getElem_mem hk)
  have hnd : L.Nodup := by
    have hlen : L.length = Nat.card H := by rw [hcard, hLdef, List.length_map, Array.length_toList]
    have hle : Nat.card H ≤ L.dedup.length := by
      rw [show Nat.card H = (H : Set (Equiv.Perm (Fin n))).ncard from Nat.card_coe_set_eq _,
        ← List.toFinset_card_of_nodup (List.nodup_dedup L), ← Set.ncard_coe_finset]
      exact Set.ncard_le_ncard (fun y hy => List.mem_toFinset.2 (List.mem_dedup.2 ((hmem y).2 hy)))
        (Set.toFinite _)
    have hsub := List.dedup_sublist L
    have heq := hsub.eq_of_length_le (by omega)
    rw [← heq]
    exact List.nodup_dedup L
  rw [card_subtype_eq_countP H L hnd hmem P, hLdef, List.countP_map]
  apply List.countP_congr
  intro T hT
  obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp hT)
  have := hrep k hk
  rw [getElem!_pos E k hk] at this
  simp only [Function.comp, decide_eq_true_eq]
  exact (hp _ _ this).symm

end CertificateChecks.KernelGH74

end
