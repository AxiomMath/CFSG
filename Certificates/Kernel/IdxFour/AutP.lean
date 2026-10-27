
module

public import CFSG.Certificates.Kernel.IdxFourLbarSound
public import CFSG.Certificates.Kernel.IdxFourSiftSound
public import CFSG.Certificates.Kernel.GammaUSigmaSoundBase
public import CFSG.GF2Type.Smith1979.GammaU.Violation

public section

namespace CFSG.KD.IF4L

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.KC.IF4L CFSG.GF2Type.Smith1979.GammaU
open CFSG.GF2Type.Smith1979.GammaU.Viol

@[expose] noncomputable def autP (m : ℕ) : V12 ≃ₗ[ZMod 2] V12 :=
  open Classical in if h : ∃ U, IsP U m then h.choose else 1

theorem isP_autP {m : ℕ} (h : ∃ U, IsP U m) : IsP (autP m) m := by
  classical
  rw [autP, dif_pos h]
  exact h.choose_spec

theorem forall₂_autP : ∀ {LP : List ℕ}, (∀ g ∈ LP, ∃ U, IsP U g) →
    List.Forall₂ IsP (LP.map autP) LP
  | [], _ => .nil
  | g :: LP, h => .cons (isP_autP (h g List.mem_cons_self))
      (forall₂_autP fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))

theorem isP_getD : ∀ {Us : List (V12 ≃ₗ[ZMod 2] V12)} {LP : List ℕ}, List.Forall₂ IsP Us LP →
    ∀ i (hi : i < Us.length), IsP Us[i] (LP.getD i 0)
  | _, _, .nil, _, hi => absurd hi (Nat.not_lt_zero _)
  | _, _, .cons h _, 0, _ => h
  | _, _, .cons _ hr, i + 1, hi => by
    simpa using isP_getD hr i (by simpa using hi)

theorem genGrp_eq {gs : List (Array ℕ)} (hrows : ∀ r ∈ gs, rowsP (packR r) = r)
    (hex : ∀ g ∈ gs.map packR, ∃ U, IsP U g) :
    genGrp gs = Subgroup.closure {U | U ∈ (gs.map packR).map autP} := by
  have hex' : ∀ r ∈ gs, ∃ U, IsP U (packR r) := fun r hr => hex _ (List.mem_map_of_mem hr)
  rw [genGrp]
  congr 1
  ext U
  simp only [GenSet, Set.mem_setOf_eq, List.map_map, List.mem_map, Function.comp_apply]
  constructor
  · rintro ⟨r, hr, hU⟩
    exact ⟨r, hr, IsP.inj (isP_autP (hex' r hr)) ((isP_iff_of_rowsP (hrows r hr) U).2 hU)⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r, hr, (isP_iff_of_rowsP (hrows r hr) _).1 (isP_autP (hex' r hr))⟩

theorem fld_zero_eq (m : ℕ) : fld m 0 = m &&& 4095 := by
  change (m >>> (12 * 0)) &&& 4095 = _
  rw [Nat.mul_zero, Nat.shiftRight_zero]

theorem mulPk_congr' : ∀ (k : ℕ) {g h g' h' : ℕ},
    (∀ j < k, ap12 g (fld h j) = ap12 g' (fld h' j)) → mulPk k g h = mulPk k g' h'
  | 0, _, _, _, _, _ => rfl
  | k + 1, g, h, g', h', hf => by
    change (ap12 g (h &&& 4095) ||| mulPk k g (h >>> 12) <<< 12) =
      (ap12 g' (h' &&& 4095) ||| mulPk k g' (h' >>> 12) <<< 12)
    have h0 := hf 0 (Nat.succ_pos k)
    rw [fld_zero_eq, fld_zero_eq] at h0
    rw [h0, mulPk_congr' k (g := g) (h := h >>> 12) (g' := g') (h' := h' >>> 12) (fun j hj => by
      rw [fld_shiftRight, fld_shiftRight]
      exact hf (j + 1) (by omega))]

theorem mulP_eq_of_isP' {U : V12 ≃ₗ[ZMod 2] V12} {g h g' h' : ℕ} (h1 : IsP U (mulP g h))
    (h2 : IsP U (mulP g' h')) : mulP g h = mulP g' h' := by
  refine mulPk_congr' 12 fun j hj => ?_
  have e := (h1 (Pi.single ⟨j, hj⟩ 1)).symm.trans (h2 (Pi.single ⟨j, hj⟩ 1))
  rw [CFSG.KC.GUS.linP_single, CFSG.KC.GUS.linP_single, fld_mulP, fld_mulP] at e
  exact vecOf_inj (ap12_lt _ _) (ap12_lt _ _) e

theorem mulP_idP' : mulP idP idP = idP := by decide +kernel

theorem commInv_of {Us : List (V12 ≃ₗ[ZMod 2] V12)} {LP : List ℕ} (hF : List.Forall₂ IsP Us LP)
    (h : commOK LP = true) : CommInv Us := by
  have hlen := hF.length_eq
  have hs := commOK_spec h
  intro g hg
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
  have hi' : i < LP.length := by rw [← hlen]; exact hi
  refine ⟨?_, fun h' hh => ?_⟩
  · have := (isP_getD hF i hi).mul (isP_getD hF i hi)
    rw [(hs i hi').1] at this
    exact IsP.inj this IsP.one
  · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hh
    have hj' : j < LP.length := by rw [← hlen]; exact hj
    have a := (isP_getD hF i hi).mul (isP_getD hF j hj)
    have b := (isP_getD hF j hj).mul (isP_getD hF i hi)
    rcases lt_trichotomy j i with hji | rfl | hij
    · rw [(hs i hi').2 j hji] at a
      exact IsP.inj a b
    · rfl
    · rw [(hs j hj').2 i hij] at b
      exact IsP.inj a b

theorem ne_one_of_subOK {Us : List (V12 ≃ₗ[ZMod 2] V12)} {LP : List ℕ}
    (hF : List.Forall₂ IsP Us LP) (hne : LP ≠ []) (h : subOK LP = true) :
    ∀ m, 0 < m → m < 2 ^ Us.length → subG Us m ≠ 1 := by
  intro m h0 hm e
  have a := isP_subG hF m
  rw [e] at a
  have b : IsP 1 (mulP idP idP) := by rw [mulP_idP']; exact IsP.one
  obtain ⟨g, LP', rfl⟩ := List.exists_cons_of_ne_nil hne
  have := mulP_eq_of_isP' a b
  exact subOK_spec h m h0 (by rw [← hF.length_eq]; exact hm) (this.trans mulP_idP')

end CFSG.KD.IF4L

end
