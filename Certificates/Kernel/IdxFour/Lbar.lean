module

public import Certificates.Kernel.IdxFour.LbarOK
public import Certificates.Kernel.IdxFour.AutP
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.KD.IF4L

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.KC.IF4L CFSG.GF2Type.Smith1979.GammaU
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.IdxFour

@[expose] def sInv : List (Array ℕ × Array ℕ) :=
  [(#[1389, 2695, 1687, 2418, 3731, 3734, 3605, 2922, 858, 1509, 2682, 2874],
    #[606, 3464, 622, 3511, 3401, 3763, 1481, 4022, 2505, 118, 3893, 634]),
   (#[1, 2, 4, 8, 16, 32, 65, 130, 260, 520, 1040, 2080],
    #[1, 2, 4, 8, 16, 32, 65, 130, 260, 520, 1040, 2080]),
   (#[2, 1, 4, 8, 16, 32, 128, 64, 256, 512, 1024, 2048],
    #[2, 1, 4, 8, 16, 32, 128, 64, 256, 512, 1024, 2048])]

theorem lbar_rows : ∀ r ∈ lbarGens, rowsP (packR r) = r := by decide +kernel

theorem s_rows : ∀ r ∈ sGens, rowsP (packR r) = r := by decide +kernel

theorem lbar_ex : ∀ g ∈ lbarGens.map packR, ∃ U, IsP U g := by
  intro g hg
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
  have := (commOK_spec cf17608comm i hi).1
  rw [List.getD_eq_getElem _ _ hi] at this
  exact IsP.exists_of_mul this

theorem s_ex : ∀ g ∈ sGens.map packR, ∃ U, IsP U g := by
  have hp : ∀ p ∈ sInv, mulP (packR p.1) (packR p.2) = idP := by decide +kernel
  have he : sGens = sInv.map Prod.fst := rfl
  intro g hg
  rw [he, List.map_map, List.mem_map] at hg
  obtain ⟨p, hp', rfl⟩ := hg
  exact IsP.exists_of_mul (hp p hp')

@[expose] noncomputable def lbarL : List (V12 ≃ₗ[ZMod 2] V12) := (lbarGens.map packR).map autP

@[expose] noncomputable def sL : List (V12 ≃ₗ[ZMod 2] V12) := (sGens.map packR).map autP

theorem lbar_F : List.Forall₂ IsP lbarL (lbarGens.map packR) := forall₂_autP lbar_ex

theorem s_F : List.Forall₂ IsP sL (sGens.map packR) := forall₂_autP s_ex

theorem genGrp_lbar : genGrp lbarGens = Subgroup.closure {U | U ∈ lbarL} :=
  genGrp_eq lbar_rows lbar_ex

theorem genGrp_s : genGrp sGens = Subgroup.closure {U | U ∈ sL} := genGrp_eq s_rows s_ex

theorem lbarL_length : lbarL.length = 5 := by simp [lbarL, lbarGens]

theorem sL_length : sL.length = 3 := by simp [sL, sGens]

theorem lbar_commInv : CommInv lbarL := commInv_of lbar_F cf17608comm

theorem lbar_ne : ∀ m, 0 < m → m < 2 ^ lbarL.length → subG lbarL m ≠ 1 :=
  ne_one_of_subOK lbar_F (by simp [lbarGens]) cf17608sub

theorem mem_Lbar_iff {U : V12 ≃ₗ[ZMod 2] V12} :
    U ∈ genGrp lbarGens ↔ ∃ m < 32, subG lbarL m = U := by
  rw [genGrp_lbar, mem_closure_iff lbar_commInv, lbarL_length]
  rfl

theorem subG_mem_Lbar (m : ℕ) : subG lbarL m ∈ genGrp lbarGens := by
  rw [genGrp_lbar]
  exact subG_mem (fun g hg => Subgroup.subset_closure hg) m

theorem subG_inj_Lbar {m n : ℕ} (hm : m < 32) (hn : n < 32) (e : subG lbarL m = subG lbarL n) :
    m = n :=
  subG_inj lbar_commInv lbar_ne (by rw [lbarL_length]; exact hm) (by rw [lbarL_length]; exact hn) e

theorem card_Lbar : Nat.card (genGrp lbarGens) = 32 := by
  rw [genGrp_lbar, card_closure lbar_commInv lbar_ne, lbarL_length]
  rfl

theorem Lbar_sq {l : V12 ≃ₗ[ZMod 2] V12} (hl : l ∈ genGrp lbarGens) : l * l = 1 := by
  obtain ⟨m, -, rfl⟩ := mem_Lbar_iff.1 hl
  exact subG_mul_self lbar_commInv m

theorem Lbar_comm {l l' : V12 ≃ₗ[ZMod 2] V12} (hl : l ∈ genGrp lbarGens)
    (hl' : l' ∈ genGrp lbarGens) : l * l' = l' * l := by
  obtain ⟨m, -, rfl⟩ := mem_Lbar_iff.1 hl
  obtain ⟨n, -, rfl⟩ := mem_Lbar_iff.1 hl'
  rw [← subG_xor lbar_commInv, ← subG_xor lbar_commInv, Nat.xor_comm]

@[expose] def conjHom (g : V12 ≃ₗ[ZMod 2] V12) : (V12 ≃ₗ[ZMod 2] V12) →* (V12 ≃ₗ[ZMod 2] V12) where
  toFun a := g * a * g⁻¹
  map_one' := by group
  map_mul' a b := by group

theorem forall₂_of_getElem {α β : Type*} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, l₁.length = l₂.length →
      (∀ i (h₁ : i < l₁.length) (h₂ : i < l₂.length), R l₁[i] l₂[i]) → List.Forall₂ R l₁ l₂
  | [], [], _, _ => .nil
  | [], _ :: _, h, _ => absurd h (by simp)
  | _ :: _, [], h, _ => absurd h (by simp)
  | a :: l₁, b :: l₂, h, hR => .cons (hR 0 (by simp) (by simp))
      (forall₂_of_getElem (by simpa using h) fun i h₁ h₂ =>
        hR (i + 1) (by simpa using h₁) (by simpa using h₂))

theorem s_conj_gen {s : ℕ} (hs : s < sL.length) {i : ℕ} (hi : i < lbarL.length) :
    sL[s] * lbarL[i] * sL[s]⁻¹ = subG lbarL ((CM.getD s []).getD i 0) := by
  obtain ⟨-, hc⟩ := conjOK_spec cf17608conj
  have hs' : s < (sGens.map packR).length := by rw [← s_F.length_eq]; exact hs
  have hi' : i < (lbarGens.map packR).length := by rw [← lbar_F.length_eq]; exact hi
  have e := ((hc s hs').2 i hi').2
  have a := (isP_getD s_F s hs).mul (isP_getD lbar_F i hi)
  have b := (isP_subG lbar_F ((CM.getD s []).getD i 0)).mul (isP_getD s_F s hs)
  rw [e] at a
  rw [IsP.inj a b, mul_inv_cancel_right]

theorem s_conj {s : ℕ} (hs : s < sL.length) (m : ℕ) :
    sL[s] * subG lbarL m * sL[s]⁻¹ = subG lbarL (xsel (CM.getD s []) m) := by
  obtain ⟨hCM, hc⟩ := conjOK_spec cf17608conj
  have hs' : s < (sGens.map packR).length := by rw [← s_F.length_eq]; exact hs
  have hlen : lbarL.length = (CM.getD s []).length := by
    rw [(hc s hs').1, lbar_F.length_eq]
  exact map_subG lbar_commInv (conjHom sL[s])
    (forall₂_of_getElem hlen fun i h₁ h₂ => by
      rw [← List.getD_eq_getElem _ 0 h₂]
      exact s_conj_gen hs h₁) m

theorem CM_lt : ∀ s < CM.length, ∀ c ∈ CM.getD s [], c < 2 ^ 5 := by decide +kernel

@[expose] noncomputable def sAt (s : ℕ) : V12 ≃ₗ[ZMod 2] V12 := sL.getD s 1

theorem sAt_mem (s : ℕ) : sAt s ∈ genGrp sGens := by
  rw [genGrp_s, sAt]
  by_cases hs : s < sL.length
  · rw [List.getD_eq_getElem _ _ hs]
    exact Subgroup.subset_closure (List.getElem_mem hs)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Subgroup.one_mem _

theorem sAt_conj : ∀ s < CM.length, ∀ m,
    sAt s * subG lbarL m * (sAt s)⁻¹ = subG lbarL (xsel (CM.getD s []) m) := by
  intro s hs m
  have hs' : s < sL.length := by rw [sL_length]; exact hs
  rw [sAt, List.getD_eq_getElem _ _ hs']
  exact s_conj hs' m

theorem conj_mem_Lbar {g : V12 ≃ₗ[ZMod 2] V12} (hg : g ∈ genGrp sGens) {l : V12 ≃ₗ[ZMod 2] V12}
    (hl : l ∈ genGrp lbarGens) : g * l * g⁻¹ ∈ genGrp lbarGens := by
  rw [genGrp_s] at hg
  refine mem_of_closure (K := {g | ∀ l ∈ genGrp lbarGens, g * l * g⁻¹ ∈ genGrp lbarGens})
    (fun l hl => by simpa using hl) ?_ hg l hl
  rintro s hs y hy l hl
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs
  obtain ⟨m, -, hm⟩ := mem_Lbar_iff.1 (hy l hl)
  have e : sL[i] * y * l * (sL[i] * y)⁻¹ = sL[i] * (y * l * y⁻¹) * sL[i]⁻¹ := by group
  rw [e, ← hm, s_conj hi m]
  exact subG_mem_Lbar _

theorem conj_word {w : List ℕ} (hw : ∀ s ∈ w, s < CM.length) (m : ℕ) :
    wordG sAt w * subG lbarL m * (wordG sAt w)⁻¹ = subG lbarL (wact CM w m) :=
  conj_wordG sAt_conj hw m

theorem wordG_mem_s (w : List ℕ) : wordG sAt w ∈ genGrp sGens := wordG_mem sAt_mem w

theorem INN_lt : ∀ m ∈ INN, m < 2 ^ 5 := by decide +kernel

theorem exists_conj_inn {m m' : ℕ} (hm : m ∈ INN) (hm' : m' ∈ INN) :
    ∃ g ∈ genGrp sGens, g * subG lbarL m * g⁻¹ = subG lbarL m' := by
  obtain ⟨hlen, ho⟩ := orbOK_spec cf17608orb
  have key : ∀ m ∈ INN, ∃ g ∈ genGrp sGens, g * subG lbarL 3 * g⁻¹ = subG lbarL m := by
    intro m hm
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hm
    obtain ⟨hw, hwk⟩ := ho k hk
    refine ⟨_, wordG_mem_s (OW.getD k []), ?_⟩
    rw [conj_word hw, hwk, List.getD_eq_getElem _ _ hk]
  obtain ⟨g, hg, e⟩ := key m hm
  obtain ⟨g', hg', e'⟩ := key m' hm'
  refine ⟨g' * g⁻¹, mul_mem hg' (inv_mem hg), ?_⟩
  rw [← e, ← e']
  group

theorem chainG_of_index {G : Type*} [Group G] : ∀ {Ls : List (List G)} {ts : List G},
    Ls.length = ts.length →
    (∀ k < Ls.length, ((Ls.getD k []).map fun x => x * ts.getD k 1 * x⁻¹).Nodup) →
    (∀ k < Ls.length, ∀ j < k, ∀ y ∈ Ls.getD k [], y * ts.getD j 1 = ts.getD j 1 * y) →
    ChainG Ls ts
  | [], [], _, _, _ => trivial
  | [], _ :: _, h, _, _ => absurd h (by simp)
  | _ :: _, [], h, _, _ => absurd h (by simp)
  | X :: Ls, t :: ts, hl, h1, h2 => by
    refine ⟨h1 0 (by simp), fun Y hY y hy => ?_, chainG_of_index (by simpa using hl)
      (fun k hk => by simpa using h1 (k + 1) (by simpa using hk))
      (fun k hk j hj y hy => by
        simpa using h2 (k + 1) (by simpa using hk) (j + 1) (by omega) y (by simpa using hy))⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hY
    have hy' : y ∈ (X :: Ls).getD (k + 1) [] := by
      rw [List.getD_eq_getElem _ _ (by simpa using hk)]
      simpa using hy
    simpa using h2 (k + 1) (by simpa using hk) 0 (Nat.succ_pos k) y hy'

theorem le_relIndex {C : Subgroup (V12 ≃ₗ[ZMod 2] V12)}
    (hC : ∀ c ∈ C, ∀ m ∈ INN, c * subG lbarL m = subG lbarL m * c) :
    720 ≤ C.relIndex (genGrp sGens) := by
  obtain ⟨hτ, hlen, hlev, hn⟩ := chainOK_spec cf17608chain
  have hτlt : ∀ k < TAU.length, TAU.getD k 0 < 2 ^ 5 := by decide +kernel
  have hCM : ∀ s < CM.length, ∀ c ∈ CM.getD s [], c < 2 ^ 5 := CM_lt
  set Ls := TT.map fun ws => ws.map (wordG sAt) with hLs
  set ts := TAU.map (subG lbarL) with hts
  have hLsk : ∀ k, Ls.getD k [] = (TT.getD k []).map (wordG sAt) := fun k => by
    rw [hLs]
    by_cases hk : k < TT.length
    · rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map,
        List.getD_eq_getElem _ _ hk]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega),
        List.map_nil]
  have htsk : ∀ k < TAU.length, ts.getD k 1 = subG lbarL (TAU.getD k 0) := fun k hk => by
    rw [hts, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map,
      List.getD_eq_getElem _ _ hk]
  have hLlen : Ls.length = TAU.length := by rw [hLs, List.length_map, hlen]
  have hch : ChainG Ls ts := by
    refine chainG_of_index (by rw [hLlen, hts, List.length_map]) (fun k hk => ?_)
      (fun k hk j hj y hy => ?_)
    · rw [hLlen] at hk
      obtain ⟨hw, hnd⟩ := levelOK_spec (hlev k hk)
      rw [hLsk, htsk k hk]
      have e : ((TT.getD k []).map (wordG sAt)).map
          (fun x => x * subG lbarL (TAU.getD k 0) * x⁻¹) =
          ((TT.getD k []).map fun w => wact CM w (TAU.getD k 0)).map (subG lbarL) := by
        rw [List.map_map, List.map_map]
        exact List.map_congr_left fun w hw' => conj_word (hw w hw').1 _
      rw [e]
      refine List.Nodup.map_on (fun a ha b hb hab => ?_) hnd
      obtain ⟨w, hw', rfl⟩ := List.mem_map.1 ha
      obtain ⟨w', hw'', rfl⟩ := List.mem_map.1 hb
      exact subG_inj_Lbar (wact_lt hCM (hw w hw').1 _ (hτlt k hk))
        (wact_lt hCM (hw w' hw'').1 _ (hτlt k hk)) hab
    · rw [hLlen] at hk
      rw [hLsk] at hy
      obtain ⟨w, hw', rfl⟩ := List.mem_map.1 hy
      obtain ⟨hw, -⟩ := levelOK_spec (hlev k hk)
      rw [htsk j (by omega)]
      have e := conj_word (hw w hw').1 (TAU.getD j 0)
      rw [(hw w hw').2 j hj] at e
      calc wordG sAt w * subG lbarL (TAU.getD j 0)
          = (wordG sAt w * subG lbarL (TAU.getD j 0) * (wordG sAt w)⁻¹) * wordG sAt w := by
            group
        _ = subG lbarL (TAU.getD j 0) * wordG sAt w := by rw [e]
  have hH : ∀ Y ∈ Ls, ∀ y ∈ Y, y ∈ genGrp sGens := by
    intro Y hY y hy
    rw [hLs, List.mem_map] at hY
    obtain ⟨ws, -, rfl⟩ := hY
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hy
    exact wordG_mem_s w
  have hCt : ∀ c ∈ C, ∀ t ∈ ts, c * t = t * c := by
    intro c hc t ht
    rw [hts, List.mem_map] at ht
    obtain ⟨m, hm, rfl⟩ := ht
    exact hC c hc m (hτ m hm)
  have := prod_le_relIndex hch hH hCt
  rw [hLs, List.map_map] at this
  have e : (List.length ∘ fun ws : List (List ℕ) => ws.map (wordG sAt)) = List.length := by
    funext ws
    simp
  rw [e] at this
  omega

end CFSG.KD.IF4L

end
