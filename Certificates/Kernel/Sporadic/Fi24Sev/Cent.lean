module

public import Certificates.Kernel.Sporadic.Fi24ThreeO.Group
public import CFSG.Certificates.Kernel.Spor.Fi24SevSound
import Certificates.Kernel.Sporadic.Fi24OrbL.Bridge
public import CFSG.Sporadic.FischerOddCore.Fi24AlmostSimple
public import CFSG.Sporadic.FischerOddCore.Fi24R2CompBase
public import CFSG.Sporadic.FischerOddCore.FischerOuterBasic
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

namespace CFSG.KD.Fi24Sev.Cent

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
open CFSG.Sporadic.Fi24 (R J JR jR tR cls lvl gs letters)
open CFSG.Perm CFSG.Perm.Native CFSG.Sporadic.Th CFSG.KC CFSG.KC.Fi24Kit CFSG.KC.Fi24ThreeO
  CFSG.KC.Fi24Sev CFSG.KS.Fi24Net CFSG.KS.Fi24Kit CFSG.KS.Fi24ThreeO CFSG.KS.Fi24Sev CFSG.KD.Fi24Net
  CFSG.KD.Fi24Kit CFSG.KD.Fi24ThreeO CFSG.KD.Fi24ThreeO.Group

attribute [local instance] CFSG.Sporadic.Fi24.rAction


local notation "DK" => clsK CFSG.KD.Fi24ThreeO.OL NT

theorem DK_lt (hB : Bridge) {a b : ℕ} (ha : a < 306936) (hb : b < 306936) : DK a b < 306936 := by
  rw [← cls_val hB a b ha hb]
  exact Fin.isLt _

theorem DK_idx (hB : Bridge) (g : J) {a b : ℕ} (ha : a < 306936) (hb : b < 306936) :
    DK (idx 306936 g a) (idx 306936 g b) = idx 306936 g (DK a b) := by
  have key : ∀ a' b' : Fin 306936, DK a'.val b'.val = (cls a' • b').val :=
    fun a' b' => (hB.cls a' b').symm
  have e1 : idx 306936 g a = (g • (⟨a, ha⟩ : Fin 306936)).val := idx_of_lt g ha
  have e2 : idx 306936 g b = (g • (⟨b, hb⟩ : Fin 306936)).val := idx_of_lt g hb
  have e3 : DK a b = (cls (⟨a, ha⟩ : Fin 306936) • (⟨b, hb⟩ : Fin 306936)).val :=
    key ⟨a, ha⟩ ⟨b, hb⟩
  rw [e1, e2, key, e3, idx_of_lt g (Fin.isLt _), Fin.eta]
  congr 1
  rw [CFSG.Sporadic.Fi24.cls_smul, mul_smul, mul_smul, ← CFSG.Sporadic.Fi24.jR_smul g ⟨b, hb⟩,
    inv_smul_smul, CFSG.Sporadic.Fi24.jR_smul]

@[expose] def ProgOK : ℕ → List (ℕ × ℕ) → Prop
  | _, [] => True
  | n, p :: ps => p.1 < n ∧ p.2 < n ∧ ProgOK (n + 1) ps

instance (n : ℕ) (ps : List (ℕ × ℕ)) : Decidable (ProgOK n ps) := by
  induction ps generalizing n with
  | nil => exact isTrue trivial
  | cons p ps ih =>
    unfold ProgOK
    exact instDecidableAnd

theorem cfgL_cons (D : ℕ → ℕ → ℕ) (Z : List ℕ) (p : ℕ × ℕ) (ps : List (ℕ × ℕ)) :
    cfgL D Z (p :: ps) = cfgL D (Z ++ [D (Z.getD p.1 0) (Z.getD p.2 0)]) ps := rfl

theorem cfgL_length (D : ℕ → ℕ → ℕ) : ∀ (ps : List (ℕ × ℕ)) (Z : List ℕ),
    (cfgL D Z ps).length = Z.length + ps.length
  | [], _ => by simp [cfgL]
  | p :: ps, Z => by
    rw [cfgL_cons, cfgL_length D ps, List.length_append, List.length_cons]
    simp
    omega

theorem getD_map_of_lt (f : ℕ → ℕ) {L : List ℕ} {i : ℕ} (hi : i < L.length) :
    (L.map f).getD i 0 = f (L.getD i 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi,
    List.getElem_map]

theorem cfg_map (hB : Bridge) (g : J) : ∀ (ps : List (ℕ × ℕ)) (Z : List ℕ),
    (∀ z ∈ Z, z < 306936) → ProgOK Z.length ps →
      cfgL DK (Z.map (idx 306936 g)) ps = (cfgL DK Z ps).map (idx 306936 g) ∧
        ∀ z ∈ cfgL DK Z ps, z < 306936
  | [], Z, hZ, _ => ⟨rfl, hZ⟩
  | p :: ps, Z, hZ, hP => by
    obtain ⟨h1, h2, hP'⟩ := hP
    have hm : ∀ {i : ℕ}, i < Z.length → Z.getD i 0 < 306936 := fun hi => by
      rw [List.getD_eq_getElem _ _ hi]
      exact hZ _ (List.getElem_mem hi)
    have e : Z.map (idx 306936 g) ++
        [DK ((Z.map (idx 306936 g)).getD p.1 0) ((Z.map (idx 306936 g)).getD p.2 0)] =
        (Z ++ [DK (Z.getD p.1 0) (Z.getD p.2 0)]).map (idx 306936 g) := by
      rw [getD_map_of_lt _ h1, getD_map_of_lt _ h2, DK_idx hB g (hm h1) (hm h2), List.map_append,
        List.map_singleton]
    have hZ' : ∀ z ∈ Z ++ [DK (Z.getD p.1 0) (Z.getD p.2 0)], z < 306936 := by
      intro z hz
      rcases List.mem_append.1 hz with hz | hz
      · exact hZ z hz
      · rw [List.mem_singleton.1 hz]
        exact DK_lt hB (hm h1) (hm h2)
    have hP'' : ProgOK (Z ++ [DK (Z.getD p.1 0) (Z.getD p.2 0)]).length ps := by
      simpa using hP'
    rw [cfgL_cons, cfgL_cons, e]
    exact cfg_map hB g ps _ hZ' hP''

theorem cP_idx (hB : Bridge) {w : List ℕ} (hw : ∀ l ∈ w, l < 26) {x : ℕ} (hx : x < 306936) :
    cP NW NT w x = idx 306936 (wordElt w) x := by
  rw [idx_of_lt _ hx, word_val hB w hw]

theorem iter_idx (hB : Bridge) {w : List ℕ} (hw : ∀ l ∈ w, l < 26) {g : J}
    (hc : g * wordElt w = wordElt w * g) : ∀ (i : ℕ) {x : ℕ}, x < 306936 →
      (cP NW NT w)^[i] (idx 306936 g x) = idx 306936 g ((cP NW NT w)^[i] x) ∧
        (cP NW NT w)^[i] x < 306936
  | 0, _, hx => ⟨rfl, hx⟩
  | i + 1, x, hx => by
    obtain ⟨e, h⟩ := iter_idx hB hw hc i hx
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', e,
      cP_idx hB hw (idx_lt _ h), cP_idx hB hw h, ← idx_mul, ← idx_mul, hc]
    exact ⟨rfl, idx_lt _ h⟩

theorem tupN_map (hB : Bridge) {w : List ℕ} (hw : ∀ l ∈ w, l < 26) {g : J}
    (hc : g * wordElt w = wordElt w * g) {q : ℕ} (hq : q < 306936) (n : ℕ) :
    tupN (cP NW NT w) (idx 306936 g q) n = (tupN (cP NW NT w) q n).map (idx 306936 g) ∧
      ∀ z ∈ tupN (cP NW NT w) q n, z < 306936 := by
  unfold tupN
  refine ⟨?_, ?_⟩
  · rw [List.map_map]
    exact List.map_congr_left fun i _ => (iter_idx hB hw hc i hq).1
  · intro z hz
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hz
    exact (iter_idx hB hw (g := 1) (by group) i hq).2

theorem tupN_length (f : ℕ → ℕ) (q n : ℕ) : (tupN f q n).length = n := by simp [tupN]

theorem cfgT_map (hB : Bridge) {w : List ℕ} (hw : ∀ l ∈ w, l < 26) {g : J}
    (hc : g * wordElt w = wordElt w * g) {om : ℕ} (hom : om < 306936) {n : ℕ} {ps : List (ℕ × ℕ)}
    (hP : ProgOK n ps) :
    cfgL DK (tupN (cP NW NT w) (idx 306936 g om) n) ps =
        (cfgL DK (tupN (cP NW NT w) om n) ps).map (idx 306936 g) ∧
      ∀ z ∈ cfgL DK (tupN (cP NW NT w) om n) ps, z < 306936 := by
  obtain ⟨e, hlt⟩ := tupN_map hB hw hc hom n
  rw [e]
  exact cfg_map hB g ps _ hlt (by rw [tupN_length]; exact hP)

theorem not_conj_of_ref (hB : Bridge) {w : List ℕ} (hw : ∀ l ∈ w, l < 26) {om q n a b : ℕ}
    {ps : List (ℕ × ℕ)} (hom : om < 306936) (hP : ProgOK n ps) (ha : a < n + ps.length)
    (hb : b < n + ps.length)
    (hq : (cfgL DK (tupN (cP NW NT w) q n) ps).getD a 0 = (cfgL DK (tupN (cP NW NT w) q n) ps).getD b 0)
    (ho : (cfgL DK (tupN (cP NW NT w) om n) ps).getD a 0 ≠
      (cfgL DK (tupN (cP NW NT w) om n) ps).getD b 0)
    (g : J) (hc : g * wordElt w = wordElt w * g) : idx 306936 g om ≠ q := by
  intro hgq
  obtain ⟨e, hlt⟩ := cfgT_map hB hw hc hom hP
  rw [hgq] at e
  rw [e] at hq
  have hlen : (cfgL DK (tupN (cP NW NT w) om n) ps).length = n + ps.length := by
    rw [cfgL_length, tupN_length]
  rw [getD_map_of_lt _ (by omega), getD_map_of_lt _ (by omega)] at hq
  have hma : ∀ {i : ℕ}, i < n + ps.length → (cfgL DK (tupN (cP NW NT w) om n) ps).getD i 0 < 306936 :=
    fun hi => by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact hlt _ (List.getElem_mem _)
  have := congrArg (idx 306936 g⁻¹) hq
  rw [idx_inv_idx, idx_inv_idx] at this
  exact ho this

theorem wordElt_InW_comm {ws : List (List ℕ)} {r : J} (h : ∀ u ∈ ws, wordElt u * r = r * wordElt u)
    {v : List ℕ} (hv : InW ws v) : wordElt v * r = r * wordElt v := by
  obtain ⟨L, hL, rfl⟩ := hv
  induction L with
  | nil => rw [List.flatten_nil, wordElt_nil, one_mul, mul_one]
  | cons w L ih =>
    rw [List.flatten_cons, wordElt_append, mul_assoc,
      ih (fun w' h' => hL w' (List.mem_cons_of_mem w h')), ← mul_assoc,
      h w (hL w List.mem_cons_self), mul_assoc]

theorem cP_pad : ∀ {v : List ℕ}, (∀ l ∈ v, l < 26) → ∀ {x : ℕ}, 306936 ≤ x → x < 524288 →
    306936 ≤ cP NW NT v x ∧ cP NW NT v x < 524288
  | [], _, _, h1, h2 => ⟨h1, h2⟩
  | l :: v, hv, x, h1, h2 => by
    obtain ⟨e1, e2⟩ := cP_pad (fun l' h => hv l' (List.mem_cons_of_mem l h)) h1 h2
    rw [cP_cons]
    unfold CF
    rw [if_neg (by have := hv l List.mem_cons_self; omega)]
    exact CertificateChecks.KernelFi24OrbL.LN_pad (hv l List.mem_cons_self) e1 e2

theorem card_cent (hB : Bridge) {w : List ℕ} (hw : ∀ l ∈ w, l < 26) {ws : List (List ℕ)}
    (hws : ∀ u ∈ ws, ∀ l ∈ u, l < 26) {om : ℕ} (hom : om < 306936) {reps : List ℕ} {F c : ℕ}
    (hF1 : ∀ x < 524288, F.testBit x = true → ∃ v, InW ws v ∧ cP NW NT v x = om)
    (hF2 : Finset.card ((Finset.range 524288).filter (fun x => F.testBit x = true)) = c)
    (hF3 : ∀ x < 306936, F.testBit x = true ∨ ∃ v, InW ws v ∧ cP NW NT v x ∈ reps)
    (hcomm : ∀ u ∈ ws, wordElt u * wordElt w = wordElt w * wordElt u)
    (hrep : ∀ q ∈ reps, ∀ g : J, g * wordElt w = wordElt w * g → idx 306936 g om ≠ q)
    (hstab : ∀ g : J, g * wordElt w = wordElt w * g → idx 306936 g om = om → g = 1) :
    Nat.card (Subgroup.centralizer ({wordElt w} : Set J)) = c := by
  classical
  set r := wordElt w with hr
  have memC : ∀ g : J, g ∈ Subgroup.centralizer ({r} : Set J) ↔ g * r = r * g := by
    intro g
    exact Subgroup.mem_centralizer_singleton_iff
  set ω : Fin 306936 := ⟨om, hom⟩ with hω
  have hidx : ∀ g : J, idx 306936 g om = (g • ω).val := fun g => idx_of_lt g hom
  have himg : ∀ g : J, g * r = r * g → F.testBit (g • ω).val = true := by
    intro g hg
    rcases hF3 _ (g • ω).isLt with h | ⟨v, hv, hvr⟩
    · exact h
    · exfalso
      have hvl := InW_lt hws hv
      have hvc := wordElt_InW_comm hcomm hv
      refine hrep _ hvr (wordElt v * g) ?_ ?_
      · rw [mul_assoc, hg, ← mul_assoc, hvc, mul_assoc]
      · rw [hidx, mul_smul, ← word_val hB v hvl]
  have hpre : ∀ x < 524288, F.testBit x = true →
      ∃ g : J, g * r = r * g ∧ x < 306936 ∧ (g • ω).val = x := by
    intro x hx hFx
    obtain ⟨v, hv, hvx⟩ := hF1 x hx hFx
    have hvl := InW_lt hws hv
    have hvc := wordElt_InW_comm hcomm hv
    have hxN : x < 306936 := by
      by_contra hn
      have := (cP_pad hvl (by omega) hx).1
      omega
    refine ⟨(wordElt v)⁻¹, ?_, hxN, ?_⟩
    · calc (wordElt v)⁻¹ * r = (wordElt v)⁻¹ * (r * wordElt v) * (wordElt v)⁻¹ := by group
        _ = (wordElt v)⁻¹ * (wordElt v * r) * (wordElt v)⁻¹ := by rw [hvc]
        _ = r * (wordElt v)⁻¹ := by group
    · have e : (wordElt v • (⟨x, hxN⟩ : Fin 306936)) = ω := by
        apply Fin.ext
        rw [word_val hB v hvl]
        exact hvx
      rw [← e, inv_smul_smul]
  set S := (Finset.range 524288).filter (fun x => F.testBit x = true) with hS
  let φ : Subgroup.centralizer ({r} : Set J) → S := fun g =>
    ⟨(g.1 • ω).val, by
      rw [hS, Finset.mem_filter, Finset.mem_range]
      exact ⟨by have := (g.1 • ω).isLt; omega, himg g.1 ((memC g.1).1 g.2)⟩⟩
  have hinj : Function.Injective φ := by
    intro g h e
    have e' : g.1 • ω = h.1 • ω := Fin.ext (congrArg Subtype.val e)
    have hg := (memC g.1).1 g.2
    have hh := (memC h.1).1 h.2
    have hgh : (h.1⁻¹ * g.1) * r = r * (h.1⁻¹ * g.1) := by
      calc h.1⁻¹ * g.1 * r = h.1⁻¹ * (g.1 * r) := by group
        _ = h.1⁻¹ * (r * g.1) := by rw [hg]
        _ = h.1⁻¹ * (r * h.1) * (h.1⁻¹ * g.1) := by group
        _ = h.1⁻¹ * (h.1 * r) * (h.1⁻¹ * g.1) := by rw [hh]
        _ = r * (h.1⁻¹ * g.1) := by group
    have h1 := hstab _ hgh (by rw [hidx, mul_smul, e', inv_smul_smul])
    apply Subtype.ext
    rw [← mul_inv_cancel_left h.1 g.1, h1, mul_one]
  have hsurj : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    rw [hS, Finset.mem_filter, Finset.mem_range] at hx
    obtain ⟨g, hg, -, hgx⟩ := hpre x hx.1 hx.2
    exact ⟨⟨g, (memC g).2 hg⟩, Subtype.ext hgx⟩
  rw [Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩), Nat.card_eq_fintype_card,
    Fintype.card_coe, ← hF2]

end CFSG.KD.Fi24Sev.Cent

end
