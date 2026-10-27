module

public import Certificates.Kernel.U43Cube.ChecksL
public import Certificates.Kernel.CU43Aut.SylGlue
public import CFSG.Certificates.Kernel.Spor.KeyWordSound
public import CFSG.Certificates.Kernel.Spor.ConjRunSound
public import CFSG.Sporadic.SmallOddCore.CentSpec

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU43Cube.Glue

open Subgroup CFSG.EvenSporadicStandard.M24Std.CU43 CFSG.EvenSporadicStandard.HSStd.U43
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.KeyWord CFSG.KS.ConjRun
open CertificateChecks.KernelU43B CertificateChecks.KernelCU43Aut CertificateChecks.KernelCU43Aut.CentG
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.KC.BfsPin (eq_unpack_of_bindListK)

theorem hKP : ∀ t < 3, pg 10 (mask 10) KP t < 820 := by
  intro t ht
  interval_cases t <;> decide

theorem permOfArr_eq_of_rep {t : Array ℕ} {g : Equiv.Perm (Fin 820)}
    (h : CFSG.Monster.B.Co2.Rep 820 t g) :
    CFSG.Monster.B.Co2.permOfArr 820 t = g := by
  have hc : (∀ i < 820, t[i]! < 820) ∧ ∀ i < 820, ∀ j < 820, t[i]! = t[j]! → i = j :=
    ⟨fun i hi => h.lt hi, fun i hi j hj hij => by
      rw [h.apply hi, h.apply hj] at hij
      have := g.injective (Fin.ext hij)
      simpa using this⟩
  ext x
  rw [CFSG.Monster.B.Co2.permOfArr, dite_eq_left hc]
  simp [h.apply x.2]

theorem pr_conj {Z H Y : Nat} {h y : Equiv.Perm (Fin 820)} (hH : PR H h) (hY : PR Y y)
    (e : pc H Y = pc Z H) : PR Z (h * y * h⁻¹) := fun x => by
  have hx := congrArg (fun p => pg 10 (mask 10) p ((h⁻¹ x : Fin 820) : Nat)) e
  simp only [pc] at hx
  rw [CFSG.KS.PF.pg_pcomp (by norm_num) (h⁻¹ x).2, CFSG.KS.PF.pg_pcomp (by norm_num) (h⁻¹ x).2,
    hY (h⁻¹ x), hH (y (h⁻¹ x)), hH (h⁻¹ x)] at hx
  simpa using hx.symm

section P


theorem sep (x : Equiv.Perm (Fin 820)) (hx : x ∈ P)
    (hfix : ∀ t (ht : t < 3), x ⟨pg 10 (mask 10) KP t, hKP t ht⟩ = ⟨_, hKP t ht⟩) : x = 1 := by
  have G := CFSG.KC.J2Enum.GrpPf.group3 KernelU43B.binds C.head C.hl (by norm_num) C.hs
  rw [P_eq_Gen] at hx
  refine G.1 x hx fun t ht h => ?_
  have e : pg 10 (mask 10) C.BP t = pg 10 (mask 10) KP t :=
    Nat.eq_of_beq_eq_true (allN_spec kBP t ht)
  have hfin : (⟨pg 10 (mask 10) C.BP t, h⟩ : Fin 820) = ⟨pg 10 (mask 10) KP t, hKP t ht⟩ :=
    Fin.ext e
  rw [hfin]
  exact hfix t ht

theorem cK_pidn : cK (pidn 820 10) = true := by
  have h := kSz
  simp only [Bool.and_eq_true] at h
  exact h.1.2

theorem rep_natArr {a : Array ℕ} {g : Equiv.Perm (Fin 820)} (hs : a.size = 820)
    (h : CFSG.Monster.B.Co2.Rep 820 a g) :
    CFSG.Monster.B.Co2.Rep 820 (natArr (a.map UInt32.ofNat)) g := by
  intro x
  have hx : x.1 < a.size := by rw [hs]; exact x.2
  have h1 : a[x.1]! = (g x : ℕ) := h x
  unfold natArr
  rw [getElem!_pos _ x.1 (by simpa using hx), Array.getElem_map, Array.getElem_map,
    UInt32.toNat_ofNat', ← getElem!_pos a x.1 hx, h1]
  exact Nat.mod_eq_of_lt (lt_trans (g x).2 (by norm_num))

theorem y_facts {k : Nat} (hk : k < 4) {A : Array ℕ} (hs : A.size = 820)
    (hb : bindListK 820 10 (YP k) A.toList = true) :
    PR (YP k) (tp 820 (A.map UInt32.ofNat)) ∧ tp 820 (A.map UInt32.ofNat) ∈ P ∧
      orderOf (tp 820 (A.map UInt32.ofNat)) = 3 := by
  have h := allN_spec kY k hk
  simp only [bAnd_iff] at h
  obtain ⟨hc, hin, h3, h1⟩ := h
  obtain ⟨γ, hγ, hγP⟩ := mem_P hc hin
  have hrep : CFSG.Monster.B.Co2.Rep 820 (natArr (A.map UInt32.ofNat)) γ := by
    refine rep_natArr hs ?_
    rw [eq_unpack_of_bindListK hb]
    exact Raw.Orb.rep_unpack hγ
  have e : tp 820 (A.map UInt32.ofNat) = γ := permOfArr_eq_of_rep hrep
  rw [e]
  refine ⟨hγ, hγP, ?_⟩
  have e3 : pc (YP k) (pc (YP k) (pc (YP k) (pidn 820 10))) = pidn 820 10 :=
    Nat.eq_of_beq_eq_true h3
  have hcube : γ * (γ * (γ * 1)) = 1 :=
    pr_eq (pr_pc hγ (pr_pc hγ (pr_pc hγ SylG.pr_pidn))) SylG.pr_pidn e3
  have hne : γ ≠ 1 := by
    intro h1'
    rw [h1'] at hγ
    have := SylG.canon_eq hc cK_pidn hγ SylG.pr_pidn
    rw [this] at h1
    simp at h1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ hne
  rw [pow_three]
  simpa using hcube

theorem yA_facts : PR (YP 0) (tp 820 yATab) ∧ tp 820 yATab ∈ P ∧ orderOf (tp 820 yATab) = 3 :=
  y_facts (by norm_num) (by rfl) kBind.1
theorem yB_facts : PR (YP 1) (tp 820 yBTab) ∧ tp 820 yBTab ∈ P ∧ orderOf (tp 820 yBTab) = 3 :=
  y_facts (by norm_num) (by rfl) kBind.2.1
theorem yC_facts : PR (YP 2) (tp 820 yCTab) ∧ tp 820 yCTab ∈ P ∧ orderOf (tp 820 yCTab) = 3 :=
  y_facts (by norm_num) (by rfl) kBind.2.2.1
theorem yD_facts : PR (YP 3) (tp 820 yDTab) ∧ tp 820 yDTab ∈ P ∧ orderOf (tp 820 yDTab) = 3 :=
  y_facts (by norm_num) (by rfl) kBind.2.2.2

theorem let_exists (j : Nat) : ∃ s : Equiv.Perm (Fin 820), j < 7 →
    PR (C.S j) s ∧ PR (C.SI j) s⁻¹ ∧ s ∈ P := by
  by_cases hj : j < 7
  · have h := allN_spec kLet j hj
    simp only [bAnd_iff] at h
    obtain ⟨γ, hγ, hγP⟩ := mem_P h.1 h.2
    refine ⟨γ, fun _ => ⟨hγ, fun x => ?_, hγP⟩⟩
    have hp := (Raw.Orb.permOK_facts (allN_spec KernelU43B.perm j hj)).2.2 _ (γ⁻¹ x).2
    rw [hγ (γ⁻¹ x)] at hp
    simpa using hp.2
  · exact ⟨1, fun h => absurd h hj⟩

@[expose] noncomputable def sg (j : Nat) : Equiv.Perm (Fin 820) := (let_exists j).choose

theorem sg_spec {j : Nat} (hj : j < 7) : PR (C.S j) (sg j) ∧ PR (C.SI j) (sg j)⁻¹ ∧ sg j ∈ P :=
  (let_exists j).choose_spec hj

theorem gens_rep : GensRep 820 10 (mask 10) 7 C.S C.SI sg := fun l hl p hp =>
  ⟨(sg_spec hl).1 ⟨p, hp⟩, (sg_spec hl).2.1 ⟨p, hp⟩⟩

theorem hL : ∀ l < 14, Raw.Orb.PRep 820 10 (cgK 7 C.S C.SI l) (gL 7 sg l) := fun l hl x =>
  (cg_rep gens_rep (by omega) x.2).1

theorem hLI : ∀ l < 14, Raw.Orb.PRep 820 10 (cgiK 7 C.S C.SI l) (gL 7 sg l)⁻¹ := fun l hl x =>
  (cg_rep gens_rep (by omega) x.2).2

theorem hLP : ∀ l < 14, gL 7 sg l ∈ P := fun l _ => gL_mem (fun j hj => (sg_spec hj).2.2) l

theorem card_ge_of_lb {r : Nat} {ρ : Equiv.Perm (Fin 820)} (hr : PR r ρ) {G L : Nat → Nat}
    {nh nl c : Nat} (hl : lbOK r G L nh nl c = true) :
    c ≤ Nat.card ↥(P ⊓ centralizer ({ρ} : Set (Equiv.Perm (Fin 820)))) := by
  unfold lbOK at hl
  obtain ⟨hg, hl2⟩ := (bAnd_iff _ _).1 hl
  obtain ⟨ht, hc⟩ := (bAnd_iff _ _).1 hl2
  have hex : ∀ l, ∃ γ : Equiv.Perm (Fin 820), l < nh →
      PR (G l) γ ∧ γ ∈ P ⊓ centralizer ({ρ} : Set (Equiv.Perm (Fin 820))) := by
    intro l
    by_cases hlt : l < nh
    · have hx := allN_spec hg l hlt
      simp only [bAnd_iff] at hx
      obtain ⟨h1, h2, h3⟩ := hx
      obtain ⟨γ, hγ, hγP⟩ := mem_P h1 h2
      refine ⟨γ, fun _ => ⟨hγ, mem_inf.2 ⟨hγP, mem_centralizer_singleton_iff.2 ?_⟩⟩⟩
      exact pr_eq (pr_pc hγ hr) (pr_pc hr hγ) (Nat.eq_of_beq_eq_true h3)
    · exact ⟨1, fun h => absurd h hlt⟩
  choose h hh using hex
  have hlow := CFSG.KS.CentBound.towerProdK_sound (h := h) (fun l hl => (hh l hl).1) ht
  rw [Nat.eq_of_beq_eq_true hc] at hlow
  have hle : closure (h '' {l | l < nh}) ≤ P ⊓ centralizer ({ρ} : Set (Equiv.Perm (Fin 820))) := by
    rw [closure_le]
    rintro _ ⟨l, hl, rfl⟩
    exact (hh l hl).2
  exact hlow.trans (Subgroup.card_le_of_le hle)

theorem hm30 : mask (10 * 3) = 1073741823 := by decide

theorem card_le_of_cj {k : Nat} {T : Nat → Nat} {y : Equiv.Perm (Fin 820)} (hY : PR (YP k) y)
    (hs : ∀ s < 3, cjS k T 3360 (s * 1120) 1120 = true) :
    Nat.card ↥(P ⊓ centralizer ({y} : Set (Equiv.Perm (Fin 820)))) ≤ 972 := by
  have hn := cj_ncard (H := P) (N := 3360) (NS := 3) (CH := 1120) hL hLI hY hKP (by norm_num)
    (by norm_num) (fun s hs' => by rw [hm30]; exact hs s hs') hLP
  have hc := ncard_conjClass_mul_card P y
  rw [card_P] at hc
  have hn' : 3360 ≤ (conjClass P y).ncard := hn
  by_contra hlt0
  have hlt := Nat.lt_of_not_le hlt0
  have : 3360 * 973 ≤ (conjClass P y).ncard *
      Nat.card ↥(P ⊓ centralizer ({y} : Set (Equiv.Perm (Fin 820)))) :=
    Nat.mul_le_mul hn' hlt
  omega

theorem cardB : Nat.card ↥(P ⊓ centralizer ({tp 820 yBTab} : Set (Equiv.Perm (Fin 820)))) = 972 :=
  le_antisymm (card_le_of_cj yB_facts.1 fun s hs => by
      interval_cases s
      · exact kC1_0
      · exact kC1_1
      · exact kC1_2)
    (card_ge_of_lb yB_facts.1 kL1)

theorem cardC : Nat.card ↥(P ⊓ centralizer ({tp 820 yCTab} : Set (Equiv.Perm (Fin 820)))) = 972 :=
  le_antisymm (card_le_of_cj yC_facts.1 fun s hs => by
      interval_cases s
      · exact kC2_0
      · exact kC2_1
      · exact kC2_2)
    (card_ge_of_lb yC_facts.1 kL2)

theorem card_of_conj {k : Nat} {y : Equiv.Perm (Fin 820)} (hY : PR (YP k) y) {Z H : Nat}
    (hHc : cK H = true) (hHi : inPK H = true) (e : pc H (YP k) = pc Z H) {O G L : Nat → Nat}
    {nh nl c : Nat} (hu : ubOK Z O c = true) (hl : lbOK Z G L nh nl c = true) :
    Nat.card ↥(P ⊓ centralizer ({y} : Set (Equiv.Perm (Fin 820)))) = c := by
  obtain ⟨h, hh, hhP⟩ := mem_P hHc hHi
  rw [← card_inf_centralizer_conj hhP y]
  exact card_of_bounds (pr_conj hh hY e) hu hl

theorem kZ_facts : cK (H0P 0) = true ∧ inPK (H0P 0) = true ∧
    pc (H0P 0) (YP 0) = pc (Z0P 0) (H0P 0) ∧ cK (H3P 0) = true ∧ inPK (H3P 0) = true ∧
    pc (H3P 0) (YP 3) = pc (Z3P 0) (H3P 0) := by
  have h := kZ
  simp only [bAnd_iff] at h
  obtain ⟨-, h1, h2, h3, -, h5, h6, h7⟩ := h
  exact ⟨h1, h2, Nat.eq_of_beq_eq_true h3, h5, h6, Nat.eq_of_beq_eq_true h7⟩

theorem cardA : Nat.card ↥(P ⊓ centralizer ({tp 820 yATab} : Set (Equiv.Perm (Fin 820)))) = 5832 :=
  card_of_conj yA_facts.1 kZ_facts.1 kZ_facts.2.1 kZ_facts.2.2.1 kU0 kL0

theorem cardD : Nat.card ↥(P ⊓ centralizer ({tp 820 yDTab} : Set (Equiv.Perm (Fin 820)))) = 81 :=
  card_of_conj yD_facts.1 kZ_facts.2.2.2.1 kZ_facts.2.2.2.2.1 kZ_facts.2.2.2.2.2 kU3 kL3

@[expose] noncomputable def yT (k : Nat) : CFSG.Sporadic.Th.Native.Table :=
  if k = 0 then yATab else if k = 1 then yBTab else if k = 2 then yCTab else yDTab

theorem yT_facts : ∀ k < 4, PR (YP k) (tp 820 (yT k)) ∧ tp 820 (yT k) ∈ P := by
  intro k hk
  interval_cases k
  · exact ⟨yA_facts.1, yA_facts.2.1⟩
  · exact ⟨yB_facts.1, yB_facts.2.1⟩
  · exact ⟨yC_facts.1, yC_facts.2.1⟩
  · exact ⟨yD_facts.1, yD_facts.2.1⟩

theorem sgS_exists (j : Nat) : ∃ s : Equiv.Perm (Fin 820), j < 3 → PR (SGP j) s ∧ s ∈ P := by
  by_cases hj : j < 3
  · have h := allN_spec kG j hj
    simp only [bAnd_iff] at h
    obtain ⟨γ, hγ, hγP⟩ := mem_P h.1 h.2
    exact ⟨γ, fun _ => ⟨hγ, hγP⟩⟩
  · exact ⟨1, fun h => absurd h hj⟩

@[expose] noncomputable def sS (j : Nat) : Equiv.Perm (Fin 820) := (sgS_exists j).choose

theorem sS_spec {j : Nat} (hj : j < 3) : PR (SGP j) (sS j) ∧ sS j ∈ P :=
  (sgS_exists j).choose_spec hj

theorem rows_of_sl {lo len : Nat} (h : syS lo len = true) : ∀ d < len, lo + d < 729 →
    syRowK 10 (mask 10) 3 3 14 4 1073741823 SGP (cgK 7 C.S C.SI) YP KP EP 729 (lo + d) = true := by
  intro d hd hN
  have e := allN_spec h d hd
  change strictB (lo + d) _ = true at e
  rw [strictB_eqK] at e
  change bIf(Nat.blt (lo + d) 729, _, true) = true at e
  rw [show Nat.blt (lo + d) 729 = true by simpa [Nat.blt_eq] using hN] at e
  exact e

theorem rows : ∀ i < 729,
    syRowK 10 (mask 10) 3 3 14 4 1073741823 SGP (cgK 7 C.S C.SI) YP KP EP 729 i = true := by
  intro i hi
  have hq : i / 243 < 3 := by omega
  have hi' : 243 * (i / 243) + i % 243 = i := Nat.div_add_mod i 243
  have hr : i % 243 < 243 := Nat.mod_lt _ (by norm_num)
  rw [← hi']
  interval_cases h : i / 243
  · exact rows_of_sl kS_0 _ hr (by omega)
  · exact rows_of_sl kS_1 _ hr (by omega)
  · exact rows_of_sl kS_2 _ hr (by omega)

theorem sylow_facts : Nat.card (closure (sS '' {j | j < 3})) = 729 ∧
    ∀ x ∈ closure (sS '' {j | j < 3}), x * x * x = 1 → x ≠ 1 →
      ∃ c < 4, ∃ u ∈ P, x = u * tp 820 (yT c) * u⁻¹ :=
  sy_card_cover (fun j hj => (sS_spec hj).1) hL (fun c hc => (yT_facts c hc).1) hKP
    (by rw [hm30]) (by norm_num) (fun i hi => by rw [← hm30] at *; exact rows i hi)
    (fun j hj => (sS_spec hj).2) hLP (fun c hc => (yT_facts c hc).2) sep

theorem exists_conj_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S S₁ : Sylow p G) :
    ∃ g : G, ∀ y : G, y ∈ (S₁ : Subgroup G) ↔ g⁻¹ * y * g ∈ (S : Subgroup G) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S S₁
  refine ⟨g, fun y => ?_⟩
  rw [← hg, Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def]

theorem fact3 : (3265920 : ℕ).factorization 3 = 6 := by
  have e : (3265920 : ℕ) = 3 ^ 6 * 4480 := by norm_num
  rw [e, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.prime_three.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (n := 4480) (by norm_num)]
  rfl

theorem cover (β : Equiv.Perm (Fin 820)) (hβ : β ∈ P) (h3 : β * β * β = 1) (h1 : β ≠ 1) :
    ∃ c < 4, ∃ g ∈ P, β = g * tp 820 (yT c) * g⁻¹ := by
  set Q := closure (sS '' {j | j < 3})
  have hQP : Q ≤ P := by
    rw [closure_le]
    rintro _ ⟨j, hj, rfl⟩
    exact (sS_spec hj).2
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (Q.subgroupOf P) = 3 ^ (Nat.card P).factorization 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQP).toEquiv, sylow_facts.1, card_P, fact3]
    norm_num
  let S : Sylow 3 P := Sylow.ofCard (Q.subgroupOf P) hcard
  let X : P := ⟨β, hβ⟩
  have hX3 : X ^ 3 = 1 := Subtype.ext (by
    change β ^ 3 = 1
    rw [pow_three, ← mul_assoc]
    exact h3)
  have hZ : IsPGroup 3 (zpowers X) := by
    have hd : orderOf X ∣ 3 := orderOf_dvd_of_pow_eq_one hX3
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  obtain ⟨R, hR⟩ := IsPGroup.exists_le_sylow hZ
  obtain ⟨g, hg⟩ := exists_conj_sylow S R
  have hm := (hg X).1 (hR (mem_zpowers X))
  have hS : ((S : Subgroup P)) = Q.subgroupOf P := rfl
  rw [hS, mem_subgroupOf] at hm
  set x : Equiv.Perm (Fin 820) := (g : Equiv.Perm (Fin 820))⁻¹ * β * g
  have hxQ : x ∈ Q := by simpa [x] using hm
  have hx3 : x * x * x = 1 := by
    simp only [x]
    calc (g : Equiv.Perm (Fin 820))⁻¹ * β * g * ((g : Equiv.Perm (Fin 820))⁻¹ * β * g) *
          ((g : Equiv.Perm (Fin 820))⁻¹ * β * g) = (g : Equiv.Perm (Fin 820))⁻¹ * (β * β * β) * g := by
          group
      _ = 1 := by rw [h3]; group
  have hx1 : x ≠ 1 := by
    intro hx
    apply h1
    calc β = g * x * (g : Equiv.Perm (Fin 820))⁻¹ := by simp only [x]; group
      _ = 1 := by rw [hx]; group
  obtain ⟨c, hc, u, huP, hu⟩ := sylow_facts.2 x hxQ hx3 hx1
  refine ⟨c, hc, g * u, P.mul_mem g.2 huP, ?_⟩
  calc β = g * x * (g : Equiv.Perm (Fin 820))⁻¹ := by simp only [x]; group
    _ = g * u * tp 820 (yT c) * (g * u)⁻¹ := by rw [hu]; group

end P

end CertificateChecks.KernelU43Cube.Glue

end
