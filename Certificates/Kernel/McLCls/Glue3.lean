module

public import Certificates.Kernel.McLCls.Glue2
public import Certificates.Kernel.McLCls.E8
public import CFSG.Certificates.Kernel.PermCent.OrbGroup

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMcLCls

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KC.M305
  CertificateChecks.KernelLC.McLC CFSG.Sporadic.Th CFSG.Sporadic.SmallOddCore CFSG.Quasithin.KGC31
  CFSG.SectionRank.QTK.Insp443.McLCls CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.SmallOddCore.Native CFSG.KS.MulH

theorem exists_conj_le_of_index {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {H R E : Subgroup G} (hRH : R ≤ H) (hEH : E ≤ H) (hR : IsPGroup p R) (hE : IsPGroup p E)
    {m : ℕ} (hm : ¬ p ∣ m) (hcard : Nat.card H = Nat.card R * m) :
    ∃ c ∈ H, ∀ x ∈ E, c * x * c⁻¹ ∈ R := by
  have hRcard : Nat.card (R.subgroupOf H) = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRH).toEquiv
  have hR' : IsPGroup p (R.subgroupOf H) := hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRH).symm
  have hindex : (R.subgroupOf H).index = m := by
    have h := (R.subgroupOf H).index_mul_card
    rw [hRcard, hcard] at h
    have hpos : 0 < Nat.card R := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h, mul_comm])
  have hp : ¬ p ∣ (R.subgroupOf H).index := by
    rw [hindex]
    exact hm
  let RS : Sylow p H := hR'.toSylow hp
  have hE' : IsPGroup p (E.subgroupOf H) := hE.of_equiv (Subgroup.subgroupOfEquivOfLe hEH).symm
  obtain ⟨Q, hQ⟩ := hE'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Q RS
  refine ⟨g, g.2, fun x hx => ?_⟩
  have hxQ : (⟨x, hEH hx⟩ : H) ∈ (Q : Subgroup H) := hQ (Subgroup.mem_subgroupOf.2 hx)
  have h1 := Subgroup.smul_mem_pointwise_smul (⟨x, hEH hx⟩ : H) (MulAut.conj g) (Q : Subgroup H)
    hxQ
  rw [← Sylow.coe_subgroup_smul, hg] at h1
  exact Subgroup.mem_subgroupOf.1 h1

theorem pgroup_zpowers {p : ℕ} [hp : Fact p.Prime] {x : Equiv.Perm (Fin 275)} (hx1 : x ≠ 1)
    (hxp : x ^ p = 1) : IsPGroup p (zpowers x) := by
  refine IsPGroup.of_card (n := 1) ?_
  rw [Nat.card_zpowers, pow_one]
  exact orderOf_eq_prime hxp hx1


theorem card_H : Nat.card F.H = 40320 := mclT0_facts.2.2.2.1

theorem H_eq : F.H = closure (tp 275 '' {x | x ∈ [mclCentTbl 5, mclCentTbl 6].toArray}) :=
  mclT0_facts.2.2.1.symm

theorem t0_comm {c : Equiv.Perm (Fin 275)} (hc : c ∈ F.H) : c * F.t0 = F.t0 * c :=
  (mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).2)

theorem IE_gens : ∀ k < IE.ng, PRep 275 9 (IE.G k) (gH k) := by
  have h := e8gens
  simp only [band] at h
  intro k hk
  have hk2 : k < 2 := hk
  interval_cases k
  · rw [Nat.eq_of_beq_eq_true h.2.2.2.2.1]
    exact prep_hL 0
  · rw [Nat.eq_of_beq_eq_true h.2.2.2.2.2]
    exact prep_hL 1

theorem IE_root : PRep 275 9 (IE.T IE.r0) (tp 275 (clsTbl 0)) := by
  have e : IE.T IE.r0 = CT.F 0 := by decide +kernel
  rw [e]
  exact prep_cls (k := 0) (by norm_num)

theorem IE_reps : ∃ c : Nat → Equiv.Perm (Fin 275), (∀ i < IE.N, PRep 275 9 (IE.T i) (c i)) ∧
    ∀ i < IE.N, ∀ k < IE.ng, ∃ j < IE.N, gH k * c i * (gH k)⁻¹ = c j := by
  obtain ⟨c, h1, -, h3, -⟩ := CFSG.KC.OrbGroup.conjOrb_reps (by norm_num) IE.h IE_gens IE.cl IE.tr0
    (by decide +kernel) IE_root (by decide) IE.k
  exact ⟨c, h1, h3⟩

theorem IE_closed {c : Nat → Equiv.Perm (Fin 275)}
    (hc : ∀ i < IE.N, ∀ k < IE.ng, ∃ j < IE.N, gH k * c i * (gH k)⁻¹ = c j) :
    ∀ h ∈ F.H, ∀ i < IE.N, ∃ j < IE.N, h * c i * h⁻¹ = c j := by
  let C : Set (Equiv.Perm (Fin 275)) := {y | ∃ i < IE.N, c i = y}
  let K : Subgroup (Equiv.Perm (Fin 275)) :=
    { carrier := {h | ∀ y ∈ C, h * y * h⁻¹ ∈ C}
      mul_mem' := fun {a b} ha hb y hy => by
        have e : a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := by group
        rw [e]
        exact ha _ (hb y hy)
      one_mem' := fun y hy => by simpa using hy
      inv_mem' := fun {a} ha y hy => by
        obtain ⟨z, hz, e⟩ := CFSG.KC.OrbGroup.surj_of_mapsTo (T := C) (fun z => a * z * a⁻¹)
          (fun u v e => by simpa using e) ha y hy
        rw [← e]
        have e2 : a⁻¹ * (a * z * a⁻¹) * a⁻¹⁻¹ = z := by group
        rw [e2]
        exact hz }
  have hK : F.H ≤ K := by
    rw [H_eq, closure_le]
    rintro _ ⟨T, hT, rfl⟩
    simp only [List.toArray, Set.mem_setOf_eq, List.mem_toArray, List.mem_cons, List.not_mem_nil,
      or_false] at hT
    rcases hT with rfl | rfl
    · rintro y ⟨i, hi, rfl⟩
      obtain ⟨j, hj, e⟩ := hc i hi 0 (by decide +kernel)
      exact ⟨j, hj, e.symm⟩
    · rintro y ⟨i, hi, rfl⟩
      obtain ⟨j, hj, e⟩ := hc i hi 1 (by decide +kernel)
      exact ⟨j, hj, e.symm⟩
  intro h hh i hi
  obtain ⟨j, hj, e⟩ := hK hh (c i) ⟨i, hi, rfl⟩
  exact ⟨j, hj, e.symm⟩

theorem t0_eq : F.t0 = tp 275 (mclCentTbl 4) := rfl

theorem inv_mem_IE {c : Nat → Equiv.Perm (Fin 275)} (hcT : ∀ i < IE.N, PRep 275 9 (IE.T i) (c i))
    (hc : ∀ i < IE.N, ∀ k < IE.ng, ∃ j < IE.N, gH k * c i * (gH k)⁻¹ = c j)
    {y : Equiv.Perm (Fin 275)} (hy : y ∈ F.H) (hy2 : y * y = 1) (hy1 : y ≠ 1) (hyt : y ≠ F.t0) :
    ∃ j < IE.N, c j = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 F.S := IsPGroup.of_card (n := 7) (by rw [sTwo_fact.2]; norm_num)
  have hE : IsPGroup 2 (zpowers y) := pgroup_zpowers hy1 (by rw [pow_two]; exact hy2)
  obtain ⟨g, hg, hconj⟩ := exists_conj_le_of_index sTwo_fact.1
    ((zpowers_le (H := F.H)).mpr hy) hS2 hE (m := 315) (by norm_num)
    (by rw [card_H, sTwo_fact.2])
  set s := g * y * g⁻¹ with hs
  have hsS : s ∈ F.S := hconj y (mem_zpowers y)
  obtain ⟨j, hj, hsj⟩ := (mem_S_iff s).1 hsS
  have hs2 : s * s = 1 := by
    rw [hs]
    have e : g * y * g⁻¹ * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
    rw [e, hy2]
    group
  have hgt := t0_comm hg
  have hcv := CFSG.KS.Raw.Orb.allN_iff.1 cov j hj
  rcases bif_iff.1 hcv with ⟨-, hcv⟩ | ⟨h0, -⟩
  · rcases bif_iff.1 hcv with ⟨h1, -⟩ | ⟨-, hcv⟩
    · exfalso
      apply hy1
      have e := eq_of_beq hsj prep_one h1
      have e2 : y = g⁻¹ * s * g := by rw [hs]; group
      rw [e2, e]
      group
    rcases bif_iff.1 hcv with ⟨h1, -⟩ | ⟨-, hcv⟩
    · exfalso
      apply hyt
      have e := eq_of_beq hsj prep_cen4 h1
      have e2 : y = g⁻¹ * s * g := by rw [hs]; group
      rw [e2, e, ← t0_eq]
      calc g⁻¹ * F.t0 * g = g⁻¹ * (F.t0 * g) := by group
        _ = g⁻¹ * (g * F.t0) := by rw [hgt]
        _ = F.t0 := by group
    obtain ⟨hk, hk2⟩ := band.1 hcv
    have hkN := Nat.blt_eq.mp hk
    have e := eq_of_beq hsj (hcT _ hkN) hk2
    obtain ⟨j', hj', e'⟩ := IE_closed hc g⁻¹ (F.H.inv_mem hg) _ hkN
    refine ⟨j', hj', ?_⟩
    rw [← e', ← e, hs]
    group
  · exfalso
    rw [(sq_iff (canon_SE j hj) hsj).2 hs2] at h0
    exact Bool.noConfusion h0

theorem bfsK_zero {ng N : Nat} {G T E S : Nat → Nat}
    (hk : CFSG.KC.BfsPin.bfsK 275 9 ng G N T E S = true) :
    T 0 = pidn 275 9 := by
  unfold CFSG.KC.BfsPin.bfsK at hk
  simp only [band] at hk
  exact Nat.eq_of_beq_eq_true hk.2.2.2.1

theorem e8_at {ng N : Nat} {G T E S : Nat → Nat}
    (hk : CFSG.KC.BfsPin.bfsK 275 9 ng G N T E S = true)
    {gl : List (Equiv.Perm (Fin 275))} (hl : gl.length = ng)
    (hG : ∀ k < ng, PRep 275 9 (G k) (gl.getD k 1)) (he8 : e8At N T = true)
    (hgH : ∀ g ∈ gl, g ∈ F.H) {p m : ℕ} [Fact p.Prime] (hR : IsPGroup p (closure {s | s ∈ gl}))
    (hm : ¬ p ∣ m) (hcard : 40320 = N * m)
    {x a b : Equiv.Perm (Fin 275)} (hx : x ∈ F.H) (ha : a ∈ F.H) (hb : b ∈ F.H) (hx1 : x ≠ 1)
    (hxp : x ^ p = 1) (ha2 : a * a = 1) (ha1 : a ≠ 1) (hat : a ≠ F.t0) (hb2 : b * b = 1)
    (hb1 : b ≠ 1) (hbt : b ≠ F.t0) (hxa : x * a = a * x) (hxb : x * b = b * x)
    (hab : a * b = b * a) : b = a ∨ b = a * F.t0 := by
  obtain ⟨hmem, hcardR⟩ := CFSG.ClassicalInvolution.ListBridge.enum_closure hk hl hG
  have hRH : closure {s | s ∈ gl} ≤ F.H := by
    rw [closure_le]
    exact fun g hg => hgH g hg
  obtain ⟨c, hc, hconj⟩ := exists_conj_le_of_index hRH ((zpowers_le (H := F.H)).mpr hx) hR
    (pgroup_zpowers hx1 hxp) hm (by rw [card_H, hcardR]; exact hcard)
  obtain ⟨i, hi, hxi⟩ := (hmem _).1 (hconj x (mem_zpowers x))
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [bfsK_zero hk] at hxi
    apply hx1
    have e := prep_eq hxi prep_one
    calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
      _ = 1 := by rw [e]; group
  have h8 := CFSG.KS.Raw.Orb.allN_iff.1 he8 i hi
  have e0 : Nat.beq i 0 = false := Bool.eq_false_iff.mpr fun h => hi0 (Nat.eq_of_beq_eq_true h)
  rw [e0] at h8
  change m305e8 (T i) (MC.F 4) IE.N IE.T = true at h8
  obtain ⟨cI, hcT, hcl⟩ := IE_reps
  have hgt := t0_comm hc
  have hconjH : ∀ y ∈ F.H, c * y * c⁻¹ ∈ F.H := fun y hy =>
    F.H.mul_mem (F.H.mul_mem hc hy) (F.H.inv_mem hc)
  have hsq : ∀ y : Equiv.Perm (Fin 275), y * y = 1 → c * y * c⁻¹ * (c * y * c⁻¹) = 1 := by
    intro y hy
    have e : c * y * c⁻¹ * (c * y * c⁻¹) = c * (y * y) * c⁻¹ := by group
    rw [e, hy]
    group
  have hne1 : ∀ y : Equiv.Perm (Fin 275), y ≠ 1 → c * y * c⁻¹ ≠ 1 := by
    intro y hy e
    apply hy
    calc y = c⁻¹ * (c * y * c⁻¹) * c := by group
      _ = 1 := by rw [e]; group
  have hnet : ∀ y : Equiv.Perm (Fin 275), y ≠ F.t0 → c * y * c⁻¹ ≠ F.t0 := by
    intro y hy e
    apply hy
    calc y = c⁻¹ * (c * y * c⁻¹) * c := by group
      _ = c⁻¹ * (F.t0 * c) := by rw [e]; group
      _ = c⁻¹ * (c * F.t0) := by rw [hgt]
      _ = F.t0 := by group
  have hcomm : ∀ y z : Equiv.Perm (Fin 275), y * z = z * y →
      c * y * c⁻¹ * (c * z * c⁻¹) = c * z * c⁻¹ * (c * y * c⁻¹) := by
    intro y z hyz
    calc c * y * c⁻¹ * (c * z * c⁻¹) = c * (y * z) * c⁻¹ := by group
      _ = c * (z * y) * c⁻¹ := by rw [hyz]
      _ = c * z * c⁻¹ * (c * y * c⁻¹) := by group
  obtain ⟨ia, hia, ea⟩ := inv_mem_IE hcT hcl (hconjH a ha) (hsq a ha2) (hne1 a ha1) (hnet a hat)
  obtain ⟨ib, hib, eb⟩ := inv_mem_IE hcT hcl (hconjH b hb) (hsq b hb2) (hne1 b hb1) (hnet b hbt)
  unfold m305e8 at h8
  have h1 := CFSG.KS.Raw.Orb.allN_iff.1 h8 ia hia
  have hxa' := (comm_iff hxi (hcT ia hia)).2 (by rw [ea]; exact hcomm x a hxa)
  rw [hxa'] at h1
  change CFSG.KC.Enum.allN IE.N _ = true at h1
  have h2 := CFSG.KS.Raw.Orb.allN_iff.1 h1 ib hib
  have hxb' := (comm_iff hxi (hcT ib hib)).2 (by rw [eb]; exact hcomm x b hxb)
  have hab' := (comm_iff (hcT ia hia) (hcT ib hib)).2 (by rw [ea, eb]; exact hcomm a b hab)
  rw [hxb'] at h2
  change bIf(m305comm (IE.T ia) (IE.T ib), _, true) = true at h2
  rw [hab'] at h2
  change bIf(Nat.beq (IE.T ib) (IE.T ia), true, _) = true at h2
  have back : ∀ y z : Equiv.Perm (Fin 275), c * y * c⁻¹ = c * z * c⁻¹ → y = z := by
    intro y z e
    calc y = c⁻¹ * (c * y * c⁻¹) * c := by group
      _ = c⁻¹ * (c * z * c⁻¹) * c := by rw [e]
      _ = z := by group
  rcases bif_iff.1 h2 with ⟨h3, -⟩ | ⟨-, h3⟩
  · left
    have e := eq_of_beq (hcT ib hib) (hcT ia hia) h3
    rw [ea, eb] at e
    exact back b a e
  · right
    have e := eq_of_beq (hcT ib hib) (prep_mul (hcT ia hia) prep_cen4) h3
    rw [ea, eb, ← t0_eq] at e
    apply back
    rw [e]
    calc c * a * c⁻¹ * F.t0 = c * a * (c⁻¹ * F.t0) := by group
      _ = c * a * (F.t0 * c⁻¹) := by rw [(t0_comm (F.H.inv_mem hc)).symm]
      _ = c * (a * F.t0) * c⁻¹ := by group

@[expose] noncomputable def xP (k : Nat) : Equiv.Perm (Fin 275) := ((nthW xWd k).map gH).prod

theorem prep_xP (k : Nat) : PRep 275 9 (m305word hL (nthW xWd k)) (xP k) := prep_word prep_hL _

theorem xP_mem (k : Nat) : xP k ∈ F.H := word_mem _

theorem e8_fact : ∀ x ∈ F.H, ∀ a ∈ F.H, ∀ b ∈ F.H, x ≠ 1 → (∃ p ∈ [3, 5, 7], x ^ p = 1) →
    a * a = 1 → a ≠ 1 → a ≠ F.t0 → b * b = 1 → b ≠ 1 → b ≠ F.t0 → x * a = a * x →
    x * b = b * x → a * b = b * a → b = a ∨ b = a * F.t0 := by
  intro x hx a ha b hb hx1 ⟨p, hp, hxp⟩ ha2 ha1 hat hb2 hb1 hbt hxa hxb hab
  have hg := e8gens
  simp only [band] at hg
  obtain ⟨g5, g7, g3a, g3b, -, -⟩ := hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have hG : ∀ k < P3E.ng, PRep 275 9 (P3E.G k) ([xP 2, xP 3].getD k 1) := by
      intro k hk
      have hk2 : k < 2 := hk
      interval_cases k
      · rw [Nat.eq_of_beq_eq_true g3a]
        exact prep_xP 2
      · rw [Nat.eq_of_beq_eq_true g3b]
        exact prep_xP 3
    have hR := (CFSG.ClassicalInvolution.ListBridge.enum_closure P3E.ok rfl hG).2
    refine e8_at P3E.ok rfl hG e8c ?_ (IsPGroup.of_card (n := 2) (by rw [hR]; rfl))
      (m := 4480) (by norm_num) (by decide +kernel) hx ha hb hx1 hxp ha2 ha1 hat hb2 hb1 hbt hxa
      hxb hab
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact xP_mem 2
    · exact xP_mem 3
  · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hG : ∀ k < R5E.ng, PRep 275 9 (R5E.G k) ([xP 0].getD k 1) := by
      intro k hk
      have hk1 : k < 1 := hk
      interval_cases k
      rw [Nat.eq_of_beq_eq_true g5]
      exact prep_xP 0
    have hR := (CFSG.ClassicalInvolution.ListBridge.enum_closure R5E.ok rfl hG).2
    refine e8_at R5E.ok rfl hG e8a ?_ (IsPGroup.of_card (n := 1) (by rw [hR]; rfl))
      (m := 8064) (by norm_num) (by decide +kernel) hx ha hb hx1 hxp ha2 ha1 hat hb2 hb1 hbt hxa
      hxb hab
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rw [hg]
    exact xP_mem 0
  · have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have hG : ∀ k < R7E.ng, PRep 275 9 (R7E.G k) ([xP 1].getD k 1) := by
      intro k hk
      have hk1 : k < 1 := hk
      interval_cases k
      rw [Nat.eq_of_beq_eq_true g7]
      exact prep_xP 1
    have hR := (CFSG.ClassicalInvolution.ListBridge.enum_closure R7E.ok rfl hG).2
    refine e8_at R7E.ok rfl hG e8b ?_ (IsPGroup.of_card (n := 1) (by rw [hR]; rfl))
      (m := 5760) (by norm_num) (by decide +kernel) hx ha hb hx1 hxp ha2 ha1 hat hb2 hb1 hbt hxa
      hxb hab
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rw [hg]
    exact xP_mem 1

end CertificateChecks.KernelMcLCls

end
