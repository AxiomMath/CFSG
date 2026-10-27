module

public import Certificates.Kernel.HN1408.XCentFacts
public import Certificates.Kernel.HN1408.CzInvFacts
public import Certificates.Kernel.HN1408.TabXCntFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.XCentSpec
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.XCent

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.KD.HN1408.CzT CFSG.EvenSporadicStandard.HNRecog.Section4.XModel

#kc_forall_chunks good_all (fun r => goodD r = true) 6 CFSG.KD.HN1408.ch441898.good 1
#kc_forall_chunks scan_all (fun r => scanD r = true) 6 CFSG.KD.HN1408.ch441898.scan 1
#kc_forall_chunks cnt_all (fun r => cntD r = true) 6 CFSG.KD.HN1408.ch441898.cnt 1

theorem ncard_cent_conj {G : Type} [Group G] (H : Subgroup G) {T R h : G} (hh : h ∈ H)
    (e : T * h = h * R) :
    {g | g ∈ H ∧ g * T = T * g}.ncard = {g | g ∈ H ∧ g * R = R * g}.ncard := by
  have hT : T = h * R * h⁻¹ := by rw [← e]; group
  subst hT
  have hs : {g | g ∈ H ∧ g * (h * R * h⁻¹) = h * R * h⁻¹ * g} =
      (fun g => h * g * h⁻¹) '' {g | g ∈ H ∧ g * R = R * g} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hg, hc⟩
      refine ⟨h⁻¹ * g * h, ⟨H.mul_mem (H.mul_mem (H.inv_mem hh) hg) hh, ?_⟩, by group⟩
      have e1 : h⁻¹ * g * h * R = h⁻¹ * (g * (h * R * h⁻¹)) * h := by group
      rw [e1, hc]
      group
    · rintro ⟨g', ⟨hg', hc'⟩, rfl⟩
      refine ⟨H.mul_mem (H.mul_mem hh hg') (H.inv_mem hh), ?_⟩
      have e1 : h * g' * h⁻¹ * (h * R * h⁻¹) = h * (g' * R) * h⁻¹ := by group
      rw [e1, hc']
      group
  rw [hs, Set.ncard_image_of_injective _ fun a b hab => by simpa using hab]

def HiiP {G : Type} [Group G] (H N : Subgroup G) (T : G) : Prop :=
  ∀ g ∈ H, (∀ x ∈ N, x * T = T * x → g * x = x * g) →
    ∃ z₀ ∈ N, (∀ x ∈ N, z₀ * x = x * z₀) ∧ (g = z₀ ∨ g = z₀ * T)

def Ha1P {G : Type} [Group G] (H N : Subgroup G) (T : G) : Prop :=
  ∀ y ∈ H, ∃ n ∈ N, ∃ c ∈ H, c * T = T * c ∧ y = n * c

theorem hii_conj {G : Type} [Group G] {H N : Subgroup G}
    (hN : ∀ g ∈ H, ∀ n ∈ N, g * n * g⁻¹ ∈ N) {T R h : G} (hh : h ∈ H) (e : T * h = h * R)
    (hR : HiiP H N R) : HiiP H N T := by
  have hT : T = h * R * h⁻¹ := by rw [← e]; group
  subst hT
  intro g hg hc
  have hg' : h⁻¹ * g * h ∈ H := H.mul_mem (H.mul_mem (H.inv_mem hh) hg) hh
  obtain ⟨z, hz, hzc, hgz⟩ := hR _ hg' (fun x hx hxR => by
    have hx' : h * x * h⁻¹ ∈ N := hN h hh x hx
    have hxT : h * x * h⁻¹ * (h * R * h⁻¹) = h * R * h⁻¹ * (h * x * h⁻¹) := by
      have e1 : h * x * h⁻¹ * (h * R * h⁻¹) = h * (x * R) * h⁻¹ := by group
      rw [e1, hxR]
      group
    have h1 := hc _ hx' hxT
    have e1 : h⁻¹ * g * h * x = h⁻¹ * (g * (h * x * h⁻¹)) * h := by group
    rw [e1, h1]
    group)
  refine ⟨h * z * h⁻¹, hN h hh z hz, fun x hx => ?_, ?_⟩
  · have hx' : h⁻¹ * x * h⁻¹⁻¹ ∈ N := hN h⁻¹ (H.inv_mem hh) x hx
    have h1 := hzc _ hx'
    have e1 : h * z * h⁻¹ * x = h * (z * (h⁻¹ * x * h⁻¹⁻¹)) * h⁻¹ := by group
    rw [e1, h1]
    group
  · rcases hgz with h1 | h1
    · left
      have e1 : g = h * (h⁻¹ * g * h) * h⁻¹ := by group
      rw [e1, h1]
    · right
      have e1 : g = h * (h⁻¹ * g * h) * h⁻¹ := by group
      rw [e1, h1]
      group

theorem ha1_conj {G : Type} [Group G] {H N : Subgroup G}
    (hN : ∀ g ∈ H, ∀ n ∈ N, g * n * g⁻¹ ∈ N) {T R h : G} (hh : h ∈ H) (e : T * h = h * R)
    (hR : Ha1P H N R) : Ha1P H N T := by
  have hT : T = h * R * h⁻¹ := by rw [← e]; group
  subst hT
  intro y hy
  obtain ⟨n, hn, c, hc, hcR, hyc⟩ := hR _ (H.mul_mem (H.mul_mem (H.inv_mem hh) hy) hh)
  refine ⟨h * n * h⁻¹, hN h hh n hn, h * c * h⁻¹, H.mul_mem (H.mul_mem hh hc) (H.inv_mem hh),
    ?_, ?_⟩
  · have e1 : h * c * h⁻¹ * (h * R * h⁻¹) = h * (c * R) * h⁻¹ := by group
    rw [e1, hcR]
    group
  · have e1 : y = h * (h⁻¹ * y * h) * h⁻¹ := by group
    rw [e1, hyc]
    group

theorem repC_u1 : RepC (G 0) (elemW xU1) := by
  have e : classz.centGens.getD 0 [] = xU1 := by rw [classz_centGens]; rfl
  have h := repC_G (l := 0) (by norm_num)
  rwa [e] at h

theorem repC_u2 : RepC (G 1) (elemW xU2) := by
  have e : classz.centGens.getD 1 [] = xU2 := by rw [classz_centGens]; rfl
  have h := repC_G (l := 1) (by norm_num)
  rwa [e] at h

theorem closure_u (hP : Nat.card ↥P1408 = 177408000) :
    closure ({elemW xU1, elemW xU2} : Set (Equiv.Perm (Fin 1408))) =
      P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) := by
  rw [← (czT_eq hP).1, czC, classz_centGens]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨xU1, Or.inl rfl, rfl⟩
    · exact ⟨xU2, Or.inr rfl, rfl⟩
  · rintro ⟨w, hw | hw, rfl⟩
    · exact Or.inl (by rw [hw])
    · exact Or.inr (by rw [hw])

theorem norm_gen {Et : Nat → Nat} (h : xcNorm Et = true) {l k : Nat} (hl : l < 2) (hk : k < 2) :
    Nat.beq (pc (G l) (CT k)) (pc (Et (Nat.add 8 (Nat.add (Nat.mul 4 l) (Nat.mul 2 k)))) (G l)) =
        true ∧
      Nat.beq (pc (CT k) (G l))
        (pc (G l) (Et (Nat.succ (Nat.add 8 (Nat.add (Nat.mul 4 l) (Nat.mul 2 k)))))) = true := by
  unfold xcNorm at h
  have h1 := allN_spec h l hl
  simp only [strictB_app] at h1
  exact mkA (allN_spec h1 k hk)

theorem conj_pair {u c e e' : Equiv.Perm (Fin 1408)} (he : e ∈ nC) (he' : e' ∈ nC)
    (h1 : u * c = e * u) (h2 : c * u = u * e') : u * c * u⁻¹ ∈ nC ∧ u⁻¹ * c * u ∈ nC := by
  refine ⟨?_, ?_⟩
  · rw [h1, mul_inv_cancel_right]
    exact he
  · rw [mul_assoc, h2, inv_mul_cancel_left]
    exact he'

theorem norm_lk {l k : Nat} (hl : l < 2) (hk : k < 2) {u c : Equiv.Perm (Fin 1408)}
    (hu : RepC (G l) u) (hc : RepC (CT k) c) : u * c * u⁻¹ ∈ nC ∧ u⁻¹ * c * u ∈ nC := by
  have hn : Nat.add 8 (Nat.add (Nat.mul 4 l) (Nat.mul 2 k)) < 45 := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  obtain ⟨a, b⟩ := norm_gen norm_ok hl hk
  have s1 := eP_spec (k := Nat.add 8 (Nat.add (Nat.mul 4 l) (Nat.mul 2 k))) (by omega)
  have s2 := eP_spec (k := Nat.succ (Nat.add 8 (Nat.add (Nat.mul 4 l) (Nat.mul 2 k))))
    (by omega)
  exact conj_pair s1.1 s2.1 (eq_of_beq_pc hu hc s1.2 hu a) (eq_of_beq_pc hc hu hu s2.2 b)

theorem norm_nC (hP : Nat.card ↥P1408 = 177408000) :
    ∀ g ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))), ∀ n ∈ nC,
      g * n * g⁻¹ ∈ nC := by
  rw [← closure_u hP]
  refine Section4.normalized_of_gen ?_
  intro u hu c hc
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hc
  rcases hu with rfl | rfl <;> rcases hc with rfl | rfl
  · exact norm_lk (by norm_num) (by norm_num) repC_u1 repC_c1
  · exact norm_lk (by norm_num) (by norm_num) repC_u1 repC_c2
  · exact norm_lk (by norm_num) (by norm_num) repC_u2 repC_c1
  · exact norm_lk (by norm_num) (by norm_num) repC_u2 repC_c2

theorem repC_repT {c : Nat} (hq : fd (CzInv.R c) 0 < 1280) (hq' : fd (CzInv.R c) 1 < 24) :
    RepC (repT CzInv.R c) (CzInv.repE c) := by
  rw [repT.eq_1, TabX.strictN_eq']
  exact repC_pc (t0P_spec hq).2 (t1P_spec hq').2

theorem good_gen {Et Rc : Nat → Nat} {r : Nat} (h : xcGood Et Rc r = true) :
    commP (Et (Nat.add 16 (Nat.mul 5 r))) (repT Rc (good r)) = true ∧
      commP (Et (Nat.add (Nat.add 16 (Nat.mul 5 r)) 1)) (repT Rc (good r)) = true ∧
      commP (Et (Nat.add (Nat.add 16 (Nat.mul 5 r)) 2)) (repT Rc (good r)) = true ∧
      commP (pc (G 0) (Et (Nat.add (Nat.add 16 (Nat.mul 5 r)) 3))) (repT Rc (good r)) = true ∧
      commP (pc (G 1) (Et (Nat.add (Nat.add 16 (Nat.mul 5 r)) 4))) (repT Rc (good r)) = true := by
  unfold xcGood at h
  simp only [strictB_app] at h
  obtain ⟨a, h⟩ := mkA h
  obtain ⟨b, h⟩ := mkA h
  obtain ⟨c, h⟩ := mkA h
  obtain ⟨d, f⟩ := mkA h
  exact ⟨a, b, c, d, f⟩

theorem scan_gen {Et Rc : Nat → Nat} {r : Nat} (h : xcScan Et Rc r = true) :
    czScan T0 T1 (cutRow Et (Et (Nat.add 16 (Nat.mul 5 r)))
      (Et (Nat.add (Nat.add 16 (Nat.mul 5 r)) 1)) (Et (Nat.add (Nat.add 16 (Nat.mul 5 r)) 2))
      (repT Rc (good r))) = true := by
  unfold xcScan at h
  simp only [strictB_app] at h
  exact h

theorem cutRow_of {Et : Nat → Nat} {K₀ K₁ K₂ R A B : Nat}
    (h : cutRow Et K₀ K₁ K₂ R A B = true)
    (h0 : commB A B K₀ (pt A (pt B 0)) (pt A (pt B 1)) = true)
    (h1 : commB A B K₁ (pt A (pt B 0)) (pt A (pt B 1)) = true)
    (h2 : commB A B K₂ (pt A (pt B 0)) (pt A (pt B 1)) = true) :
    inZ Et R (pt A (pt B 0)) (pt A (pt B 1)) = true := by
  unfold cutRow at h
  simp only [strictB_app] at h
  rcases mkIf h with ⟨-, h⟩ | ⟨hf, -⟩
  · exact h
  · rw [h0, h1, h2] at hf
    exact absurd hf (by decide)

theorem inZ_of {Et : Nat → Nat} {R g0 g1 : Nat} (h : inZ Et R g0 g1 = true) :
    ∃ k < 8, isBase g0 g1 (pt (Et k) 0) (pt (Et k) 1) = true ∨
      isBase g0 g1 (pt (Et k) (pt R 0)) (pt (Et k) (pt R 1)) = true := by
  unfold inZ at h
  simp only [Bool.not_eq_true'] at h
  by_contra hne
  push Not at hne
  have ha : allN 8 (fun k => strictB (Et k) fun Zk =>
      !(bIf(isBase g0 g1 (pt Zk 0) (pt Zk 1), true,
        isBase g0 g1 (pt Zk (pt R 0)) (pt Zk (pt R 1))))) = true := by
    refine Orb.allN_iff.2 fun k hk => ?_
    simp only [strictB_app]
    obtain ⟨a, b⟩ := hne k hk
    rw [Bool.eq_false_iff.2 a, Bool.eq_false_iff.2 b]
    rfl
  rw [ha] at h
  exact absurd h (by decide)

theorem nC_le' : nC ≤ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) := nC_le

theorem central_eP {k : Nat} (hk : k < 8) : ∀ x ∈ nC, eP k * x = x * eP k := by
  intro x hx
  refine (commute_of_mem_closure (a := eP k) ?_ hx).symm
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl
  · exact (center_eP hk).1.symm
  · exact (center_eP hk).2.symm

theorem bnd {r : Nat} (hr : r < 6) :
    Nat.add 16 (Nat.mul 5 r) < 46 ∧ Nat.add (Nat.add 16 (Nat.mul 5 r)) 1 < 46 ∧
      Nat.add (Nat.add 16 (Nat.mul 5 r)) 2 < 46 ∧ Nat.add (Nat.add 16 (Nat.mul 5 r)) 3 < 46 ∧
      Nat.add (Nat.add 16 (Nat.mul 5 r)) 4 < 46 := by
  simp only [Nat.add_eq, Nat.mul_eq]
  omega

theorem hii_rep (hP : Nat.card ↥P1408 = 177408000) {r c : Nat} (hr : r < 6) (hc : good r = c)
    (hq : fd (CzInv.R c) 0 < 1280) (hq' : fd (CzInv.R c) 1 < 24) :
    HiiP (P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408)))) nC (CzInv.repE c) := by
  subst hc
  have hR := repC_repT hq hq'
  obtain ⟨b0, b1, b2, -, -⟩ := bnd hr
  obtain ⟨g0, g1, g2, -, -⟩ := good_gen (Et := E) (Rc := CzInv.R) (good_all r hr)
  have s0 := eP_spec b0
  have s1 := eP_spec b1
  have s2 := eP_spec b2
  have hs := scan_gen (Et := E) (Rc := CzInv.R) (scan_all r hr)
  intro g hg hcent
  have k0 := hcent _ s0.1 (comm_of_commP s0.2 hR g0)
  have k1 := hcent _ s1.1 (comm_of_commP s1.2 hR g1)
  have k2 := hcent _ s2.1 (comm_of_commP s2.2 hR g2)
  obtain ⟨i, hi, j, hj, rfl⟩ := (mem_iff hP).1 hg
  have hev : ∀ y (hy : y < 1408), pt (T0 i) (pt (T1 j) y) = ((t0P i * t1P j) ⟨y, hy⟩).val :=
    fun y hy => ev_eq hi hj hy
  obtain ⟨k, hk, e | e⟩ := inZ_of (cutRow_of (czScan_spec hs i hi j hj)
    (commB_of hev s0.2 k0) (commB_of hev s1.2 k1) (commB_of hev s2.2 k2))
  · have sk := eP_spec (k := k) (by omega)
    exact ⟨eP k, sk.1, central_eP hk, Or.inl (base_eq hP hg (nC_le sk.1) hev
      (repC_pt sk.2 _).symm (repC_pt sk.2 _).symm e)⟩
  · have sk := eP_spec (k := k) (by omega)
    have hm : eP k * CzInv.repE (good r) ∈
        P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) :=
      mul_mem (nC_le sk.1) (CzInv.mem_cz hP hq hq')
    have hp := repC_pc sk.2 hR
    have v0 : ((eP k * CzInv.repE (good r)) ⟨0, by norm_num⟩).val =
        pt (E k) (pt (repT CzInv.R (good r)) 0) := by
      rw [← pt_pc sk.2.1 (by norm_num)]
      exact (repC_pt hp _).symm
    have v1 : ((eP k * CzInv.repE (good r)) ⟨1, by norm_num⟩).val =
        pt (E k) (pt (repT CzInv.R (good r)) 1) := by
      rw [← pt_pc sk.2.1 (by norm_num)]
      exact (repC_pt hp _).symm
    exact ⟨eP k, sk.1, central_eP hk, Or.inr (base_eq hP hg hm hev v0 v1 e)⟩

theorem decomp_u (hP : Nat.card ↥P1408 = 177408000) {u m R : Equiv.Perm (Fin 1408)}
    (hu : u ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408)))) (hm : m ∈ nC)
    (hc : u * m * R = R * (u * m)) :
    ∃ n ∈ nC, ∃ c ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) ⊓
      centralizer ({R} : Set (Equiv.Perm (Fin 1408))), u = n * c := by
  refine ⟨u * m⁻¹ * u⁻¹, norm_nC hP u hu _ (inv_mem hm), u * m,
    mem_inf.2 ⟨mul_mem hu (nC_le hm), mem_centralizer_singleton_iff.2 hc⟩, by group⟩

theorem ha1_rep (hP : Nat.card ↥P1408 = 177408000) {r c : Nat} (hr : r < 6) (hc : good r = c)
    (hq : fd (CzInv.R c) 0 < 1280) (hq' : fd (CzInv.R c) 1 < 24) :
    Ha1P (P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408)))) nC (CzInv.repE c) := by
  subst hc
  have hR := repC_repT hq hq'
  obtain ⟨-, -, -, b3, b4⟩ := bnd hr
  obtain ⟨-, -, -, g3, g4⟩ := good_gen (Et := E) (Rc := CzInv.R) (good_all r hr)
  have s3 := eP_spec b3
  have s4 := eP_spec b4
  have hu1 : elemW xU1 ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) := by
    rw [← closure_u hP]
    exact subset_closure (by simp)
  have hu2 : elemW xU2 ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) := by
    rw [← closure_u hP]
    exact subset_closure (by simp)
  have d1 := decomp_u hP hu1 s3.1 (comm_of_commP (repC_pc repC_u1 s3.2) hR g3)
  have d2 := decomp_u hP hu2 s4.1 (comm_of_commP (repC_pc repC_u2 s4.2) hR g4)
  have hN : ∀ g ∈ closure ({elemW xU1, elemW xU2} : Set (Equiv.Perm (Fin 1408))), ∀ n ∈ nC,
      g * n * g⁻¹ ∈ nC := by
    rw [closure_u hP]
    exact norm_nC hP
  have hC : P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) ⊓
      centralizer ({CzInv.repE (good r)} : Set (Equiv.Perm (Fin 1408))) ≤
        closure ({elemW xU1, elemW xU2} : Set (Equiv.Perm (Fin 1408))) := by
    rw [closure_u hP]
    exact inf_le_left
  have hall := Section4.exists_mul_of_gen hN hC d1 d2
  intro y hy
  rw [← closure_u hP] at hy
  obtain ⟨n, hn, c, hc, rfl⟩ := hall y hy
  obtain ⟨hcX, hcR⟩ := mem_inf.1 hc
  exact ⟨n, hn, c, hcX, mem_centralizer_singleton_iff.1 hcR, rfl⟩

theorem foldr_add (g : Nat → Nat) : ∀ (L : List Nat) (s : Nat),
    L.foldr (fun j s => s + g j) s = s + (L.map g).sum
  | [], s => by simp
  | j :: L, s => by
    rw [List.foldr_cons, foldr_add g L s, List.map_cons, List.sum_cons]
    ring

theorem range_sum (g : Nat → Nat) : ∀ n, ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, range_sum g n, Finset.sum_range_succ]
    simp

theorem cntRow_eq (R A s : Nat) :
    cntRow R A s = s + ((Finset.range 24).filter fun j =>
      commB A (T1 j) R (pt A (pt (T1 j) 0)) (pt A (pt (T1 j) 1)) = true).card := by
  have hf : (fun j s => strictN (T1 j) fun B =>
      nIf(commB A B R (pt A (pt B 0)) (pt A (pt B 1)), Nat.succ s, s)) =
      fun j s => s + (if commB A (T1 j) R (pt A (pt (T1 j) 0)) (pt A (pt (T1 j) 1)) = true
        then 1 else 0) := by
    funext j s
    rw [TabX.strictN_eq']
    cases commB A (T1 j) R (pt A (pt (T1 j) 0)) (pt A (pt (T1 j) 1)) <;> rfl
  rw [cntRow.eq_1, Orb.foldN_eq, hf, foldr_add, range_sum, Finset.card_filter]

theorem czSet_sum (F : Nat → Nat → Bool) : ∀ n, (TabX.czSet T0 T1 F n).card =
    ∑ i ∈ Finset.range n, ((Finset.range 24).filter fun j => F (T0 i) (T1 j) = true).card
  | 0 => by
    rw [Finset.sum_range_zero]
    exact (TabX.czCnt_rec T0 T1 F 0).symm
  | n + 1 => by rw [TabX.czSet_succ, czSet_sum F n, Finset.sum_range_succ]

theorem cntC_eq (R : Nat) :
    cntC R = TabX.czCnt T0 T1 fun A B => commB A B R (pt A (pt B 0)) (pt A (pt B 1)) := by
  have hf : (fun i s => strictN (T0 i) fun A => cntRow R A s) =
      fun i s => s + ((Finset.range 24).filter fun j =>
        commB (T0 i) (T1 j) R (pt (T0 i) (pt (T1 j) 0)) (pt (T0 i) (pt (T1 j) 1)) = true).card := by
    funext i s
    rw [TabX.strictN_eq', cntRow_eq]
  rw [TabX.czCnt_eq, czSet_sum, cntC.eq_1, Orb.foldN_eq, hf, foldr_add, range_sum, zero_add]

theorem card_rep (hP : Nat.card ↥P1408 = 177408000) {c : Nat} (hq : fd (CzInv.R c) 0 < 1280)
    (hq' : fd (CzInv.R c) 1 < 24) :
    {g | g ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) ∧
      g * CzInv.repE c = CzInv.repE c * g}.ncard = cntC (repT CzInv.R c) := by
  rw [cntC_eq]
  exact TabX.ncard_eq_czCnt hP (Q := fun g => g * CzInv.repE c = CzInv.repE c * g)
    (fun i hi j hj => TabX.commB_iff hP (repC_repT hq hq') (CzInv.mem_cz hP hq hq') hi hj)

theorem card_bad (hP : Nat.card ↥P1408 = 177408000) {r c : Nat} (hr : r < 6) (hc : bad r = c)
    (hq : fd (CzInv.R c) 0 < 1280) (hq' : fd (CzInv.R c) 1 < 24) :
    {g | g ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) ∧
      g * CzInv.repE c = CzInv.repE c * g}.ncard = badN r := by
  subst hc
  rw [card_rep hP hq hq']
  have h := cnt_all r hr
  rw [cntD.eq_1, xcCnt.eq_1] at h
  exact Nat.eq_of_beq_eq_true h

theorem xCent_core (hP : Nat.card ↥P1408 = 177408000) {T : Equiv.Perm (Fin 1408)}
    (hT : T ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408)))) (hT2 : T * T = 1)
    (hcard : {g | g ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) ∧
        g * T = T * g}.ncard = 768 ∨
      {g | g ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) ∧
        g * T = T * g}.ncard = 384) :
    HiiP (P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408)))) nC T ∧
      Ha1P (P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408)))) nC T := by
  have hT1 : T ≠ 1 := by
    rintro rfl
    have hs : {g | g ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) ∧
        g * 1 = 1 * g} = ↑(P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408)))) := by
      ext g
      simp
    have hc : (↑(P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408)))) :
        Set (Equiv.Perm (Fin 1408))).ncard = 30720 := by
      rw [← Nat.card_coe_set_eq, ← (czT_eq hP).1]
      exact (czT_eq hP).2
    rw [hs, hc] at hcard
    omega
  obtain ⟨c, hc, hq, hq', h, hh, e⟩ := CzInv.inv_conj hP hT hT2 hT1
  rw [ncard_cent_conj _ hh e] at hcard
  have hN := norm_nC hP
  have fin : ∀ r < 6, good r = c →
      HiiP (P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408)))) nC T ∧
        Ha1P (P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408)))) nC T :=
    fun r hr hgc => ⟨hii_conj hN hh e (hii_rep hP hr hgc hq hq'),
      ha1_conj hN hh e (ha1_rep hP hr hgc hq hq')⟩
  have bad_ne : ∀ r < 6, bad r = c → badN r ≠ 768 ∧ badN r ≠ 384 → False := by
    intro r hr hbc hne
    rw [card_bad hP hr hbc hq hq'] at hcard
    omega
  interval_cases c
  · exact (bad_ne 0 (by norm_num) rfl (by decide)).elim
  · exact (bad_ne 1 (by norm_num) rfl (by decide)).elim
  · exact (bad_ne 2 (by norm_num) rfl (by decide)).elim
  · exact fin 0 (by norm_num) rfl
  · exact fin 1 (by norm_num) rfl
  · exact fin 2 (by norm_num) rfl
  · exact fin 3 (by norm_num) rfl
  · exact (bad_ne 3 (by norm_num) rfl (by decide)).elim
  · exact (bad_ne 4 (by norm_num) rfl (by decide)).elim
  · exact fin 4 (by norm_num) rfl
  · exact fin 5 (by norm_num) rfl
  · exact (bad_ne 5 (by norm_num) rfl (by decide)).elim

theorem xCentK : Nat.card ↥P1408 = 177408000 → ∀ T : ↥XP, T * T = 1 →
    (Nat.card ↥(centralizer ({T} : Set ↥XP)) = 768 ∨
      Nat.card ↥(centralizer ({T} : Set ↥XP)) = 384) →
    (∀ g ∈ XP, (∀ x ∈ closure ({elemW xC1, elemW xC2} : Set (Equiv.Perm (Fin 1408))),
        x * (T : Equiv.Perm (Fin 1408)) = T * x → g * x = x * g) →
      ∃ z₀ ∈ closure ({elemW xC1, elemW xC2} : Set (Equiv.Perm (Fin 1408))),
        (∀ x ∈ closure ({elemW xC1, elemW xC2} : Set (Equiv.Perm (Fin 1408))),
          z₀ * x = x * z₀) ∧ (g = z₀ ∨ g = z₀ * T)) ∧
    (∀ y ∈ XP, ∃ n ∈ closure ({elemW xC1, elemW xC2} : Set (Equiv.Perm (Fin 1408))),
      ∃ c ∈ XP, c * (T : Equiv.Perm (Fin 1408)) = T * c ∧ y = n * c) := by
  intro hP T hT2 hcard
  rw [card_cent_eq] at hcard
  exact xCent_core hP T.2 (congrArg Subtype.val hT2) hcard

end CFSG.KD.HN1408.XCent

end
