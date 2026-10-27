module

public import Certificates.Kernel.P1L43.GlueBase
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic

set_option maxRecDepth 400000

public section


namespace CertificateChecks.KernelP1L43

open CFSG.ComponentClassification.HarrisLit.P1 CFSG.ComponentClassification.HarrisLit.P1.L43
  CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KC.Misc.ArrEnum CFSG.KC.OrbFind
  CFSG.KC.OrbGroup CFSG.KC.ConjOrb CFSG.KC.LeftOrb CFSG.KC.BfsPin CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native CFSG.Certificates Subgroup

theorem si {x : ℕ} (hx : x ∈ [UD, US, UDS, K2106.T K2106.r0, K2106.T K2106.r1, K2106.T K2106.r2,
    K5265.T K5265.r0, K5265.T K5265.r1, K5265.T K5265.r2, K1080.T K1080.r0, K10530.T K10530.r0,
    K117a.T K117a.r0, K117b.T K117b.r0, K8424.T K8424.r0]) : selfInv x = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, h⟩ := binds
  exact List.all_eq_true.1 h x hx

theorem tpR {T : Table} {P : ℕ} (hb : bindT T P = true) (hs : selfInv P = true) :
    tp 80 T = pp P :=
  (tp_of_bind hb (prep_si hs)).1

theorem gensK {G : ℕ → ℕ} (h0 : G 0 = K2106.G 0) (h1 : G 1 = K2106.G 1) :
    ∀ k < 2, PRep 80 7 (G k) (l43Gens k) := by
  intro k hk
  interval_cases k
  · rw [h0]
    exact gens2106 0 (by norm_num)
  · rw [h1]
    exact gens2106 1 (by norm_num)

theorem gens_eq :
    K5265.G 0 = K2106.G 0 ∧ K5265.G 1 = K2106.G 1 ∧ K1080.G 0 = K2106.G 0 ∧
      K1080.G 1 = K2106.G 1 ∧ K10530.G 0 = K2106.G 0 ∧ K10530.G 1 = K2106.G 1 ∧
      K117a.G 0 = K2106.G 0 ∧ K117a.G 1 = K2106.G 1 ∧ K117b.G 0 = K2106.G 0 ∧
      K117b.G 1 = K2106.G 1 ∧ K8424.G 0 = K2106.G 0 ∧ K8424.G 1 = K2106.G 1 := by
  obtain ⟨-, -, -, -, -, h0, h1, -⟩ := binds
  have e0 := fun x hx => Nat.eq_of_beq_eq_true (List.all_eq_true.1 h0 x hx)
  have e1 := fun x hx => Nat.eq_of_beq_eq_true (List.all_eq_true.1 h1 x hx)
  exact ⟨e0 _ (by simp), e1 _ (by simp), e0 _ (by simp), e1 _ (by simp), e0 _ (by simp),
    e1 _ (by simp), e0 _ (by simp), e1 _ (by simp), e0 _ (by simp), e1 _ (by simp),
    e0 _ (by simp), e1 _ (by simp)⟩

@[expose] def ClassF (N : ℕ) (T : ℕ → ℕ) (t : Equiv.Perm (Fin 80)) : Prop :=
  (conjClass pi.range t).ncard = N ∧
    N * Nat.card ↥(pi.range ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 80)))) = 6065280 ∧
    ∀ i < N, ∀ v, PRep 80 7 (T i) v → ∃ g ∈ pi.range, v = g * t * g⁻¹

theorem c2106_0 : ClassF K2106.N K2106.T (pp (K2106.T K2106.r0)) :=
  class_facts K2106.h gens2106 (fun i hi => K2106.cl i (lt_of_lt_of_le hi (by decide)))
    (fun i hi => K2106.tr0 i (lt_of_lt_of_le hi (by decide))) (by decide) (prep_si (si (by simp)))
    K2106.k

theorem c2106_1 : ClassF K2106.N K2106.T (pp (K2106.T K2106.r1)) :=
  class_facts K2106.h gens2106 (fun i hi => K2106.cl i (lt_of_lt_of_le hi (by decide)))
    (fun i hi => K2106.tr1 i (lt_of_lt_of_le hi (by decide))) (by decide) (prep_si (si (by simp)))
    K2106.k

theorem c2106_2 : ClassF K2106.N K2106.T (pp (K2106.T K2106.r2)) :=
  class_facts K2106.h gens2106 (fun i hi => K2106.cl i (lt_of_lt_of_le hi (by decide)))
    (fun i hi => K2106.tr2 i (lt_of_lt_of_le hi (by decide))) (by decide) (prep_si (si (by simp)))
    K2106.k

theorem c5265_0 : ClassF K5265.N K5265.T (pp (K5265.T K5265.r0)) :=
  class_facts K5265.h (gensK gens_eq.1 gens_eq.2.1)
    (fun i hi => K5265.cl i (lt_of_lt_of_le hi (by decide)))
    (fun i hi => K5265.tr0 i (lt_of_lt_of_le hi (by decide))) (by decide) (prep_si (si (by simp)))
    K5265.k

theorem c5265_1 : ClassF K5265.N K5265.T (pp (K5265.T K5265.r1)) :=
  class_facts K5265.h (gensK gens_eq.1 gens_eq.2.1)
    (fun i hi => K5265.cl i (lt_of_lt_of_le hi (by decide)))
    (fun i hi => K5265.tr1 i (lt_of_lt_of_le hi (by decide))) (by decide) (prep_si (si (by simp)))
    K5265.k

theorem c5265_2 : ClassF K5265.N K5265.T (pp (K5265.T K5265.r2)) :=
  class_facts K5265.h (gensK gens_eq.1 gens_eq.2.1)
    (fun i hi => K5265.cl i (lt_of_lt_of_le hi (by decide)))
    (fun i hi => K5265.tr2 i (lt_of_lt_of_le hi (by decide))) (by decide) (prep_si (si (by simp)))
    K5265.k

theorem c1080 : ClassF K1080.N K1080.T (pp (K1080.T K1080.r0)) :=
  class_facts K1080.h (gensK gens_eq.2.2.1 gens_eq.2.2.2.1)
    (fun i hi => K1080.cl i (lt_of_lt_of_le hi (by decide)))
    (fun i hi => K1080.tr0 i (lt_of_lt_of_le hi (by decide))) (by decide) (prep_si (si (by simp)))
    K1080.k

theorem c10530 : ClassF K10530.N K10530.T (pp (K10530.T K10530.r0)) :=
  class_facts K10530.h (gensK gens_eq.2.2.2.2.1 gens_eq.2.2.2.2.2.1)
    (fun i hi => K10530.cl i (lt_of_lt_of_le hi (by decide)))
    (fun i hi => K10530.tr0 i (lt_of_lt_of_le hi (by decide))) (by decide)
    (prep_si (si (by simp))) K10530.k

theorem c117a : ClassF K117a.N K117a.T (pp (K117a.T K117a.r0)) :=
  class_facts K117a.h (gensK gens_eq.2.2.2.2.2.2.1 gens_eq.2.2.2.2.2.2.2.1)
    (fun i hi => K117a.cl i (lt_of_lt_of_le hi (by decide)))
    (fun i hi => K117a.tr0 i (lt_of_lt_of_le hi (by decide))) (by decide)
    (prep_si (si (by simp))) K117a.k

theorem c117b : ClassF K117b.N K117b.T (pp (K117b.T K117b.r0)) :=
  class_facts K117b.h (gensK gens_eq.2.2.2.2.2.2.2.2.1 gens_eq.2.2.2.2.2.2.2.2.2.1)
    (fun i hi => K117b.cl i (lt_of_lt_of_le hi (by decide)))
    (fun i hi => K117b.tr0 i (lt_of_lt_of_le hi (by decide))) (by decide)
    (prep_si (si (by simp))) K117b.k

theorem c8424 : ClassF K8424.N K8424.T (pp (K8424.T K8424.r0)) :=
  class_facts K8424.h (gensK gens_eq.2.2.2.2.2.2.2.2.2.2.1 gens_eq.2.2.2.2.2.2.2.2.2.2.2)
    (fun i hi => K8424.cl i (lt_of_lt_of_le hi (by decide)))
    (fun i hi => K8424.tr0 i (lt_of_lt_of_le hi (by decide))) (by decide)
    (prep_si (si (by simp))) K8424.k

theorem mem_class {N : ℕ} {T S : ℕ → ℕ} {t : Equiv.Perm (Fin 80)} (hc : ClassF N T t) {v : ℕ}
    (hm : memK 80 7 ps N T S v = true) {s : Equiv.Perm (Fin 80)} (hs : PRep 80 7 v s) :
    ∃ g ∈ pi.range, s = g * t * g⁻¹ := by
  obtain ⟨j, hj, e⟩ := memK_spec hm
  exact hc.2.2 j hj s (e ▸ hs)

theorem test_of_cover {mem : ℕ → Bool} {N ng : ℕ} {G GI T E D S : ℕ → ℕ} {R : Run}
    (hc : coverK mem N T = true) (hh : headK 80 7 ng G GI = true)
    (hcl : ∀ i < N, closPtL 80 7 ng N G T E i = true)
    (htr : ∀ i < N, treePt ng N 0 E D i = true) (hN : 0 < N) (h0 : T 0 = pidn 80 7)
    (hK : distinctK N (fun i => pkeyK 80 7 ps (T i)) S = true)
    (hmem : ∀ v, mem v = true → ∀ s, PRep 80 7 v s →
      ∃ r ∈ R.rows, ∃ g ∈ pi.range, s = g * tp 80 r.row.rep * g⁻¹) :
    ∀ s ∈ closure ((fun k => pp (G k)) '' {k | k < ng}), orderOf s = 2 →
      ∃ r ∈ R.rows, ∃ g ∈ pi.range, s = g * tp 80 r.row.rep * g⁻¹ := by
  intro s hs hs2
  obtain ⟨i, hi, hPs⟩ := (group_facts hh hcl htr hN h0 hK).2 s hs
  unfold coverK at hc
  rw [CFSG.KS.Raw.Orb.allN_iff] at hc
  have h1 := hc i hi
  rw [strictB_eq', (isInvK_iff hn80 hPs).2 hs2, Bool.not_true, Bool.false_or] at h1
  exact hmem _ h1 s hPs

theorem ucl_of {mem : ℕ → Bool} {U P : ℕ} {R : Run} {T : Table} (hsU : selfInv U = true)
    (hbU : bindT R.u U = true) (hsP : selfInv P = true) (hbP : bindT T P = true)
    (hm : mem (pc U (pc P U)) = true)
    (hmem : ∀ v, mem v = true → ∀ s, PRep 80 7 v s →
      ∃ r ∈ R.rows, ∃ g ∈ pi.range, s = g * tp 80 r.row.rep * g⁻¹) :
    ∃ r' ∈ R.rows, ∃ g ∈ pi.range,
      tp 80 R.u * tp 80 T * (tp 80 R.u)⁻¹ = g * tp 80 r'.row.rep * g⁻¹ := by
  have hU := prep_si hsU
  have hP := prep_si hsP
  rw [tpR hbU hsU, tpR hbP hsP, inv_eq_of_mul_self (pp_mul_self hsU), mul_assoc]
  exact hmem _ hm _ (prep_pcomp hn80 hU (prep_pcomp hn80 hP hU))

theorem ucl_parts :
    (∀ t ∈ [K2106.T K2106.r0, K1080.T K1080.r0, K5265.T K5265.r0], memD (pc UD (pc t UD)) = true) ∧
    (∀ t ∈ [K2106.T K2106.r1, K10530.T K10530.r0, K5265.T K5265.r1, K117a.T K117a.r0,
      K117b.T K117b.r0], memS (pc US (pc t US)) = true) ∧
    (∀ t ∈ [K5265.T K5265.r2, K2106.T K2106.r2, K8424.T K8424.r0],
      memDS (pc UDS (pc t UDS)) = true) := by
  obtain ⟨h1, h2, h3⟩ := ucl
  unfold uclK at h1 h2 h3
  exact ⟨List.all_eq_true.1 h1, List.all_eq_true.1 h2, List.all_eq_true.1 h3⟩

theorem memRowD (v : ℕ) (hv : memD v = true) (s : Equiv.Perm (Fin 80)) (hs : PRep 80 7 v s) :
    ∃ r ∈ runuD.rows, ∃ g ∈ pi.range, s = g * tp 80 r.row.rep * g⁻¹ := by
  obtain ⟨-, -, -, -, -, -, -, b0, -, -, b2, -, -, b1, -⟩ := binds
  unfold memD at hv
  simp only [Bool.or_eq_true] at hv
  rcases hv with (h | h) | h
  · obtain ⟨g, hg, e⟩ := mem_class c2106_0 h hs
    have e' : s = g * tp 80 (tm 11821474) * g⁻¹ := by rw [tpR b0 (si (by simp))]; exact e
    exact ⟨_, .head _, g, hg, e'⟩
  · obtain ⟨g, hg, e⟩ := mem_class c5265_0 h hs
    have e' : s = g * tp 80 (tm 38855539) * g⁻¹ := by rw [tpR b2 (si (by simp))]; exact e
    exact ⟨_, .tail _ (.tail _ (.head _)), g, hg, e'⟩
  · obtain ⟨g, hg, e⟩ := mem_class c1080 h hs
    have e' : s = g * tp 80 (tm 14650228) * g⁻¹ := by rw [tpR b1 (si (by simp))]; exact e
    exact ⟨_, .tail _ (.head _), g, hg, e'⟩

theorem runFactsD : RunFacts pi.range runuD := by
  obtain ⟨bU, -, -, bA, bB, -, -, b0, -, -, b2, -, -, b1, -, -, -, -, g00, g01, g10, g11, g20,
    g21, -⟩ := binds
  have hsU : selfInv UD = true := si (by simp)
  have hcard := (group_facts SD.h (fun i hi => SD.cl i (lt_of_lt_of_le hi (by decide)))
    (fun i hi => SD.tr i (lt_of_lt_of_le hi (by decide))) (by decide) (by decide +kernel)
    SD.k).1
  refine runFacts_of bU hsU (by decide +kernel) bA bB runs.1 SD.h hcard ?_ ?_ ?_
  · intro hout r hr
    have hUo : ∀ u, some UD = some u → ∃ σ, PRep 80 7 u σ ∧ σ ∉ pi.range := by
      rintro u ⟨⟩
      exact ⟨pp UD, prep_si hsU, hout⟩
    obtain ⟨r0, r1, r2, -⟩ := rows
    simp only [runuD, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact row_of_check (si (by simp)) b0 r0 (by simp) (by rfl) (by rfl) g00 g01 CD0.h
        (fun i hi => CD0.cl i (lt_of_lt_of_le hi (by decide)))
        (fun i hi => CD0.tr i (lt_of_lt_of_le hi (by decide))) (by decide +kernel) CD0.k
        ⟨c2106_0.1, c2106_0.2.1⟩ (by rfl)
    · exact row_of_check (si (by simp)) b1 r1 hUo (by rfl) (by rfl) g10 g11 CD1.h
        (fun i hi => CD1.cl i (lt_of_lt_of_le hi (by decide)))
        (fun i hi => CD1.tr i (lt_of_lt_of_le hi (by decide))) (by decide +kernel) CD1.k
        ⟨c1080.1, c1080.2.1⟩ (by rfl)
    · exact row_of_check (si (by simp)) b2 r2 (by simp) (by rfl) (by rfl) g20 g21 CD2.h
        (fun i hi => CD2.cl i (lt_of_lt_of_le hi (by decide)))
        (fun i hi => CD2.tr i (lt_of_lt_of_le hi (by decide))) (by decide +kernel) CD2.k
        ⟨c5265_0.1, c5265_0.2.1⟩ (by rfl)
  · exact test_of_cover coverD SD.h (fun i hi => SD.cl i (lt_of_lt_of_le hi (by decide)))
      (fun i hi => SD.tr i (lt_of_lt_of_le hi (by decide))) (by decide) (by decide +kernel) SD.k
      memRowD
  · intro r hr
    simp only [runuD, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ucl_of hsU bU (si (by simp)) b0 (ucl_parts.1 _ (by simp)) memRowD
    · exact ucl_of hsU bU (si (by simp)) b1 (ucl_parts.1 _ (by simp)) memRowD
    · exact ucl_of hsU bU (si (by simp)) b2 (ucl_parts.1 _ (by simp)) memRowD

theorem memRowS (v : ℕ) (hv : memS v = true) (s : Equiv.Perm (Fin 80)) (hs : PRep 80 7 v s) :
    ∃ r ∈ runuS.rows, ∃ g ∈ pi.range, s = g * tp 80 r.row.rep * g⁻¹ := by
  obtain ⟨-, -, -, -, -, -, -, -, b0, -, -, b2, -, -, b1, b3, b4, -⟩ := binds
  unfold memS at hv
  simp only [Bool.or_eq_true] at hv
  rcases hv with (((h | h) | h) | h) | h
  · obtain ⟨g, hg, e⟩ := mem_class c2106_1 h hs
    have e' : s = g * tp 80 (tm 40942156) * g⁻¹ := by rw [tpR b0 (si (by simp))]; exact e
    exact ⟨_, .head _, g, hg, e'⟩
  · obtain ⟨g, hg, e⟩ := mem_class c5265_1 h hs
    have e' : s = g * tp 80 (tm 28874841) * g⁻¹ := by rw [tpR b2 (si (by simp))]; exact e
    exact ⟨_, .tail _ (.tail _ (.head _)), g, hg, e'⟩
  · obtain ⟨g, hg, e⟩ := mem_class c10530 h hs
    have e' : s = g * tp 80 (ts 6629227) * g⁻¹ := by rw [tpR b1 (si (by simp))]; exact e
    exact ⟨_, .tail _ (.head _), g, hg, e'⟩
  · obtain ⟨g, hg, e⟩ := mem_class c117a h hs
    have e' : s = g * tp 80 (ts 12439050) * g⁻¹ := by rw [tpR b3 (si (by simp))]; exact e
    exact ⟨_, .tail _ (.tail _ (.tail _ (.head _))), g, hg, e'⟩
  · obtain ⟨g, hg, e⟩ := mem_class c117b h hs
    have e' : s = g * tp 80 (ts 12940497) * g⁻¹ := by rw [tpR b4 (si (by simp))]; exact e
    exact ⟨_, .tail _ (.tail _ (.tail _ (.tail _ (.head _)))), g, hg, e'⟩

theorem runFactsS : RunFacts pi.range runuS := by
  obtain ⟨-, bU, -, bA, bB, -, -, -, b0, -, -, b2, -, -, b1, b3, b4, -, -, -, -, -, -, -, g00,
    g01, g10, g11, g20, g21, g30, g31, g40, g41, -⟩ := binds
  have hsU : selfInv US = true := si (by simp)
  have hcard := (group_facts SS.h (fun i hi => SS.cl i (lt_of_lt_of_le hi (by decide)))
    (fun i hi => SS.tr i (lt_of_lt_of_le hi (by decide))) (by decide) (by decide +kernel)
    SS.k).1
  refine runFacts_of bU hsU (by decide +kernel) bA bB runs.2.1 SS.h hcard ?_ ?_ ?_
  · intro hout r hr
    have hUo : ∀ u, some US = some u → ∃ σ, PRep 80 7 u σ ∧ σ ∉ pi.range := by
      rintro u ⟨⟩
      exact ⟨pp US, prep_si hsU, hout⟩
    obtain ⟨-, -, -, r0, r1, r2, r3, r4, -⟩ := rows
    simp only [runuS, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact row_of_check (si (by simp)) b0 r0 (by simp) (by rfl) (by rfl) g00 g01 CS0.h
        (fun i hi => CS0.cl i (lt_of_lt_of_le hi (by decide)))
        (fun i hi => CS0.tr i (lt_of_lt_of_le hi (by decide))) (by decide +kernel) CS0.k
        ⟨c2106_1.1, c2106_1.2.1⟩ (by rfl)
    · exact row_of_check (si (by simp)) b1 r1 hUo (by rfl) (by rfl) g10 g11 CS1.h
        (fun i hi => CS1.cl i (lt_of_lt_of_le hi (by decide)))
        (fun i hi => CS1.tr i (lt_of_lt_of_le hi (by decide))) (by decide +kernel) CS1.k
        ⟨c10530.1, c10530.2.1⟩ (by rfl)
    · exact row_of_check (si (by simp)) b2 r2 (by simp) (by rfl) (by rfl) g20 g21 CS2.h
        (fun i hi => CS2.cl i (lt_of_lt_of_le hi (by decide)))
        (fun i hi => CS2.tr i (lt_of_lt_of_le hi (by decide))) (by decide +kernel) CS2.k
        ⟨c5265_1.1, c5265_1.2.1⟩ (by rfl)
    · exact row_of_check (si (by simp)) b3 r3 hUo (by rfl) (by rfl) g30 g31 CS3.h
        (fun i hi => CS3.cl i (lt_of_lt_of_le hi (by decide)))
        (fun i hi => CS3.tr i (lt_of_lt_of_le hi (by decide))) (by decide +kernel) CS3.k
        ⟨c117a.1, c117a.2.1⟩ (by rfl)
    · exact row_of_check (si (by simp)) b4 r4 hUo (by rfl) (by rfl) g40 g41 CS4.h
        (fun i hi => CS4.cl i (lt_of_lt_of_le hi (by decide)))
        (fun i hi => CS4.tr i (lt_of_lt_of_le hi (by decide))) (by decide +kernel) CS4.k
        ⟨c117b.1, c117b.2.1⟩ (by rfl)
  · exact test_of_cover coverS SS.h (fun i hi => SS.cl i (lt_of_lt_of_le hi (by decide)))
      (fun i hi => SS.tr i (lt_of_lt_of_le hi (by decide))) (by decide) (by decide +kernel) SS.k
      memRowS
  · intro r hr
    simp only [runuS, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ucl_of hsU bU (si (by simp)) b0 (ucl_parts.2.1 _ (by simp)) memRowS
    · exact ucl_of hsU bU (si (by simp)) b1 (ucl_parts.2.1 _ (by simp)) memRowS
    · exact ucl_of hsU bU (si (by simp)) b2 (ucl_parts.2.1 _ (by simp)) memRowS
    · exact ucl_of hsU bU (si (by simp)) b3 (ucl_parts.2.1 _ (by simp)) memRowS
    · exact ucl_of hsU bU (si (by simp)) b4 (ucl_parts.2.1 _ (by simp)) memRowS

theorem memRowDS (v : ℕ) (hv : memDS v = true) (s : Equiv.Perm (Fin 80)) (hs : PRep 80 7 v s) :
    ∃ r ∈ runuDS.rows, ∃ g ∈ pi.range, s = g * tp 80 r.row.rep * g⁻¹ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, b1, -, -, b0, -, -, -, -, b2, -⟩ := binds
  unfold memDS at hv
  simp only [Bool.or_eq_true] at hv
  rcases hv with (h | h) | h
  · obtain ⟨g, hg, e⟩ := mem_class c2106_2 h hs
    have e' : s = g * tp 80 (tm 12703935) * g⁻¹ := by rw [tpR b1 (si (by simp))]; exact e
    exact ⟨_, .tail _ (.head _), g, hg, e'⟩
  · obtain ⟨g, hg, e⟩ := mem_class c5265_2 h hs
    have e' : s = g * tp 80 (tm 28777033) * g⁻¹ := by rw [tpR b0 (si (by simp))]; exact e
    exact ⟨_, .head _, g, hg, e'⟩
  · obtain ⟨g, hg, e⟩ := mem_class c8424 h hs
    have e' : s = g * tp 80 (ts 7174611) * g⁻¹ := by rw [tpR b2 (si (by simp))]; exact e
    exact ⟨_, .tail _ (.tail _ (.head _)), g, hg, e'⟩

theorem runFactsDS : RunFacts pi.range runuDS := by
  obtain ⟨-, -, bU, bA, bB, -, -, -, -, b1, -, -, b0, -, -, -, -, b2, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, g00, g01, g10, g11, g20, g21, -⟩ := binds
  have hsU : selfInv UDS = true := si (by simp)
  have hcard := (group_facts SDS.h (fun i hi => SDS.cl i (lt_of_lt_of_le hi (by decide)))
    (fun i hi => SDS.tr i (lt_of_lt_of_le hi (by decide))) (by decide) (by decide +kernel)
    SDS.k).1
  refine runFacts_of bU hsU (by decide +kernel) bA bB runs.2.2 SDS.h hcard ?_ ?_ ?_
  · intro hout r hr
    have hUo : ∀ u, some UDS = some u → ∃ σ, PRep 80 7 u σ ∧ σ ∉ pi.range := by
      rintro u ⟨⟩
      exact ⟨pp UDS, prep_si hsU, hout⟩
    obtain ⟨-, -, -, -, -, -, -, -, r0, r1, r2⟩ := rows
    simp only [runuDS, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact row_of_check (si (by simp)) b0 r0 (by simp) (by rfl) (by rfl) g00 g01 CDS0.h
        (fun i hi => CDS0.cl i (lt_of_lt_of_le hi (by decide)))
        (fun i hi => CDS0.tr i (lt_of_lt_of_le hi (by decide))) (by decide +kernel) CDS0.k
        ⟨c5265_2.1, c5265_2.2.1⟩ (by rfl)
    · exact row_of_check (si (by simp)) b1 r1 (by simp) (by rfl) (by rfl) g10 g11 CDS1.h
        (fun i hi => CDS1.cl i (lt_of_lt_of_le hi (by decide)))
        (fun i hi => CDS1.tr i (lt_of_lt_of_le hi (by decide))) (by decide +kernel) CDS1.k
        ⟨c2106_2.1, c2106_2.2.1⟩ (by rfl)
    · exact row_of_check (si (by simp)) b2 r2 hUo (by rfl) (by rfl) g20 g21 CDS2.h
        (fun i hi => CDS2.cl i (lt_of_lt_of_le hi (by decide)))
        (fun i hi => CDS2.tr i (lt_of_lt_of_le hi (by decide))) (by decide +kernel) CDS2.k
        ⟨c8424.1, c8424.2.1⟩ (by rfl)
  · exact test_of_cover coverDS SDS.h (fun i hi => SDS.cl i (lt_of_lt_of_le hi (by decide)))
      (fun i hi => SDS.tr i (lt_of_lt_of_le hi (by decide))) (by decide) (by decide +kernel) SDS.k
      memRowDS
  · intro r hr
    simp only [runuDS, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ucl_of hsU bU (si (by simp)) b0 (ucl_parts.2.2 _ (by simp)) memRowDS
    · exact ucl_of hsU bU (si (by simp)) b1 (ucl_parts.2.2 _ (by simp)) memRowDS
    · exact ucl_of hsU bU (si (by simp)) b2 (ucl_parts.2.2 _ (by simp)) memRowDS

theorem l43_runFacts : ∀ R ∈ l43Runs, RunFacts pi.range R := by
  intro R hR
  simp only [l43Runs, List.mem_cons, List.not_mem_nil, or_false] at hR
  rcases hR with rfl | rfl | rfl
  · exact runFactsD
  · exact runFactsS
  · exact runFactsDS

end CertificateChecks.KernelP1L43

end
