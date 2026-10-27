module

public import Certificates.Data.TwoF4LocCheck
public import Certificates.Data.TitsLocData
public import CFSG.Sporadic.Schreier.TitsActionCheckInputs
public import CFSG.Sporadic.Schreier.TitsCentralCheckInputs
public import Certificates.Certificate4180
public import CFSG.Sporadic.Schreier.TitsCert
public import Certificates.Kernel.TwoF4Lie.Glue
import all Certificates.Kernel.TwoF4Lie.Glue
import Certificates.Kernel.TitsLoc.Checks
import Certificates.Kernel.TitsLoc.Gens
import CFSG.Certificates.Kernel.TitsLocSound
import CFSG.Sporadic.Schreier.TitsInv
import CFSG.Sporadic.Schreier.TitsIso
import CFSG.Sporadic.Schreier.TitsLocal
import CFSG.Sporadic.Schreier.TitsAbelCheckInputs
meta import CFSG.Sporadic.Schreier.TitsData
meta import CFSG.Sporadic.Schreier.TitsArrays
meta import CFSG.Sporadic.Schreier.TitsBasic
meta import CFSG.Sporadic.Schreier.TitsCertCheck
meta import CFSG.Sporadic.Schreier.TitsLocalCheck
meta import CFSG.Sporadic.Schreier.TitsEnum
meta import CFSG.Sporadic.Schreier.TitsCentralCheck
meta import Certificates.Data.CFSGNative.Schreier.Check
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
import CFSG.Sporadic.Schreier.TitsInvCheckInputs
meta import CFSG.Sporadic.Schreier.TitsAbelCheck
public import Certificates.Certificate4182Base
public import Certificates.Certificate7050Base
public import Certificates.Data.CFSGNative.Schreier.Check

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsLoc

open CFSG.KC.Enum CFSG.KS CFSG.KC.TwoF4LieK CFSG.KC.TitsLocK CFSG.KD.TwoF4Lie CFSG.KD.TitsLoc
  CFSG.KC.TwoF4LieSound CFSG.KC.TitsLocSound CFSG.Sporadic.Schreier.Tits
  CFSG.Quasithin.RuType.J47 CertificateChecks.KernelMisc CertificateChecks.KernelSporSch.TitsAction
  CertificateChecks.KernelSporSch CertificateChecks.KernelTwoF4Lie

open CFSG.Quasithin (twoF4S)

open scoped Pointwise

local notation "tK" => Certificates.c4180T

local notation "cK" => Certificates.c4180C

theorem gen_sq : ∀ h < 4, h ≠ 1 → titsGen h * titsGen h = 1 := by
  intro h hh h1
  have hg := ch4182_gens
  simp only [bAnd_eq', Bool.and_eq_true] at hg
  have key : ∀ h < 4, Nat.beq (mul (F h) (F h)) idP = true → titsGen h * titsGen h = 1 := by
    intro h hh e
    have hP := prep_mul (hF h hh) (hF h hh)
    rw [Nat.eq_of_beq_eq_true e] at hP
    exact CFSG.KC.EnumSound.prep_unique hP prep_idP
  interval_cases h
  · exact key 0 (by norm_num) hg.1
  · exact absurd rfl h1
  · exact key 2 (by norm_num) hg.2.1
  · exact key 3 (by norm_num) hg.2.2

theorem mem_D_of_sq {x : Pm} (hx : x ∈ titsA) (h2 : x * x = 1) : x ∈ titsD := by
  by_cases h1 : x = 1
  · rw [h1]
    exact titsD.one_mem
  · exact titsA_involution_mem_D hx (orderOf_eq_prime (by rw [sq]; exact h2) h1)

theorem wordP_mem_D {w : List ℕ} (h : wordD w = true) : wordP titsGen w ∈ titsD := by
  obtain ⟨hc, he⟩ := wordD_sound h
  exact wordP_mem_of_even titsD_index (fun _ hh => titsGen_mem_titsA hh)
    (fun h hh h1 => mem_D_of_sq (titsGen_mem_titsA hh) (gen_sq h hh h1)) hc he

theorem conj_mem_D {m x : Pm} (hm : m ∈ titsA) (hx : x ∈ titsD) : m * x * m⁻¹ ∈ titsD := by
  have := titsD_normal_A.conj_mem ⟨x, titsD_le_titsA hx⟩ (Subgroup.mem_subgroupOf.2 hx) ⟨m, hm⟩
  simpa [Subgroup.mem_subgroupOf] using this

theorem t_eq : wordP titsGen tW = tK := by
  rw [dTC.2.2.1]
  simp [wordP, letP, Certificates.c4180T, mul_assoc]

theorem c_eq : wordP titsGen cW = cK := by
  rw [dTC.2.2.2]
  simp [wordP, letP, Certificates.c4180C, mul_assoc]

theorem q_eq : wordP titsGen qW = Certificates.c4182Q := by
  have e : qW = [6, 4, 4, 6, 8, 2, 9] := by decide +kernel
  rw [e]
  simp [wordP, letP, Certificates.c4182Q, mul_assoc]

theorem t_mem_D : tK ∈ titsD := t_eq ▸ wordP_mem_D ch4182_tD

theorem c_mem_A : cK ∈ titsA := c_eq ▸ codes_mem dTC.2.1

theorem cc_eq : cK * cK = cK⁻¹ := by
  refine (inv_eq_of_mul_eq_one_right ?_).symm
  have h := cFacts'.1
  rw [pow_succ, pow_two] at h
  rw [← mul_assoc]
  exact h

noncomputable abbrev SD : Subgroup Pm := twoF4S ⊓ titsD

theorem S_of {x : Pm} (hx : x ∈ twoF4S) (hD : x ∈ titsD) : Certificates.c4182S x :=
  ⟨hD, (mem_twoF4S_iff (twoF4S_le_A hx)).1 hx⟩

theorem SD_of {x : Pm} (h : Certificates.c4182S x) : x ∈ SD :=
  Subgroup.mem_inf.2 ⟨mem_S_of (titsD_le_titsA h.1) h.2, h.1⟩

theorem z_SD : titsZ ∈ SD := by
  refine Subgroup.mem_inf.2 ⟨?_, titsZ_mem_titsD⟩
  rw [← root0_eq]
  exact twoF4S.mul_mem (aE_spec dR.1).1 (bE_spec dR.2.1).1

theorem t_SD : tK ∈ SD := Subgroup.mem_inf.2 ⟨t_mem, t_mem_D⟩

theorem conj_of_row (hS : Nat.card twoF4S = 4096) {r : List ℕ} (hr : RowOK r)
    (h : rowF F TGI TA TB lpK base r = true) :
    aE (r.getD 0 0) * bE (r.getD 1 0) = wordP titsGen (r.drop 4) *
      (aE (r.getD 2 0) * bE (r.getD 3 0)) * (wordP titsGen (r.drop 4))⁻¹ ∧
      QS (wordP titsGen (r.drop 4)) := by
  obtain ⟨h0, h1, h2, h3, hc⟩ := hr
  obtain ⟨hy0, hyL, hyb, hW⟩ := rowF_sound hF hFI hc (aE_spec h0).2 (bE_spec h1).2
    (aE_spec h2).2 (bE_spec h3).2 (fun k hk => lpK_lt hk) h
  have hWA := codes_mem hc
  have hxS := twoF4S.mul_mem (aE_spec h0).1 (bE_spec h1).1
  have hpS := twoF4S.mul_mem (aE_spec h2).1 (bE_spec h3).1
  have hyA : (wordP titsGen (r.drop 4))⁻¹ * (aE (r.getD 0 0) * bE (r.getD 1 0)) *
      wordP titsGen (r.drop 4) ∈ titsA :=
    titsA.mul_mem (titsA.mul_mem (titsA.inv_mem hWA) (twoF4S_le_A hxS)) hWA
  have hyS := mem_S_of hyA ⟨hy0, smul_eq_of_maps fun p hp => (onL0_iff _).1 (hyL p
    ((onL0_iff p).2 hp))⟩
  have e := faithful hS hyS hpS hyb
  refine ⟨?_, ?_⟩
  · rw [← e]
    group
  · rcases hW with hW | hW
    · exact Or.inl hW
    · exact Or.inr (smul_eq_of_maps fun p hp => (onL0_iff _).1 (hW p ((onL0_iff p).2 hp)))

def ReachD (k : ℕ) : Prop := ∀ i < 64, ∀ j < 64, 64 * i + j = k →
  Relation.ReflTransGen (StepR SD titsD QS) titsZ (aE i * bE j) ∨
    Relation.ReflTransGen (StepR SD titsD QS) tK (aE i * bE j)

theorem mem_of_rtg {a x : Pm} (h : Relation.ReflTransGen (StepR SD titsD QS) a x) (ha : a ∈ SD) :
    x ∈ SD := by
  induction h with
  | refl => exact ha
  | tail _ hbc _ => exact hbc.2.1

theorem idx_of_nodeOf {r : List ℕ} {i j : ℕ} (hj : j < 64) (hr : r.getD 1 0 < 64)
    (e : 64 * i + j = nodeOf r) : i = r.getD 0 0 ∧ j = r.getD 1 0 := by
  unfold nodeOf at e
  rw [headD_eq, tail_headD_eq] at e
  simp only [Nat.add_eq, Nat.mul_eq] at e
  omega

theorem reachD_root0 : ReachD (nodeOf r0) := by
  intro i hi j hj e
  have hr := dR
  obtain ⟨rfl, rfl⟩ := idx_of_nodeOf hj (by rw [← tail_headD_eq]; exact hr.2.1) e
  rw [← headD_eq, ← tail_headD_eq, root0_eq]
  exact Or.inl Relation.ReflTransGen.refl

theorem reachD_root1 : ReachD (nodeOf r1) := by
  intro i hi j hj e
  have hr := dR
  obtain ⟨rfl, rfl⟩ := idx_of_nodeOf hj (by rw [← tail_headD_eq]; exact hr.2.2.2) e
  rw [← headD_eq, ← tail_headD_eq, root1_eq]
  exact Or.inr Relation.ReflTransGen.refl

theorem dFD : ∀ r ∈ fD, r.getD 0 0 < 64 ∧ r.getD 1 0 < 64 ∧ r.getD 2 0 < 64 ∧
    r.getD 3 0 < 64 ∧ ∀ c ∈ r.drop 4, 2 ≤ c ∧ c < 10 := by decide +kernel

def RowD (r : List ℕ) : Prop := RowOK r ∧ wordD (r.drop 4) = true

theorem rowD_fD : ∀ r ∈ fD, RowD r := fun r hr =>
  ⟨dFD r hr, List.all_eq_true.1 ch4182_forD r hr⟩

theorem reachD_step (hS : Nat.card twoF4S = 4096) (r : List ℕ) (hr : RowD r)
    (h : rowF F TGI TA TB lpK base r = true)
    (hp : ReachD (Nat.add (Nat.mul 64 (r.getD 2 0)) (r.getD 3 0))) : ReachD (nodeOf r) := by
  intro i hi j hj e
  obtain ⟨hrok, hwd⟩ := hr
  obtain ⟨h0, h1, h2, h3, -⟩ := id hrok
  obtain ⟨rfl, rfl⟩ := idx_of_nodeOf hj h1 e
  obtain ⟨hx, hQ⟩ := conj_of_row hS hrok h
  have hWD := wordP_mem_D hwd
  have hst (a : Pm) (ha : a ∈ SD) (hpa : Relation.ReflTransGen (StepR SD titsD QS) a
      (aE (r.getD 2 0) * bE (r.getD 3 0))) :
      Relation.ReflTransGen (StepR SD titsD QS) a (aE (r.getD 0 0) * bE (r.getD 1 0)) := by
    have hpSD := mem_of_rtg hpa ha
    have hxD : aE (r.getD 0 0) * bE (r.getD 1 0) ∈ titsD := by
      rw [hx]
      exact titsD.mul_mem (titsD.mul_mem hWD (Subgroup.mem_inf.1 hpSD).2) (titsD.inv_mem hWD)
    have hxSD : aE (r.getD 0 0) * bE (r.getD 1 0) ∈ SD := Subgroup.mem_inf.2
      ⟨twoF4S.mul_mem (aE_spec h0).1 (bE_spec h1).1, hxD⟩
    exact hpa.tail ⟨hpSD, hxSD, _, hWD, hQ, hx⟩
  rcases hp _ h2 _ h3 rfl with hz | ht
  · exact Or.inl (hst _ z_SD hz)
  · exact Or.inr (hst _ t_SD ht)

theorem nodeReachD (hS : Nat.card twoF4S = 4096) : ∀ k ∈ nodesD, ReachD k := by
  have hacc0 : ∀ k ∈ [nodeOf r1, nodeOf r0], ReachD k := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · exact reachD_root1
    · exact reachD_root0
  have h0 := reach_forK (Rw := RowD) (reachD_step hS) (fD.take 71) _
    (fun r hr => rowD_fD r (List.mem_of_mem_take hr)) hacc0 ch4182_for0
  have h1 := reach_forK (Rw := RowD) (reachD_step hS) (fD.drop 71) _
    (fun r hr => rowD_fD r (List.mem_of_mem_drop hr)) (by
      intro k hk
      rcases List.mem_append.1 hk with hk | hk
      · exact h0 k (List.mem_append_right _ (List.mem_reverse.1 hk))
      · exact hacc0 k hk) ch4182_for1
  intro k hk
  unfold nodesD at hk
  rcases List.mem_cons.1 hk with rfl | hk
  · exact reachD_root0
  rcases List.mem_cons.1 hk with rfl | hk
  · exact reachD_root1
  rw [← List.take_append_drop 71 fD, List.map_append] at hk
  rcases List.mem_append.1 hk with hk | hk
  · exact h0 k (List.mem_append_right _ hk)
  · exact h1 k (List.mem_append_right _ hk)

theorem chainD (hS : Nat.card twoF4S = 4096) : ∀ x, Certificates.c4182S x → x * x = 1 → x ≠ 1 →
    Relation.ReflTransGen Certificates.c4182Step titsZ x ∨
      Relation.ReflTransGen Certificates.c4182Step tK x := by
  intro x hx h2 h1
  have hcov : ∀ i < 64, ∀ j < 64, aE i * bE j * (aE i * bE j) ≠ 1 ∨ 64 * i + j = 0 ∨
      ReachD (64 * i + j) := by
    intro i hi j hj
    rcases covNodes i hi j hj with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (nodeReachD hS _
        (memK_iff.1 (List.all_eq_true.1 ch4182_nodes _ h))))
  have hlift : ∀ {a b : Pm}, Relation.ReflTransGen (StepR SD titsD QS) a b →
      Relation.ReflTransGen Certificates.c4182Step a b := by
    intro a b h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih =>
      obtain ⟨haS, hbS, c, hcD, hc, e⟩ := hbc
      exact ih.tail ⟨S_of (Subgroup.mem_inf.1 haS).1 (Subgroup.mem_inf.1 haS).2,
        S_of (Subgroup.mem_inf.1 hbS).1 (Subgroup.mem_inf.1 hbS).2, c, hcD, hc, e⟩
  rcases chain_of_cover (S := SD) (M := titsD) (Q := QS) (node := ReachD)
      (fun y hy => cover hS y (Subgroup.mem_inf.1 hy).1) aE_zero bE_zero hcov
      (fun i hi j hj h => h i hi j hj rfl) x (SD_of hx) h2 h1 with h | h
  · exact Or.inl (hlift h)
  · exact Or.inr (hlift h)

noncomputable def pairOf (q : ℕ × ℕ × ℕ × ℕ) : Pm × Pm :=
  (aE q.1 * bE q.2.1, aE q.2.2.1 * bE q.2.2.2)

def PairR (q q' : ℕ × ℕ × ℕ × ℕ) : Prop :=
  (pairOf q).1 ∈ titsD → (pairOf q).2 ∈ titsD → Certificates.c4182Pair (pairOf q) (pairOf q')

theorem pair_lift {a b : ℕ × ℕ × ℕ × ℕ} (h : Relation.ReflTransGen PairR a b)
    (h1 : (pairOf a).1 ∈ titsD) (h2 : (pairOf a).2 ∈ titsD) :
    Relation.ReflTransGen Certificates.c4182Pair (pairOf a) (pairOf b) ∧
      (pairOf b).1 ∈ titsD ∧ (pairOf b).2 ∈ titsD := by
  induction h with
  | refl => exact ⟨Relation.ReflTransGen.refl, h1, h2⟩
  | tail _ hbc ih =>
    obtain ⟨ch, hb1, hb2⟩ := ih
    have st := hbc hb1 hb2
    exact ⟨ch.tail st, st.2.2.1.1, st.2.2.2.1.1⟩

theorem dPC : ∀ k < 24, ∀ r ∈ pC.getD k [], 8 ≤ r.length ∧ (∀ i < 8, r.getD i 0 < 64) ∧
    ∀ c ∈ r.drop 8, 2 ≤ c ∧ c < 10 := by decide +kernel

theorem pairR_of_row (hS : Nat.card twoF4S = 4096) {r : List ℕ} (hlen : 8 ≤ r.length)
    (hb : ∀ i < 8, r.getD i 0 < 64) (hc : ∀ c ∈ r.drop 8, 2 ≤ c ∧ c < 10)
    (h : pairK F TGI TA TB lpK base r = true) :
    PairR (r.getD 2 0, r.getD 3 0, r.getD 6 0, r.getD 7 0)
      (r.getD 0 0, r.getD 1 0, r.getD 4 0, r.getD 5 0) := by
  obtain ⟨hd, h1, h2⟩ := pairK_sound h
  rcases r with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, _ | ⟨k, w⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at hlen <;> try omega
  have b0 : a < 64 := hb 0 (by norm_num)
  have b1 : b < 64 := hb 1 (by norm_num)
  have b2 : c < 64 := hb 2 (by norm_num)
  have b3 : d < 64 := hb 3 (by norm_num)
  have b4 : e < 64 := hb 4 (by norm_num)
  have b5 : f < 64 := hb 5 (by norm_num)
  have b6 : g < 64 := hb 6 (by norm_num)
  have b7 : k < 64 := hb 7 (by norm_num)
  obtain ⟨e1, q1⟩ : aE a * bE b = wordP titsGen w * (aE c * bE d) * (wordP titsGen w)⁻¹ ∧
      QS (wordP titsGen w) :=
    conj_of_row hS (r := [a, b, c, d] ++ w) ⟨b0, b1, b2, b3, hc⟩ h1
  obtain ⟨e2, -⟩ : aE e * bE f = wordP titsGen w * (aE g * bE k) * (wordP titsGen w)⁻¹ ∧
      QS (wordP titsGen w) :=
    conj_of_row hS (r := [e, f, g, k] ++ w) ⟨b4, b5, b6, b7, hc⟩ h2
  have hWD : wordP titsGen w ∈ titsD := wordP_mem_D hd
  unfold PairR pairOf
  intro hp1 hp2
  change aE c * bE d ∈ titsD at hp1
  change aE g * bE k ∈ titsD at hp2
  have hm (x y : ℕ) (hx : x < 64) (hy : y < 64) := twoF4S.mul_mem (aE_spec hx).1 (bE_spec hy).1
  have hcj (x : Pm) (hx : x ∈ titsD) : wordP titsGen w * x * (wordP titsGen w)⁻¹ ∈ titsD :=
    titsD.mul_mem (titsD.mul_mem hWD hx) (titsD.inv_mem hWD)
  refine ⟨S_of (hm c d b2 b3) hp1, S_of (hm g k b6 b7) hp2, S_of (hm a b b0 b1) ?_,
    S_of (hm e f b4 b5) ?_, _, hWD, q1, e1, e2⟩
  · change aE a * bE b ∈ titsD
    rw [e1]
    exact hcj _ hp1
  · change aE e * bE f ∈ titsD
    rw [e2]
    exact hcj _ hp2

theorem dUR : uR.length = 24 ∧ ∀ u ∈ uR, u.getD 1 0 < 64 ∧ u.getD 2 0 < 64 ∧
    ∀ c ∈ u.drop 3, 2 ≤ c ∧ c < 10 := by decide +kernel

theorem dER : ∀ k < 24, (eR.getD k []).getD 0 0 < 64 ∧ (eR.getD k []).getD 1 0 < 64 ∧
    (eR.getD k []).getD 2 0 < 1755 ∧ (eR.getD k []).getD 3 0 < 2925 := by decide +kernel

theorem locRow : ∀ k (hk : k < uR.length), uK F TGI TA TB lpK base TitsZ uR[k] = true ∧
    endK TA TB lpK (eR.getD k []) = true ∧
    pchK F TGI TA TB lpK base (r0.headD 0) (r0.tail.headD 0) ((eR.getD k []).headD 0)
      ((eR.getD k []).getD 1 0) (pC.getD k []) (uR[k].getD 1 0) (uR[k].getD 2 0) (r1.headD 0)
      (r1.tail.headD 0) = true := by
  intro k hk
  have hl := dUR.1
  by_cases h12 : k < 12
  · have := locK_sound ch4182_loc0 k (by rw [List.length_take]; omega)
    simp only [List.getElem_take, Nat.zero_add] at this
    exact this
  · have := locK_sound ch4182_loc1 (k - 12) (by rw [List.length_drop]; omega)
    simp only [List.getElem_drop, Nat.add_sub_cancel' (by omega : 12 ≤ k)] at this
    exact this

theorem mem_of_onLine {p w : ℕ} (hp : p < 1755) (hw : w < 2925) (h : onLine lpK p w = true) :
    (⟨p, hp⟩ : Fin 1755) ∈ titsLine ⟨w, hw⟩ := by
  rw [hline]
  unfold CFSG.KC.TwoF4LieK.onLine at h
  cases e0 : Nat.beq p (lpK (Nat.mul 3 w))
  · rw [e0] at h
    cases e1 : Nat.beq p (lpK (Nat.add (Nat.mul 3 w) 1))
    · rw [e1] at h
      exact ⟨2, by norm_num, (Nat.eq_of_beq_eq_true h).symm⟩
    · exact ⟨1, by norm_num, (Nat.eq_of_beq_eq_true e1).symm⟩
  · exact ⟨0, by norm_num, (Nat.eq_of_beq_eq_true e0).symm⟩

theorem rtg_congr {r : Pm × Pm → Pm × Pm → Prop} {a a' b b' : Pm × Pm}
    (h : Relation.ReflTransGen r a b) (ha : a = a') (hb : b = b') :
    Relation.ReflTransGen r a' b' := ha ▸ hb ▸ h

theorem moves_of_endK {e : List ℕ} (h0 : e.getD 0 0 < 64) (h1 : e.getD 1 0 < 64)
    (h2 : e.getD 2 0 < 1755)
    (h : gp (TA (e.getD 0 0)) (gp (TB (e.getD 1 0)) (e.getD 2 0)) ≠ e.getD 2 0) :
    (aE (e.getD 0 0) * bE (e.getD 1 0)) ⟨_, h2⟩ ≠ ⟨_, h2⟩ := by
  intro e'
  apply h
  have g1 : gp (TB (e.getD 1 0)) (e.getD 2 0) = (bE (e.getD 1 0) ⟨_, h2⟩ : ℕ) :=
    gp_eq (bE_spec h1).2 ⟨_, h2⟩
  have g2 : gp (TA (e.getD 0 0)) (bE (e.getD 1 0) ⟨_, h2⟩ : ℕ) =
      (aE (e.getD 0 0) (bE (e.getD 1 0) ⟨_, h2⟩) : ℕ) := gp_eq (aE_spec h0).2 _
  rw [g1, g2]
  exact congrArg Fin.val e'

theorem fixU (hS : Nat.card twoF4S = 4096) (k : ℕ) (hk : k < uR.length) :
    ∃ m ∈ titsA, (m 0 : ℕ) = uR[k].headD 0 ∧
      (Certificates.c4182S (m * titsZ * m⁻¹) ∧ ∃ b, Certificates.c4182S b ∧
        (∃ q, (∃ w : Fin 2925, (0 : Fin 1755) ∈ titsLine w ∧ q ∈ titsLine w) ∧ b q ≠ q) ∧
        Relation.ReflTransGen Certificates.c4182Pair (m * titsZ * m⁻¹, tK) (titsZ, b)) := by
  have hu : uR[k] ∈ uR := List.getElem_mem hk
  obtain ⟨hU, hE, hP⟩ := locRow k hk
  obtain ⟨hi, hj, hc⟩ := dUR.2 _ hu
  have hk24 : k < 24 := dUR.1 ▸ hk
  obtain ⟨hW0, hu0, huL, hub⟩ := uK_sound hF hFI hc prep_z (aE_spec hi).2 (bE_spec hj).2 hU
  set W := wordP titsGen (uR[k].drop 3) with hWdef
  have hWA : W ∈ titsA := codes_mem hc
  have hzA : titsZ ∈ titsA := titsD_le_titsA titsZ_mem_titsD
  have huA : W * titsZ * W⁻¹ ∈ titsA := titsA.mul_mem (titsA.mul_mem hWA hzA) (titsA.inv_mem hWA)
  have huS := mem_S_of huA ⟨hu0, smul_eq_of_maps fun p hp => (onL0_iff _).1 (huL p
    ((onL0_iff p).2 hp))⟩
  have hxS := twoF4S.mul_mem (aE_spec hi).1 (bE_spec hj).1
  have hux : W * titsZ * W⁻¹ = aE (uR[k].getD 1 0) * bE (uR[k].getD 2 0) :=
    faithful hS huS hxS hub
  have huD : W * titsZ * W⁻¹ ∈ titsD := conj_mem_D hWA titsZ_mem_titsD
  refine ⟨W, hWA, hW0, ?_⟩
  obtain ⟨he0, he1, he2, he3⟩ := dER k hk24
  have hR := pchK_sound (R := PairR) (pC.getD k []) _ _ _ _ (fun r hr h => by
    obtain ⟨hlen, hb, hc⟩ := dPC k hk24 r hr
    exact pairR_of_row hS hlen hb hc h) hP
  have hst : pairOf (uR[k].getD 1 0, uR[k].getD 2 0, r1.headD 0, r1.tail.headD 0) =
      (W * titsZ * W⁻¹, tK) := by
    simp only [pairOf]
    rw [← hux, root1_eq]
  have hen : pairOf (r0.headD 0, r0.tail.headD 0, (eR.getD k []).headD 0,
      (eR.getD k []).getD 1 0) = (titsZ, aE ((eR.getD k []).getD 0 0) *
        bE ((eR.getD k []).getD 1 0)) := by
    simp only [pairOf]
    rw [root0_eq, headD_eq]
  obtain ⟨hch, -, hbD⟩ := pair_lift hR
    ((congrArg (· ∈ titsD) (congrArg Prod.fst hst)).mpr huD)
    ((congrArg (· ∈ titsD) (congrArg Prod.snd hst)).mpr t_mem_D)
  replace hch := rtg_congr hch hst hen
  replace hbD := (congrArg (· ∈ titsD) (congrArg Prod.snd hen)).mp hbD
  obtain ⟨hmv, hl0, hlq⟩ := endK_sound hE
  exact ⟨S_of huS huD, _, S_of (twoF4S.mul_mem (aE_spec he0).1 (bE_spec he1).1) hbD,
    ⟨⟨_, he2⟩, ⟨⟨_, he3⟩, mem_of_onLine (by norm_num) he3 hl0, mem_of_onLine he2 he3 hlq⟩,
      moves_of_endK he0 he1 he2 hmv⟩, hch⟩

theorem fixD (hS : Nat.card twoF4S = 4096) : ∀ p : Fin 1755, tK p = p → ∃ m ∈ titsA, m 0 = p ∧
    (m * titsZ * m⁻¹ = titsZ ∨ m * titsZ * m⁻¹ = cK * titsZ * cK⁻¹ ∨
      m * titsZ * m⁻¹ = cK⁻¹ * titsZ * cK ∨
      (Certificates.c4182S (m * titsZ * m⁻¹) ∧ ∃ b, Certificates.c4182S b ∧
        (∃ q, (∃ w : Fin 2925, (0 : Fin 1755) ∈ titsLine w ∧ q ∈ titsLine w) ∧ b q ≠ q) ∧
        Relation.ReflTransGen Certificates.c4182Pair (m * titsZ * m⁻¹, tK) (titsZ, b))) := by
  intro p hp
  rcases fixK_sound prep_t prep_c ch4182_fix p hp with h | h | h | ⟨u, hu, hup⟩
  · refine ⟨1, titsA.one_mem, ?_, Or.inl (by simp)⟩
    rw [h, Equiv.Perm.one_apply]
  · exact ⟨cK, c_mem_A, h.symm, Or.inr (Or.inl rfl)⟩
  · refine ⟨cK * cK, titsA.mul_mem c_mem_A c_mem_A, ?_, Or.inr (Or.inr (Or.inl ?_))⟩
    · rw [h, Equiv.Perm.mul_apply]
    · rw [cc_eq, inv_inv]
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hu
  obtain ⟨m, hm, hm0, hrest⟩ := fixU hS k hk
  exact ⟨m, hm, Fin.ext (hm0.trans hup), Or.inr (Or.inr (Or.inr hrest))⟩

public theorem facts4182 (hS : Nat.card twoF4S = 4096) :
    tK ∈ titsD ∧
    (Certificates.c4182S Certificates.c4182Q ∧ Certificates.c4182Q * Certificates.c4182Q = titsZ ∧
      Certificates.c4182Q * tK = tK * Certificates.c4182Q ∧
      Certificates.c4182Q * (cK * titsZ * cK⁻¹) = cK * titsZ * cK⁻¹ * Certificates.c4182Q) ∧
    (∀ x, Certificates.c4182S x → x * x = 1 → x ≠ 1 →
      Relation.ReflTransGen Certificates.c4182Step titsZ x ∨
        Relation.ReflTransGen Certificates.c4182Step tK x) ∧
    ∀ p : Fin 1755, tK p = p → ∃ m ∈ titsA, m 0 = p ∧
      (m * titsZ * m⁻¹ = titsZ ∨ m * titsZ * m⁻¹ = cK * titsZ * cK⁻¹ ∨
        m * titsZ * m⁻¹ = cK⁻¹ * titsZ * cK ∨
        (Certificates.c4182S (m * titsZ * m⁻¹) ∧ ∃ b, Certificates.c4182S b ∧
          (∃ q, (∃ w : Fin 2925, (0 : Fin 1755) ∈ titsLine w ∧ q ∈ titsLine w) ∧ b q ≠ q) ∧
          Relation.ReflTransGen Certificates.c4182Pair (m * titsZ * m⁻¹, tK) (titsZ, b))) := by
  obtain ⟨hc, he, hs, h1, h2, h3⟩ := qK_sound hF hFI prep_z prep_t prep_c ch4182_q
  have hQ := wN_prep hF hFI qW hc
  rw [q_eq] at hQ h1 h2 h3
  have hqD : Certificates.c4182Q ∈ titsD := q_eq ▸ wordP_mem_of_even titsD_index
    (fun _ hh => titsGen_mem_titsA hh)
    (fun h hh h1 => mem_D_of_sq (titsGen_mem_titsA hh) (gen_sq h hh h1)) hc he
  refine ⟨t_mem_D, ⟨⟨hqD, stabS_sound hQ hs⟩, h1, h2, ?_⟩, chainD hS, fixD hS⟩
  rw [← cc_eq]
  simpa [mul_assoc] using h3

end CertificateChecks.KernelTitsLoc
