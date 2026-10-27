module

public import Certificates.Kernel.TitsN12.Checks
public import Certificates.Kernel.TitsN12.Walk
public import CFSG.Certificates.Kernel.Spor.PcompFacts
public import CFSG.Certificates.Kernel.Spor.SiftRSound
public import CFSG.Certificates.Kernel.TitsN12Sound
public import Certificates.Kernel.SporSch.Tits.Help
public import Certificates.Kernel.SporSch.Tits.Inv2266
public import Certificates.Kernel.TitsOct.Glue
public import Certificates.Certificate2263
public import CFSG.Sporadic.Schreier.TitsCentral
public import CFSG.Certificates.Kernel.SporSch.TitsCntSound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawSiftK
import Mathlib.Tactic.IntervalCases
public import Certificates.Certificate7050Base

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsN12

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.BfsPin
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Monster.B.Co2
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2264
open CertificateChecks.KernelSpor.Tits2268
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.TitsCommon
open CertificateChecks.KernelSporSch.TitsHelp
open CFSG.KC.TitsN12K CFSG.KC.TitsN12Sound
open scoped Pointwise

theorem strictB_eq7470 (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem allN_congr7470 {n : Nat} {f g : Nat → Bool} (h : ∀ i < n, f i = g i) :
    allN n f = allN n g := by
  cases hg : allN n g
  · cases hf : allN n f
    · rfl
    · have : allN n g = true := allN_of_forall fun i hi => by rw [← h i hi]; exact allN_spec hf i hi
      rw [this] at hg
      exact absurd hg (by decide)
  · exact allN_of_forall fun i hi => by rw [h i hi]; exact allN_spec hg i hi

section Congr

variable {BP : Nat} {f g : Nat → Nat} (hfg : ∀ i < 1755, f i = g i) (hg : ∀ i < 1755, g i < 1755)
  (hBP : ∀ t < 5, pg 11 (mask 11) BP t < 1755)
include hfg hg hBP

theorem sqB_congr : sqB BP f = sqB BP g := by
  unfold sqB
  refine allN_congr7470 fun t ht => ?_
  rw [strictB_eq7470, strictB_eq7470, hfg _ (hBP t ht), hfg _ (hg _ (hBP t ht))]

theorem n2T_congr : n2T BP f = n2T BP g := by
  unfold n2T
  rw [strictB_eq7470, strictB_eq7470, sqB_congr hfg hg hBP, hfg 0 (by norm_num),
    hfg _ (hg 0 (by norm_num))]

theorem restK_congr {a b : Nat} (ha : a < 1755) (hb : b < 1755) :
    restK BP a b f = restK BP a b g := by
  unfold restK
  rw [hfg a ha, hfg b hb, hfg 2 (by norm_num), hfg 0 (by norm_num), sqB_congr hfg hg hBP]

theorem swT_congr : swT BP f = swT BP g := by
  unfold swT
  rw [strictB_eq7470, strictB_eq7470, hfg 1 (by norm_num),
    restK_congr hfg hg hBP (a := 3) (b := 4) (by norm_num) (by norm_num),
    restK_congr hfg hg hBP (a := 5) (b := 7) (by norm_num) (by norm_num),
    restK_congr hfg hg hBP (a := 9) (b := 13) (by norm_num) (by norm_num),
    restK_congr hfg hg hBP (a := 17) (b := 25) (by norm_num) (by norm_num)]

end Congr

theorem bpH {t : Nat} (ht : t < 5) : pg 11 (mask 11) TitsH.BP t < 1755 := by
  rw [← bindsH.2.2.2.2.2.2 t ht]
  exact Raw.Orb.base_lt_of_levels bindsH TitsH.hl t ht

theorem bpN {t : Nat} (ht : t < 5) : pg 11 (mask 11) TitsN.BP t < 1755 := by
  rw [← bindsN.2.2.2.2.2.2 t ht]
  exact Raw.Orb.base_lt_of_levels bindsN TitsN.hl t ht

open CertificateChecks.KernelSporSch.TitsAction (lpK) in
theorem line_mem3 {v : Fin 2925} {p0 p1 p2 : Nat} (h0 : lpK (3 * (v : Nat)) = p0)
    (h1 : lpK (3 * (v : Nat) + 1) = p1) (h2 : lpK (3 * (v : Nat) + 2) = p2) (x : Fin 1755) :
    x ∈ titsLine v ↔ (x : Nat) = p0 ∨ (x : Nat) = p1 ∨ (x : Nat) = p2 := by
  rw [KernelTitsOct.lineK]
  constructor
  · rintro ⟨k, hk, e⟩
    interval_cases k
    · exact Or.inl (e.symm.trans h0)
    · exact Or.inr (Or.inl (e.symm.trans h1))
    · exact Or.inr (Or.inr (e.symm.trans h2))
  · rintro (e | e | e)
    · exact ⟨0, by norm_num, h0.trans e.symm⟩
    · exact ⟨1, by norm_num, h1.trans e.symm⟩
    · exact ⟨2, by norm_num, h2.trans e.symm⟩

open CertificateChecks.KernelSporSch.TitsAction (lpK) in
theorem line0 (x : Fin 1755) :
    x ∈ titsLine 0 ↔ (x : Nat) = 0 ∨ (x : Nat) = 1 ∨ (x : Nat) = 2 :=
  line_mem3 (v := 0) (by decide +kernel) (by decide +kernel) (by decide +kernel) x

theorem sq_of_sqB_N {a : Array Nat} {g : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a g)
    (hs : siftA 1755 titsNLevels (baseArr 1755 titsNBase) 0 a = true)
    (hq : sqB TitsN.BP (fun i => a[i]!) = true) : g * g = 1 := by
  obtain ⟨G, hmem, hsep⟩ := chain_group bindsN TitsN.head TitsN.hl (NS := 220) (CH := 8)
    (by norm_num) TitsN.hs TitsInv.ndN
  have hgG := (hmem _ _ ha).1 hs
  refine hsep _ (G.mul_mem hgG hgG) fun t ht hb => Fin.ext ?_
  have h1 := allN_spec hq t ht
  simp only [strictB_eq7470] at h1
  rw [← bindsN.2.2.2.2.2.2 t ht] at h1
  have h2 := Nat.eq_of_beq_eq_true h1
  rw [ha.apply hb, ha (g ⟨_, hb⟩)] at h2
  rw [Equiv.Perm.mul_apply]
  exact h2

theorem sqB_of_sq_N {a : Array Nat} {g : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a g)
    (hsq : g * g = 1) : sqB TitsN.BP (fun i => a[i]!) = true :=
  allN_of_forall fun t ht => by
    simp only [strictB_eq7470]
    have hb := bpN ht
    rw [ha.apply hb, ha (g ⟨_, hb⟩), ← Equiv.Perm.mul_apply, hsq]
    exact Nat.beq_refl _

@[expose] noncomputable def pN7 (a : Array Nat) : Bool := n2T TitsN.BP (fun i => a[i]!)

theorem survN : survivors5 1755 titsNLevels pN7 =
    SN.C.map (fun k => unpack 1755 11 (prodCode 1755 11 (mask 11) (1755 * 11) TitsN.LR TitsN.TR k)) :=
  survivors5_codes bindsN permN TitsN.hl (fun t0 t1 t2 t3 t4 c0 c1 c2 c3 c4 => by
    obtain ⟨-, hP⟩ := gpt_facts c0 c1 c2 c3 c4
    unfold PN pN7
    exact n2T_congr (fun i hi => (gptR_eq _ _ _ _ _ i).trans (hP i hi).1.symm)
      (fun i hi => lt_of_eq_of_lt (hP i hi).1 (hP i hi).2) fun _ ht => bpN ht) mN aN EN.all

theorem nBase : (finList 1755 titsNBase).length = 5 := by
  simp [finList, titsCentral_check.2.2.1]

theorem pN7_eq {a : Array Nat} {g : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a g) :
    pN7 a = bAnd(in2 1 2 (g 0 : Nat), bAnd(Nat.beq (g (g 0) : Nat) 0,
      sqB TitsN.BP (fun i => a[i]!))) := by
  have e0 : a[0]! = a[((0 : Fin 1755) : Nat)]! := rfl
  unfold pN7 n2T
  simp only [strictB_eq7470]
  rw [e0, ha 0, ha (g 0)]

theorem pN7_sound {a : Array Nat} {g : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a g)
    (hs : siftA 1755 titsNLevels (baseArr 1755 titsNBase) 0 a = true) (h : pN7 a = true) :
    g * g = 1 ∧ ((g 0 : Nat) = 1 ∨ (g 0 : Nat) = 2) ∧ g (g 0) = 0 := by
  rw [pN7_eq ha, bAnd_iff, bAnd_iff, in2_iff, beq_iff] at h
  exact ⟨sq_of_sqB_N ha hs h.2.2, h.1, Fin.ext h.2.1⟩

theorem pN7_of {a : Array Nat} {g : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a g) (hsq : g * g = 1)
    (h0 : (g 0 : Nat) = 1 ∨ (g 0 : Nat) = 2) (h1 : g (g 0) = 0) : pN7 a = true := by
  rw [pN7_eq ha, bAnd_iff, bAnd_iff, in2_iff, beq_iff, h1]
  exact ⟨h0, rfl, sqB_of_sq_N ha hsq⟩

theorem card_N2 (y : Fin 1755) (hy : y ∈ titsLine 0) (hy0 : y ≠ 0) :
    {g : Equiv.Perm (Fin 1755) | g ∈ titsN ∧ g * g = 1 ∧ g 0 = y ∧ g y = 0}.ncard = 64 := by
  have hy12 : (y : Nat) = 1 ∨ (y : Nat) = 2 := by
    rcases (line0 y).1 hy with h | h | h
    · exact absurd (Fin.ext h) hy0
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨hpr, hpw⟩ := surv5K_propsT pN7 bindsN permN TitsN.hl
  have hset : {g : Equiv.Perm (Fin 1755) | g ∈ titsN ∧ g * g = 1 ∧ g 0 = y ∧ g y = 0} =
      {g | g ∈ ((survivors5 1755 titsNLevels pN7).filter fun a => a[0]! == (y : Nat)).map
        (permOfArr 1755)} := by
    ext g
    simp only [Set.mem_setOf_eq, List.mem_map, List.mem_filter]
    constructor
    · rintro ⟨hgN, hsq, h0, hy'⟩
      have hgQ : g ∈ titsQN.originalSubgroup := by rw [titsQN_facts.2.2.1]; exact hgN
      obtain ⟨a, ha, hp⟩ := all5_spec titsN_chainArrays (by norm_num : 0 < 4)
        titsLocalChains_check.2.2.1 nBase (all5_surv titsNLevels pN7) hgQ
      have hpa : pN7 a = true := by
        refine pN7_of ha hsq ?_ ?_
        · rw [h0]
          exact hy12
        · rw [h0, hy']
      rw [hpa, Bool.not_true, Bool.false_or, anyEq, List.any_eq_true] at hp
      obtain ⟨w, hw, haw⟩ := hp
      have hwr := (rep_permOfArr (hpr w hw).1).1
      have e := eq_of_eqA ha hwr haw
      refine ⟨w, ⟨hw, ?_⟩, e.symm⟩
      have e00 : w[0]! = w[((0 : Fin 1755) : Nat)]! := rfl
      rw [beq_iff_eq, e00, hwr 0, ← e, h0]
    · rintro ⟨c, ⟨hc, hc0⟩, rfl⟩
      have hcr := (rep_permOfArr (hpr c hc).1).1
      have hs : siftA 1755 titsNLevels (baseArr 1755 titsNBase) 0 c = true := (hpr c hc).2
      obtain ⟨hsq, -, h2⟩ := pN7_sound hcr hs (TitsInv.mem_surv hc)
      have e0 : permOfArr 1755 c 0 = y := by
        apply Fin.ext
        rw [← hcr 0]
        exact beq_iff_eq.1 hc0
      rw [e0] at h2
      exact ⟨mem_titsN_of_sift hcr hs, hsq, e0, h2⟩
  have hnd : (((survivors5 1755 titsNLevels pN7).filter fun a => a[0]! == (y : Nat)).map
      (permOfArr 1755)).Nodup := nodup_map_permOfArr (fun c hc => (hpr c (List.mem_filter.1 hc).1).1)
    (hpw.filter _)
  rw [hset, ncard_list_set hnd, List.length_map, survN, List.filter_map, List.length_map]
  have hf : SN.C.filter ((fun (a : Array Nat) => a[0]! == (y : Nat)) ∘
      fun k => unpack 1755 11 (prodCode 1755 11 (mask 11) (1755 * 11) TitsN.LR TitsN.TR k)) =
      SN.C.filter (fun c => in2 y y (gptC TitsN.LR TitsN.TR c 0)) := by
    refine List.filter_congr fun c hc => ?_
    have hct := ((ascK_spec aN).2 c hc).2
    rw [Function.comp_apply, ← gptC_get bindsN permN TitsN.hl hct 0 (by norm_num), Bool.eq_iff_iff,
      beq_iff_eq, in2_iff, or_self]
  rw [hf, ← cntAt_eq]
  rcases hy12 with h | h <;> rw [h]
  · exact Nat.eq_of_beq_eq_true cntN1
  · exact Nat.eq_of_beq_eq_true cntN2

@[expose] def pairB (x y : Nat) : Bool :=
  (x == 3 && y == 4) || (x == 5 && y == 7) || (x == 9 && y == 13) || (x == 17 && y == 25)

open CertificateChecks.KernelSporSch.TitsAction (lpK) in
@[expose] noncomputable def nb0OK (k : Nat) : Bool :=
  lpK (3 * CFSG.KC.TitsOctK.plK CFSG.KD.TitsOct.PL 0 k) == 0 &&
    (CFSG.KC.TitsOctK.plK CFSG.KD.TitsOct.PL 0 k == 0 ||
      pairB (lpK (3 * CFSG.KC.TitsOctK.plK CFSG.KD.TitsOct.PL 0 k + 1))
        (lpK (3 * CFSG.KC.TitsOctK.plK CFSG.KD.TitsOct.PL 0 k + 2)))

theorem nb0K : allN 5 nb0OK = true := by decide +kernel

abbrev Pr (a b : Nat) : Prop := (a = 3 ∧ b = 4) ∨ (a = 5 ∧ b = 7) ∨ (a = 9 ∧ b = 13) ∨ (a = 17 ∧ b = 25)

theorem lines0 (v : Fin 2925) (h0 : (0 : Fin 1755) ∈ titsLine v) (hv : v ≠ 0) :
    ∃ a b : Nat, Pr a b ∧
      ∀ x : Fin 1755, x ∈ titsLine v ↔ (x : Nat) = 0 ∨ (x : Nat) = a ∨ (x : Nat) = b := by
  have hadj := CFSG.Quasithin.H13.F45Ru.octGraph_adj_inl_inr.2 h0
  rw [KernelTitsOct.adj_iff] at hadj
  obtain ⟨k, hk, e⟩ := (KernelTitsOct.nbOK.1 0 (by norm_num) _).1 hadj
  have hk5 : k < 5 := by
    rw [CFSG.KC.TitsOctSound.degK_eq] at hk
    simpa using hk
  have ev : (v : Nat) = CFSG.KC.TitsOctK.plK CFSG.KD.TitsOct.PL 0 k := by
    have e' : CFSG.KC.TitsOctK.nbK KernelTitsOct.lpD CFSG.KD.TitsOct.PL 0 k =
        CFSG.KC.TitsOctK.plK CFSG.KD.TitsOct.PL 0 k + 1755 := rfl
    rw [e'] at e
    simp only [CFSG.Quasithin.H13.F45Ru.vCode] at e
    omega
  have h := allN_spec nb0K k hk5
  simp only [nb0OK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  rw [← ev] at h
  obtain ⟨h1, h2 | h2⟩ := h
  · exact absurd (Fin.ext h2) hv
  · refine ⟨_, _, ?_, line_mem3 h1 rfl rfl⟩
    simpa [pairB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, or_assoc] using h2

theorem card_line (v : Fin 2925) : (titsLine v).card = 3 := by
  obtain ⟨h1, h2⟩ := titsLinePt_lt v
  rw [titsLine_eq, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_singleton]
  · simp only [Finset.mem_singleton]
    exact ne_of_lt h2
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨ne_of_lt h1, ne_of_lt (h1.trans h2)⟩

theorem smul_line_iff (g : Equiv.Perm (Fin 1755)) (v w : Fin 2925) :
    g • titsLine v = titsLine w ↔ ∀ x ∈ titsLine v, g x ∈ titsLine w := by
  constructor
  · intro h x hx
    rw [← h]
    exact Finset.smul_mem_smul_finset hx
  · intro h
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_smul_finset.1 hx
      exact h y hy
    · rw [Finset.card_smul_finset, card_line, card_line]

theorem swap_iff {arr : Array Nat} {g : Equiv.Perm (Fin 1755)} (ha : Rep 1755 arr g)
    {v : Fin 2925} {a b : Nat} (hab : Pr a b)
    (hlv : ∀ x : Fin 1755, x ∈ titsLine v ↔ (x : Nat) = 0 ∨ (x : Nat) = a ∨ (x : Nat) = b) :
    (g • titsLine 0 = titsLine v ∧ g • titsLine v = titsLine 0) ↔
      ((arr[1]! = a ∨ arr[1]! = b) ∧ (arr[a]! = 1 ∨ arr[a]! = 2) ∧ (arr[b]! = 1 ∨ arr[b]! = 2) ∧
        (arr[2]! = a ∨ arr[2]! = b) ∧ arr[0]! = 0) := by
  have hlt : 3 ≤ a ∧ a < 1755 ∧ 3 ≤ b ∧ b < 1755 ∧ a ≠ b := by
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  let pa : Fin 1755 := ⟨a, hlt.2.1⟩
  let pb : Fin 1755 := ⟨b, hlt.2.2.2.1⟩
  have e0 : arr[0]! = (g 0 : Nat) := ha 0
  have e1 : arr[1]! = (g 1 : Nat) := ha 1
  have e2 : arr[2]! = (g 2 : Nat) := ha 2
  have ea : arr[a]! = (g pa : Nat) := ha pa
  have eb : arr[b]! = (g pb : Nat) := ha pb
  rw [e0, e1, e2, ea, eb, smul_line_iff, smul_line_iff]
  have ne : ∀ x y : Fin 1755, (x : Nat) ≠ y → (g x : Nat) ≠ g y := fun x y hxy h =>
    hxy (congrArg Fin.val (g.injective (Fin.ext h)))
  have l0 : ∀ x : Fin 1755, x ∈ titsLine 0 ↔ (x : Nat) = 0 ∨ (x : Nat) = 1 ∨ (x : Nat) = 2 := line0
  constructor
  · rintro ⟨h1, h2⟩
    have m0 := (hlv _).1 (h1 0 ((l0 0).2 (Or.inl rfl)))
    have m1 := (hlv _).1 (h1 1 ((l0 1).2 (Or.inr (Or.inl rfl))))
    have m2 := (hlv _).1 (h1 2 ((l0 2).2 (Or.inr (Or.inr rfl))))
    have n0 := (l0 _).1 (h2 0 ((hlv 0).2 (Or.inl rfl)))
    have na := (l0 _).1 (h2 pa ((hlv pa).2 (Or.inr (Or.inl rfl))))
    have nb := (l0 _).1 (h2 pb ((hlv pb).2 (Or.inr (Or.inr rfl))))
    have d01 := ne 0 1 (by decide)
    have d02 := ne 0 2 (by decide)
    have d12 := ne 1 2 (by decide)
    have d0a := ne 0 pa (by change (0 : Nat) ≠ a; omega)
    have d0b := ne 0 pb (by change (0 : Nat) ≠ b; omega)
    have dab := ne pa pb (by change a ≠ b; omega)
    omega
  · rintro ⟨h1, ha', hb', h2, h0⟩
    constructor
    · intro x hx
      rw [hlv]
      rcases (l0 x).1 hx with h | h | h
      · have hx' : x = 0 := Fin.ext h
        rw [hx']
        omega
      · have hx' : x = 1 := Fin.ext h
        rw [hx']
        omega
      · have hx' : x = 2 := Fin.ext h
        rw [hx']
        omega
    · intro x hx
      rw [l0]
      rcases (hlv x).1 hx with h | h | h
      · have hx' : x = 0 := Fin.ext h
        rw [hx']
        omega
      · have hx' : x = pa := Fin.ext h
        rw [hx']
        omega
      · have hx' : x = pb := Fin.ext h
        rw [hx']
        omega

theorem dist_inl (p : Fin 1755) :
    CFSG.Quasithin.H13.F45Ru.octGraph.dist (Sum.inl 0) (Sum.inl p) =
      CFSG.KC.TitsOctK.layAt CFSG.KD.TitsOct.LAY0 p := by
  have hL := (KernelTitsOct.lay_at KernelTitsOct.lay0).1
  rw [CFSG.Quasithin.H13.F45Ru.ofCode_zero] at hL
  exact hL.dist_eq (Sum.inl p)

theorem noFar_iff (LAY : Nat) (f : Nat → Nat) :
    noFar LAY f = true ↔ ∀ p < 1755, CFSG.KC.TitsOctK.layAt LAY p = 8 → f p ≠ p := by
  unfold noFar
  constructor
  · intro h p hp hl he
    have h1 := allN_spec h p hp
    beta_reduce at h1
    rw [hl, he, Nat.beq_refl, Nat.beq_refl] at h1
    exact absurd h1 (by decide)
  · intro h
    refine allN_of_forall fun p hp => ?_
    beta_reduce
    cases hl : Nat.beq (CFSG.KC.TitsOctK.layAt LAY p) 8
    · rfl
    · cases he : Nat.beq (f p) p
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true he) (h p hp (Nat.eq_of_beq_eq_true hl))

theorem noFar_congr {LAY : Nat} {f g : Nat → Nat} (h : ∀ i < 1755, f i = g i) :
    noFar LAY f = noFar LAY g := by
  unfold noFar
  exact allN_congr7470 fun p hp => by rw [h p hp]

theorem far_iff {arr : Array Nat} {g : Equiv.Perm (Fin 1755)} (ha : Rep 1755 arr g) :
    noFar CFSG.KD.TitsOct.LAY0 (fun i => arr[i]!) = false ↔
      ∃ p : Fin 1755, CFSG.Quasithin.H13.F45Ru.octGraph.dist (Sum.inl 0) (Sum.inl p) = 8 ∧
        g p = p := by
  rw [← Bool.not_eq_true, noFar_iff]
  push Not
  constructor
  · rintro ⟨p, hp, hl, he⟩
    refine ⟨⟨p, hp⟩, by rw [dist_inl]; exact hl, Fin.ext ?_⟩
    rw [← ha.apply hp]
    exact he
  · rintro ⟨p, hd, hgp⟩
    refine ⟨p, p.2, by rw [← dist_inl]; exact hd, ?_⟩
    beta_reduce
    rw [ha p, hgp]

@[expose] noncomputable def pH7 (a : Array Nat) : Bool := swT TitsH.BP (fun i => a[i]!)

theorem survH : survivors5 1755 titsHLevels pH7 = SH.L.map (unpack 1755 11) :=
  surv5K_sound bindsH permH TitsH.hl (fun t0 t1 t2 t3 t4 c0 c1 c2 c3 c4 => by
    obtain ⟨-, hP⟩ := gpt_facts c0 c1 c2 c3 c4
    unfold PH pH7
    exact swT_congr (fun i hi => (gptR_eq _ _ _ _ _ i).trans (hP i hi).1.symm)
      (fun i hi => lt_of_eq_of_lt (hP i hi).1 (hP i hi).2) fun _ ht => bpH ht) mH aH zH EH.all

theorem hBase : (finList 1755 titsHBase).length = 5 := by
  simp [finList, titsCentral_check.2.1]

theorem sq_of_sqB_H {a : Array Nat} {g : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a g)
    (hs : siftA 1755 titsHLevels (baseArr 1755 titsHBase) 0 a = true)
    (hq : sqB TitsH.BP (fun i => a[i]!) = true) : g * g = 1 := by
  obtain ⟨G, hmem, hsep⟩ := chain_group bindsH TitsH.head TitsH.hl (NS := 220) (CH := 8)
    (by norm_num) TitsH.hs TitsInv.ndH
  have hgG := (hmem _ _ ha).1 hs
  refine hsep _ (G.mul_mem hgG hgG) fun t ht hb => Fin.ext ?_
  have h1 := allN_spec hq t ht
  simp only [strictB_eq7470] at h1
  rw [← bindsH.2.2.2.2.2.2 t ht] at h1
  have h2 := Nat.eq_of_beq_eq_true h1
  rw [ha.apply hb, ha (g ⟨_, hb⟩)] at h2
  rw [Equiv.Perm.mul_apply]
  exact h2

theorem sqB_of_sq_H {a : Array Nat} {g : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a g)
    (hsq : g * g = 1) : sqB TitsH.BP (fun i => a[i]!) = true :=
  allN_of_forall fun t ht => by
    simp only [strictB_eq7470]
    have hb := bpH ht
    rw [ha.apply hb, ha (g ⟨_, hb⟩), ← Equiv.Perm.mul_apply, hsq]
    exact Nat.beq_refl _

theorem swT_at {BP : Nat} {f : Nat → Nat} {a b : Nat} (hab : Pr a b) (h1 : f 1 = a ∨ f 1 = b) :
    swT BP f = restK BP a b f := by
  unfold swT
  rw [strictB_eq7470]
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases h1 with h | h <;> rw [h] <;> rfl

theorem pH7_iff {arr : Array Nat} {g : Equiv.Perm (Fin 1755)} (ha : Rep 1755 arr g)
    (hs : siftA 1755 titsHLevels (baseArr 1755 titsHBase) 0 arr = true) {a b : Nat}
    (hab : Pr a b) (h1 : arr[1]! = a ∨ arr[1]! = b) :
    pH7 arr = true ↔ ((arr[a]! = 1 ∨ arr[a]! = 2) ∧ (arr[b]! = 1 ∨ arr[b]! = 2) ∧
      (arr[2]! = a ∨ arr[2]! = b) ∧ arr[0]! = 0) ∧ g * g = 1 := by
  unfold pH7
  rw [swT_at hab h1]
  unfold restK
  rw [bAnd_iff, bAnd_iff, bAnd_iff, bAnd_iff, in2_iff, in2_iff, in2_iff, beq_iff]
  constructor
  · rintro ⟨h2, h3, h4, h5, h6⟩
    exact ⟨⟨h2, h3, h4, h5⟩, sq_of_sqB_H ha hs h6⟩
  · rintro ⟨⟨h2, h3, h4, h5⟩, h6⟩
    exact ⟨h2, h3, h4, h5, sqB_of_sq_H ha h6⟩

@[expose] noncomputable def qH (a b : Nat) (x : Array Nat) : Bool :=
  in2 a b x[1]! && !noFar CFSG.KD.TitsOct.LAY0 (fun i => x[i]!)

abbrev N1s (v : Fin 2925) : Set (Equiv.Perm (Fin 1755)) :=
  {g | g ∈ titsH ∧ g * g = 1 ∧ g • titsLine 0 = titsLine v ∧ g • titsLine v = titsLine 0 ∧
    ∃ p : Fin 1755, CFSG.Quasithin.H13.F45Ru.octGraph.dist (Sum.inl 0) (Sum.inl p) = 8 ∧ g p = p}

theorem N1_eq (v : Fin 2925) {a b : Nat} (hab : Pr a b)
    (hlv : ∀ x : Fin 1755, x ∈ titsLine v ↔ (x : Nat) = 0 ∨ (x : Nat) = a ∨ (x : Nat) = b) :
    N1s v = {g | g ∈ ((survivors5 1755 titsHLevels pH7).filter (qH a b)).map (permOfArr 1755)} := by
  obtain ⟨hpr, -⟩ := surv5K_propsT pH7 bindsH permH TitsH.hl
  ext g
  simp only [Set.mem_setOf_eq, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨hgH, hsq, hs1, hs2, hfar⟩
    have hgQ : g ∈ titsQH.originalSubgroup := by rw [titsQH_facts.2.2.1]; exact hgH
    obtain ⟨x, hx, hp⟩ := all5_spec titsH_chainArrays (by norm_num : 0 < 4)
      titsLocalChains_check.1 hBase (all5_surv titsHLevels pH7) hgQ
    obtain ⟨m1, m2⟩ := (swap_iff hx hab hlv).1 ⟨hs1, hs2⟩
    have hpx : pH7 x = true := by
      unfold pH7
      rw [swT_at hab m1]
      unfold restK
      rw [bAnd_iff, bAnd_iff, bAnd_iff, bAnd_iff, in2_iff, in2_iff, in2_iff, beq_iff]
      exact ⟨m2.1, m2.2.1, m2.2.2.1, m2.2.2.2, sqB_of_sq_H hx hsq⟩
    rw [hpx, Bool.not_true, Bool.false_or, anyEq, List.any_eq_true] at hp
    obtain ⟨w, hw, hxw⟩ := hp
    have hwr := (rep_permOfArr (hpr w hw).1).1
    have e := eq_of_eqA hx hwr hxw
    refine ⟨w, ⟨hw, ?_⟩, e.symm⟩
    rw [← e] at hwr
    have hw1 : w[1]! = (g 1 : Nat) := hwr 1
    have hx1 : x[1]! = (g 1 : Nat) := hx 1
    unfold qH
    rw [Bool.and_eq_true, in2_iff, hw1, ← hx1, Bool.not_eq_true', (far_iff hwr).2 hfar]
    exact ⟨m1, rfl⟩
  · rintro ⟨w, ⟨hw, hq⟩, rfl⟩
    have hwr := (rep_permOfArr (hpr w hw).1).1
    have hs : siftA 1755 titsHLevels (baseArr 1755 titsHBase) 0 w = true := (hpr w hw).2
    unfold qH at hq
    rw [Bool.and_eq_true, in2_iff, Bool.not_eq_true', far_iff hwr] at hq
    obtain ⟨m2, hsq⟩ :=(pH7_iff hwr hs hab hq.1).1 (TitsInv.mem_surv hw)
    obtain ⟨hs1, hs2⟩ := (swap_iff hwr hab hlv).2 ⟨hq.1, m2⟩
    exact ⟨mem_titsH_of_sift hwr hs, hsq, hs1, hs2, hq.2⟩

theorem zipK_map {f : Nat → Nat → Bool} {g : Nat → Nat} :
    ∀ {C : List Nat}, zipK f C (C.map g) = true → ∀ c ∈ C, f c (g c) = true
  | [], _, c, hc => absurd hc List.not_mem_nil
  | d :: C, h, c, hc => by
    have h' : bAnd(f d (g d), zipK f C (C.map g)) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h1
    · exact zipK_map h2 c hc

theorem hasBit_land (m n k : Nat) : hasBit (Nat.land m n) k = (hasBit m k && hasBit n k) := by
  rw [Raw.Orb.hasBit_eq, Raw.Orb.hasBit_eq, Raw.Orb.hasBit_eq]
  exact Nat.testBit_land m n k

theorem farOK_iff {LAY M c x : Nat} (h : farOK LAY M c x = true) :
    (!noFar LAY (pg 11 (mask 11) x)) = hasBit M c := by
  unfold farOK at h
  cases hn : noFar LAY (pg 11 (mask 11) x) <;> cases hb : hasBit M c <;> rw [hn, hb] at h <;>
    first | rfl | exact absurd h (by decide)

noncomputable abbrev pcH (k : Nat) : Nat := prodCode 1755 11 (mask 11) (1755 * 11) TitsH.LR TitsH.TR k

theorem sub_SF {c : Nat} (hc : c ∈ SF.C) : c ∈ SH.C := by
  have h1 : hasBit SF.M c = true := by
    rw [← Nat.eq_of_beq_eq_true mF, hasBit_maskOf]
    exact decide_eq_true hc
  rw [← Nat.eq_of_beq_eq_true sF, hasBit_land, Bool.and_eq_true] at h1
  have h2 := h1.2
  rw [← Nat.eq_of_beq_eq_true mH, hasBit_maskOf] at h2
  exact of_decide_eq_true h2

theorem filter_SF : SH.C.filter (fun c => decide (c ∈ SF.C)) = SF.C := by
  refine List.Pairwise.eq_of_mem_iff (r := (· < ·)) ((ascK_spec aH).1.filter _) (ascK_spec aF).1
    fun k => ?_
  rw [List.mem_filter, decide_eq_true_iff]
  exact ⟨fun h => h.2, fun h => ⟨sub_SF h, h⟩⟩

theorem qH_code {a b c : Nat} (hc : c ∈ SH.C) :
    qH a b (unpack 1755 11 (pcH c)) = (decide (c ∈ SF.C) && in2 a b (gptC TitsH.LR TitsH.TR c 1)) := by
  have hct := ((ascK_spec aH).2 c hc).2
  have hL : SH.L = SH.C.map pcH := zipK_beq_map zH
  have hf := farOK_iff (zipK_map (hL ▸ farH) c hc)
  rw [← Nat.eq_of_beq_eq_true mF, hasBit_maskOf] at hf
  unfold qH
  rw [← gptC_get bindsH permH TitsH.hl hct 1 (by norm_num),
    noFar_congr (g := pg 11 (mask 11) (pcH c)) fun i hi => unpack_getT hi, hf, Bool.and_comm]

theorem card_N1 (v : Fin 2925) (h0 : (0 : Fin 1755) ∈ titsLine v) (hv : v ≠ 0) :
    (N1s v).ncard = 16 := by
  obtain ⟨a, b, hab, hlv⟩ := lines0 v h0 hv
  obtain ⟨hpr, hpw⟩ := surv5K_propsT pH7 bindsH permH TitsH.hl
  have hnd : (((survivors5 1755 titsHLevels pH7).filter (qH a b)).map (permOfArr 1755)).Nodup :=
    nodup_map_permOfArr (fun c hc => (hpr c (List.mem_filter.1 hc).1).1) (hpw.filter _)
  have hL : SH.L = SH.C.map pcH := zipK_beq_map zH
  rw [N1_eq v hab hlv, ncard_list_set hnd, List.length_map, survH, hL, List.map_map,
    List.filter_map, List.length_map]
  have hf : SH.C.filter (qH a b ∘ unpack 1755 11 ∘ pcH) =
      SF.C.filter (fun c => in2 a b (gptC TitsH.LR TitsH.TR c 1)) := by
    rw [← filter_SF, List.filter_filter]
    refine List.filter_congr fun c hc => ?_
    simp only [Function.comp_apply]
    rw [qH_code hc, Bool.and_comm]
  rw [hf, ← cntAt_eq]
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Nat.eq_of_beq_eq_true cnt3
  · exact Nat.eq_of_beq_eq_true cnt5
  · exact Nat.eq_of_beq_eq_true cnt9
  · exact Nat.eq_of_beq_eq_true cnt17

theorem lookC_map {f : Nat → Nat} : ∀ {C : List Nat} {c : Nat}, c ∈ C → lookC c C (C.map f) = f c
  | [], _, h => absurd h List.not_mem_nil
  | d :: C, c, h => by
    change Bool.rec (motive := fun _ => Nat) (lookC c C (C.map f)) (f d) (Nat.beq c d) = f c
    cases hb : Nat.beq c d
    · exact lookC_map ((List.mem_cons.1 h).resolve_left (Nat.ne_of_beq_eq_false hb))
    · exact (congrArg f (Nat.eq_of_beq_eq_true hb)).symm

theorem oneOK_spec : ∀ {R : List Nat}, oneOK R = true → ∃ r, R = [r] ∧ r ∈ SH.C
  | [], h => absurd h (by decide)
  | [r], h => by
    have h' : bAnd(memL r SH.C, true) = true := h
    exact ⟨r, rfl, (memL_iff r SH.C).1 ((bAnd_iff _ _).1 h').1⟩
  | r :: s :: t, h => by
    have h' : bAnd(memL r SH.C, false) = true := h
    exact absurd ((bAnd_iff _ _).1 h').2 (by decide)

noncomputable abbrev sH (c : Nat) : Equiv.Perm (Fin 1755) := permOfArr 1755 (unpack 1755 11 (pcH c))

theorem rep_sH {c : Nat} (hc : c ∈ SH.C) : Rep 1755 (unpack 1755 11 (pcH c)) (sH c) := by
  obtain ⟨hpr, -⟩ := surv5K_propsT pH7 bindsH permH TitsH.hl
  have hm : unpack 1755 11 (pcH c) ∈ survivors5 1755 titsHLevels pH7 := by
    rw [survH, zipK_beq_map zH, List.map_map]
    exact List.mem_map_of_mem hc
  exact (rep_permOfArr (hpr _ hm).1).1

theorem U_facts {x : Nat} (hx : x = U 0 ∨ x = U 1) :
    Rep 1755 (unpack 1755 11 x) (permOfArr 1755 (unpack 1755 11 x)) ∧
      permOfArr 1755 (unpack 1755 11 x) ∈ titsJ ⊓ titsK := by
  have key : ∀ {x : Nat}, canonK 1755 11 (mask 11) (1755 * 11) x = true →
      permOK 1755 11 (mask 11) (1755 * 11) x (pinvS 1755 11 (mask 11) x) = true →
      siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsJ.LR TitsJ.TRI TitsJ.BP 4 0 x = true →
      siftK 1755 11 (mask 11) (1755 * 11) (pidn 1755 11) TitsK.LR TitsK.TRI TitsK.BP 5 0 x = true →
      Rep 1755 (unpack 1755 11 x) (permOfArr 1755 (unpack 1755 11 x)) ∧
        permOfArr 1755 (unpack 1755 11 x) ∈ titsJ ⊓ titsK := fun hc hp hJ hK => by
    have hr := (rep_permOfArr (isInv_of hp)).1
    have sJ : siftA 1755 titsJLevels (baseArr 1755 titsJBase) 0 (unpack 1755 11 _) = true :=
      siftK_soundR bindsJ permJ TitsJ.hl rfl (hi_of hc) (range_of_canonK hc) hJ
    have sK : siftA 1755 titsKLevels (baseArr 1755 titsKBase) 0 (unpack 1755 11 _) = true :=
      siftK_soundR bindsK permK TitsK.hl rfl (hi_of hc) (range_of_canonK hc) hK
    exact ⟨hr, mem_titsJ_of_sift hr sJ, mem_titsK_of_sift hr sK⟩
  rcases hx with rfl | rfl
  · exact key cU0 pU0 uJ0 kU0
  · exact key cU1 pU1 uJ1 kU1

theorem conj_step {u x y : Nat} {μ ξ η : Equiv.Perm (Fin 1755)} (hu : Rep 1755 (unpack 1755 11 u) μ)
    (hx : Rep 1755 (unpack 1755 11 x) ξ) (hy : Rep 1755 (unpack 1755 11 y) η)
    (h : pcomp 1755 11 (mask 11) u x = pcomp 1755 11 (mask 11) y u) : η = μ * ξ * μ⁻¹ := by
  have key : μ * ξ = η * μ := by
    refine Equiv.ext fun i => Fin.ext ?_
    have e := congrArg (fun P => pg 11 (mask 11) P i) h
    beta_reduce at e
    rw [PF.pg_pcomp (by norm_num) i.2, PF.pg_pcomp (by norm_num) i.2] at e
    have hx' : pg 11 (mask 11) x i = ξ i := (unpack_getT i.2).symm.trans (hx i)
    have hu' : pg 11 (mask 11) u i = μ i := (unpack_getT i.2).symm.trans (hu i)
    have hux : pg 11 (mask 11) u (ξ i) = μ (ξ i) := (unpack_getT (ξ i).2).symm.trans (hu (ξ i))
    have hyu : pg 11 (mask 11) y (μ i) = η (μ i) := (unpack_getT (μ i).2).symm.trans (hy (μ i))
    rw [hx', hux, hu', hyu] at e
    exact e
  rw [key, mul_inv_cancel_right]

theorem walk_inv {E : List (Nat × Nat × Nat)} {r : Nat} (hr : r ∈ SH.C) :
    ∀ c ∈ walkK (okW (U 0) (U 1)) E [r],
      c ∈ SH.C ∧ ∃ u ∈ titsJ ⊓ titsK, u * sH r * u⁻¹ = sH c := by
  have hL : SH.L = SH.C.map pcH := zipK_beq_map zH
  refine walkK_inv (fun c p j hp hok => ?_) E [r] fun x hx => ?_
  · obtain ⟨hpC, u, hu, e⟩ := hp
    unfold okW at hok
    obtain ⟨hcm, hcj⟩ := (bAnd_iff _ _).1 hok
    have hcC := (memL_iff _ _).1 hcm
    unfold conjOK at hcj
    beta_reduce at hcj
    rw [hL, lookC_map hpC, lookC_map hcC] at hcj
    have he := Nat.eq_of_beq_eq_true hcj
    generalize hUj : Bool.rec (motive := fun _ => Nat) (U 1) (U 0) (Nat.beq j 0) = Uj at he
    have hUo : Uj = U 0 ∨ Uj = U 1 := by
      rcases Bool.eq_false_or_eq_true (Nat.beq j 0) with hb | hb
      · rw [hb] at hUj
        exact Or.inl hUj.symm
      · rw [hb] at hUj
        exact Or.inr hUj.symm
    obtain ⟨hrU, hUJK⟩ := U_facts hUo
    have hc := conj_step hrU (rep_sH hpC) (rep_sH hcC) he
    refine ⟨hcC, permOfArr 1755 (unpack 1755 11 Uj) * u, Subgroup.mul_mem _ hUJK hu, ?_⟩
    rw [hc, ← e]
    group
  · rw [List.mem_singleton] at hx
    rw [hx]
    exact ⟨hr, 1, Subgroup.one_mem _, by group⟩

theorem trans_tree {a b : Nat} {E : List (Nat × Nat × Nat)} {R : List Nat} (hR : oneOK R = true)
    (hcov : covW a b E R = true) {c c' : Nat} (hc : c ∈ SF.C)
    (hc1 : in2 a b (gptC TitsH.LR TitsH.TR c 1) = true) (hc' : c' ∈ SF.C)
    (hc1' : in2 a b (gptC TitsH.LR TitsH.TR c' 1) = true) :
    ∃ u ∈ titsJ ⊓ titsK, u * sH c * u⁻¹ = sH c' := by
  obtain ⟨r, rfl, hr⟩ := oneOK_spec hR
  unfold covW at hcov
  simp only [strictB_eq7470] at hcov
  unfold covL at hcov
  have hW : ∀ x ∈ SF.C, in2 a b (gptC TitsH.LR TitsH.TR x 1) = true →
      x ∈ walkK (okW (U 0) (U 1)) E [r] := fun x hx hx1 => by
    have h := allL_spec hcov x hx
    beta_reduce at h
    rw [hx1] at h
    exact (memL_iff _ _).1 h
  obtain ⟨-, u, hu, e⟩ := walk_inv hr c (hW c hc hc1)
  obtain ⟨-, u', hu', e'⟩ := walk_inv hr c' (hW c' hc' hc1')
  refine ⟨u' * u⁻¹, Subgroup.mul_mem _ hu' (Subgroup.inv_mem _ hu), ?_⟩
  rw [← e, ← e']
  group

theorem trans_N1 (v : Fin 2925) (h0 : (0 : Fin 1755) ∈ titsLine v) (hv : v ≠ 0)
    {g g' : Equiv.Perm (Fin 1755)} (hg : g ∈ N1s v) (hg' : g' ∈ N1s v) :
    ∃ u ∈ titsJ ⊓ titsK, u * g * u⁻¹ = g' := by
  obtain ⟨a, b, hab, hlv⟩ := lines0 v h0 hv
  have key : ∀ g ∈ N1s v, ∃ c ∈ SF.C, in2 a b (gptC TitsH.LR TitsH.TR c 1) = true ∧ g = sH c := by
    intro g hg
    have hg2 : g ∈ ((survivors5 1755 titsHLevels pH7).filter (qH a b)).map (permOfArr 1755) := by
      rw [N1_eq v hab hlv] at hg
      exact hg
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hg2
    obtain ⟨hw1, hq⟩ := List.mem_filter.1 hw
    rw [survH, zipK_beq_map zH, List.map_map] at hw1
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hw1
    have hq2 : qH a b (unpack 1755 11 (pcH c)) = true := hq
    rw [qH_code hc, Bool.and_eq_true, decide_eq_true_iff] at hq2
    exact ⟨c, hq2.1, hq2.2, rfl⟩
  obtain ⟨c, hc, hc1, rfl⟩ := key g hg
  obtain ⟨c', hc', hc1', rfl⟩ := key g' hg'
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact trans_tree r3 cov3 hc hc1 hc' hc1'
  · exact trans_tree r5 cov5 hc hc1 hc' hc1'
  · exact trans_tree r9 cov9 hc hc1 hc' hc1'
  · exact trans_tree r17 cov17 hc hc1 hc' hc1'

end CertificateChecks.KernelTitsN12

end
