
module

public import Certificates.Kernel.Sporadic.L2.G1

public section

namespace CertificateChecks.KernelSpor.L2G

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.FpBfs
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzRecog.LevelTwo CFSG.Sporadic.SuzRecog.LevelTwoData
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.L2K
open CertificateChecks.KernelSpor.SuzTwCF (P p_comp eqA_P pidn_P)

local notation "pgk" => pg 11 (mask 11)
local notation "pgv" => pg 12 (mask 12)
local notation "pc" => pcomp 1782 11 (mask 11)
local notation "cn" => canonK 1782 11 (mask 11) (1782 * 11)

theorem sort_mono {n : Nat} {f ord : Nat → Nat}
    (h : allN (Nat.pred n) (fun m => Nat.blt (f (ord m)) (f (ord (Nat.succ m)))) = true) :
    ∀ a b, a < b → b < n → f (ord a) < f (ord b) := by
  intro a b hab hb
  induction b with
  | zero => omega
  | succ b ih =>
    have hs := nblt.1 (allN_get h (show b < Nat.pred n by rw [Nat.pred_eq_sub_one]; omega))
    rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h1 | h1
    · exact (ih h1 (by omega)).trans hs
    · subst h1
      exact hs

theorem sort_inj {n : Nat} {f ord pos : Nat → Nat} (h : sortK n f ord pos = true) :
    ∀ i < n, ∀ j < n, f i = f j → i = j := by
  unfold sortK at h
  rw [band] at h
  obtain ⟨hm, hp⟩ := h
  have hpos : ∀ i < n, pos i < n ∧ ord (pos i) = i := fun i hi => by
    have := allN_get hp hi
    rw [sB, band, nblt, nbeq] at this
    exact this
  intro i hi j hj he
  obtain ⟨hi1, hi2⟩ := hpos i hi
  obtain ⟨hj1, hj2⟩ := hpos j hj
  have : pos i = pos j := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := sort_mono hm _ _ hlt hj1
      rw [hi2, hj2, he] at this
      exact lt_irrefl _ this
    · have := sort_mono hm _ _ hlt hi1
      rw [hi2, hj2, he] at this
      exact lt_irrefl _ this
  rw [← hi2, ← hj2, this]

theorem getD_pairs (L : List (Nat × Nat)) (m : Std.HashMap Nat Nat) {k v d : Nat}
    (hmem : (k, v) ∈ L) (hu : ∀ p ∈ L, p.1 = k → p.2 = v) :
    (L.foldl (fun m p => m.insert p.1 p.2) m).getD k d = v := by
  induction L using List.reverseRecOn with
  | nil => simp at hmem
  | append_singleton L a ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, Std.HashMap.getD_insert]
    by_cases ha : a.1 = k
    · rw [if_pos (by simp [ha])]
      exact hu a (by simp) ha
    · rw [if_neg (by simpa using ha)]
      refine ih ?_ fun p hp => hu p (List.mem_append_left _ hp)
      rcases List.mem_append.1 hmem with h | h
      · exact h
      · simp only [List.mem_singleton] at h
        exact absurd (congrArg Prod.fst h).symm ha

theorem fpTable_eq (L : Array (Array Nat)) :
    fpTable L = ((List.range L.size).map fun i => (fp L[i]!, i)).foldl
      (fun m p => m.insert p.1 p.2) ∅ := by
  rw [List.foldl_map]
  unfold fpTable
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, List.range_eq_range']

theorem fp_A (hv : ∀ i < 2835, aVt i = true) {i : Nat} (hi : i < 2835) : fp aPts[i]! = fA i := by
  rw [(pA hv hi).1, fp_unpack]
  rfl

theorem fp_T (hw : ∀ j < 162, tVt j = true) {j k : Nat} (hj : j < 162) (hk : k < 3) :
    fp (trip j)[k]! = fT (3 * j + k) := by
  rw [(pT hw hj hk).1, fp_unpack]
  rfl

theorem fpConj_unpack {G GI A : Nat} (hG : cn G = true) (hGI : cn GI = true) (hA : cn A = true) :
    fpConj (unpack 1782 11 G) (unpack 1782 11 GI) (unpack 1782 11 A) = fpCK 11 (mask 11) G GI A := by
  have e : ∀ i < 1782, (unpack 1782 11 G)[(unpack 1782 11 A)[(unpack 1782 11 GI)[i]!]!]! =
      pgk G (pgk A (pgk GI i)) := fun i hi => by
    have h1 := CFSG.KC.HeFixK.pg_lt_of_canonK hGI hi
    have h2 := CFSG.KC.HeFixK.pg_lt_of_canonK hA h1
    rw [CFSG.KC.HeFixK.unpack_getElem! hi, CFSG.KC.HeFixK.unpack_getElem! h1,
      CFSG.KC.HeFixK.unpack_getElem! h2]
  unfold fpConj
  simp only
  rw [e 17 (by norm_num), e 333 (by norm_num), e 901 (by norm_num), e 1500 (by norm_num),
    e 1234 (by norm_num), e 77 (by norm_num)]
  rfl

theorem fpConj_eq (g gi a : Array Nat) : fpConj g gi a = fp (conjA g gi a) := by
  unfold fpConj fp conjA
  simp only [compA_get (by norm_num : 17 < 1782), compA_get (by norm_num : 333 < 1782),
    compA_get (by norm_num : 901 < 1782), compA_get (by norm_num : 1500 < 1782),
    compA_get (by norm_num : 1234 < 1782), compA_get (by norm_num : 77 < 1782)]

theorem aIdx_get (hv : ∀ i < 2835, aVt i = true) (hs : sortK 2835 fA ordA posA = true)
    {j : Nat} (hj : j < 2835) : aIdx.getD (fA j) 2835 = j := by
  unfold aIdx
  rw [fpTable_eq, aPts_size]
  refine getD_pairs _ _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, by rw [fp_A hv hj]⟩) ?_
  intro p hp he
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hp
  have hi' := List.mem_range.1 hi
  exact sort_inj hs i hi' j hj (by rw [← fp_A hv hi']; exact he)

theorem vIdx_eq : vIdx = ((List.range wPts.size).flatMap fun j =>
    (trip j).toList.map fun z => (fp z, j)).foldl (fun m p => m.insert p.1 p.2) ∅ := by
  rw [List.foldl_flatMap]
  unfold vIdx
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, List.range_eq_range',
    List.foldl_map]

theorem trip_size {j : Nat} (hj : j < 162) : (trip j).size = 3 := by
  rw [trip_eq hj]
  rfl

theorem vIdx_get (hw : ∀ j < 162, tVt j = true) (hs : sortK 486 fT ordT posT = true)
    {j k : Nat} (hj : j < 162) (hk : k < 3) : vIdx.getD (fT (3 * j + k)) 162 = j := by
  rw [vIdx_eq, wPts_size]
  refine getD_pairs _ _ (List.mem_flatMap.2 ⟨j, List.mem_range.2 hj, List.mem_map.2
    ⟨(trip j)[k]!, ?_, by rw [fp_T hw hj hk]⟩⟩) ?_
  · rw [getElem!_pos _ k (by rw [trip_size hj]; exact hk)]
    exact Array.getElem_mem_toList _
  · intro p hp he
    obtain ⟨i, hi, hz⟩ := List.mem_flatMap.1 hp
    have hi' := List.mem_range.1 hi
    obtain ⟨z, hz', rfl⟩ := List.mem_map.1 hz
    rw [Array.mem_toList_iff] at hz'
    obtain ⟨k', hk', rfl⟩ := Array.mem_iff_getElem.1 hz'
    have hk3 : k' < 3 := by rw [trip_size hi'] at hk'; exact hk'
    have e : (trip i)[k'] = (trip i)[k']! := by
      rw [getElem!_pos _ k' hk']
    simp only at he ⊢
    rw [e, fp_T hw hi' hk3] at he
    have := sort_inj hs _ (by omega) _ (by omega) he
    omega

theorem vtab_at {s v : Nat} (hs : s < 2) (hv : v < 2997) :
    (vtab s)[v]! = actV gens[s]! gensInv[s]! v := by
  unfold vtab vtabs
  rw [getElem!_pos _ s (by simp; omega), Array.getElem_ofFn,
    getElem!_pos _ v (by simp; exact hv), Array.getElem_ofFn]

theorem vtab_getA (hv : ∀ i < 2835, aVt i = true) (hsA : sortK 2835 fA ordA posA = true)
    {s v : Nat} (hs : s < 2) (hvl : v < 2835) (h : vtA s v = true) : (vtab s)[v]! = VK s v := by
  unfold vtA at h
  rw [sB, band, band, nblt, nbeq] at h
  obtain ⟨hlt, hf, -⟩ := h
  rw [vtab_at hs (by omega)]
  unfold actV
  rw [if_pos hvl, (pA hv hvl).1, (pG hs).1, (pGI hs).1,
    fpConj_unpack (pG hs).2 (pGI hs).2 (pA hv hvl).2, ← hf]
  exact aIdx_get hv hsA hlt

theorem vtab_getW (hw : ∀ j < 162, tVt j = true) (hsT : sortK 486 fT ordT posT = true)
    {s j : Nat} (hs : s < 2) (hj : j < 162) (h : vtW s j = true) :
    (vtab s)[2835 + j]! = VK s (2835 + j) := by
  unfold vtW at h
  simp only [show Nat.add 2835 j = 2835 + j from rfl] at h
  rw [sB, band, band, nble, nblt, sB, sB] at h
  obtain ⟨h1, h2, h3⟩ := h
  set C := pc (XG s) (pc (TK j 0) (XGI s))
  have hC : P (conjA gens[s]! gensInv[s]! wPts[j]!) C := p_conj (pG hs) (pGI hs) (pW hw hj)
  have hj' : VK s (2835 + j) - 2835 < 162 := by omega
  have key : ∃ k < 3, fp (conjA gens[s]! gensInv[s]! wPts[j]!) =
      fT (3 * (VK s (2835 + j) - 2835) + k) := by
    simp only [bif_true, nbeq] at h3
    by_cases e0 : TK (VK s (2835 + j) - 2835) 0 = C
    · exact ⟨0, by norm_num, by rw [hC.1, fp_unpack, ← e0]; rfl⟩
    · have h3' := h3.2 (Q3AG.nbeq_false e0)
      by_cases e1 : TK (VK s (2835 + j) - 2835) 1 = C
      · exact ⟨1, by norm_num, by rw [hC.1, fp_unpack, ← e1]; rfl⟩
      · exact ⟨2, by norm_num, by rw [hC.1, fp_unpack, ← h3'.2 (Q3AG.nbeq_false e1)]; rfl⟩
  obtain ⟨k, hk, hfk⟩ := key
  rw [vtab_at hs (by omega)]
  unfold actV
  rw [if_neg (by omega), show 2835 + j - 2835 = j by omega]
  rw [fpConj_eq, hfk, vIdx_get hw hsT hj' hk]
  omega

theorem conjEq_P {g gi a b : Array Nat} {G GI A B : Nat} (hg : P g G) (hgi : P gi GI)
    (ha : P a A) (hb : P b B) : conjEq g gi a b = Nat.beq B (pc G (pc A GI)) := by
  unfold conjEq
  exact eqA_P hb (p_comp hg (p_comp ha hgi))

theorem sendsB_eq (hv : ∀ i < 2835, aVt i = true) (hw : ∀ j < 162, tVt j = true)
    {g gi : Array Nat} {G GI : Nat} (hg : P g G) (hgi : P gi GI) {v v' : Nat} (hvl : v < 2997) :
    sendsB g gi v v' = sendsK G GI v v' := by
  unfold sendsB sendsK
  by_cases ha : v < 2835
  · rw [if_pos ha, show Nat.blt v 2835 = true from nblt.2 ha]
    by_cases hb : v' < 2835
    · rw [decide_eq_true hb, show Nat.blt v' 2835 = true from nblt.2 hb,
        conjEq_P hg hgi (pA hv ha) (pA hv hb)]
      rfl
    · rw [decide_eq_false hb,
        nblt_f hb]
      rfl
  · rw [if_neg ha, nblt_f (b := 2835) ha]
    have hj : v - 2835 < 162 := by omega
    by_cases hb : 2835 ≤ v' ∧ v' < 2997
    · have hj' : v' - 2835 < 162 := Nat.sub_lt_left_of_lt_add hb.1 hb.2
      rw [decide_eq_true hb.1,
        decide_eq_true hb.2,
        show Nat.ble 2835 v' = true from nble.2 hb.1, show Nat.blt v' 2997 = true from nblt.2 hb.2,
        sB, sB, conjEq_P hg hgi (pW hw hj) (pT hw hj' (by norm_num : 0 < 3)),
        conjEq_P hg hgi (pW hw hj) (pT hw hj' (by norm_num : 1 < 3)),
        conjEq_P hg hgi (pW hw hj) (pT hw hj' (by norm_num : 2 < 3))]
      cases Nat.beq (TK (v' - 2835) 0) (pc G (pc (TK (v - 2835) 0) GI)) <;>
        cases Nat.beq (TK (v' - 2835) 1) (pc G (pc (TK (v - 2835) 0) GI)) <;> rfl
    · rcases not_and_or.1 hb with hb | hb
      · rw [decide_eq_false hb,
          nble_f hb]
        rfl
      · rw [decide_eq_false hb,
          nblt_f hb]
        cases decide (2835 ≤ v') <;> cases Nat.ble 2835 v' <;> rfl

end CertificateChecks.KernelSpor.L2G

end
