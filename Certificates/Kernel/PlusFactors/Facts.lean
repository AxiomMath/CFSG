module

public import Certificates.Kernel.PlusFactors.Checks
public import CFSG.Certificates.Kernel.BfsPinAlg
public import CFSG.Certificates.Kernel.BfsPinBaseSound
public import CFSG.Certificates.Kernel.Misc.PermWitSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import CFSG.Certificates.Kernel.BfsPinSound

public section

namespace CertificateChecks.KernelPlusF

open CFSG.OddTranspositions.PartThree CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw
  CFSG.KC.BfsPin CFSG.KC.PermWit CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.RankThree.Native
local notation "AI" => CFSG.KS.Raw.Orb.allN_iff

theorem any_range_of {m : ℕ} {f : ℕ → Bool} (i : ℕ) (hi : i < m) (h : f i = true) :
    (List.range m).any f = true :=
  List.any_eq_true.2 ⟨i, List.mem_range.2 hi, h⟩

theorem and_of {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  simpa using h

theorem or4 {a b c d : Bool} (h : (a || b || c || d) = true) :
    a = true ∨ b = true ∨ c = true ∨ d = true := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

theorem of6 {a b c d e f : Bool}
    (h : a = true ∨ b = true ∨ c = true ∨ d = true ∨ e = true ∨ f = true) :
    (a || b || c || d || e || f) = true := by
  rcases h with h | h | h | h | h | h <;> simp [h]

theorem beqf {b : Bool} (h : (!b) = true) : (b == false) = true := by
  cases b <;> simp_all

theorem kSz : szOK 60 6 = true := by decide +kernel

theorem keysOK : ∀ p ∈ plusBase, p < 60 := by decide

theorem nums : PE.ng = 60 ∧ PE.N = 7200 ∧ PA.ng = 2 ∧ PA.N = 60 ∧ PB.ng = 2 ∧ PB.N = 60 := by
  have h := kNums
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  tauto

theorem bindE : plusTable.size = 60 ∧ ∀ k < 60, plusTable[k]! = unpack 60 6 (PE.G k) :=
  binds_of_check kBindE

theorem bindA : plusFactorsAgens.size = 2 ∧
    ∀ k < 2, plusFactorsAgens[k]! = unpack 60 6 (PA.G k) :=
  binds_of_check kBindA

theorem bindB : plusFactorsBgens.size = 2 ∧
    ∀ k < 2, plusFactorsBgens[k]! = unpack 60 6 (PB.G k) :=
  binds_of_check kBindB

theorem permE : ∀ k < PE.ng,
    permOK 60 6 (mask 6) (60 * 6) (PE.G k) (pinvS 60 6 (mask 6) (PE.G k)) = true := by
  intro k hk
  rw [nums.1] at hk
  exact AI.1 (and_of (and_of kPerm).1).1 k hk

theorem permA : ∀ k < PA.ng,
    permOK 60 6 (mask 6) (60 * 6) (PA.G k) (pinvS 60 6 (mask 6) (PA.G k)) = true := by
  intro k hk
  rw [nums.2.2.1] at hk
  exact AI.1 (and_of (and_of kPerm).1).2 k hk

theorem permB' : ∀ k < PB.ng,
    permOK 60 6 (mask 6) (60 * 6) (PB.G k) (pinvS 60 6 (mask 6) (PB.G k)) = true := by
  intro k hk
  rw [nums.2.2.2.2.1] at hk
  exact AI.1 (and_of kPerm).2 k hk

theorem ppE : ∀ i < PE.N, PP 60 6 (PE.T i) := PP_pts PE.ok permE
theorem ppA : ∀ i < PA.N, PP 60 6 (PA.T i) := PP_pts PA.ok permA
theorem ppB : ∀ i < PB.N, PP 60 6 (PB.T i) := PP_pts PB.ok permB'

theorem gE {k : ℕ} (hk : k < 60) : PP 60 6 (PE.G k) :=
  PP_gen PE.ok permE k (by rw [nums.1]; exact hk)

theorem gA {k : ℕ} (hk : k < 2) : PP 60 6 (PA.G k) :=
  PP_gen PA.ok permA k (by rw [nums.2.2.1]; exact hk)

theorem gB {k : ℕ} (hk : k < 2) : PP 60 6 (PB.G k) :=
  PP_gen PB.ok permB' k (by rw [nums.2.2.2.2.1]; exact hk)

theorem pinE : (plusEnum ()).pts = Array.ofFn (n := PE.N) fun i => unpack 60 6 (PE.T i.val) :=
  enumBfs_pts_base (by rw [bindE.1, nums.1]) (fun k hk => bindE.2 k (by rw [nums.1] at hk; exact hk))
    PE.ok keysOK kKE nums.2.1.le

theorem pinA : (plusFactorsCA ()).pts =
    Array.ofFn (n := PA.N) fun i => unpack 60 6 (PA.T i.val) :=
  enumBfs_pts_base (by rw [bindA.1, nums.2.2.1])
    (fun k hk => bindA.2 k (by rw [nums.2.2.1] at hk; exact hk)) PA.ok keysOK kKA
    (by have := nums.2.2.2.1; omega)

theorem pinB : (plusFactorsCB ()).pts =
    Array.ofFn (n := PB.N) fun i => unpack 60 6 (PB.T i.val) :=
  enumBfs_pts_base (by rw [bindB.1, nums.2.2.2.2.1])
    (fun k hk => bindB.2 k (by rw [nums.2.2.2.2.1] at hk; exact hk)) PB.ok keysOK kKB
    (by have := nums.2.2.2.2.2; omega)

theorem enumA : plusFactorsEnumA () = true :=
  enumOK_of_bfsK_base (by rw [bindA.1, nums.2.2.1])
    (fun k hk => bindA.2 k (by rw [nums.2.2.1] at hk; exact hk)) permA PA.ok keysOK kKA
    (by have := nums.2.2.2.1; omega)

theorem enumB : plusFactorsEnumB () = true :=
  enumOK_of_bfsK_base (by rw [bindB.1, nums.2.2.2.2.1])
    (fun k hk => bindB.2 k (by rw [nums.2.2.2.2.1] at hk; exact hk)) permB' PB.ok keysOK kKB
    (by have := nums.2.2.2.2.2; omega)

theorem ofFn_get {N : ℕ} {T : ℕ → ℕ} {i : ℕ} (hi : i < N) :
    (Array.ofFn (n := N) fun i => unpack 60 6 (T i.val))[i]! = unpack 60 6 (T i) := by
  rw [getElem!_pos _ i (by rw [Array.size_ofFn]; exact hi), Array.getElem_ofFn]

theorem any_pin {c : ArrCert} {N : ℕ} {T : ℕ → ℕ}
    (hc : c.pts = Array.ofFn (n := N) fun i => unpack 60 6 (T i.val))
    (hT : ∀ i < N, PP 60 6 (T i)) {p : ℕ} (hp : PP 60 6 p) :
    c.pts.toList.any (eqA 60 (unpack 60 6 p)) = memT N T p := by
  rw [hc, pts_toList (fun i => unpack 60 6 (T i)), List.any_map, memT, anyN_eq]
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true, List.mem_range, Function.comp]
  constructor
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, by rwa [eqA_PP hp (hT j hj)] at h⟩
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, by rwa [eqA_PP hp (hT j hj)]⟩

theorem comm_PP {p q : ℕ} (hp : PP 60 6 p) (hq : PP 60 6 q) :
    commutatorA 60 (unpack 60 6 p) (unpack 60 6 q) = unpack 60 6 (cmt p q) := by
  unfold commutatorA
  rw [invCand_PP hp, invCand_PP hq, compA_PP hp hq, compA_PP hp.inv hq.inv,
    compA_PP (hp.mul hq) (hp.inv.mul hq.inv)]
  rfl

theorem cmt_PP {p q : ℕ} (hp : PP 60 6 p) (hq : PP 60 6 q) : PP 60 6 (cmt p q) :=
  (hp.mul hq).mul (hp.inv.mul hq.inv)

theorem conj_PP {g y : ℕ} (hg : PP 60 6 g) (hy : PP 60 6 y) :
    conjA 60 (unpack 60 6 g) (unpack 60 6 y) = unpack 60 6 (cj g y) := by
  unfold conjA
  rw [invCand_PP hg, compA_PP hy hg.inv, compA_PP hg (hy.mul hg.inv)]
  rfl

theorem cj_PP {g y : ℕ} (hg : PP 60 6 g) (hy : PP 60 6 y) : PP 60 6 (cj g y) :=
  hg.mul (hy.mul hg.inv)

theorem keyInj {N : ℕ} {T : ℕ → ℕ} {SK : List ℕ} (hK : keysSK 60 6 plusBase N T SK = true) :
    ∀ i < N, ∀ j < N, keyA 60 plusBase (unpack 60 6 (T i)) =
      keyA 60 plusBase (unpack 60 6 (T j)) → i = j := by
  intro i hi j hj e
  rw [keyA_unpack keysOK, keyA_unpack keysOK] at e
  exact keysSK_spec hK i hi j hj e

theorem sizeA : plusFactorsSizeA () = true := by
  have h : (plusFactorsCA ()).pts.size = 60 := by rw [pinA, Array.size_ofFn, nums.2.2.2.1]
  simp [plusFactorsSizeA, h]

theorem sizeB : plusFactorsSizeB () = true := by
  have h : (plusFactorsCB ()).pts.size = 60 := by rw [pinB, Array.size_ofFn, nums.2.2.2.2.2]
  simp [plusFactorsSizeB, h]

theorem simpleA : plusFactorsSimpleA () = true := by
  have hN := nums.2.2.2.1
  refine conjSimpleOK_of_ctree (WT := WA) kSz keysOK enumA pinA
    (fun i hi => AI.1 (and_of kPermT).1 i (by rw [hN] at hi; exact hi))
    (Nat.eq_of_beq_eq_true (and_of kT0).1) (keyInj kKA) (fun k hk => ?_)
  rw [hN] at hk ⊢
  have h := AI.1 kTreeA k hk
  rw [Bool.or_eq_true] at h
  exact h.imp id fun h' => AI.1 h'

theorem simpleB : plusFactorsSimpleB () = true := by
  have hN := nums.2.2.2.2.2
  refine conjSimpleOK_of_ctree (WT := WB) kSz keysOK enumB pinB
    (fun i hi => AI.1 (and_of kPermT).2 i (by rw [hN] at hi; exact hi))
    (Nat.eq_of_beq_eq_true (and_of kT0).2) (keyInj kKB) (fun k hk => ?_)
  rw [hN] at hk ⊢
  have h := AI.1 kTreeB k hk
  rw [Bool.or_eq_true] at h
  exact h.imp id fun h' => AI.1 h'

theorem tableOK : plusFactorsTableOK () = true := by
  unfold plusFactorsTableOK
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro i hi
  rw [bindE.2 i hi]
  exact CFSG.KC.BfsPin.validA_unpack (permE i (by rw [nums.1]; exact hi))

theorem memGens : plusFactorsMemGens () = true := by
  unfold plusFactorsMemGens
  simp only [Bool.and_eq_true, CFSG.Monster.B.Co2.allLt_iff]
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · rw [bindA.1] at hk
    rw [bindA.2 k hk, any_pin pinE ppE (gA hk)]
    exact AI.1 (and_of kMem).1 k hk
  · rw [bindB.1] at hk
    rw [bindB.2 k hk, any_pin pinE ppE (gB hk)]
    exact AI.1 (and_of kMem).2 k hk

theorem commGens : plusFactorsCommGens () = true := by
  unfold plusFactorsCommGens
  simp only [CFSG.Monster.B.Co2.allLt_iff]
  intro i hi j hj
  rw [bindA.1] at hi
  rw [bindB.1] at hj
  rw [bindA.2 i hi, bindB.2 j hj, comm_PP (gA hi) (gB hj), idA_eq kSz,
    eqA_PP (cmt_PP (gA hi) (gB hj)) (PP.id kSz)]
  exact AI.1 (AI.1 kComm i hi) j hj

theorem disjoint : plusFactorsDisjoint () = true := by
  unfold plusFactorsDisjoint
  simp only [CFSG.Monster.B.Co2.allLt_iff]
  rw [pinA, pinB]
  intro i hi j hj
  rw [Array.size_ofFn] at hi hj
  rw [ofFn_get hi, ofFn_get hj, eqA_PP (ppA i hi) (ppB j hj), idA_eq kSz,
    eqA_PP (ppA i hi) (PP.id kSz)]
  have h := AI.1 (AI.1 kDisj i (by rw [nums.2.2.2.1] at hi; exact hi)) j
    (by rw [nums.2.2.2.2.2] at hj; exact hj)
  rw [Bool.or_eq_true] at h ⊢
  exact h.imp beqf id

theorem conjGens : plusFactorsConjGens () = true := by
  unfold plusFactorsConjGens
  simp only [CFSG.Monster.B.Co2.allLt_iff, Bool.and_eq_true]
  intro i hi
  have hc := and_of (AI.1 kConj i hi)
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · rw [bindA.1] at hk
    rw [bindE.2 i hi, bindA.2 k hk, conj_PP (gE hi) (gA hk),
      any_pin pinB ppB (cj_PP (gE hi) (gA hk)), nums.2.2.2.2.2]
    exact AI.1 hc.1 k hk
  · rw [bindB.1] at hk
    rw [bindE.2 i hi, bindB.2 k hk, conj_PP (gE hi) (gB hk),
      any_pin pinA ppA (cj_PP (gE hi) (gB hk)), nums.2.2.2.1]
    exact AI.1 hc.2 k hk

theorem nonabelian : plusFactorsNonabelian () = true := by
  unfold plusFactorsNonabelian
  rw [bindA.2 0 (by norm_num), bindA.2 1 (by norm_num),
    comm_PP (gA (k := 0) (by norm_num)) (gA (k := 1) (by norm_num)), idA_eq kSz,
    eqA_PP (cmt_PP (gA (k := 0) (by norm_num)) (gA (k := 1) (by norm_num))) (PP.id kSz)]
  exact beqf kNonab

theorem invAll {k : ℕ} (hk : k < 7200) : invPt IE k = true := by
  have h : ∀ s, s < 12 → ∀ k, 600 * s ≤ k → k < 600 * s + 600 → invPt IE k = true := by
    intro s hs k h1 h2
    have hc : invOK (600 * s) 600 = true := by
      rcases (by omega : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨
          s = 8 ∨ s = 9 ∨ s = 10 ∨ s = 11) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ch1383003i_0
      · exact ch1383003i_1
      · exact ch1383003i_2
      · exact ch1383003i_3
      · exact ch1383003i_4
      · exact ch1383003i_5
      · exact ch1383003i_6
      · exact ch1383003i_7
      · exact ch1383003i_8
      · exact ch1383003i_9
      · exact ch1383003i_10
      · exact ch1383003i_11
    have h3 : invPt IE (Nat.add (600 * s) (k - 600 * s)) = true := AI.1 hc (k - 600 * s) (by omega)
    have e : Nat.add (600 * s) (k - 600 * s) = k := Nat.add_sub_cancel' h1
    rw [e] at h3
    exact h3
  exact h (k / 600) (by omega) k (by omega) (by omega)

theorem rowMem_of {x j : ℕ} (hx : PP 60 6 x) (hj : j < 60) (h : Nat.beq (PE.G j) x = true) :
    plusFactorsRowMem (unpack 60 6 x) = true := by
  unfold plusFactorsRowMem
  refine any_range_of j hj ?_
  rw [bindE.2 j hj, eqA_PP (gE hj) hx]
  exact h

theorem prodMem_of {x i j : ℕ} (hx : PP 60 6 x) (hi : i < 60) (hj : j < 60) (hij : i ≠ j)
    (hpg : pg 6 (mask 6) (PE.G i) j = j)
    (h : Nat.beq (pcomp 60 6 (mask 6) (PE.G i) (PE.G j)) x = true) :
    plusFactorsProdMem (unpack 60 6 x) = true := by
  unfold plusFactorsProdMem
  refine any_range_of i hi (any_range_of j hj ?_)
  rw [bindE.2 i hi, bindE.2 j hj, compA_PP (gE hi) (gE hj),
    eqA_PP ((gE hi).mul (gE hj)) hx, unpack_getElem!, if_pos hj]
  simp [hij, hpg, h]

theorem enumMemA_of {x : ℕ} (hx : PP 60 6 x) (h : memT 60 PA.T x = true) :
    plusFactorsEnumMem (plusFactorsCA ()) (unpack 60 6 x) = true := by
  unfold plusFactorsEnumMem
  rw [any_pin pinA ppA hx, nums.2.2.2.1]
  exact h

theorem enumMemB_of {x : ℕ} (hx : PP 60 6 x) (h : memT 60 PB.T x = true) :
    plusFactorsEnumMem (plusFactorsCB ()) (unpack 60 6 x) = true := by
  unfold plusFactorsEnumMem
  rw [any_pin pinB ppB hx, nums.2.2.2.2.2]
  exact h

theorem involutions : plusFactorsInvolutions () = true := by
  unfold plusFactorsInvolutions
  simp only [CFSG.Monster.B.Co2.allLt_iff]
  rw [pinE]
  intro k hk
  rw [Array.size_ofFn] at hk
  have hk' : k < 7200 := by rw [nums.2.1] at hk; exact hk
  have hx := ppE k hk
  rw [ofFn_get hk, compA_PP hx hx, idA_eq kSz, eqA_PP (hx.mul hx) (PP.id kSz),
    eqA_PP hx (PP.id kSz)]
  have h := invAll hk'
  refine of6 ?_
  rcases or4 h with ha | hb | hc | hd
  · have h1 := (and_of ha).2
    rw [Bool.or_eq_true] at h1
    rcases h1 with h1 | h1
    · exact Or.inl (beqf h1)
    · exact Or.inr (Or.inl h1)
  · obtain ⟨h12, h3⟩ := and_of hb
    obtain ⟨h1, h2⟩ := and_of h12
    have e1 := Nat.le_of_ble_eq_true h1
    have e2 := Nat.le_of_ble_eq_true h2
    exact Or.inr (Or.inr (Or.inl (rowMem_of hx (by omega) h3)))
  · obtain ⟨h12, h345⟩ := and_of hc
    obtain ⟨h1, h2⟩ := and_of h12
    obtain ⟨h34, h5⟩ := and_of h345
    obtain ⟨h3, h4⟩ := and_of h34
    have e1 := Nat.le_of_ble_eq_true h1
    have e2 : IE k < 3661 := Nat.blt_eq.mp h2
    have hij : Nat.beq ((IE k - 61) % 60) ((IE k - 61) / 60) = false := by simpa using h3
    exact Or.inr (Or.inr (Or.inr (Or.inl (prodMem_of hx (by omega) (by omega)
      (Nat.ne_of_beq_eq_false hij) (Nat.eq_of_beq_eq_true h4) h5))))
  · have h1 := (and_of hd).2
    rw [Bool.or_eq_true] at h1
    rcases h1 with h1 | h1
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (enumMemA_of hx h1)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (enumMemB_of hx h1)))))

theorem facts : plusFactorsEnumA () = true ∧ plusFactorsEnumB () = true ∧
    plusFactorsSizeA () = true ∧ plusFactorsSizeB () = true ∧ plusFactorsSimpleA () = true ∧
    plusFactorsSimpleB () = true ∧ plusFactorsTableOK () = true ∧ plusFactorsMemGens () = true ∧
    plusFactorsCommGens () = true ∧ plusFactorsDisjoint () = true ∧
    plusFactorsConjGens () = true ∧ plusFactorsNonabelian () = true ∧
    plusFactorsInvolutions () = true :=
  ⟨enumA, enumB, sizeA, sizeB, simpleA, simpleB, tableOK, memGens, commGens, disjoint, conjGens,
    nonabelian, involutions⟩

end CertificateChecks.KernelPlusF
