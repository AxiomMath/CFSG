module

public import Certificates.Kernel.Sporadic.Q3A.K0
public import Certificates.Kernel.Sporadic.OddCore.SuzTwCF
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.Spor.PackFld
public import CFSG.Certificates.Kernel.HeFixKFix
public import CFSG.Certificates.Kernel.PackSetSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Monster.B.Co2.PermArr

public section

namespace CertificateChecks.KernelSpor.Q3AG

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzRecog.Q3A.Check
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Q3AK
open CertificateChecks.KernelSpor.SuzTwCF (P p_comp eqA_P pidn_P)

local notation "pgk" => pg 11 (mask 11)
local notation "pc" => pcomp 1782 11 (mask 11)
local notation "Idn" => pidn 1782 11
local notation "cn" => canonK 1782 11 (mask 11) (1782 * 11)

theorem sN (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem sB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem nIf_eq (c : Bool) (t e : Nat) : nIf(c, t, e) = if c = true then t else e := by
  cases c <;> rfl

theorem bIf_eq (c t e : Bool) : bIf(c, t, e) = if c = true then t else e := by cases c <;> rfl

theorem band (a b : Bool) : bAnd(a, b) = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp

theorem beqN (a b : Nat) : (a == b) = Nat.beq a b := by
  by_cases h : a = b
  · subst h
    rw [Nat.beq_refl]
    exact beq_self_eq_true a
  · rw [Bool.eq_false_iff.2 (fun e => h (Nat.eq_of_beq_eq_true e))]
    simpa using h

theorem nbeq {a b : Nat} : Nat.beq a b = true ↔ a = b := ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

theorem nblt {a b : Nat} : Nat.blt a b = true ↔ a < b := by rw [Nat.blt_eq]

theorem nbeq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false :=
  Bool.eq_false_iff.2 fun e => h (Nat.eq_of_beq_eq_true e)

theorem allN_get {n : Nat} {f : Nat → Bool} (h : allN n f = true) {i : Nat} (hi : i < n) :
    f i = true := CFSG.KS.allN_spec h i hi

theorem allBlk_get {b len : Nat} {f : Nat → Bool} (h : allBlk b f len = true) {i : Nat}
    (h1 : b ≤ i) (h2 : i < b + len) : f i = true := by
  have := CFSG.KS.allBlk_spec h (i - b) (by omega)
  have e : Nat.add b (i - b) = i := by
    change b + (i - b) = i
    omega
  rwa [e] at this

theorem slices160 {f : Nat → Bool} (h : ∀ s < 143, allBlk (Nat.mul 160 s) f 160 = true) :
    ∀ i < 22880, f i = true := by
  intro i hi
  exact allBlk_get (h (i / 160) (by omega)) (by change 160 * (i / 160) ≤ i; omega)
    (by change i < 160 * (i / 160) + 160; omega)

theorem hexTable_get {d n k0 : Nat} {s : String} {i : Nat} (hi : i < n) :
    (hexTable d n k0 s)[i]! = hexAt s.toUTF8 (d * (k0 + i)) d := by
  unfold hexTable
  rw [getElem!_pos _ i (by simpa using hi)]
  simp

theorem hexTable_size {d n k0 : Nat} {s : String} : (hexTable d n k0 s).size = n := by
  unfold hexTable
  simp

theorem hex_entry {cs : List Char} {s : String} {n N : Nat} {F : Nat → Nat}
    (hs : s = String.ofList cs) (h : CFSG.KC.Misc.HexFlat.hexFlat cs 4 n 16 N F = true)
    {e : Nat} (he : e < n * N) (hn : 0 < n) :
    hexAt s.toUTF8 (4 * e) 4 = pg 16 (mask 16) (F (e / n)) (e % n) := by
  have hj : e / n < N := Nat.div_lt_of_lt_mul he
  have h1 := CFSG.KC.Misc.HexFlat.hexTable_sound h (e / n) hj
  rw [← hs] at h1
  have h2 := congrArg (fun a : Array Nat => a[e % n]!) h1
  rw [hexTable_get (Nat.mod_lt _ hn), CFSG.KC.HeFixK.unpack_getElem! (Nat.mod_lt _ hn),
    Nat.div_add_mod] at h2
  exact h2

theorem hx_get {cs : List Char} {s : String} {F : Nat → Nat} (hs : s = String.ofList cs)
    (h : CFSG.KC.Misc.HexFlat.hexFlat cs 4 160 16 143 F = true) {i : Nat} (hi : i < 22880) :
    (hexTable 4 22880 0 s)[i]! = hx F i := by
  rw [hexTable_get hi, Nat.zero_add, hex_entry hs h (by omega) (by norm_num)]
  rfl

theorem tpar_get {i : Nat} (hi : i < 22880) : tpar[i]! = tparK i := by
  unfold tpar
  exact hx_get Q3ATP.eq Q3ATP.all hi

theorem tlab_get {i : Nat} (hi : i < 22880) : tlab[i]! = tlabK i := by
  unfold tlab
  exact hx_get Q3ATL.eq Q3ATL.all hi

theorem froot_get {i : Nat} (hi : i < 22880) : froot[i]! = frootK i := by
  unfold froot
  exact hx_get Q3AFR.eq Q3AFR.all hi

theorem fpar_get {i : Nat} (hi : i < 22880) : fpar[i]! = fparK i := by
  unfold fpar
  exact hx_get Q3AFP.eq Q3AFP.all hi

theorem flab_get {i : Nat} (hi : i < 22880) : flab[i]! = flabK i := by
  unfold flab
  exact hx_get Q3AFL.eq Q3AFL.all hi

theorem fdep_get {i : Nat} (hi : i < 22880) : fdep[i]! = fdepK i := by
  unfold fdep
  exact hx_get Q3AFD.eq Q3AFD.all hi

theorem tpar_size : tpar.size = 22880 := by unfold tpar; exact hexTable_size
theorem tlab_size : tlab.size = 22880 := by unfold tlab; exact hexTable_size
theorem froot_size : froot.size = 22880 := by unfold froot; exact hexTable_size
theorem fpar_size : fpar.size = 22880 := by unfold fpar; exact hexTable_size
theorem flab_size : flab.size = 22880 := by unfold flab; exact hexTable_size
theorem fdep_size : fdep.size = 22880 := by unfold fdep; exact hexTable_size

theorem span_get {n k0 b : Nat} (hb : b < n) (he : k0 + b < 1016) :
    (hexTable 4 n k0 CFSG.Sporadic.SuzRecog.Q3AVtxData.spanHex)[b]! = spanK (k0 + b) := by
  rw [hexTable_get hb, hex_entry Q3ASP.eq Q3ASP.all (by omega) (by norm_num)]
  rfl

theorem pB0 : P b0 Suz2306.B0 := ⟨Suz2306.b0Arr_eq, kcB0⟩

theorem pB1 : P b1 Suz2306.B1 := ⟨Suz2306.b1Arr_eq, kcB1⟩

theorem pBA (s : Nat) : P (bA s) (BK s) := by
  unfold bA BK
  rw [beqN]
  cases h : Nat.beq s 0
  · exact pB1
  · exact pB0

theorem cBK (s : Nat) : cn (BK s) = true := (pBA s).2

theorem pInv {a : Array Nat} {A AI : Nat} (ha : P a A) (hi : invEqK 1782 11 (mask 11) (1782 * 11) A AI = true)
    (hc : cn AI = true) : P (invCand 1782 a) AI ∧ isInvA 1782 a (invCand 1782 a) = true := by
  have h := invEqK_sound hi
  rw [ha.1, h.1]
  exact ⟨⟨rfl, hc⟩, h.2⟩

theorem cI {j : Nat} (hj : j < 13) : cn (Q3AI j) = true := allN_get kcI hj

theorem pBAi {s : Nat} (hs : s < 2) :
    P (bAi s) (BIK s) ∧ isInvA 1782 (bA s) (bAi s) = true := by
  unfold bAi BIK bA b0i b1i
  rw [beqN]
  interval_cases s
  · exact pInv pB0 kiB0 (cI (by norm_num))
  · exact pInv pB1 kiB1 (cI (by norm_num))

theorem pRho : P CFSG.Sporadic.SuzRecog.LevelTwoData.rhoArr RHO := SuzTwCF.pRho

theorem pRhoI : P rhoInv (Q3AI 2) ∧
    isInvA 1782 CFSG.Sporadic.SuzRecog.LevelTwoData.rhoArr rhoInv = true :=
  pInv pRho kiR (cI (by norm_num))

theorem xStrong_eq {j : Nat} (hj : j < 2) :
    CFSG.Sporadic.SuzRecog.LevelTwoData.xStrong j = unpack 1782 11 (Q3AX.F j) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound Q3AX.all j hj
  rw [← Q3AX.eq] at h
  unfold CFSG.Sporadic.SuzRecog.LevelTwoData.xStrong
  exact h

theorem xA0 : xA 0 = CFSG.Sporadic.SuzRecog.LevelTwoData.xStrong 0 := ite_eq_left rfl
theorem xA1 : xA 1 = CFSG.Sporadic.SuzRecog.LevelTwoData.xStrong 1 := ite_eq_right (by decide)
theorem XK0 : XK 0 = Q3AX.F 0 := rfl
theorem XK1 : XK 1 = Q3AX.F 1 := rfl
theorem XIK0 : XIK 0 = Q3AI 3 := rfl
theorem XIK1 : XIK 1 = Q3AI 4 := rfl

theorem pX {s : Nat} (hs : s < 2) : P (xA s) (XK s) := by
  obtain rfl | rfl : s = 0 ∨ s = 1 := by omega
  · rw [xA0, XK0]
    exact ⟨xStrong_eq (by norm_num), kcX0⟩
  · rw [xA1, XK1]
    exact ⟨xStrong_eq (by norm_num), kcX1⟩

theorem pXI {s : Nat} (hs : s < 2) :
    P (invCand 1782 (xA s)) (XIK s) ∧ isInvA 1782 (xA s) (invCand 1782 (xA s)) = true := by
  have hx := pX hs
  obtain rfl | rfl : s = 0 ∨ s = 1 := by omega
  · rw [XK0] at hx
    rw [XIK0]
    exact pInv hx kiX0 (cI (by norm_num))
  · rw [XK1] at hx
    rw [XIK1]
    exact pInv hx kiX1 (cI (by norm_num))

theorem unpack_size {n w X : Nat} : (unpack n w X).size = n := by
  unfold unpack
  exact Array.size_ofFn

theorem unpack_getElem {n w X t : Nat} (h : t < (unpack n w X).size) :
    (unpack n w X)[t] = pg w (mask w) X t := by
  simp only [unpack, Array.getElem_ofFn]

@[expose] def FL (l : Array Nat) (X : Nat) : Prop :=
  l = unpack 162 11 X ∧ ∀ t < 162, pgk X t < 1782

theorem img_FL {G X : Nat} (hG : cn G = true) (hX : ∀ t < 162, pgk X t < 1782) :
    FL (imgA (unpack 1782 11 G) (unpack 162 11 X)) (imgK G X) := by
  have e : ∀ t < 162, pgk (imgK G X) t = pgk G (pgk X t) := fun t ht =>
    PackFld.pg_pcomp (by norm_num) ht
  refine ⟨?_, fun t ht => by rw [e t ht]; exact CFSG.KC.HeFixK.pg_lt_of_canonK hG (hX t ht)⟩
  apply Array.ext
  · simp only [imgA, Array.size_map, unpack_size]
  · intro t h1 h2
    have ht : t < 162 := by rwa [unpack_size] at h2
    simp only [imgA, Array.getElem_map]
    rw [unpack_getElem, unpack_getElem, CFSG.KC.HeFixK.unpack_getElem! (hX t ht), e t ht]

theorem f0_parts : (∀ t < 161, pgk (Q3AF 0) t < pgk (Q3AF 0) (t + 1)) ∧
    (∀ t < 162, pgk (Q3AF 0) t < 1782 ∧ pgk RHO (pgk (Q3AF 0) t) = pgk (Q3AF 0) t) ∧
    (∀ x < 1782, pgk RHO x = x → ∃ t < 162, pgk (Q3AF 0) t = x) := by
  have h := kF0
  unfold f0OK at h
  rw [band, band] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun t ht => nblt.1 (allN_get h1 ht), fun t ht => ?_, fun x hx hr => ?_⟩
  · have := allN_get h2 ht
    rw [sB, band] at this
    exact ⟨nblt.1 this.1, nbeq.1 this.2⟩
  · have := allN_get h3 hx
    rw [bIf_eq, ite_eq_left (nbeq.2 hr)] at this
    unfold memF at this
    by_contra hne
    have : allN 162 (fun t => Bool.not (Nat.beq (pgk (Q3AF 0) t) x)) = true :=
      PackFld.allN_of_forall fun t ht => by rw [nbeq_false (fun e => hne ⟨t, ht, e⟩)]; rfl
    simp_all

theorem f0_mono {a b : Nat} (hab : a < b) (hb : b < 162) : pgk (Q3AF 0) a < pgk (Q3AF 0) b := by
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h | h
    · exact (ih h (by omega)).trans (f0_parts.1 b (by omega))
    · subst h
      exact f0_parts.1 a (by omega)

theorem fix0_eq : fix0 = unpack 162 11 (Q3AF 0) := by
  have hr : ∀ x < 1782, CFSG.Sporadic.SuzRecog.LevelTwoData.rhoArr[x]! = pgk RHO x := fun x hx => by
    rw [pRho.1]
    exact CFSG.KC.HeFixK.unpack_getElem! hx
  apply Array.ext'
  refine List.Pairwise.eq_of_mem_iff (r := (· < ·)) ?_ ?_ fun x => ?_
  · unfold fix0
    rw [Array.toList_filter, Array.toList_range]
    exact List.pairwise_lt_range.filter _
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    have hj' : j < 162 := by rwa [Array.length_toList, unpack_size] at hj
    rw [Array.getElem_toList, Array.getElem_toList, unpack_getElem, unpack_getElem]
    exact f0_mono hij hj'
  · rw [Array.mem_toList_iff, Array.mem_toList_iff]
    unfold fix0
    rw [Array.mem_filter, Array.mem_range, beq_iff_eq]
    constructor
    · rintro ⟨hx, hfx⟩
      rw [hr x hx] at hfx
      obtain ⟨t, ht, rfl⟩ := f0_parts.2.2 x hx hfx
      have ht' : t < (unpack 162 11 (Q3AF 0)).size := by rwa [unpack_size]
      exact Array.mem_iff_getElem.2 ⟨t, ht', unpack_getElem ht'⟩
    · intro hm
      obtain ⟨t, ht, rfl⟩ := Array.mem_iff_getElem.1 hm
      have ht' : t < 162 := by rwa [unpack_size] at ht
      rw [unpack_getElem]
      obtain ⟨h1, h2⟩ := f0_parts.2.1 t ht'
      exact ⟨h1, by rw [hr _ h1, h2]⟩

theorem fix0_FL : FL fix0 (Q3AF 0) := ⟨fix0_eq, fun t ht => (f0_parts.2.1 t ht).1⟩

theorem fix0_size : fix0.size = 162 := by rw [fix0_eq, unpack_size]

theorem vt_parts (hv : ∀ i < 22880, vtOK i = true) {i : Nat} (hi : i < 22880) :
    (i ≠ 0 → tparK i < i ∧ tlabK i < 2 ∧ Q3AF i = imgK (BK (tlabK i)) (Q3AF (tparK i))) ∧
    searchK (keyF (Q3AF i)) = i ∧ sidx i < 22880 ∧ skey i = keyF (Q3AF (sidx i)) := by
  have h := hv i hi
  unfold vtOK at h
  obtain ⟨h1, h23⟩ := (band _ _).1 h
  obtain ⟨h2, h3⟩ := (band _ _).1 h23
  simp only [sB] at h3
  obtain ⟨h3, h4⟩ := (band _ _).1 h3
  refine ⟨fun h0 => ?_, nbeq.1 h2, nblt.1 h3, nbeq.1 h4⟩
  rw [bIf_eq, ite_eq_right (by rw [nbeq]; exact h0)] at h1
  simp only [sB] at h1
  obtain ⟨h5, h6⟩ := (band _ _).1 h1
  obtain ⟨h6, h7⟩ := (band _ _).1 h6
  exact ⟨nblt.1 h5, nblt.1 h6, nbeq.1 h7⟩

theorem fimgAt_eq (i : Nat) :
    fimgAt i = if 0 < i ∧ tpar[i]! < i then imgA (bA tlab[i]!) (fimgAt tpar[i]!) else fix0 := by
  rw [fimgAt]
  split_ifs <;> rfl

theorem fimg_get {i : Nat} (hi : i < 22880) : fimg[i]! = fimgAt i := by
  unfold fimg
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_map, Array.getElem_range]

section Vertices

variable (hv : ∀ i < 22880, vtOK i = true)
include hv

theorem fimgAt_FL : ∀ i < 22880, FL (fimgAt i) (Q3AF i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rw [fimgAt_eq]
    by_cases h0 : i = 0
    · subst h0
      simpa using fix0_FL
    · obtain ⟨hp, hl, he⟩ := (vt_parts hv hi).1 h0
      rw [tpar_get hi, tlab_get hi, ite_eq_left ⟨by omega, hp⟩, he]
      obtain ⟨e1, e2⟩ := ih _ hp (by omega)
      rw [e1, (pBA _).1]
      exact img_FL (cBK _) e2

theorem fimg_FL {i : Nat} (hi : i < 22880) : FL fimg[i]! (Q3AF i) := by
  rw [fimg_get hi]
  exact fimgAt_FL hv i hi

end Vertices

theorem mix_toNat {x : Nat} (hx : x < 1782) : (mix x).toNat = mixK x := by
  unfold mix mixK
  simp only [sN, UInt64.toNat_xor, UInt64.toNat_mul, UInt64.toNat_add, UInt64.toNat_shiftRight,
    UInt64.toNat_ofNat, Nat.toUInt64]
  have h1 : x % 2 ^ 64 = x := Nat.mod_eq_of_lt (by omega)
  simp only [UInt64.toNat_ofNat', h1]
  norm_num [Nat.mod_eq_of_lt (by omega : x + 1 < 2 ^ 64)]
  rfl

theorem wt_get {x : Nat} (hx : x < 1782) : (wt[x]!).toNat = wtK x := by
  have h : wt[x]! = mix x := by
    unfold wt
    rw [getElem!_pos _ x (by simpa using hx)]
    simp
  rw [h, mix_toNat hx]
  exact (nbeq.1 (allN_get kWt hx)).symm

theorem foldl_wt (L : List Nat) (hL : ∀ x ∈ L, x < 1782) (a : UInt64) :
    (L.foldl (fun acc x => acc + wt[x]!) a).toNat = (a.toNat + (L.map wtK).sum) % 2 ^ 64 := by
  induction L generalizing a with
  | nil => simp [Nat.mod_eq_of_lt a.toNat_lt]
  | cons x L ih =>
    rw [List.foldl_cons, ih (fun y hy => hL y (List.mem_cons_of_mem _ hy)), UInt64.toNat_add,
      wt_get (hL x List.mem_cons_self), List.map_cons, List.sum_cons, Nat.mod_add_mod,
      Nat.add_assoc]

theorem unpack_toList (n w X : Nat) :
    (unpack n w X).toList = (List.range n).map (pg w (mask w) X) := by
  apply List.ext_getElem
  · rw [Array.length_toList, unpack_size, List.length_map, List.length_range]
  · intro t h1 h2
    rw [Array.getElem_toList, unpack_getElem, List.getElem_map, List.getElem_range]

theorem foldr_sum (n : Nat) (w : Nat → Nat) (s : Nat) :
    (List.range n).foldr (fun t a => Nat.add a (w t)) s = s + ((List.range n).map w).sum := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, ih, List.map_append,
      List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    change s + w n + _ = _
    omega

theorem keyOf_FL {l : Array Nat} {X : Nat} (h : FL l X) : (keyOf l).toNat = keyF X := by
  unfold keyOf keyF
  rw [← Array.foldl_toList, foldl_wt _ (fun x hx => ?_)]
  · rw [CFSG.KC.Pack.foldN_eq, foldr_sum, UInt64.toNat_zero, h.1, unpack_toList, List.map_map]
    rfl
  · rw [h.1, unpack_toList] at hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
    exact h.2 t (List.mem_range.1 ht)

theorem searchK_cases (hv : ∀ i < 22880, vtOK i = true) (k : Nat) : searchK k = 22880 ∨
    (searchK k < 22880 ∧ ∃ m < 22880, skey m = k ∧ searchK k = sidx m) := by
  unfold searchK
  rw [sN, nIf_eq]
  split_ifs with h
  · rw [band, nblt, nbeq] at h
    exact Or.inr ⟨(vt_parts hv h.1).2.2.1, _, h.1, h.2, rfl⟩
  · exact Or.inl rfl

theorem find_range {p : Nat → Bool} {s : Nat} :
    ∀ n, (∀ i < n, p i = true ↔ i = s) → (List.range n).find? p = if s < n then some s else none
  | 0, _ => by simp
  | n + 1, h => by
    rw [List.range_succ, List.find?_append, find_range n fun i hi => h i (by omega)]
    by_cases hs : s < n
    · rw [ite_eq_left hs, ite_eq_left (by omega)]
      rfl
    · rw [ite_eq_right hs]
      simp only [Option.none_or, List.find?_cons, List.find?_nil]
      by_cases hn : s = n
      · subst hn
        rw [ite_eq_left (by omega), (h s (by omega)).2 rfl]
      · rw [ite_eq_right (by omega)]
        have : p n = false := Bool.eq_false_iff.2 fun e => hn ((h n (by omega)).1 e).symm
        rw [this]

theorem keyIdx_eq (hv : ∀ i < 22880, vtOK i = true) (k : UInt64) :
    keyIdx k = searchK k.toNat := by
  have hk : ∀ i < 22880, (keyOf fimg[i]! == k) = true ↔ i = searchK k.toNat := by
    intro i hi
    have hkey := keyOf_FL (fimg_FL hv hi)
    rw [beq_iff_eq]
    constructor
    · rintro rfl
      rw [hkey]
      exact ((vt_parts hv hi).2.1).symm
    · intro he
      rcases searchK_cases hv k.toNat with h | ⟨hlt, m, hm, hmk, hs⟩
      · omega
      · obtain ⟨-, -, hsl, hsk⟩ := vt_parts hv hm
        apply UInt64.toNat_inj.1
        rw [hkey, he, hs, ← hsk, hmk]
  unfold keyIdx
  rw [find_range (p := fun i => keyOf fimg[i]! == k) 22880 hk]
  rcases searchK_cases hv k.toNat with h | ⟨hlt, -⟩
  · rw [h]
    rfl
  · rw [ite_eq_left hlt]
    rfl

theorem actIdx_eq (hv : ∀ i < 22880, vtOK i = true) {a : Array Nat} {G : Nat} (ha : P a G)
    {i : Nat} (hi : i < 22880) : actIdx a i = actK G i := by
  unfold actIdx actK
  obtain ⟨e1, e2⟩ := fimg_FL hv hi
  rw [keyIdx_eq hv, e1, ha.1, keyOf_FL (img_FL ha.2 e2)]

theorem cArr_eq (i : Nat) :
    cArr i = if 0 < i ∧ tpar[i]! < i then compA 1782 (bA tlab[i]!) (cArr tpar[i]!) else idA 1782 := by
  rw [cArr]
  split_ifs <;> rfl

theorem cArrInv_eq (i : Nat) :
    cArrInv i =
      if 0 < i ∧ tpar[i]! < i then compA 1782 (cArrInv tpar[i]!) (bAi tlab[i]!) else idA 1782 := by
  rw [cArrInv]
  split_ifs <;> rfl

theorem cond_eq {i : Nat} (hi : i < 22880) :
    bAnd(Nat.blt 0 i, Nat.blt (tparK i) i) = true ↔ 0 < i ∧ tpar[i]! < i := by
  rw [band, nblt, nblt, tpar_get hi]

theorem p_cK : ∀ i < 22880, ∀ f, i < f → P (cArr i) (cK f i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi f hf
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    change P (cArr i) (nIf(bAnd(Nat.blt 0 i, Nat.blt (tparK i) i),
      strictN (cK f (tparK i)) (fun C => pc (BK (tlabK i)) C), Idn))
    rw [cArr_eq, nIf_eq, sN]
    by_cases h : 0 < i ∧ tpar[i]! < i
    · rw [ite_eq_left h, ite_eq_left ((cond_eq hi).2 h), ← tpar_get hi, ← tlab_get hi]
      exact p_comp (pBA _) (ih _ h.2 (by omega) f (by omega))
    · rw [ite_eq_right h, ite_eq_right (fun e => h ((cond_eq hi).1 e))]
      exact pidn_P

theorem p_cArr {i : Nat} (hi : i < 22880) : P (cArr i) (cA i) := p_cK i hi _ (Nat.lt_succ_self i)

theorem p_cIK (hv : ∀ i < 22880, vtOK i = true) :
    ∀ i < 22880, ∀ f, i < f → P (cArrInv i) (cIK f i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi f hf
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    change P (cArrInv i) (nIf(bAnd(Nat.blt 0 i, Nat.blt (tparK i) i),
      strictN (cIK f (tparK i)) (fun C => pc C (BIK (tlabK i))), Idn))
    rw [cArrInv_eq, nIf_eq, sN]
    by_cases h : 0 < i ∧ tpar[i]! < i
    · rw [ite_eq_left h, ite_eq_left ((cond_eq hi).2 h), ← tpar_get hi, ← tlab_get hi]
      have hl : tlab[i]! < 2 := by
        rw [tlab_get hi]
        exact ((vt_parts hv hi).1 (by omega)).2.1
      exact p_comp (ih _ h.2 (by omega) f (by omega)) (pBAi hl).1
    · rw [ite_eq_right h, ite_eq_right (fun e => h ((cond_eq hi).1 e))]
      exact pidn_P

theorem p_cArrInv (hv : ∀ i < 22880, vtOK i = true) {i : Nat} (hi : i < 22880) :
    P (cArrInv i) (cIA i) := p_cIK hv i hi _ (Nat.lt_succ_self i)

end CertificateChecks.KernelSpor.Q3AG

end
