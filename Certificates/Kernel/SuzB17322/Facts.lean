module

public import Certificates.Data.TabSuzB
public import CFSG.Sporadic.SuzOddCore.Perms
public import CFSG.RankThree.Native.PermEnumeration
public import Certificates.Kernel.SuzB17322.ChecksX
public import Certificates.Kernel.SuzPump.PairFacts
public import CFSG.Certificates.Kernel.K426KSound
public import CFSG.Certificates.Kernel.BfsPinSliceSound
public import CFSG.Certificates.Kernel.D4Sound
public import CFSG.Certificates.Kernel.Misc.ArrEnumSound
public import CFSG.Certificates.Kernel.Misc.ArrEnumOps
public import CFSG.Certificates.Kernel.Misc.CentHeadSound
public import CFSG.Certificates.Kernel.Misc.SupPow
public import CFSG.Certificates.Kernel.PermCent.OrbGroup
public import CFSG.Certificates.NativeValidSchreier
public import CFSG.Sporadic.SuzOddCore.SmallChain
import CFSG.Sporadic.SuzOddCore.ArraysCheckInputs
import CFSG.Sporadic.SuzOddCore.SmallChainCheckInputs
meta import CFSG.Sporadic.SuzOddCore.ArraysCheck
meta import Certificates.Data.CFSGNative.Schreier.Check
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Misc.ArrBind
public import CFSG.Certificates.LiftedSchreierData
public import CFSG.Sporadic.Th.F2Spec

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSuzB17322

open Subgroup
open CFSG.KS hiding levels
open CFSG.KC.Enum CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K CFSG.KC.K426K CFSG.KC.BfsPin
open CFSG.KC.CentSrch CFSG.KC.CentHead CertificateChecks.KernelSpor CertificateChecks.KernelSuzPump
open CFSG.HardMathSupport.Dickson.I271.TabSuzB CFSG.HardMathSupport.Dickson.I271.TabSuzFuse
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu
open CFSG.Sporadic.SuzOddCore CFSG.Certificates
open CFSG.Monster.B.Co2 (permOfArr)

@[expose] noncomputable def pp (p : Nat) : Equiv.Perm (Fin 1782) := permOfArr 1782 (unpack 1782 11 p)

theorem prep_pp {p : Nat} (hp : permB 1782 11 p = true) : Orb.PRep 1782 11 p (pp p) :=
  Orb.prep_of_rep (rep_of_validA (validA_of hp))

theorem prep_cm {p q : Nat} {g h : Equiv.Perm (Fin 1782)} (hp : Orb.PRep 1782 11 p g)
    (hq : Orb.PRep 1782 11 q h) : Orb.PRep 1782 11 (cm 1782 11 p q) (g * h) :=
  Orb.prep_pcomp (by norm_num) hp hq

theorem prep_cj {p q : Nat} {g h : Equiv.Perm (Fin 1782)} (hp : permB 1782 11 p = true)
    (hg : Orb.PRep 1782 11 p g) (hh : Orb.PRep 1782 11 q h) :
    Orb.PRep 1782 11 (cj 1782 11 p q) (g * h * g⁻¹) := by
  rw [mul_assoc]
  exact prep_cm hg (prep_cm hh (CFSG.KC.OrbGroup.prep_inv hg hp))

theorem prep_pw {p : Nat} (hp : permB 1782 11 p = true) {g : Equiv.Perm (Fin 1782)}
    (hg : Orb.PRep 1782 11 p g) (e : Nat) : Orb.PRep 1782 11 (pw 1782 11 p e) (g ^ e) := by
  apply Orb.prep_of_rep
  have h := rep_powArr (Orb.rep_unpack hg) e
  rw [pow_unpack hw hp] at h
  exact h

theorem prep_id : Orb.PRep 1782 11 (pidn 1782 11) 1 := Orb.prep_pidn (by norm_num) (by norm_num)

theorem eq_of_beq {p q : Nat} {g h : Equiv.Perm (Fin 1782)} (e : Nat.beq p q = true)
    (hp : Orb.PRep 1782 11 p g) (hq : Orb.PRep 1782 11 q h) : g = h := by
  rw [Nat.eq_of_beq_eq_true e] at hp
  exact CFSG.KC.OrbGroup.prep_eq hp hq

theorem code_eq {p q : Nat} (hp : permB 1782 11 p = true) (hq : permB 1782 11 q = true)
    (h : pp p = pp q) : p = q := by
  have e := (CFSG.Monster.B.Co2.eqA_iff (rep_of_validA (validA_of hp))
    (rep_of_validA (validA_of hq))).2 h
  rw [eqA_unpack hw hp hq] at e
  exact Nat.eq_of_beq_eq_true e

theorem comm_of {p q : Nat} (hp : permB 1782 11 p = true) (hq : permB 1782 11 q = true)
    (h : Nat.beq (cm 1782 11 p q) (cm 1782 11 q p) = true) : pp p * pp q = pp q * pp p :=
  eq_of_beq h (prep_cm (prep_pp hp) (prep_pp hq)) (prep_cm (prep_pp hq) (prep_pp hp))

theorem aN : AE.N = 729 := Nat.eq_of_beq_eq_true nE.1
theorem aNg : AE.ng = 4 := Nat.eq_of_beq_eq_true nE.2.1
theorem qN : QE.N = 16 := Nat.eq_of_beq_eq_true nE.2.2.1
theorem qNg : QE.ng = 3 := Nat.eq_of_beq_eq_true nE.2.2.2.1
theorem bN : BE.N = 81 := Nat.eq_of_beq_eq_true nE.2.2.2.2.1
theorem bNg : BE.ng = 4 := Nat.eq_of_beq_eq_true nE.2.2.2.2.2.1
theorem kN : KC.N = 432 := Nat.eq_of_beq_eq_true nE.2.2.2.2.2.2.1
theorem kNg : KC.ng = 2 := Nat.eq_of_beq_eq_true nE.2.2.2.2.2.2.2

theorem get_map {f : Array Nat → Array Nat} {a : Array (Array Nat)} {k : Nat} (hk : k < a.size) :
    (a.map f)[k]! = f a[k]! := by
  rw [getElem!_pos (a.map f) k (by simpa using hk), getElem!_pos a k hk, Array.getElem_map]

theorem pXB : permB 1782 11 X = true := pXH.1

theorem pH : ∀ k < 9, permB 1782 11 (H k) = true := pXH.2

theorem hGet : ∀ k < 9, hGs[k]! = unpack 1782 11 (H k) := fun k hk => by
  have e : hGs[k]! = rebuild (levels ()) hT[k]! := get_map (lt_of_lt_of_eq hk rfl)
  rw [e]
  exact rebuild_eq (rbH k hk)

theorem aSize : (aGens ()).size = 4 := by
  unfold aGens
  rw [Array.size_map]
  rfl

theorem aGet : ∀ k < 4, (aGens ())[k]! = unpack 1782 11 (AE.G k) := by
  intro k hk
  obtain ⟨h1, h2⟩ := rbA k hk
  have e : (aGens ())[k]! = rebuild (levels ()) aTuples[k]! := get_map (lt_of_lt_of_eq hk rfl)
  rw [e, rebuild_eq h1, Nat.eq_of_beq_eq_true h2]

theorem bindA : BindA 1782 11 (aGens ()) AE.ng AE.G := by
  rw [aNg]
  exact ⟨aSize, aGet⟩

theorem qSize : qGs.size = 3 := by
  first
  | rfl
  | simp [qGs, hGs, hT]

theorem qGet : ∀ k < 3, qGs[k]! = unpack 1782 11 (QE.G k) := by
  intro k hk
  have e : qGs[k]! = hGs[k + 1]! := by
    first
    | (interval_cases k <;> rfl)
    | (rw [getElem!_pos qGs k (by rw [qSize]; exact hk),
        getElem!_pos hGs (k + 1) (by simp [hGs, hT]; omega)]
       simp [qGs, Array.getElem_extract, Nat.add_comm])
  rw [e, hGet (k + 1) (by omega), Nat.eq_of_beq_eq_true (bindC.1 k hk)]

theorem bindQ : BindA 1782 11 qGs QE.ng QE.G := by
  rw [qNg]
  exact ⟨qSize, qGet⟩

theorem bG0 : BE.G 0 = H 4 := (Nat.eq_of_beq_eq_true bindC.2.1).symm

theorem bG : ∀ k < 3, BE.G (k + 1) = H (k + 6) := fun k hk =>
  (Nat.eq_of_beq_eq_true (bindC.2.2.1 k hk)).symm

theorem bGet : ∀ k < 4, bGs[k]! = unpack 1782 11 (BE.G k) := by
  intro k hk
  interval_cases k
  · change hGs[4]! = _
    rw [hGet 4 (by norm_num), bG0]
  · change hGs[6]! = _
    rw [hGet 6 (by norm_num), bG 0 (by norm_num)]
  · change hGs[7]! = _
    rw [hGet 7 (by norm_num), bG 1 (by norm_num)]
  · change hGs[8]! = _
    rw [hGet 8 (by norm_num), bG 2 (by norm_num)]

theorem bindB : BindA 1782 11 bGs BE.ng BE.G := by
  rw [bNg]
  exact ⟨rfl, bGet⟩

theorem pA : ∀ k < AE.ng, permB 1782 11 (AE.G k) = true := fun k hk =>
  pAG k (by rw [aNg] at hk; exact hk)

theorem pQ : ∀ k < QE.ng, permB 1782 11 (QE.G k) = true := fun k hk => by
  rw [qNg] at hk
  rw [← Nat.eq_of_beq_eq_true (bindC.1 k hk)]
  exact pH (k + 1) (by omega)

theorem pB : ∀ k < BE.ng, permB 1782 11 (BE.G k) = true := by
  intro k hk
  rw [bNg] at hk
  rcases k with _ | k
  · rw [bG0]
    exact pH 4 (by norm_num)
  · rw [bG k (by omega)]
    exact pH (k + 6) (by omega)

theorem kG0 : KC.G 0 = H 5 := (Nat.eq_of_beq_eq_true bindC.2.2.2.1).symm

theorem kG1 : KC.G 1 = H 2 := (Nat.eq_of_beq_eq_true bindC.2.2.2.2.1).symm

theorem pK : ∀ k < KC.ng, permB 1782 11 (KC.G k) = true := by
  intro k hk
  rw [kNg] at hk
  interval_cases k
  · rw [kG0]
    exact pH 5 (by norm_num)
  · rw [kG1]
    exact pH 2 (by norm_num)

theorem okA : bfsK 1782 11 AE.ng AE.G AE.N AE.T AE.E AE.S = true :=
  bfsK_of_slices (L := 81) (K := 9) (C := AE.C) (aN.trans (by norm_num)) (by norm_num) hw AE.g
    AE.csAll AE.t0 AE.dist (Nat.eq_of_beq_eq_true AE.c0) (Nat.eq_of_beq_eq_true AE.cK) AE.rsAll

theorem okB : bfsK 1782 11 BE.ng BE.G BE.N BE.T BE.E BE.S = true :=
  bfsK_of_slices (L := 27) (K := 3) (C := BE.C) (bN.trans (by norm_num)) (by norm_num) hw BE.g
    BE.csAll BE.t0 BE.dist (Nat.eq_of_beq_eq_true BE.c0) (Nat.eq_of_beq_eq_true BE.cK) BE.rsAll

theorem enumA : enumOK 1782 (aGens ()) aKeys (enumBfs 1782 (aGens ()) aKeys 800) = true ∧
    (enumBfs 1782 (aGens ()) aKeys 800).pts.size = AE.N ∧
    ∀ i < AE.N, (enumBfs 1782 (aGens ()) aKeys 800).pts[i]! = unpack 1782 11 (AE.T i) :=
  enum_of (fuel := 800) bindA pA okA (by decide) AE.keys (by rw [aN]; omega)

theorem enumQ : enumOK 1782 qGs smallBaseNat (enumBfs 1782 qGs smallBaseNat 16) = true ∧
    (enumBfs 1782 qGs smallBaseNat 16).pts.size = QE.N ∧
    ∀ i < QE.N, (enumBfs 1782 qGs smallBaseNat 16).pts[i]! = unpack 1782 11 (QE.T i) :=
  enum_of (fuel := 16) bindQ pQ QE.ok (by decide) QE.keys (le_of_eq qN)

theorem enumB : enumOK 1782 bGs smallBaseNat (enumBfs 1782 bGs smallBaseNat 81) = true ∧
    (enumBfs 1782 bGs smallBaseNat 81).pts.size = BE.N ∧
    ∀ i < BE.N, (enumBfs 1782 bGs smallBaseNat 81).pts[i]! = unpack 1782 11 (BE.T i) :=
  enum_of (fuel := 81) bindB pB okB (by decide) BE.keys (le_of_eq bN)

theorem pAT : ∀ i < AE.N, permB 1782 11 (AE.T i) = true := CFSG.KC.D4K.permB_pts okA pA

noncomputable abbrev A : Subgroup (Equiv.Perm (Fin 1782)) := closure (permsA 1782 (aGens ()))

theorem cardA : Nat.card A = 729 := by
  rw [(enumOK_spec (by decide) enumA.1).2.1, enumA.2.1, aN]

theorem cardQ : Nat.card (closure (permsA 1782 qGs)) = 16 := by
  rw [(enumOK_spec (by decide) enumQ.1).2.1, enumQ.2.1, qN]

theorem cardB : Nat.card (closure (permsA 1782 bGs)) = 81 := by
  rw [(enumOK_spec (by decide) enumB.1).2.1, enumB.2.1, bN]

theorem memAT : ∀ j < AE.N, pp (AE.T j) ∈ A := fun j hj => by
  refine ((enumOK_spec (by decide) enumA.1).1 _).2 ⟨j, by rw [enumA.2.1]; exact hj, ?_⟩
  rw [enumA.2.2 j hj]
  rfl

theorem memA' {z : Nat} {g : Equiv.Perm (Fin 1782)} (hz : Orb.PRep 1782 11 z g)
    (h : memIdxK AE.N AE.T AE.S z = true) : g ∈ A := by
  obtain ⟨j, hj, rfl⟩ := memIdxK_spec h
  rw [CFSG.KC.OrbGroup.prep_eq hz (prep_pp (pAT j hj))]
  exact memAT j hj

theorem gensOf {gs : Array (Array Nat)} {m : Nat} {F : Nat → Nat} (hb : BindA 1782 11 gs m F)
    {r : Equiv.Perm (Fin 1782)} (hr : r ∈ permsA 1782 gs) : ∃ k < m, r = pp (F k) := by
  obtain ⟨k, hk, rfl⟩ := hr
  have hk' : k < m := by
    rw [← hb.1]
    exact hk
  refine ⟨k, hk', ?_⟩
  dsimp only
  rw [hb.2 k hk']
  rfl

theorem gen_mem {gs : Array (Array Nat)} {m : Nat} {F : Nat → Nat} (hb : BindA 1782 11 gs m F)
    {k : Nat} (hk : k < m) : pp (F k) ∈ closure (permsA 1782 gs) := by
  refine subset_closure ⟨k, by rw [hb.1]; exact hk, ?_⟩
  change permOfArr 1782 gs[k]! = pp (F k)
  rw [hb.2 k hk]
  rfl

theorem conj_mem_closure {G : Type*} [Group G] {s : Set G} {h : G}
    (hs : ∀ a ∈ s, h * a * h⁻¹ ∈ closure s) : ∀ r ∈ closure s, h * r * h⁻¹ ∈ closure s := by
  intro r hr
  induction hr using Subgroup.closure_induction with
  | mem a ha => exact hs a ha
  | one => simp
  | mul a b _ _ iha ihb =>
    have e : h * (a * b) * h⁻¹ = (h * a * h⁻¹) * (h * b * h⁻¹) := by group
    rw [e]
    exact mul_mem iha ihb
  | inv a _ ih =>
    have e : h * a⁻¹ * h⁻¹ = (h * a * h⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem ih

theorem card_mul_le_of_conj {G : Type*} [Group G] [Finite G] (C : Subgroup G) (y : G) {N : Nat}
    (c : Nat → G) (hreach : ∀ i < N, ∃ h ∈ C, c i = h * y * h⁻¹)
    (hinj : ∀ i < N, ∀ j < N, c i = c j → i = j) :
    N * Nat.card ↥(centralizer ({y} : Set G) ⊓ C) ≤ Nat.card C := by
  classical
  let K : Subgroup C := (centralizer ({y} : Set G) ⊓ C).subgroupOf C
  have hex : ∀ i : Fin N, ∃ h : C, c i = (h : G) * y * (h : G)⁻¹ := fun i => by
    obtain ⟨h, hm, e⟩ := hreach i i.2
    exact ⟨⟨h, hm⟩, e⟩
  choose hf hfs using hex
  let f : Fin N → C ⧸ K := fun i => QuotientGroup.mk (hf i)
  have hfi : Function.Injective f := by
    intro i j e
    have hm : (hf i)⁻¹ * hf j ∈ K := QuotientGroup.eq.1 e
    rw [mem_subgroupOf] at hm
    have hu := mem_centralizer_singleton_iff.1 (mem_inf.1 hm).1
    have hc : (((hf i)⁻¹ * hf j : C) : G) = ((hf i : G))⁻¹ * (hf j : G) := by simp
    rw [hc] at hu
    have e2 : c j = c i := by
      rw [hfs j, hfs i]
      calc (hf j : G) * y * (hf j : G)⁻¹
          = (hf i : G) * ((((hf i : G))⁻¹ * (hf j : G)) * y) * (((hf i : G))⁻¹ * (hf j : G))⁻¹ *
              (hf i : G)⁻¹ := by group
        _ = (hf i : G) * (y * (((hf i : G))⁻¹ * (hf j : G))) * (((hf i : G))⁻¹ * (hf j : G))⁻¹ *
              (hf i : G)⁻¹ := by rw [hu]
        _ = (hf i : G) * y * (hf i : G)⁻¹ := by group
    exact Fin.ext (hinj j.1 j.2 i.1 i.2 e2).symm
  have h1 : N ≤ K.index := by
    have := Nat.card_le_card_of_injective f hfi
    rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  have h2 : Nat.card K = Nat.card ↥(centralizer ({y} : Set G) ⊓ C) :=
    Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv
  have h3 := K.index_mul_card
  rw [h2] at h3
  rw [← h3]
  exact Nat.mul_le_mul_right _ h1

theorem class_y : ∃ c : Nat → Equiv.Perm (Fin 1782),
    (∀ i < KC.N, ∃ h ∈ closure ((fun k => pp (KC.G k)) '' {k | k < KC.ng}),
      c i = h * pp (H 4) * h⁻¹) ∧ (∀ i < KC.N, ∀ j < KC.N, c i = c j → i = j) := by
  have ht : Orb.PRep 1782 11 (KC.T KC.r0) (pp (H 4)) := by
    rw [← Nat.eq_of_beq_eq_true bindC.2.2.2.2.2]
    exact prep_pp (pH 4 (by norm_num))
  obtain ⟨c, -, hr, -, hi⟩ := CFSG.KC.OrbGroup.conjOrb_reps (n := 1782) (w := 11) (ng := KC.ng)
    (N := KC.N) (r := KC.r0) (G := KC.G) (GI := KC.GI) (T := KC.T) (E := KC.E) (D := KC.D0)
    (S := KC.S) (ps := ps) (g := fun k => pp (KC.G k)) (t := pp (H 4)) (by norm_num)
    KC.h (fun k hk => prep_pp (pK k hk))
    (fun i hi => KC.cl i (lt_of_lt_of_eq hi (by rw [kN] <;> rfl)))
    (fun i hi => by
      rw [kNg]
      exact KC.tr0 i (lt_of_lt_of_eq hi (by rw [kN] <;> rfl)))
    (by rw [kN]; decide) ht (by decide) KC.k
  exact ⟨c, hr, hi⟩

theorem memP {G : Nat} (hG : permB 1782 11 G = true)
    (h : Nat.beq (Nat.shiftRight G (1782 * 11)) 0 = true ∧
      allN 1782 (fun t => Nat.blt (pg 11 (mask 11) G t) 1782) = true ∧
      siftK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) SuzC.LR SuzC.TRI SuzC.BP 6 0 G = true) :
    pp G ∈ suzM :=
  (mem_suzM_iff_siftA (rep_of_validA (validA_of hG))).1
    (siftA_of Suz2306.binds Suz2306.perm SuzC.hl h)

noncomputable abbrev C : Subgroup (Equiv.Perm (Fin 1782)) :=
  centralizer {pp X} ⊓ suzM

theorem memC {G : Nat} (hG : permB 1782 11 G = true)
    (h : Nat.beq (Nat.shiftRight G (1782 * 11)) 0 = true ∧
      allN 1782 (fun t => Nat.blt (pg 11 (mask 11) G t) 1782) = true ∧
      siftK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) SuzC.LR SuzC.TRI SuzC.BP 6 0 G = true)
    (hc : Nat.beq (cm 1782 11 G X) (cm 1782 11 X G) = true) : pp G ∈ C :=
  mem_inf.2 ⟨mem_centralizer_singleton_iff.2 (comm_of hG pXB hc), memP hG h⟩

theorem memCH : ∀ k < 6, pp (H k) ∈ C := fun k hk =>
  memC (pH k (by omega)) (siftH k hk) (commH k hk)

theorem A_le_C : A ≤ C := (closure_le _).2 fun r hr => by
  obtain ⟨k, hk, rfl⟩ := gensOf bindA hr
  rw [aNg] at hk
  exact memC (pAG k hk) (siftAG k hk) (commA k hk)

theorem x_memA : pp X ∈ A := memA' (prep_pp pXB) memX

theorem x_mem : pp X ∈ suzM := (mem_inf.1 (A_le_C x_memA)).2

theorem x_cube : pp X ^ 3 = 1 := eq_of_beq cubeX (prep_pw pXB (prep_pp pXB) 3) prep_id

theorem x_ne : pp X ≠ 1 := by
  intro h
  have e : pg 11 (mask 11) X 0 = ((pp X ⟨0, by norm_num⟩ : Fin 1782) : Nat) :=
    prep_pp pXB ⟨0, by norm_num⟩
  rw [Nat.eq_of_beq_eq_true relX.1, h] at e
  simp at e

theorem base_val (i : Nat) (hi : i < smallChain.baseCount) :
    ((smallChain.base.get ⟨i, hi⟩ : Fin 1782) : Nat) = smallBaseNat.toArray[i]! :=
  smallChain_arrays.base_val ⟨i, hi⟩

theorem hro : ∀ i < 6, roff 1782 (1782 * 11) (SuzC.LR i) + rcnt (SuzC.LR i) ≤ 65536 :=
  fun i hi => Nat.le_of_ble_eq_true (Orb.allN_iff.1 roK i hi)

theorem hr1 (h0 : 0 < smallChain.baseCount) (h1 : 1 < smallChain.baseCount) :
    pp X (smallChain.base.get ⟨0, h0⟩) = smallChain.base.get ⟨1, h1⟩ := by
  apply Fin.ext
  rw [base_val 1 h1, ← prep_pp pXB, base_val 0 h0]
  exact Nat.eq_of_beq_eq_true relX.1

theorem hr2 (h0 : 0 < smallChain.baseCount) (h2 : 2 < smallChain.baseCount) :
    (pp X ^ 2) (smallChain.base.get ⟨0, h0⟩) = smallChain.base.get ⟨2, h2⟩ := by
  apply Fin.ext
  rw [base_val 2 h2, ← prep_pw pXB (prep_pp pXB) 2, base_val 0 h0]
  exact Nat.eq_of_beq_eq_true relX.2

theorem countP_bits (M : Nat) : ∀ k, (List.range k).countP (fun i => Nat.testBit M i) = bits M k
  | 0 => rfl
  | k + 1 => by
    have e : bits M (k + 1) = bits M k + ((M >>> k) &&& 1) := rfl
    rw [List.range_succ, List.countP_append, countP_bits M k, e]
    congr 1
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
    simp only [List.countP_cons, List.countP_nil, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (M / 2 ^ k) with h | h <;>
      simp [Nat.testBit_eq_decide_div_mod_eq, h]

theorem bits_eq (M k : Nat) :
    ((List.finRange k).filter fun a : Fin k => Nat.testBit M a.val).length = bits M k := by
  rw [← countP_bits M k, ← List.countP_eq_length_filter]
  have e : (List.finRange k).map Fin.val = List.range k := by
    first
    | exact List.map_coe_finRange k
    | simp
  rw [← e, List.countP_map]
  rfl

theorem xQ : pp X ∈ smallChain.originalSubgroup := by
  rw [smallChain_originalSubgroup]
  exact x_mem

theorem cardH3 :
    Nat.card ↥(smallChain.levelSubgroup 3 ⊓ centralizer ({pp X} : Set (Equiv.Perm (Fin 1782)))) =
      108 := by
  have h := srch_node_sound smallChain_arrays (chainCheckFacts smallChain_check.1) smallChain_valid
    Suz2306.binds Suz2306.perm SuzC.hl smallChain_baseCount hro (prep_pp pXB) (prep_pp pXB) xQ xQ
    (i := 3) (by norm_num) idPre plan dX
  rw [Set.pair_eq_singleton] at h
  rw [h]
  exact Nat.eq_of_beq_eq_true tail

theorem cardC_le : Nat.card C ≤ 34992 := by
  have h := card_centralizer_le_of_head smallChain_arrays (chainCheckFacts smallChain_check.1)
    smallChain_valid Suz2306.binds Suz2306.perm SuzC.hl smallChain_baseCount (by norm_num) hro
    (prep_pp pXB) (prep_pw pXB (prep_pp pXB) 2) (hr1 _ _) (hr2 _ _) head
  rw [smallChain_originalSubgroup, bits_eq, Nat.eq_of_beq_eq_true headCnt.1, cardH3] at h
  exact h

theorem norm_H : ∀ k < 4, ∀ r ∈ A, pp (H k) * r * (pp (H k))⁻¹ ∈ A := fun k hk =>
  conj_mem_closure fun a ha => by
    obtain ⟨l, hl, rfl⟩ := gensOf bindA ha
    rw [aNg] at hl
    exact memA' (prep_cj (pH k (by omega)) (prep_pp (pH k (by omega))) (prep_pp (pAG l hl)))
      (normA k hk l hl)

theorem g_notin : pp (H 0) ∉ A := by
  intro h
  obtain ⟨i, hi, e⟩ := ((enumOK_spec (by decide) enumA.1).1 _).1 h
  rw [enumA.2.1] at hi
  rw [enumA.2.2 i hi] at e
  have e2 : AE.T i = H 0 := code_eq (pAT i hi) (pH 0 (by norm_num)) e
  have h2 := Orb.allN_iff.1 gOut i hi
  simp [e2] at h2

theorem g_cube : pp (H 0) ^ 3 = 1 :=
  eq_of_beq gCube (prep_pw (pH 0 (by norm_num)) (prep_pp (pH 0 (by norm_num))) 3) prep_id

noncomputable abbrev K : Subgroup (Equiv.Perm (Fin 1782)) :=
  A ⊔ zpowers (pp (H 0)) ⊔ closure (permsA 1782 qGs)

theorem Q_gen : ∀ r ∈ permsA 1782 qGs, ∃ k < 3, r = pp (H (k + 1)) := fun r hr => by
  obtain ⟨k, hk, rfl⟩ := gensOf bindQ hr
  rw [qNg] at hk
  exact ⟨k, hk, by rw [← Nat.eq_of_beq_eq_true (bindC.1 k hk)]⟩

theorem K_le_N : K ≤ normalizer (A : Set (Equiv.Perm (Fin 1782))) := by
  refine sup_le (sup_le le_normalizer (zpowers_le.2
    (CFSG.KC.SupPow.mem_normalizer_of_conj_mem (norm_H 0 (by norm_num))))) ((closure_le _).2 ?_)
  intro r hr
  obtain ⟨k, hk, rfl⟩ := Q_gen r hr
  exact CFSG.KC.SupPow.mem_normalizer_of_conj_mem (norm_H (k + 1) (by omega))

theorem K_le_C : K ≤ C := by
  refine sup_le (sup_le A_le_C (zpowers_le.2 (memCH 0 (by norm_num)))) ((closure_le _).2 ?_)
  intro r hr
  obtain ⟨k, hk, rfl⟩ := Q_gen r hr
  exact memCH (k + 1) (by omega)

theorem C_eq : K = C := by
  have h7 : 3 ^ (6 + 1) ∣ Nat.card ↥(A ⊔ zpowers (pp (H 0))) :=
    CFSG.KC.SupPow.pow_succ_dvd_card_sup (p := 3) (k := 6) A (by rw [cardA]; norm_num)
      (norm_H 0 (by norm_num)) g_notin g_cube
  have d1 : 3 ^ (6 + 1) ∣ Nat.card K :=
    h7.trans (card_dvd_of_le (le_sup_left : A ⊔ zpowers (pp (H 0)) ≤ K))
  have d2 : 16 ∣ Nat.card K := by
    have h := card_dvd_of_le (le_sup_right : closure (permsA 1782 qGs) ≤ K)
    rwa [cardQ] at h
  have d : 3 ^ (6 + 1) * 16 ∣ Nat.card K :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d1 d2
  have hle : 34992 ≤ Nat.card K := by
    have h := Nat.le_of_dvd Nat.card_pos d
    norm_num at h
    exact h
  exact eq_of_le_of_card_ge K_le_C (cardC_le.trans hle)

theorem normC : ∀ g ∈ C, ∀ r ∈ A, g * r * g⁻¹ ∈ A := by
  intro g hg r hr
  rw [← C_eq] at hg
  exact (mem_normalizer_iff.1 (K_le_N hg) r).1 hr

noncomputable abbrev B : Subgroup (Equiv.Perm (Fin 1782)) := closure (permsA 1782 bGs)

theorem B_le_A : B ≤ A := (closure_le _).2 fun r hr => by
  obtain ⟨k, hk, rfl⟩ := gensOf bindB hr
  rw [bNg] at hk
  exact memA' (prep_pp (pB k (by rw [bNg]; exact hk))) (memB k hk)

theorem y_eq : pp (H 4) = pp (BE.G 0) := by rw [bG0]

theorem B_le : B ≤ centralizer {pp (H 4)} ⊓ C := (closure_le _).2 fun r hr => by
  obtain ⟨k, hk, rfl⟩ := gensOf bindB hr
  rw [bNg] at hk
  refine mem_inf.2 ⟨mem_centralizer_singleton_iff.2 ?_,
    A_le_C (B_le_A (gen_mem bindB (by rw [bNg]; exact hk)))⟩
  exact comm_of (pB k (by rw [bNg]; exact hk)) (pH 4 (by norm_num)) (commB k hk)

theorem cardCy : 432 * Nat.card ↥(centralizer {pp (H 4)} ⊓ C) ≤ Nat.card C := by
  obtain ⟨c, hr, hi⟩ := class_y
  rw [kN] at hr hi
  have hle : closure ((fun k => pp (KC.G k)) '' {k | k < KC.ng}) ≤ C := by
    refine (closure_le _).2 ?_
    rintro _ ⟨k, hk, rfl⟩
    change k < KC.ng at hk
    change pp (KC.G k) ∈ C
    rw [kNg] at hk
    interval_cases k
    · rw [kG0]
      exact memCH 5 (by norm_num)
    · rw [kG1]
      exact memCH 2 (by norm_num)
  exact card_mul_le_of_conj C (pp (H 4)) c (fun i hi' => by
    obtain ⟨h, hm, e⟩ := hr i hi'
    exact ⟨h, hle hm, e⟩) hi

theorem B_eq : B = centralizer {pp (H 4)} ⊓ C := by
  refine eq_of_le_of_card_ge B_le ?_
  have h1 := cardCy
  have h2 := cardC_le
  rw [cardB]
  omega

theorem centA : centralizer (A : Set (Equiv.Perm (Fin 1782))) ⊓ C ≤ A := by
  intro z hz
  obtain ⟨hzA, hzC⟩ := mem_inf.1 hz
  have hy : pp (H 4) ∈ A := by
    rw [y_eq]
    exact B_le_A (gen_mem bindB (by rw [bNg]; norm_num))
  have hzy : z ∈ centralizer ({pp (H 4)} : Set (Equiv.Perm (Fin 1782))) :=
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hzA _ hy).symm
  have hzB : z ∈ B := by
    rw [B_eq]
    exact mem_inf.2 ⟨hzy, hzC⟩
  exact B_le_A hzB

theorem hxB : permOfArr 1782 (xBArr (levels ())) = pp X := by
  change permOfArr 1782 (rebuild (levels ()) xBTuple) = _
  rw [rebuild_eq KernelSuzB17322.rbX]
  rfl

theorem main : permOfArr 1782 (xBArr (levels ())) ^ 3 = 1 ∧ permOfArr 1782 (xBArr (levels ())) ≠ 1 ∧
    Nat.card (closure (permsA 1782 (aGens ()))) = 729 ∧ permOfArr 1782 (xBArr (levels ())) ∈ suzM ∧
    closure (permsA 1782 (aGens ())) ≤
      centralizer {permOfArr 1782 (xBArr (levels ()))} ⊓ suzM ∧
    (∀ g ∈ centralizer {permOfArr 1782 (xBArr (levels ()))} ⊓ suzM,
      ∀ r ∈ closure (permsA 1782 (aGens ())), g * r * g⁻¹ ∈ closure (permsA 1782 (aGens ()))) ∧
    centralizer (closure (permsA 1782 (aGens ())) : Set (Equiv.Perm (Fin 1782))) ⊓
      (centralizer {permOfArr 1782 (xBArr (levels ()))} ⊓ suzM) ≤
        closure (permsA 1782 (aGens ())) := by
  rw [hxB]
  exact ⟨x_cube, x_ne, cardA, x_mem, A_le_C, normC, centA⟩

end CertificateChecks.KernelSuzB17322

end
