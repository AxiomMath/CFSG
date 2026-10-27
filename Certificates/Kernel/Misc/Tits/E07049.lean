
module

public import Certificates.Kernel.Misc.Tits.T7049K
public import Certificates.Kernel.Misc.Tits.E07043
import Certificates.Kernel.SporSch.Tits.Inv2266
import CFSG.Certificates.Kernel.Misc.ClosKSound
import CFSG.Certificates.Kernel.Spor.RawSiftK

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.T7049

open CFSG CFSG.Quasithin CFSG.Quasithin.RuRank3 CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.ClosK
open CertificateChecks.KernelMisc CertificateChecks.KernelMisc.Tits7050
open CertificateChecks.KernelSpor.Tits2264 CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.TitsAction

theorem get_pt {p : Nat} (hp : E7043.Cn p) (i : Nat) : (unpack 1755 11 p)[i]! = pt p i := by
  unfold E7043.Cn canonK at hp
  simp only [bAnd_iff] at hp
  exact TitsCommon.unpack_get0 hp.2.1

theorem nbeq (a b : Nat) : Nat.beq a b = (a == b) := by
  cases h : Nat.beq a b
  · symm
    rw [beq_eq_false_iff_ne]
    intro e
    rw [e, Nat.beq_refl] at h
    exact Bool.noConfusion h
  · symm
    rw [beq_iff_eq]
    exact Nat.eq_of_beq_eq_true h

theorem lp_eq {i : Nat} (hi : i < 8775) : titsLinePtArr[i]! = LPf i := by
  rw [lp_get hi, Nat.eq_of_beq_eq_true (allN_spec kLP i hi)]

theorem lineFixed_eqK {P v : Nat} (hP : E7043.Cn P) (hv : v < 2925) :
    lineFixedA (unpack 1755 11 P) v = lfixK P v := by
  unfold lineFixedA lfixK
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true, List.mem_range]
  refine forall_congr' fun k => imp_congr_right fun hk => ?_
  rw [lp_eq (i := 3 * v + k) (by omega), lp_eq (i := 3 * v) (by omega),
    lp_eq (i := 3 * v + 1) (by omega), lp_eq (i := 3 * v + 2) (by omega), get_pt hP, nbeq, nbeq,
    nbeq]

theorem lfc_eq {P : Nat} (hP : E7043.Cn P) : lineFixCount (unpack 1755 11 P) = lfc P := by
  unfold lineFixCount lfc
  refine List.countP_congr fun v hv => ?_
  rw [lineFixed_eqK hP (List.mem_range.1 hv)]

theorem pfc_eq {P : Nat} (hP : E7043.Cn P) : ptFixCount (unpack 1755 11 P) = pfc P := by
  unfold ptFixCount pfc
  refine List.countP_congr fun x _ => ?_
  rw [get_pt hP, nbeq]

theorem pX : permC X = true := by
  have h := perms
  simp only [bAnd_iff] at h
  exact h.2.2.1

theorem pT : permC TitsT = true := by
  have h := perms
  simp only [bAnd_iff] at h
  exact h.2.2.2

theorem x_eqK : titsX13Arr = unpack 1755 11 X := by
  change hexTable 3 1755 (1755 * 0) titsX13Text = _
  rw [TX.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound TX.all 0 (by norm_num)

theorem p3_eq {j : Nat} (hj : j < 3) : titsP3Gens[j]! = unpack 1755 11 (TP3.F j) := by
  rw [titsP3Gens, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  change hexTable 3 1755 (1755 * j) titsP3Text = _
  rw [TP3.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound TP3.all j hj

theorem p5_eq {j : Nat} (hj : j < 2) : titsP5Gens[j]! = unpack 1755 11 (TP5.F j) := by
  rw [titsP5Gens, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  change hexTable 3 1755 (1755 * j) titsP5Text = _
  rw [TP5.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound TP5.all j hj

theorem p3_size : titsP3Gens.size = 3 := by simp [titsP3Gens]

theorem p5_size : titsP5Gens.size = 2 := by simp [titsP5Gens]

theorem perm3 {j : Nat} (hj : j < 3) : permC (TP3.F j) = true := by
  have h := kPerm
  simp only [bAnd_iff] at h
  exact allN_spec h.1 j hj

theorem perm5 {j : Nat} (hj : j < 2) : permC (TP5.F j) = true := by
  have h := kPerm
  simp only [bAnd_iff] at h
  exact allN_spec h.2 j hj

theorem base3 : Nat.beq (pg 11 (mask 11) T7049P3C.BP 0) 0 = true := by
  have h := baseOK
  simp only [bAnd_iff] at h
  exact h.1

theorem base5 : Nat.beq (pg 11 (mask 11) T7049P5C.BP 0) 0 = true := by
  have h := baseOK
  simp only [bAnd_iff] at h
  exact h.2

theorem cnts : rcnt (T7049P3C.LR 0) = 27 ∧ rcnt (T7049P5C.LR 0) = 25 := by
  have h := kCnt
  simp only [bAnd_iff] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem sifts : siftD X = true ∧ (∀ j < 3, siftD (TP3.F j) = true) ∧
    ∀ j < 2, siftD (TP5.F j) = true := by
  have h := kSift
  simp only [bAnd_iff] at h
  exact ⟨h.1, allN_spec h.2.1, allN_spec h.2.2⟩

theorem base_get {BP : Nat} (h : Nat.beq (pg 11 (mask 11) BP 0) 0 = true) :
    ∀ t < 1, (ruBaseArr 1755 [0])[t]! = pg 11 (mask 11) BP t := by
  intro t ht
  have e : t = 0 := by omega
  subst e
  rw [Nat.eq_of_beq_eq_true h]
  rfl

theorem binds3 : Binds 1755 11 T7049P3C.S 3 1 T7049P3C.BP titsP3Gens (ruBaseArr 1755 [0]) :=
  ⟨by norm_num, by norm_num, by norm_num, p3_size, fun j hj => by
      rw [p3_eq hj, Nat.eq_of_beq_eq_true (allN_spec sOK3 j hj)],
    rfl, base_get base3⟩

theorem binds5 : Binds 1755 11 T7049P5C.S 2 1 T7049P5C.BP titsP5Gens (ruBaseArr 1755 [0]) :=
  ⟨by norm_num, by norm_num, by norm_num, p5_size, fun j hj => by
      rw [p5_eq hj, Nat.eq_of_beq_eq_true (allN_spec sOK5 j hj)],
    rfl, base_get base5⟩

theorem chain3 : ruChainOK 1755 titsP3Gens 3 3 [0] [] = true :=
  rawChainK_sound (CH := 2) (NS := T7049P3C.NS) binds3 T7049P3C.head T7049P3C.hl (by decide)
    T7049P3C.hs

theorem chain5 : ruChainOK 1755 titsP5Gens 2 2 [0] [] = true :=
  rawChainK_sound (CH := 2) (NS := T7049P5C.NS) binds5 T7049P5C.head T7049P5C.hl (by decide)
    T7049P5C.hs

theorem orbits3 : rawOrbitSizes 1755 titsP3Gens (ruBaseArr 1755 [0]) = [27] := by
  rw [rawOrbitSizesK_sound binds3 (CFSG.KS.Raw.Orb.head_facts T7049P3C.head).1 T7049P3C.hl]
  simp [cnts.1]

theorem orbits5 : rawOrbitSizes 1755 titsP5Gens (ruBaseArr 1755 [0]) = [25] := by
  rw [rawOrbitSizesK_sound binds5 (CFSG.KS.Raw.Orb.head_facts T7049P5C.head).1 T7049P5C.hl]
  simp [cnts.2]

theorem gens_ok {gens : Array (Array Nat)} {G : Nat → Nat} {ng : Nat}
    (hg : ∀ k < ng, gens[k]! = unpack 1755 11 (G k)) (hp : ∀ k < ng, permC (G k) = true)
    (hs : ∀ k < ng, siftD (G k) = true) :
    (allLt ng fun k => inTitsA gens[k]! && isInvA 1755 gens[k]! (invCand 1755 gens[k]!)) = true := by
  rw [allLt_iff]
  intro k hk
  rw [hg k hk, E7043.inA_of_D (hp k hk) (hs k hk), isInv_of (hp k hk)]
  rfl

theorem clos_eq {gens : Array (Array Nat)} {G T : Nat → Nat} {ng m : Nat} (hsz : gens.size = ng)
    (hg : ∀ k < ng, gens[k]! = unpack 1755 11 (G k)) (hp : ∀ k < ng, permC (G k) = true)
    (hl : lEq T (closK pc G ng 30 ([pidn 1755 11], 0)).1 0 m = true) :
    closureList 1755 gens 30 = (((List.range m).map T).map (unpack 1755 11)).toArray ∧
      ∀ j < m, E7043.Cn (T j) := by
  obtain ⟨h1, h2⟩ := closureList_eq_closK (n := 1755) (u := unpack 1755 11) (pc := pc)
    (C := E7043.Cn) (gens := gens) (gs := G) (e := pidn 1755 11)
    (fun p q hp hq => E7043.cmp hp hq) (fun p q hp hq => E7043.eqU hp hq)
    (fun p q hp hq => E7043.cmpC hp hq)
    (fun k hk => ⟨hg k (by omega), E7043.cOf (hp k (by omega))⟩) E7043.idA_eq' E7043.cId 30
  rw [hsz] at h1 h2
  rw [lEq_sound hl] at h1 h2
  refine ⟨h1, fun j hj => h2 _ ?_⟩
  exact List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩

theorem any_eq {T : Nat → Nat} {m x : Nat} (hT : ∀ j < m, E7043.Cn (T j)) (hx : E7043.Cn x) :
    ((((List.range m).map T).map (unpack 1755 11)).toArray.any fun e =>
      eqA 1755 e (unpack 1755 11 x)) = lmem T m x := by
  unfold lmem
  rw [List.any_toArray, List.any_map, List.any_map, Bool.eq_iff_iff]
  simp only [List.any_eq_true, List.mem_range, Function.comp_apply]
  constructor
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, by rwa [E7043.eqU (hT j hj) hx] at h⟩
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, by rwa [E7043.eqU (hT j hj) hx]⟩

theorem closed_ok {gens : Array (Array Nat)} {G T : Nat → Nat} {ng m : Nat} (hsz : gens.size = ng)
    (hg : ∀ k < ng, gens[k]! = unpack 1755 11 (G k)) (hp : ∀ k < ng, permC (G k) = true)
    (hl : lEq T (closK pc G ng 30 ([pidn 1755 11], 0)).1 0 m = true)
    (hc : closedK T G ng m = true) :
    listClosedA 1755 gens (closureList 1755 gens 30) = true := by
  obtain ⟨hL, hT⟩ := clos_eq hsz hg hp hl
  rw [hL]
  unfold closedK at hc
  obtain ⟨hc1, hc2⟩ := (bAnd_iff _ _).1 hc
  have hget : ∀ i < m, (((List.range m).map T).map (unpack 1755 11)).toArray[i]! =
      unpack 1755 11 (T i) := by
    intro i hi
    rw [List.getElem!_toArray, getElem!_pos _ i (by simpa using hi)]
    simp
  unfold listClosedA
  rw [E7043.idA_eq', any_eq hT E7043.cId, hc1, Bool.true_and, hsz, allLt_iff]
  intro k hk
  have hck := allN_spec hc2 k hk
  rw [allLt_iff]
  intro i hi'
  have hi : i < m := by simpa using hi'
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec hck i hi)
  have cG := E7043.cOf (hp k hk)
  rw [hget i hi, hg k hk, E7043.invU (hp k hk), E7043.cmp cG (hT i hi),
    E7043.cmp (E7043.cIOf (hp k hk)) (hT i hi), any_eq hT (E7043.cmpC cG (hT i hi)),
    any_eq hT (E7043.cmpC (E7043.cIOf (hp k hk)) (hT i hi)), h1, h2]
  rfl

theorem all_ok {gens : Array (Array Nat)} {G T : Nat → Nat} {ng m c : Nat} {f : Array Nat → Nat}
    {fK : Nat → Nat} (hsz : gens.size = ng)
    (hg : ∀ k < ng, gens[k]! = unpack 1755 11 (G k)) (hp : ∀ k < ng, permC (G k) = true)
    (hl : lEq T (closK pc G ng 30 ([pidn 1755 11], 0)).1 0 m = true)
    (hf : ∀ P, E7043.Cn P → f (unpack 1755 11 P) = fK P)
    (hc : allN m (fun j => bIf(Nat.beq (T j) (pidn 1755 11), true, Nat.beq (fK (T j)) c)) = true) :
    ((closureList 1755 gens 30).all fun e => eqA 1755 e (idA 1755) || f e == c) = true := by
  obtain ⟨hL, hT⟩ := clos_eq hsz hg hp hl
  rw [hL, List.all_toArray, List.all_map, List.all_map, List.all_eq_true]
  intro j hj
  have hj' := List.mem_range.1 hj
  have h := allN_spec hc j hj'
  simp only [Function.comp_apply]
  rw [E7043.idA_eq', E7043.eqU (hT j hj') E7043.cId, hf _ (hT j hj'), ← nbeq]
  cases e : Nat.beq (T j) (pidn 1755 11)
  · rw [e] at h
    simpa using h
  · rfl

open Certificates in
open CFSG CFSG.Quasithin CFSG.Quasithin.RuRank3 CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier in
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native in
open scoped Pointwise in
theorem c7049 :
    isInvA 1755 titsX13Arr (invCand 1755 titsX13Arr) = true ∧ inTitsA titsX13Arr = true ∧
      eqA 1755 (powArr 1755 titsX13Arr 13) (idA 1755) = true ∧
      eqA 1755 titsX13Arr (idA 1755) = false ∧ ptFixCount titsX13Arr = 0 ∧
      lineFixCount titsX13Arr = 0 ∧
      ruChainOK 1755 titsP3Gens 3 3 [0] [] = true ∧
      rawOrbitSizes 1755 titsP3Gens (ruBaseArr 1755 [0]) = [27] ∧
      ruChainOK 1755 titsP5Gens 2 2 [0] [] = true ∧
      rawOrbitSizes 1755 titsP5Gens (ruBaseArr 1755 [0]) = [25] ∧
      (allLt 3 fun k => inTitsA titsP3Gens[k]! &&
        isInvA 1755 titsP3Gens[k]! (invCand 1755 titsP3Gens[k]!)) = true ∧
      (allLt 2 fun k => inTitsA titsP5Gens[k]! &&
        isInvA 1755 titsP5Gens[k]! (invCand 1755 titsP5Gens[k]!)) = true ∧
      listClosedA 1755 titsP3Gens (closureList 1755 titsP3Gens 30) = true ∧
      listClosedA 1755 titsP5Gens (closureList 1755 titsP5Gens 30) = true ∧
      ((closureList 1755 titsP3Gens 30).all fun e =>
        eqA 1755 e (idA 1755) || lineFixCount e == 9) = true ∧
      ((closureList 1755 titsP5Gens 30).all fun e =>
        eqA 1755 e (idA 1755) || ptFixCount e == 5) = true ∧
      lineFixCount titsZArr = 45 ∧ lineFixCount titsTArr = 61 := by
  have cX := E7043.cOf pX
  obtain ⟨sX, s3, s5⟩ := sifts
  have hk := kX
  simp only [bAnd_iff] at hk
  obtain ⟨k13, k1, kp, kl⟩ := hk
  have hzt := kZT
  simp only [bAnd_iff] at hzt
  have g3 : ∀ k < 3, titsP3Gens[k]! = unpack 1755 11 (TP3.F k) := fun k hk => p3_eq hk
  have g5 : ∀ k < 2, titsP5Gens[k]! = unpack 1755 11 (TP5.F k) := fun k hk => p5_eq hk
  have q3 : ∀ k < 3, permC (TP3.F k) = true := fun k hk => perm3 hk
  have q5 : ∀ k < 2, permC (TP5.F k) = true := fun k hk => perm5 hk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, chain3, orbits3, chain5, orbits5, gens_ok g3 q3 s3,
    gens_ok g5 q5 s5, closed_ok p3_size g3 q3 kCl3 kClosed3, closed_ok p5_size g5 q5 kCl5 kClosed5,
    all_ok p3_size g3 q3 kCl3 (fun P hP => lfc_eq hP) kLines3,
    all_ok p5_size g5 q5 kCl5 (fun P hP => pfc_eq hP) kPts5, ?_, ?_⟩
  · rw [x_eqK]
    exact isInv_of pX
  · rw [x_eqK]
    exact E7043.inA_of_D pX sX
  · rw [x_eqK, (E7043.powU cX 13).1, E7043.idA_eq', E7043.eqU (E7043.powU cX 13).2 E7043.cId]
    exact k13
  · rw [x_eqK, E7043.idA_eq', E7043.eqU cX E7043.cId]
    cases e : Nat.beq X (pidn 1755 11)
    · rfl
    · rw [e] at k1
      exact absurd k1 Bool.false_ne_true
  · rw [x_eqK, pfc_eq cX]
    exact Nat.eq_of_beq_eq_true kp
  · rw [x_eqK, lfc_eq cX]
    exact Nat.eq_of_beq_eq_true kl
  · rw [TitsCommon.z_eq, lfc_eq TitsCommon.canonZ]
    exact Nat.eq_of_beq_eq_true hzt.1
  · rw [TitsInv.t_eq, lfc_eq (E7043.cOf pT)]
    exact Nat.eq_of_beq_eq_true hzt.2

end CertificateChecks.KernelMisc.T7049

end
