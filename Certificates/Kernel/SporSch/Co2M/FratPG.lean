
module

public import Certificates.Kernel.SporSch.Co2M.FratG
public import Certificates.Kernel.SporSch.Co2M.FratP0
public import Certificates.Kernel.SporSch.Co2M.FratP1
public import Certificates.Kernel.SporSch.Co2M.FratP2
public import Certificates.Kernel.SporSch.Co2M.FratP3
public import Certificates.Kernel.SporSch.Co2M.FratTB0
public import Certificates.Kernel.SporSch.Co2M.FratTB1
public import Certificates.Kernel.SporSch.Co2M.FratTB2
public import Certificates.Kernel.SporSch.Co2M.Span
public import CFSG.Certificates.Kernel.Spor.RawAgree
public import CFSG.Certificates.Kernel.SporSch.MatInj
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option exponentiation.threshold 600

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Co2M CFSG.KS.MatRep CFSG.KS.Co2P CFSG.KS.MatInj
open CFSG.Sporadic.Co2Schreier CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native CFSG.Sporadic.Co2Cert CFSG.Sporadic.RuSchreier

noncomputable abbrev Zm : ℕ := Nat.mod (FYZ.getD 32 0) (Nat.pow 2 484)

theorem lv_check : (Nat.beq (rcnt (Co2LF.LR 0)) 128 && Nat.beq (rcnt (Co2LF.LR 1)) 64 &&
    Nat.beq (roff 2300 (2300 * 12) (Co2LF.LR 0)) 0 &&
    Nat.beq (roff 2300 (2300 * 12) (Co2LF.LR 1)) 128 &&
    Nat.beq FT0.length 128 && Nat.beq FT1.length 64) = true := by
  quickRfl

theorem lv_facts : rcnt (Co2LF.LR 0) = 128 ∧ rcnt (Co2LF.LR 1) = 64 ∧
    roff 2300 (2300 * 12) (Co2LF.LR 0) = 0 ∧ roff 2300 (2300 * 12) (Co2LF.LR 1) = 128 ∧
    FT0.length = 128 ∧ FT1.length = 64 := by
  have h := lv_check
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem tr_get {i a : ℕ} (hi : i < 2) (ha : a < rcnt (Co2LF.LR i)) {x : ℕ} (hx : x < 2300) :
    (fratLevels[i]!.tr[a]!)[x]! =
        (unpack 2300 12 (Co2LF.TR (roff 2300 (2300 * 12) (Co2LF.LR i) + a)))[x]! ∧
      (unpack 2300 12 (Co2LF.TR (roff 2300 (2300 * 12) (Co2LF.LR i) + a)))[x]! < 2300 := by
  obtain ⟨A, P⟩ := Orb.agree_levelK Co2LF.binds Co2LF.perm
    (Orb.base_lt_of_levels Co2LF.binds Co2LF.hl) hi (Co2LF.hl i hi)
  have hr := (A.tr a (by rw [← A.cnt]; exact ha)).1 ⟨x, hx⟩
  have hp := (P a ha).1 ⟨x, hx⟩
  rw [CFSG.KS.Raw.Orb.unpack_get hx]
  exact ⟨hr.trans hp.symm, by rw [hp]; exact Fin.is_lt _⟩

theorem pts_size {i : ℕ} (hi : i < 2) : fratLevels[i]!.pts.size = rcnt (Co2LF.LR i) := by
  obtain ⟨A, -⟩ := Orb.agree_levelK Co2LF.binds Co2LF.perm
    (Orb.base_lt_of_levels Co2LF.binds Co2LF.hl) hi (Co2LF.hl i hi)
  exact A.cnt.symm

theorem compA_congr {n : ℕ} {t u t' u' : Array ℕ} (hu : ∀ i < n, u[i]! = u'[i]! ∧ u'[i]! < n)
    (ht : ∀ i < n, t[i]! = t'[i]!) : compA n t u = compA n t' u' := by
  unfold compA
  congr 1
  funext i
  rw [(hu i i.2).1, ht _ (hu i i.2).2]

theorem prod2A_eq {a b : ℕ} (ha : a < 128) (hb : b < 64) :
    prod2A 2300 fratLevels a b =
      compA 2300 (unpack 2300 12 (Co2LF.TR a)) (unpack 2300 12 (Co2LF.TR (128 + b))) := by
  obtain ⟨c0, c1, o0, o1, -, -⟩ := lv_facts
  unfold prod2A
  refine compA_congr (fun i hi => ?_) (fun i hi => ?_)
  · obtain ⟨e1, l1⟩ := tr_get (i := 1) (a := b) (by norm_num) (by rw [c1]; exact hb) hi
    rw [o1] at e1 l1
    exact ⟨e1, l1⟩
  · obtain ⟨e0, -⟩ := tr_get (i := 0) (a := a) (by norm_num) (by rw [c0]; exact ha) hi
    rw [o0, Nat.zero_add] at e0
    exact e0

theorem t0Rep {a : ℕ} (ha : a < 128) :
    MatRep.Rep 22 co2PackedVecs (unpack 2300 12 (Co2LF.TR a)) (FT0.getD a 0) (FT0I.getD a 0) := by
  rcases Nat.lt_or_ge a 64 with h | h
  · exact rep_unpack (allN_spec tb0 a h)
  · have e : a = Nat.add 64 (a - 64) := by simp only [Nat.add_eq]; omega
    rw [e]
    exact rep_unpack (allN_spec tb1 (a - 64) (by omega))

theorem t1Rep {b : ℕ} (hb : b < 64) :
    MatRep.Rep 22 co2PackedVecs (unpack 2300 12 (Co2LF.TR (128 + b))) (FT1.getD b 0)
      (FT1I.getD b 0) :=
  rep_unpack (allN_spec tb2 b hb)

theorem yz_eq : (∀ w < 32, FYZ.getD w 0 = (yP w).1) ∧ FYZ.getD 32 0 = zP.1 := by
  have h := yb
  simp only [Bool.and_eq_true] at h
  refine ⟨fun w hw => ?_, (Nat.eq_of_beq_eq_true h.2)⟩
  have h2 := allN_spec h.1 w hw
  rw [Bool.and_eq_true] at h2
  exact Nat.eq_of_beq_eq_true h2.2

theorem yRepF {w : ℕ} (hw : w < 32) :
    MatRep.Rep 22 co2PackedVecs (yArr w) (FYZ.getD w 0) (yP w).2 := by
  rw [yz_eq.1 w hw]
  exact yRep w

theorem zRepF : MatRep.Rep 22 co2PackedVecs zArr (FYZ.getD 32 0) zP.2 := by
  rw [yz_eq.2]
  exact zRep

theorem mw_eq (A B : ℕ) : mw A B = mmK A B := by
  unfold mw
  rw [Co2P.strictN_eq, Co2P.strictN_eq]

theorem pow484 : (2 : ℕ) ^ (22 * 22) = Nat.pow 2 484 := rfl

theorem eqA_matM {y u : Array ℕ} {Y Y' U U' : ℕ} (hy : MatRep.Rep 22 co2PackedVecs y Y Y')
    (hu : MatRep.Rep 22 co2PackedVecs u U U') :
    eqA 2300 y u = Nat.beq (Nat.mod Y (Nat.pow 2 484)) (Nat.mod U (Nat.pow 2 484)) := by
  rw [hy.1, hu.1, ← V_size, eqA_permOfMat_mod spans hy.2.1 hu.2.1, pow484]
  rfl

theorem I22_check : Nat.beq (Nat.mod I22 (Nat.pow 2 484)) I22 = true := by quickRfl

theorem eqA_one {y : Array ℕ} {Y Y' : ℕ} (hy : MatRep.Rep 22 co2PackedVecs y Y Y') :
    eqA 2300 y (idA 2300) = isI Y := by
  rw [eqA_matM hy rep_I22, Nat.eq_of_beq_eq_true I22_check]
  rfl

theorem eqA_oneZ {y : Array ℕ} {Y Y' : ℕ} (hy : MatRep.Rep 22 co2PackedVecs y Y Y') :
    (eqA 2300 y (idA 2300) || eqA 2300 y zArr) = isIZ Zm Y := by
  rw [eqA_one hy, eqA_matM hy zRepF, isIZ_eq]

theorem fi_chain {p : Array ℕ → Bool} {q : ℕ → Bool}
    (hpq : ∀ (y : Array ℕ) (Y Y' : ℕ), MatRep.Rep 22 co2PackedVecs y Y Y' → p y = q Y) :
    ∀ (n : ℕ) (x : Array ℕ) (X X' : ℕ), MatRep.Rep 22 co2PackedVecs x X X' →
      firstIdx p (sqChain x n) = fiK q n X
  | 0, _, _, _, _ => rfl
  | n + 1, x, X, X', h => by
    have h2 := rep_cmp (p := (X, X')) (q := (X, X')) h h
    have ih := fi_chain hpq n _ _ _ h2
    rw [sqChain, firstIdx, fiK_succ, hpq _ _ _ h, mw_eq, ih]
    rfl

theorem rep_mm {a b : Array ℕ} {A A' B B' : ℕ} (ha : MatRep.Rep 22 co2PackedVecs a A A')
    (hb : MatRep.Rep 22 co2PackedVecs b B B') :
    MatRep.Rep 22 co2PackedVecs (compA 2300 a b) (mmK B A) (mmK A' B') :=
  rep_cmp (p := (A, A')) (q := (B, B')) ha hb

theorem key_eq {w a b : ℕ} (hw : w < 32) (ha : a < 128) (hb : b < 64) :
    profKey zArr (compA 2300 (yArr w) (prod2A 2300 fratLevels a b)) =
      Co2P.keyM (FYZ.getD w 0) Zm (FT0.getD a 0) (FT1.getD b 0) := by
  have hx := rep_mm (yRepF hw) (rep_mm (t0Rep ha) (t1Rep hb))
  have h1 := fi_chain (p := fun y => eqA 2300 y (idA 2300)) (q := isI)
    (fun _ _ _ h => eqA_one h) 6 _ _ _ hx
  have h2 := fi_chain (p := fun y => eqA 2300 y (idA 2300) || eqA 2300 y zArr) (q := isIZ Zm)
    (fun _ _ _ h => eqA_oneZ h) 6 _ _ _ hx
  rw [prod2A_eq ha hb]
  unfold profKey ordCode ordZCode
  rw [h1, h2, keyM_eq, mw_eq, mw_eq]
  omega

theorem map_getD_range (L : List ℕ) : (List.range L.length).map (fun i => L.getD i 0) = L := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem _ _ h2, List.getElem?_eq_getElem h2]

theorem keys_eq {w : ℕ} (hw : w < 32) :
    keys2 fratLevels (fun t => profKey zArr (compA 2300 (yArr w) t)) =
      FT0.flatMap fun A => FT1.map (Co2P.keyM (FYZ.getD w 0) Zm A) := by
  obtain ⟨c0, c1, -, -, l0, l1⟩ := lv_facts
  unfold keys2
  rw [pts_size (by norm_num), pts_size (by norm_num), c0, c1]
  conv_rhs => rw [← map_getD_range FT0, l0, List.flatMap_map]
  refine List.flatMap_congr fun a ha => ?_
  rw [List.mem_range] at ha
  conv_rhs => rw [← map_getD_range FT1, l1, List.map_map]
  refine List.map_congr_left fun b hb => ?_
  rw [List.mem_range] at hb
  exact key_eq hw ha hb

theorem len_flatMap (M : List ℕ) (f : ℕ → ℕ → ℕ) :
    ∀ L : List ℕ, (L.flatMap fun A => M.map (f A)).length = L.length * M.length
  | [] => by simp
  | A :: L => by
    rw [List.flatMap_cons, List.length_append, len_flatMap M f L, List.length_map,
      List.length_cons, Nat.succ_mul, Nat.add_comm]

theorem prows_of {lo : ℕ} (h : profAll (FYZ.getD 32 0) (fun w => FYZ.getD w 0) FT0 FT1 profTable
    lo 8 = true) : ∀ i < 8, rowK (hA (FYZ.getD (Nat.add lo i) 0) Zm FT1 FT0 0)
      (profTable.getD (Nat.add lo i) []) = true := by
  intro i hi
  unfold profAll at h
  rw [Co2P.strictB_eq] at h
  have := allN_spec h i hi
  simp only [Co2P.strictB_eq] at this
  exact this

theorem prows_ok {w : ℕ} (hw : w < 32) :
    rowK (hA (FYZ.getD w 0) Zm FT1 FT0 0) (profTable.getD w []) = true := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 8 ∧ w = 8 * q + r :=
    ⟨w / 8, w % 8, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod w 8).symm⟩
  have hq : q < 4 := by omega
  interval_cases q
  · simpa using prows_of prof0 r hr
  · simpa [Nat.add_comm] using prows_of prof1 r hr
  · simpa [Nat.add_comm] using prows_of prof2 r hr
  · simpa [Nat.add_comm] using prows_of prof3 r hr

theorem profile_check : profileOK fratLevels zArr profTable = true := by
  obtain ⟨-, -, -, -, l0, l1⟩ := lv_facts
  unfold profileOK
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro w hw
  dsimp only
  rw [keys_eq hw, CFSG.Monster.B.Co2.allLt_iff]
  intro e he
  have hrow := prows_ok hw
  rw [hA_eq, Nat.zero_add] at hrow
  have hl : ∀ k ∈ FT0.flatMap (fun A => FT1.map (Co2P.keyM (FYZ.getD w 0) Zm A)),
      k / 8 < 7 ∧ k % 8 < 7 := by
    intro k hk
    obtain ⟨A, -, hk⟩ := List.mem_flatMap.1 hk
    obtain ⟨B, -, rfl⟩ := List.mem_map.1 hk
    exact keyM_digits _ _ _ _
  have hlen : (FT0.flatMap fun A => FT1.map (Co2P.keyM (FYZ.getD w 0) Zm A)).length < 32768 := by
    rw [len_flatMap, l0, l1]
    norm_num
  obtain ⟨h1, h2⟩ := rowK_counts hl hlen hrow e he
  rw [h1, h2]
  simp

end CertificateChecks.KernelSporSch.Co2M

end
