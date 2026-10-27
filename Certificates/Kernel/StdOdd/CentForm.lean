module

public import Certificates.Kernel.StdOdd.CentBridge
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LieType.Chevalley.C2E6StdMatrixModelBase
public import Certificates.Data.CFSGNative.Chevalley.C2E6CertLie

public section

namespace CFSG.KD.StdOdd.Cent

open CFSG.KC.StdOdd.Orbit CFSG.KC.StdOdd.Chain CFSG.KS.StdOdd.Orbit CFSG.KS.StdOdd.Chain
  CFSG.KD.StdOdd.Orbit CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std.MatrixModel
  CFSG.Monster.Existence.StdOdd.Cert CFSG.Monster.B.Classical.E6Adjoint

#kc_repo #kc_natBin CFSG.KD.StdOdd.Cent.Form fmPk "Certificates/Kernel/StdOdd/data/fm.bin" 144 8291311257211374863
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.Form brPk "Certificates/Kernel/StdOdd/data/br.txt" 9122 1346143243632216051

@[expose] def pairsP (P : ℕ → ℕ → Bool) : List (ℕ × ℕ) :=
  (List.range 78).flatMap fun a => ((List.range 78).filter (P a)).map fun c => (a, c)

@[expose] def formPairs : List (ℕ × ℕ) := pairsP fbit

@[expose] def brRow (a : ℕ) : ℕ := (bracketCodes >>> (624 * a)) % 2 ^ 624

@[expose] def brPairs (k : ℕ) : List (ℕ × ℕ) :=
  pairsP fun a c => (maskOf ((brRow a >>> (8 * c)) % 256)).testBit k

theorem brMask_eq (a c : ℕ) (hc : c < 78) : brMask a c = maskOf ((brRow a >>> (8 * c)) % 256) := by
  rw [brMask, code]
  congr 1
  apply Nat.eq_of_testBit_eq
  intro j
  rw [show (256 : ℕ) = 2 ^ 8 from rfl]
  simp only [brRow, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hj : j < 8
  · have e : 624 * a + (8 * c + j) = 8 * (78 * a + c) + j := by ring
    rw [e]
    simp [hj, show 8 * c + j < 624 by omega]
  · simp [hj]

theorem fm_ok : pairsOf 6084 Form.fmPk = formPairs := by decide +kernel

theorem br_ok : Form.brPk.map (pairsOf 6084) = (List.range 78).map brPairs := by decide +kernel

@[expose] noncomputable def ptN (U : List ℕ) (i a : ℕ) : K := ofBits (cb U i (2 * a)) (cb U i (2 * a + 1))

theorem ptK_apply (U : List ℕ) (i : ℕ) (a : Fin 78) : ptK U i a = ptN U i a := rfl

theorem f4acc_ofBits (U V : List ℕ) (i : ℕ) : ∀ (ps : List (ℕ × ℕ)) (s : Bool × Bool),
    ofBits (f4acc s U V i ps).1 (f4acc s U V i ps).2 =
      ofBits s.1 s.2 + (ps.map fun p => ptN U i p.1 * ptN V i p.2).sum
  | [], s => by simp [f4acc]
  | p :: ps, s => by
    have e : f4acc s U V i (p :: ps) =
        f4acc (s.1 ^^ (f4b U V i p).1, s.2 ^^ (f4b U V i p).2) U V i ps := rfl
    rw [e, f4acc_ofBits U V i ps, List.map_cons, List.sum_cons, ofBits_add, add_assoc]
    congr 2
    simp only [f4b, ptN]
    exact ofBits_mul _ _ _ _

theorem or_iff_ofBits (x : Bool × Bool) : (x.1 || x.2) = true ↔ ofBits x.1 x.2 ≠ 0 := by
  obtain ⟨a, b⟩ := x
  constructor
  · intro h h0
    rw [← ofBits_false] at h0
    obtain ⟨rfl, rfl⟩ := ofBits_injective h0
    exact absurd h (by decide)
  · intro h
    cases a <;> cases b
    · exact absurd ofBits_false h
    all_goals rfl

theorem sum_range_list {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ n, ∑ i ∈ Finset.range n, f i = ((List.range n).map f).sum
  | 0 => rfl
  | n + 1 => by
    rw [Finset.sum_range_succ, List.range_succ, List.map_append, List.sum_append, sum_range_list f n]
    simp

theorem sum_filter_list {M : Type*} [AddCommMonoid M] (P : ℕ → Bool) (g : ℕ → M) :
    ∀ L : List ℕ, ((L.filter P).map g).sum = (L.map fun c => if P c = true then g c else 0).sum
  | [] => rfl
  | c :: L => by
    rw [List.filter_cons, List.map_cons, List.sum_cons, ← sum_filter_list P g L]
    by_cases h : P c = true
    · rw [ite_eq_left h, ite_eq_left h, List.map_cons, List.sum_cons]
    · rw [ite_eq_right h, ite_eq_right h, zero_add]

theorem sum_flatMap_list {M : Type*} [AddCommMonoid M] {α β : Type*} (f : α → List β) (g : β → M) :
    ∀ L : List α, ((L.flatMap f).map g).sum = (L.map fun a => ((f a).map g).sum).sum
  | [] => rfl
  | a :: L => by
    rw [List.flatMap_cons, List.map_append, List.sum_append, sum_flatMap_list f g L, List.map_cons,
      List.sum_cons]

theorem sum_pairsP (P : ℕ → ℕ → Bool) (u w : ℕ → K) :
    ∑ a : Fin 78, ∑ c : Fin 78, (if P a c = true then u a * w c else 0) =
      ((pairsP P).map fun p => u p.1 * w p.2).sum := by
  rw [pairsP, sum_flatMap_list]
  rw [Fin.sum_univ_eq_sum_range (fun a => ∑ c : Fin 78, if P a c = true then u a * w c else 0),
    sum_range_list]
  congr 1
  refine List.map_congr_left fun a _ => ?_
  rw [Fin.sum_univ_eq_sum_range (fun c => if P a c = true then u a * w c else 0), sum_range_list,
    List.map_map]
  exact (sum_filter_list (P a) (fun c => u a * w c) (List.range 78)).symm

theorem fsum_eq (U V : List ℕ) (i : ℕ) :
    fsum (ptK U i) (ptK V i) = (formPairs.map fun p => ptN U i p.1 * ptN V i p.2).sum := by
  rw [formPairs, ← sum_pairsP]
  rfl

theorem bsum_apply_eq (U V : List ℕ) (i : ℕ) (k : Fin 78) :
    bsum (ptK U i) (ptK V i) k = ((brPairs k).map fun p => ptN U i p.1 * ptN V i p.2).sum := by
  rw [brPairs, ← sum_pairsP]
  simp only [bsum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  rw [brMask_eq a c c.2, CFSG.Monster.Existence.StdOdd.Cert.mPt, mul_ite, mul_one, mul_zero]
  rfl

theorem eqB_iff_ptK {U V : List ℕ} (hU : lenN U = 156) (hV : lenN V = 156) (i : ℕ) :
    eqB U V i = true ↔ ptK U i = ptK V i := by
  rw [eqB_iff hU hV]
  exact ⟨ptB_inj, ptK_inj⟩

theorem fz_iff {U V : List ℕ} (i : ℕ) :
    ((f4acc (false, false) U V i (pairsOf 6084 Form.fmPk)).1 ||
      (f4acc (false, false) U V i (pairsOf 6084 Form.fmPk)).2) = true ↔
      fsum (ptK U i) (ptK V i) ≠ 0 := by
  rw [or_iff_ofBits, f4acc_ofBits, fm_ok, fsum_eq, ofBits_false, zero_add]

theorem anyB_iff {U V : List ℕ} (i : ℕ) :
    anyB U V i Form.brPk = true ↔ bsum (ptK U i) (ptK V i) ≠ 0 := by
  have e : anyB U V i Form.brPk = ((Form.brPk.map (pairsOf 6084)).any fun ps =>
      (f4acc (false, false) U V i ps).1 || (f4acc (false, false) U V i ps).2) := by
    rw [anyB, List.any_map]
    rfl
  rw [e, br_ok, List.any_map, List.any_eq_true]
  constructor
  · rintro ⟨k, hk, h⟩ h0
    have h' := (or_iff_ofBits _).1 h
    rw [f4acc_ofBits, ofBits_false, zero_add] at h'
    apply h'
    have := congrFun h0 ⟨k, List.mem_range.1 hk⟩
    rw [bsum_apply_eq] at this
    exact this
  · intro h
    by_contra hall
    apply h
    funext k
    have := hall
    simp only [not_exists, not_and, Bool.not_eq_true] at this
    have hk := this k (List.mem_range.2 k.2)
    rw [Function.comp_apply] at hk
    have h2 : ¬ ((f4acc (false, false) U V i (brPairs k)).1 ||
        (f4acc (false, false) U V i (brPairs k)).2) = true := by rw [hk]; decide
    rw [or_iff_ofBits, not_not, f4acc_ofBits, ofBits_false, zero_add] at h2
    rw [bsum_apply_eq, h2]
    rfl

theorem rhoB_eq {U V : List ℕ} (hU : lenN U = 156) (hV : lenN V = 156) (i : ℕ) :
    rhoB U V i Form.fmPk Form.brPk = rhoC (ptK U i) (ptK V i) := by
  unfold rhoB rhoC
  by_cases h1 : ptK U i = ptK V i
  · rw [ite_eq_left ((eqB_iff_ptK hU hV i).2 h1), ite_eq_left h1]
  rw [ite_eq_right (mt (eqB_iff_ptK hU hV i).1 h1), ite_eq_right h1]
  by_cases h2 : fsum (ptK U i) (ptK V i) ≠ 0
  · rw [ite_eq_left ((fz_iff i).2 h2), ite_eq_left h2]
  rw [ite_eq_right (mt (fz_iff i).1 h2), ite_eq_right h2]
  by_cases h3 : bsum (ptK U i) (ptK V i) ≠ 0
  · rw [ite_eq_left ((anyB_iff i).2 h3), ite_eq_left h3]
  · rw [ite_eq_right (mt (anyB_iff i).1 h3), ite_eq_right h3]

end CFSG.KD.StdOdd.Cent

end
