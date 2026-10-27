module

public import CFSG.Certificates.Kernel.L43Q8.Sound
public import CFSG.Certificates.Kernel.ArrBfsCert
public import Certificates.Kernel.L43Q8.Pts
import CFSG.Certificates.Kernel.PackSetSound
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelL43Q8

open CFSG.KD.L43Q8 CFSG.KS.L43Q8 CFSG.KS.ArrBfsSim CFSG.Monster.B.Fischer
open CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.Loc Certificates.L43TwinQ8

theorem ptAll : ∀ i < 512, ptQ 4 512 G T E PA LA SO SOI i = true := by
  have hb : ∀ q < 8, l43q8Blk q = true := by
    intro q hq
    interval_cases q
    exacts [l43q8Blk0, l43q8Blk1, l43q8Blk2, l43q8Blk3, l43q8Blk4, l43q8Blk5, l43q8Blk6,
      l43q8Blk7]
  intro i hi
  have h := hb (i / 64) (by omega)
  unfold l43q8Blk blkQ at h
  have e := CFSG.KC.Pack.allBlk_spec h (i % 64) (Nat.mod_lt _ (by norm_num))
  rw [CFSG.KC.Pack.strictB_eq] at e
  have hi' : Nat.add (Nat.mul 64 (i / 64)) (i % 64) = i := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  rwa [hi'] at e

theorem prAll : ∀ a < 56, ∀ b < 56,
    pairQ Q1AQ Q1BQ Q2AQ Q2BQ WCQ (T (II a)) (T (II b)) = true := by
  have hb : ∀ q < 14, l43q8Pr q = true := by
    intro q hq
    interval_cases q
    exacts [l43q8Pr0, l43q8Pr1, l43q8Pr2, l43q8Pr3, l43q8Pr4, l43q8Pr5, l43q8Pr6, l43q8Pr7,
      l43q8Pr8, l43q8Pr9, l43q8Pr10, l43q8Pr11, l43q8Pr12, l43q8Pr13]
  intro a ha b hb'
  have h := hb (a / 4) (by omega)
  unfold l43q8Pr at h
  have e := CFSG.KC.Pack.allBlk_spec h (a % 4) (Nat.mod_lt _ (by norm_num))
  have ha' : Nat.add (Nat.mul 4 (a / 4)) (a % 4) = a := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  rw [ha'] at e
  simp only [CFSG.KC.Pack.strictB_eq] at e
  have e2 := CFSG.KC.Pack.allBlk_spec e b hb'
  simp only [Nat.add_eq, Nat.zero_add, CFSG.KC.Pack.strictB_eq] at e2
  exact e2

theorem sqL : (List.range 512).filter (fun i => eqQ (mulQ (T i) (T i)) T0Q) =
    (List.range 56).map II := eq_of_beq sqB

theorem gensEq : ∀ k < 4, gens[k]! = dec (G k) := by decide +kernel

theorem t0_eq : t0 = dec T0Q := by decide +kernel

theorem q1a_eq : q1a = dec Q1AQ := by decide +kernel

theorem q1b_eq : q1b = dec Q1BQ := by decide +kernel

theorem q2a_eq : q2a = dec Q2AQ := by decide +kernel

theorem q2b_eq : q2b = dec Q2BQ := by decide +kernel

theorem wc_eq : wc = dec WCQ := by decide +kernel

theorem bfs_eq : bfs () = cert 4 512 (fun i => dec (T i)) E PA LA := by
  have hsz : gens.size = 4 := rfl
  obtain ⟨Tb, -, h0⟩ := tables_of (n := 4) (N := 512) (by norm_num) gensEq ptAll
  unfold bfs
  rw [hsz, ← h0]
  exact arrBfs_eq Tb (by norm_num)

theorem II_lt {a : ℕ} (ha : a < 56) : II a < 512 := by
  have h : II a ∈ (List.range 512).filter (fun i => eqQ (mulQ (T i) (T i)) T0Q) := by
    rw [sqL]
    exact List.mem_map.2 ⟨a, List.mem_range.2 ha, rfl⟩
  exact List.mem_range.1 (List.mem_filter.1 h).1

theorem pairsOK_true : pairsOK (cert 4 512 (fun i => dec (T i)) E PA LA).pts = true := by
  have hget : ∀ i < 512, (cert 4 512 (fun i => dec (T i)) E PA LA).pts[i]! = dec (T i) :=
    fun i hi => cert_pts_get hi
  have hf : (List.range 512).filter (fun i => eltEq 4 (eltMul 4
      (cert 4 512 (fun i => dec (T i)) E PA LA).pts[i]!
      (cert 4 512 (fun i => dec (T i)) E PA LA).pts[i]!) t0) = (List.range 56).map II := by
    rw [← sqL]
    apply List.filter_congr
    intro i hi
    rw [hget i (List.mem_range.1 hi), mul_dec, t0_eq, eq_dec']
  unfold pairsOK
  dsimp only
  rw [cert_pts_size, hf]
  simp only [List.all_eq_true, List.mem_map, List.mem_range, forall_exists_index, and_imp]
  rintro _ a ha rfl _ b hb rfl
  rw [hget _ (II_lt ha), hget _ (II_lt hb), pairOK_dec q1a_eq q1b_eq q2a_eq q2b_eq wc_eq]
  exact prAll a ha b hb

theorem gensValid : (List.range 4).all (fun k => eltValid 4 gens[k]!) = true := by
  rw [allC (g := fun k => validQ (G k)) fun k hk => by
    rw [gensEq k (List.mem_range.1 hk), valid_dec]]
  decide +kernel

theorem gensComm : (List.range 4).all (fun k => commutes gens[k]! t0) = true := by
  rw [allC (g := fun k => commQ (G k) T0Q) fun k hk => by
    rw [gensEq k (List.mem_range.1 hk), t0_eq, commutes_dec]]
  decide +kernel

theorem validC : eltValid 4 t0 = true ∧ eltValid 4 q1a = true ∧ eltValid 4 q1b = true ∧
    eltValid 4 q2a = true ∧ eltValid 4 q2b = true ∧ eltValid 4 wc = true := by
  rw [t0_eq, q1a_eq, q1b_eq, q2a_eq, q2b_eq, wc_eq, valid_dec, valid_dec, valid_dec, valid_dec,
    valid_dec, valid_dec]
  decide +kernel

theorem wcC : (eE 4 wc == 0) = true ∧ inF4 wc = true ∧ commutes wc t0 = true := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  rw [wc_eq, t0_eq, commutes_dec]
  decide +kernel

theorem check_true : check () = true := by
  have hsz : gens.size = 4 := rfl
  obtain ⟨Tb, hv, h0⟩ := tables_of (n := 4) (N := 512) (by norm_num) gensEq ptAll
  have hok := arrCertOK_cert Tb hv h0
  have hpsz : ((cert 4 512 (fun i => dec (T i)) E PA LA).pts.size == 2 ^ 9) = true := by
    rw [cert_pts_size]
    rfl
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := validC
  obtain ⟨w1, w2, w3⟩ := wcC
  unfold check
  dsimp only
  rw [bfs_eq, hsz]
  simp only [gensValid, hok, hpsz, v1, v2, v3, v4, v5, v6, w1, w2, w3, gensComm, pairsOK_true,
    Bool.and_self]

end CertificateChecks.KernelL43Q8

end
