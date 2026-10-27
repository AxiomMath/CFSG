module

public import Certificates.Data.U43TwinCheck
public import CFSG.Certificates.Kernel.U43Twin.Sound
public import CFSG.Certificates.Kernel.ArrBfsCert
public import Certificates.Kernel.U43Twin.OrbPts
public import Certificates.Kernel.U43Twin.CPts
import CFSG.Certificates.Kernel.PackSetSound
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelU43Twin

open CFSG.KD.U43Pk CFSG.KD.U43Twin CFSG.KS.U43Pk CFSG.KS.U43Twin CFSG.KS.ArrBfsSim
open CFSG.Monster.B.Fischer CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43.Check
open Certificates.U43Twin

theorem gIV : ∀ k < 2, rawValidK (GI k) = true := by decide +kernel

theorem gIiV : ∀ k < 2, rawValidK (GIi k) = true := by decide +kernel

theorem gCV : ∀ k < 2, rawValidK (GC k) = true := by decide +kernel

theorem gTV : ∀ k < 3, rawValidK (GT k) = true := by decide +kernel

theorem T0V : rawValidK T0K = true := by decide +kernel

theorem gIEq : ∀ k < 2, gI[k]! = dec (GI k) := by decide +kernel

theorem gIinvEq : ∀ k < 2, gIinv[k]! = dec (GIi k) := by decide +kernel

theorem gCEq : ∀ k < 2, gC[k]! = dec (GC k) := by decide +kernel

theorem gTEq : ∀ k < 3, gT[k]! = dec (GT k) := by decide +kernel

theorem T0Eq : T0 = dec T0K := by decide +kernel

theorem gIShape : ∀ k < 2, innerShape gI[k]! = true := by decide +kernel

theorem gCShape : ∀ k < 2, innerShape gC[k]! = true := by decide +kernel

theorem gTShape : ∀ k < 3, innerShape gT[k]! = true := by decide +kernel

theorem gIZ : ∀ k < 2, isZ (dec (mulK (GI k) (GIi k))) = true := by decide +kernel

theorem gCComm : ∀ k < 2, Nat.beq (nrmK (mulK (GC k) T0K)) (nrmK (mulK T0K (GC k))) = true := by
  decide +kernel

theorem T0Dig : Dig T0K := (rawValidK_spec T0V).2.1

theorem orbAll : ∀ i < 2835, ptAK 2 2835 orbA T0K OT OE OPA OLA OSO OSOI i = true := by
  have hb : ∀ q < 45, ch397503orb q = true := by
    intro q hq
    interval_cases q
    exacts [ch397503orb0, ch397503orb1, ch397503orb2, ch397503orb3, ch397503orb4, ch397503orb5,
      ch397503orb6, ch397503orb7, ch397503orb8, ch397503orb9, ch397503orb10, ch397503orb11,
      ch397503orb12, ch397503orb13, ch397503orb14, ch397503orb15, ch397503orb16, ch397503orb17,
      ch397503orb18, ch397503orb19, ch397503orb20, ch397503orb21, ch397503orb22, ch397503orb23,
      ch397503orb24, ch397503orb25, ch397503orb26, ch397503orb27, ch397503orb28, ch397503orb29,
      ch397503orb30, ch397503orb31, ch397503orb32, ch397503orb33, ch397503orb34, ch397503orb35,
      ch397503orb36, ch397503orb37, ch397503orb38, ch397503orb39, ch397503orb40, ch397503orb41,
      ch397503orb42, ch397503orb43, ch397503orb44]
  intro i hi
  have h := hb (i / 63) (by omega)
  unfold ch397503orb blkAK at h
  have e := CFSG.KC.Pack.allBlk_spec h (i % 63) (Nat.mod_lt _ (by norm_num))
  rw [CFSG.KC.Pack.strictB_eq] at e
  have hi' : Nat.add (Nat.mul 63 (i / 63)) (i % 63) = i := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  rwa [hi'] at e

theorem cAll : ∀ i < 1152, ptK 2 1152 GC CT CE CPA CLA CSO CSOI i = true := by
  have hb : ∀ q < 18, ch397503c q = true := by
    intro q hq
    interval_cases q
    exacts [ch397503c0, ch397503c1, ch397503c2, ch397503c3, ch397503c4, ch397503c5, ch397503c6,
      ch397503c7, ch397503c8, ch397503c9, ch397503c10, ch397503c11, ch397503c12, ch397503c13,
      ch397503c14, ch397503c15, ch397503c16, ch397503c17]
  intro i hi
  have h := hb (i / 64) (by omega)
  unfold ch397503c blkK at h
  have e := CFSG.KC.Pack.allBlk_spec h (i % 64) (Nat.mod_lt _ (by norm_num))
  rw [CFSG.KC.Pack.strictB_eq] at e
  have hi' : Nat.add (Nat.mul 64 (i / 64)) (i % 64) = i := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  rwa [hi'] at e

theorem tAll : ∀ i < 128, ptK 3 128 GT TT TE TPA TLA TSO TSOI i = true := by
  have hb : ∀ q < 2, ch397503t q = true := by
    intro q hq
    interval_cases q
    exacts [ch397503t0, ch397503t1]
  intro i hi
  have h := hb (i / 64) (by omega)
  unfold ch397503t blkK at h
  have e := CFSG.KC.Pack.allBlk_spec h (i % 64) (Nat.mod_lt _ (by norm_num))
  rw [CFSG.KC.Pack.strictB_eq] at e
  have hi' : Nat.add (Nat.mul 64 (i / 64)) (i % 64) = i := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  rwa [hi'] at e

theorem dig_of {P : ℕ} (h : rawValidK P = true) : Dig P := (rawValidK_spec h).2.1

theorem commC_of {X Y : ℕ} (hX : Dig X) (hY : Dig Y) (h : Nat.beq (nrmK (mulK X Y)) (nrmK (mulK Y X)) = true) :
    commC (dec X) (dec Y) = true := by
  unfold commC eqZ
  rw [mulRaw_dec hX hY, mulRaw_dec hY hX, normalize_dec (mulK_dig hX hY),
    normalize_dec (mulK_dig hY hX), Nat.eq_of_beq_eq_true h]
  simp

theorem actConj_eq : ∀ k < 2, ∀ P, rawValidK P = true → actConj k (dec P) = dec (orbA k P) := by
  intro k hk P hP
  unfold actConj orbA
  rw [gIEq k hk, gIinvEq k hk]
  exact cjK_dec (dig_of (gIV k hk)) (dig_of (gIiV k hk)) (dig_of hP)

theorem orbOK_true : orbOK () = true := by
  have hsz : gI.size = 2 := rfl
  obtain ⟨Tb, hv, h0⟩ := tablesA_of (by norm_num) actConj_eq orbAll
  have h0' : T0 = dec (OT 0) := by rw [h0, T0Eq]
  have hbfs : orbCert () = cert 2 2835 (fun i => dec (OT i)) OE OPA OLA := by
    unfold orbCert
    rw [hsz, h0']
    exact arrBfs_eq Tb (by norm_num)
  have hok := arrCertOK_cert Tb hv h0'.symm
  unfold orbOK
  rw [hbfs, hsz]
  dsimp only
  rw [cert_pts_size]
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq]
  refine ⟨fun k hk => ⟨⟨⟨?_, ?_⟩, gIShape k hk⟩, ?_⟩, hok, trivial⟩
  · rw [gIEq k hk]
    exact rawValid_dec (gIV k hk)
  · rw [gIinvEq k hk]
    exact rawValid_dec (gIiV k hk)
  · rw [gIEq k hk, gIinvEq k hk, mulRaw_dec (dig_of (gIV k hk)) (dig_of (gIiV k hk))]
    exact gIZ k hk

theorem cOK_true : cOK () = true := by
  have hsz : gC.size = 2 := rfl
  obtain ⟨Tb, hv, h0⟩ := tables_of (n := 2) (N := 1152) (by norm_num) gCEq gCV cAll
  have hbfs : cCert () = cert 2 1152 (fun i => dec (CT i)) CE CPA CLA := by
    unfold cCert
    rw [hsz, ← h0]
    exact arrBfs_eq Tb (by norm_num)
  have hok := arrCertOK_cert Tb hv h0
  unfold cOK
  rw [hbfs, hsz]
  dsimp only
  rw [cert_pts_size]
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq]
  refine ⟨fun k hk => ⟨⟨?_, gCShape k hk⟩, ?_⟩, hok, trivial⟩
  · rw [gCEq k hk]
    exact rawValid_dec (gCV k hk)
  · rw [gCEq k hk, T0Eq]
    exact commC_of (dig_of (gCV k hk)) T0Dig (gCComm k hk)

theorem tOK_true : tOK () = true := by
  have hsz : gT.size = 3 := rfl
  obtain ⟨Tb, hv, h0⟩ := tables_of (n := 3) (N := 128) (by norm_num) gTEq gTV tAll
  have hbfs : tCert () = cert 3 128 (fun i => dec (TT i)) TE TPA TLA := by
    unfold tCert
    rw [hsz, ← h0]
    exact arrBfs_eq Tb (by norm_num)
  have hok := arrCertOK_cert Tb hv h0
  unfold tOK
  rw [hbfs, hsz]
  dsimp only
  rw [cert_pts_size]
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq]
  refine ⟨fun k hk => ⟨?_, gTShape k hk⟩, hok, trivial⟩
  rw [gTEq k hk]
  exact rawValid_dec (gTV k hk)

end CertificateChecks.KernelU43Twin

end
